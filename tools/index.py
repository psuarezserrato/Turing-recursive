#!/usr/bin/env python3
"""
tools/index.py — Pure-Python BM25 Premise & Accepted-Proof Index for Turing-recursive

Indexes declarations (signature + docstring + file path) from:
  - Pinned Mathlib under `.lake/packages/mathlib/Mathlib/{Computability,Data/List,Data/Option,Logic,Order}`
  - Project sources under `TuringRecursive/` and `TuringRecursive.lean`
  - Verified proofs in `data/accepted.jsonl` (built from `.agents/gemma_accepted/*.lean`,
    sorry-free `TuringRecursive/` lemmas, and pinned `Mathlib/Computability` proofs).

Provides both a CLI (`build`, `query`, `query-proofs`) and a Python API used by `tools/gemma_loop.py`,
with `--exclude <decl list>` to hide target declarations and near-duplicates during calibration.
"""

import argparse
import bisect
from collections import Counter, defaultdict
import json
import math
import os
import pickle
import re
import subprocess
import sys
import time
from pathlib import Path
from typing import Any, Dict, Iterable, List, Optional, Sequence, Set, Tuple

DEFAULT_MATHLIB_SUBDIRS = (
    "Mathlib/Computability",
    "Mathlib/Data/List",
    "Mathlib/Data/Option",
    "Mathlib/Logic",
    "Mathlib/Order",
)

STOPWORDS = {
    "and", "or", "not", "the", "a", "an", "of", "in", "to", "for", "is",
    "by", "let", "have", "def", "theorem", "lemma", "fun", "with", "from",
}

LEAN_IDENT_CHARS = r"A-Za-z0-9_'\.!\?₀-₉₊₋₌₍₎ₐₑₒₓₔₕₖₗₘₙₚₛₜ¹²³⁴⁵⁶⁷⁸⁹⁰α-ωΑ-Ωℝℚℤℕ"

DECL_START_RE = re.compile(
    r"^[ \t]*(?:@\[[^\]]*\]\s*)*(?:(?:private|protected|noncomputable|scoped|local)\s+)*"
    r"(theorem|lemma|def|abbrev|instance|structure|class|inductive)\s+(["
    + LEAN_IDENT_CHARS
    + r"]+)",
    re.MULTILINE,
)

CMD_BOUNDARY_RE = re.compile(
    r"^[ \t]*(?:/--[\s\S]*?-\/\s*)*(?:@\[[^\]]+\]\s*)*"
    r"(?:(?:private|protected|noncomputable|scoped|local|partial|unsafe)\s+)*"
    r"(?:theorem|lemma|def|abbrev|structure|class|inductive|coinductive|instance|example|axiom|opaque|mutual|"
    r"set_option|attribute|register_simp_attr|register_builtin_option|register_option|"
    r"open|namespace|section|end|variable|variables|universe|universes|export|import|public|meta|"
    r"macro|macro_rules|syntax|elab|elab_rules|notation|infix|infixl|infixr|prefix|postfix|simproc|"
    r"initialize|builtin_initialize|deriving|assert_not_exists|"
    r"#\w+)\b",
    re.MULTILINE,
)

SCOPE_CMD_RE = re.compile(
    r"^[ \t]*(?:@\[[^\]]+\]\s*)*(?:public\s+|meta\s+)*(namespace|section|end)(?:[ \t]+(["
    + LEAN_IDENT_CHARS
    + r"]+))?[ \t]*$",
    re.MULTILINE,
)

SORRY_TOKEN_RE = re.compile(r"\b(?:sorry|sorryAx|admit|axiom)\b")


def _git_common_repo_root(start_dir: Path) -> Path:
    """Resolve the shared main repository root via git-common-dir, or return `start_dir`."""
    try:
        raw = subprocess.check_output(
            ["git", "-C", str(start_dir), "rev-parse", "--git-common-dir"],
            stderr=subprocess.DEVNULL,
            text=True,
            timeout=2.0,
        ).strip()
        if raw:
            p = Path(raw)
            p = (start_dir / p).resolve() if not p.is_absolute() else p.resolve()
            if p.name == ".git":
                return p.parent
    except Exception:
        pass
    return start_dir


def resolve_repo_root(root_arg: Optional[str] = None) -> Path:
    """Resolve worktree or repository root."""
    if root_arg:
        return Path(root_arg).resolve()
    env_root = os.environ.get("TURING_RECURSIVE_ROOT")
    if env_root and Path(env_root).is_dir():
        return Path(env_root).resolve()
    cwd = Path.cwd()
    if (cwd / "lakefile.toml").is_file():
        return cwd
    here_root = Path(__file__).resolve().parent.parent
    if (here_root / "lakefile.toml").is_file():
        return here_root
    return _git_common_repo_root(here_root)


def mask_comments_and_strings(content: str) -> str:
    """Character-offset-preserving masker for Lean 4 comments (`--`, `/- ... -/`) and strings."""
    result = list(content)
    n = len(content)
    i = 0
    while i < n:
        ch = content[i]
        if ch == '"':
            start = i
            i += 1
            while i < n and content[i] != '"':
                if content[i] == "\\" and i + 1 < n:
                    i += 2
                else:
                    i += 1
            if i < n:
                i += 1
            for k in range(start, i):
                if result[k] != "\n":
                    result[k] = " "
        elif ch == "-" and i + 1 < n and content[i + 1] == "-":
            j = content.find("\n", i + 2)
            if j == -1:
                j = n
            for k in range(i, j):
                result[k] = " "
            i = j
        elif ch == "/" and i + 1 < n and content[i + 1] == "-":
            depth = 1
            start = i
            i += 2
            while i < n and depth > 0:
                if content[i] == "/" and i + 1 < n and content[i + 1] == "-":
                    depth += 1
                    i += 2
                elif content[i] == "-" and i + 1 < n and content[i + 1] == "/":
                    depth -= 1
                    i += 2
                else:
                    i += 1
            for k in range(start, i):
                if result[k] != "\n":
                    result[k] = " "
        else:
            i += 1
    return "".join(result)


def find_top_level_assign(masked_chunk: str, max_scan: int = 4000) -> int:
    """Find index of top-level `:=` or `where` at bracket depth 0, or -1."""
    p_depth = b_depth = c_depth = a_depth = 0
    n = min(len(masked_chunk), max_scan)
    i = 0
    while i < n:
        ch = masked_chunk[i]
        if ch == "(":
            p_depth += 1
        elif ch == ")":
            p_depth = max(0, p_depth - 1)
        elif ch == "[":
            b_depth += 1
        elif ch == "]":
            b_depth = max(0, b_depth - 1)
        elif ch == "{":
            c_depth += 1
        elif ch == "}":
            c_depth = max(0, c_depth - 1)
        elif ch in ("⟨", "⦃"):
            a_depth += 1
        elif ch in ("⟩", "⦄"):
            a_depth = max(0, a_depth - 1)
        elif (p_depth + b_depth + c_depth + a_depth) == 0:
            if ch == ":" and i + 1 < len(masked_chunk) and masked_chunk[i + 1] == "=":
                return i
            if masked_chunk[i:i + 5] == "where" and (i == 0 or not masked_chunk[i - 1].isalnum()):
                after = i + 5
                if after == len(masked_chunk) or not masked_chunk[after].isalnum():
                    return i
        i += 1
    return -1


def tokenize_lean(text: str) -> List[str]:
    """Tokenize Lean 4 identifiers, types, and docstrings (splitting camelCase & snake_case)."""
    if not text:
        return []
    cleaned = re.sub(r"[.\-_/:;()\[\]{}⟨⟩,`'\"]", " ", text)
    cleaned = re.sub(r"([a-z0-9])([A-Z])", r"\1 \2", cleaned)
    raw_tokens = re.findall(r"[A-Za-z0-9ℕℤℚℝΓΛσ]+", cleaned.lower())
    return [t for t in raw_tokens if len(t) >= 2 and t not in STOPWORDS]


def _build_namespace_timeline(masked: str) -> List[Tuple[int, str]]:
    """Build sorted list of `(char_offset, active_namespace_prefix)` across a Lean file."""
    stack: List[Tuple[str, List[str]]] = []
    timeline: List[Tuple[int, str]] = [(0, "")]
    for m in SCOPE_CMD_RE.finditer(masked):
        cmd = m.group(1)
        arg = (m.group(2) or "").strip()
        if cmd == "namespace":
            parts = [p for p in arg.split(".") if p]
            stack.append(("namespace", parts))
        elif cmd == "section":
            stack.append(("section", [arg] if arg else []))
        elif cmd == "end":
            if stack:
                stack.pop()
        ns_parts: List[str] = []
        for kind, parts in stack:
            if kind == "namespace":
                ns_parts.extend(parts)
        timeline.append((m.end(), ".".join(ns_parts)))
    return timeline


def _namespace_at(timeline: List[Tuple[int, str]], offset: int) -> str:
    idx = bisect.bisect_right(timeline, (offset, "\uffff")) - 1
    if idx >= 0:
        return timeline[idx][1]
    return ""


def _clean_trailing_comments(text: str) -> str:
    """Strip trailing comments and empty lines from a proof body."""
    lines = text.splitlines()
    while lines:
        last = lines[-1].strip()
        if not last or last.startswith("--"):
            lines.pop()
        else:
            break
    res = "\n".join(lines).rstrip()
    while res.endswith("-/"):
        start = res.rfind("/-")
        if start == -1:
            break
        res = res[:start].rstrip()
    return res.strip()


def extract_declarations_from_file(
    fpath: Path,
    repo_root: Path,
    origin: str = "mathlib",
) -> Tuple[List[Dict[str, Any]], List[Dict[str, Any]]]:
    """
    Parse a `.lean` file and extract `(declarations, accepted_proofs)`.
    Skips `private` declarations and declarations containing `sorry`.
    """
    declarations: List[Dict[str, Any]] = []
    proofs: List[Dict[str, Any]] = []
    try:
        content = fpath.read_text(encoding="utf-8", errors="ignore")
    except Exception:
        return declarations, proofs
    if not content:
        return declarations, proofs

    try:
        rel_file = str(fpath.resolve().relative_to(repo_root.resolve()))
    except ValueError:
        rel_file = str(fpath)

    # Derive module name
    if "Mathlib/" in rel_file:
        mod_part = rel_file[rel_file.index("Mathlib/"):]
    else:
        mod_part = rel_file
    mod_name = mod_part[:-5].replace("/", ".") if mod_part.endswith(".lean") else mod_part

    masked = mask_comments_and_strings(content)
    ns_timeline = _build_namespace_timeline(masked)

    cmd_starts = [m.start() for m in CMD_BOUNDARY_RE.finditer(masked)]
    doc_starts = [m.start() for m in re.finditer(r"^[ \t]*/-!", content, re.MULTILINE)]
    boundaries = sorted(set(cmd_starts + doc_starts + [len(content)]))

    for m in DECL_START_RE.finditer(masked):
        header_text = content[m.start():m.end()]
        if re.search(r"\bprivate\b", header_text):
            continue

        kind = m.group(1)
        raw_name = m.group(2)
        start = m.start()

        b_idx = bisect.bisect_right(boundaries, start)
        next_b = boundaries[b_idx] if b_idx < len(boundaries) else len(content)

        chunk = content[start:next_b]
        chunk_m = masked[start:next_b]

        if SORRY_TOKEN_RE.search(chunk_m):
            continue

        assign_idx = find_top_level_assign(chunk_m)
        if assign_idx == -1:
            raw_sig = chunk.strip()
            raw_proof = ""
        else:
            raw_sig = chunk[:assign_idx].strip()
            if chunk_m[assign_idx:assign_idx + 2] == ":=":
                raw_proof = _clean_trailing_comments(chunk[assign_idx + 2:])
            else:
                raw_proof = ""

        if not raw_sig or len(raw_sig) > 2500:
            continue

        # Extract docstring immediately preceding declaration
        prefix = content[:start].rstrip()
        doc = ""
        if prefix.endswith("-/"):
            doc_start = prefix.rfind("/--")
            if doc_start != -1 and doc_start > prefix.rfind("/-!"):
                doc = prefix[doc_start + 3:-2].strip()

        active_ns = _namespace_at(ns_timeline, start)
        if active_ns and not raw_name.startswith(active_ns + "."):
            full_name = f"{active_ns}.{raw_name}"
        else:
            full_name = raw_name
        short_name = raw_name.rsplit(".", 1)[-1]

        compact_sig = re.sub(r"\s+", " ", raw_sig).strip()
        if kind in ("def", "abbrev") and raw_proof and len(raw_proof) <= 240:
            compact_rhs = re.sub(r"\s+", " ", raw_proof).strip()
            compact_sig = f"{compact_sig} := {compact_rhs}"
        compact_type = re.sub(
            r"^(?:@\[[^\]]*\]\s*)*(?:(?:private|protected|noncomputable|scoped|local)\s+)*"
            r"(?:theorem|lemma|def|abbrev|instance|structure|class|inductive)\s+[A-Za-z0-9_'\.]+\s*",
            "",
            compact_sig,
        ).strip()

        decl_rec = {
            "name": full_name,
            "raw_name": raw_name,
            "short_name": short_name,
            "kind": kind,
            "signature": compact_sig,
            "type": compact_type[:1200],
            "doc": re.sub(r"\s+", " ", doc)[:400] if doc else "",
            "module": mod_name,
            "file": rel_file,
        }
        declarations.append(decl_rec)

        if kind in ("theorem", "lemma", "def") and raw_proof and len(raw_proof) <= 2400:
            proofs.append({
                "name": full_name,
                "raw_name": raw_name,
                "short_name": short_name,
                "kind": kind,
                "signature": raw_sig,
                "proof": raw_proof,
                "doc": re.sub(r"\s+", " ", doc)[:300] if doc else "",
                "module": mod_name,
                "file": rel_file,
                "origin": origin,
            })

    return declarations, proofs


def normalize_exclusion_set(exclude: Optional[Iterable[str]]) -> Set[str]:
    """Expand comma-separated or list exclusions into normalized lowercase tokens."""
    out: Set[str] = set()
    if not exclude:
        return out
    for item in exclude:
        if not item:
            continue
        for part in str(item).split(","):
            clean = part.strip()
            if clean:
                out.add(clean)
                out.add(clean.lower())
    return out


def is_declaration_excluded(
    doc: Dict[str, Any],
    exclude_set: Set[str],
    hide_near_duplicates: bool = True,
) -> bool:
    """
    Check if `doc` matches any name in `exclude_set` or is an obvious near-duplicate
    (e.g., primed variant `foo'`, `_aux`, or suffix/prefix match).
    """
    if not exclude_set:
        return False

    candidates = [
        doc.get("name", ""),
        doc.get("raw_name", ""),
        doc.get("short_name", ""),
    ]
    for c in candidates:
        if not c:
            continue
        cl = c.lower()
        if c in exclude_set or cl in exclude_set:
            return True
        for ex in exclude_set:
            ex_l = ex.lower()
            if cl.endswith("." + ex_l) or ex_l.endswith("." + cl):
                # Only treat short-name suffix match as excluded if ex had no dot or matches last 2 segments
                if "." in ex_l or cl == ex_l or doc.get("short_name", "").lower() == ex_l:
                    return True
            if hide_near_duplicates:
                base_c = cl.rstrip("'")
                base_ex = ex_l.rstrip("'")
                for suffix in ("_aux", "_1", "_2", "₁", "₂"):
                    if base_c.endswith(suffix):
                        base_c = base_c[:-len(suffix)]
                    if base_ex.endswith(suffix):
                        base_ex = base_ex[:-len(suffix)]
                if base_c and base_c == base_ex:
                    return True
                if "." in base_c and base_c.endswith("." + base_ex):
                    return True
    return False


class InvertedBM25:
    """Pure-Python BM25Okapi inverted index."""

    def __init__(self, k1: float = 1.5, b: float = 0.75):
        self.k1 = k1
        self.b = b
        self.corpus_size: int = 0
        self.avg_doc_len: float = 0.0
        self.doc_lens: List[int] = []
        self.doc_len_factors: List[float] = []
        self.idf: Dict[str, float] = {}
        self.postings: Dict[str, List[Tuple[int, int]]] = defaultdict(list)
        self.documents: List[Dict[str, Any]] = []

    def fit(self, documents: List[Dict[str, Any]]) -> None:
        self.documents = documents
        self.corpus_size = len(documents)
        if self.corpus_size == 0:
            return

        total_len = 0
        doc_freqs: Counter = Counter()
        self.doc_lens = []
        self.postings = defaultdict(list)

        for idx, doc in enumerate(documents):
            name_boost = f"{doc.get('name', '')} {doc.get('raw_name', '')} {doc.get('short_name', '')} " * 3
            body = f"{name_boost} {doc.get('signature', '')} {doc.get('type', '')} {doc.get('doc', '')} {doc.get('module', '')}"
            tokens = tokenize_lean(body)
            dlen = max(1, len(tokens))
            self.doc_lens.append(dlen)
            total_len += dlen

            counts = Counter(tokens)
            for term, tf in counts.items():
                self.postings[term].append((idx, tf))
                doc_freqs[term] += 1

        self.avg_doc_len = total_len / self.corpus_size
        k1_b = self.k1 * self.b / self.avg_doc_len
        k1_1_b = self.k1 * (1.0 - self.b)
        self.doc_len_factors = [k1_1_b + k1_b * dl for dl in self.doc_lens]

        self.idf = {}
        for term, df in doc_freqs.items():
            self.idf[term] = math.log((self.corpus_size - df + 0.5) / (df + 0.5) + 1.0)

    def search(
        self,
        query_text: str,
        top_k: int = 8,
        exclude: Optional[Iterable[str]] = None,
        hide_near_duplicates: bool = True,
    ) -> List[Dict[str, Any]]:
        if not query_text or self.corpus_size == 0:
            return []
        q_tokens = tokenize_lean(query_text)
        if not q_tokens:
            return []

        exclude_set = normalize_exclusion_set(exclude)
        scores: Dict[int, float] = defaultdict(float)
        k1_p1 = self.k1 + 1.0

        unique_terms = set(q_tokens)
        scored_terms = sorted(
            [(t, self.idf[t]) for t in unique_terms if t in self.postings],
            key=lambda x: -x[1],
        )

        for term, idf_val in scored_terms[:16]:
            plist = self.postings[term]
            num_factor = idf_val * k1_p1
            for doc_idx, tf in plist:
                scores[doc_idx] += (num_factor * tf) / (tf + self.doc_len_factors[doc_idx])

        if not scores:
            return []

        ranked = sorted(scores.items(), key=lambda x: -x[1])
        results: List[Dict[str, Any]] = []
        for doc_idx, sc in ranked:
            doc = self.documents[doc_idx]
            if is_declaration_excluded(doc, exclude_set, hide_near_duplicates=hide_near_duplicates):
                continue
            item = dict(doc)
            item["score"] = round(sc, 4)
            results.append(item)
            if len(results) >= top_k:
                break
        return results

    def to_dict(self) -> Dict[str, Any]:
        return {
            "k1": self.k1,
            "b": self.b,
            "corpus_size": self.corpus_size,
            "avg_doc_len": self.avg_doc_len,
            "doc_lens": self.doc_lens,
            "doc_len_factors": self.doc_len_factors,
            "idf": self.idf,
            "postings": dict(self.postings),
            "documents": self.documents,
        }

    @classmethod
    def from_dict(cls, data: Dict[str, Any]) -> "InvertedBM25":
        idx = cls(k1=data.get("k1", 1.5), b=data.get("b", 0.75))
        idx.corpus_size = data.get("corpus_size", 0)
        idx.avg_doc_len = data.get("avg_doc_len", 0.0)
        idx.doc_lens = data.get("doc_lens", [])
        idx.doc_len_factors = data.get("doc_len_factors", [])
        idx.idf = data.get("idf", {})
        idx.postings = defaultdict(list, data.get("postings", {}))
        idx.documents = data.get("documents", [])
        return idx


class RepositoryIndex:
    """Combined BM25 index over Mathlib + TuringRecursive premises and verified accepted proofs."""

    def __init__(self, premise_index: InvertedBM25, proof_index: InvertedBM25, repo_root: Path):
        self.premise_index = premise_index
        self.proof_index = proof_index
        self.repo_root = repo_root

    @staticmethod
    def default_cache_path(repo_root: Path) -> Path:
        return repo_root / ".agents" / "bm25_index.pkl"

    @staticmethod
    def default_accepted_jsonl_path(repo_root: Path) -> Path:
        return repo_root / "data" / "accepted.jsonl"

    @classmethod
    def build(
        cls,
        repo_root: Optional[Path] = None,
        mathlib_subdirs: Sequence[str] = DEFAULT_MATHLIB_SUBDIRS,
        write_accepted_jsonl: bool = True,
        accepted_jsonl_path: Optional[Path] = None,
        cache_path: Optional[Path] = None,
    ) -> "RepositoryIndex":
        root = resolve_repo_root(str(repo_root) if repo_root else None)
        mathlib_root = root / ".lake" / "packages" / "mathlib"
        if not mathlib_root.is_dir():
            common_root = _git_common_repo_root(root)
            if (common_root / ".lake" / "packages" / "mathlib").is_dir():
                mathlib_root = common_root / ".lake" / "packages" / "mathlib"

        all_decls: List[Dict[str, Any]] = []
        all_proofs: List[Dict[str, Any]] = []

        # 1. Scan pinned Mathlib subdirectories
        for subdir in mathlib_subdirs:
            target_dir = mathlib_root / subdir
            if not target_dir.is_dir():
                continue
            is_computability_or_list = (
                "Computability" in subdir or "Data/List" in subdir or "Data/Option" in subdir
            )
            for lf in sorted(target_dir.rglob("*.lean")):
                decls, prfs = extract_declarations_from_file(lf, mathlib_root, origin="mathlib")
                all_decls.extend(decls)
                if is_computability_or_list:
                    all_proofs.extend(prfs)

        # 2. Scan project's own TuringRecursive/ sources and TuringRecursive.lean
        proj_files: List[Path] = []
        if (root / "TuringRecursive.lean").is_file():
            proj_files.append(root / "TuringRecursive.lean")
        if (root / "TuringRecursive").is_dir():
            proj_files.extend(sorted((root / "TuringRecursive").rglob("*.lean")))
        for lf in proj_files:
            decls, prfs = extract_declarations_from_file(lf, root, origin="project")
            all_decls.extend(decls)
            all_proofs.extend(prfs)

        # 3. Scan verified .agents/gemma_accepted/*.lean proofs
        accepted_dir = root / ".agents" / "gemma_accepted"
        if accepted_dir.is_dir():
            for lf in sorted(accepted_dir.glob("*.lean")):
                decls, prfs = extract_declarations_from_file(lf, root, origin="gemma_accepted")
                all_decls.extend(decls)
                all_proofs.extend(prfs)

        # Also load any pre-existing entries from data/accepted.jsonl if present
        acc_path = Path(accepted_jsonl_path) if accepted_jsonl_path else cls.default_accepted_jsonl_path(root)
        seen_proof_names = {p["name"] for p in all_proofs}
        if acc_path.is_file():
            try:
                with open(acc_path, "r", encoding="utf-8") as f:
                    for line in f:
                        line = line.strip()
                        if not line:
                            continue
                        rec = json.loads(line)
                        if rec.get("name") and rec["name"] not in seen_proof_names:
                            all_proofs.append(rec)
                            seen_proof_names.add(rec["name"])
            except Exception:
                pass

        if write_accepted_jsonl:
            acc_path.parent.mkdir(parents=True, exist_ok=True)
            with open(acc_path, "w", encoding="utf-8") as f:
                for p in all_proofs:
                    f.write(json.dumps(p) + "\n")

        premise_idx = InvertedBM25()
        premise_idx.fit(all_decls)

        proof_idx = InvertedBM25()
        proof_idx.fit(all_proofs)

        cpath = Path(cache_path) if cache_path else cls.default_cache_path(root)
        try:
            cpath.parent.mkdir(parents=True, exist_ok=True)
            with open(cpath, "wb") as f:
                pickle.dump(
                    {
                        "premise_index": premise_idx.to_dict(),
                        "proof_index": proof_idx.to_dict(),
                    },
                    f,
                    protocol=pickle.HIGHEST_PROTOCOL,
                )
        except Exception:
            pass

        return cls(premise_idx, proof_idx, root)

    @classmethod
    def load_or_build(
        cls,
        repo_root: Optional[Path] = None,
        cache_path: Optional[Path] = None,
        write_accepted_jsonl: bool = False,
    ) -> "RepositoryIndex":
        root = resolve_repo_root(str(repo_root) if repo_root else None)
        cpath = Path(cache_path) if cache_path else cls.default_cache_path(root)
        if cpath.is_file():
            try:
                with open(cpath, "rb") as f:
                    data = pickle.load(f)
                return cls(
                    InvertedBM25.from_dict(data["premise_index"]),
                    InvertedBM25.from_dict(data["proof_index"]),
                    root,
                )
            except Exception:
                pass
        return cls.build(repo_root=root, write_accepted_jsonl=write_accepted_jsonl, cache_path=cpath)

    def retrieve_premises(
        self,
        query_text: str,
        top_k: int = 8,
        exclude: Optional[Iterable[str]] = None,
        hide_near_duplicates: bool = True,
    ) -> List[Dict[str, Any]]:
        """Retrieve top-k premises (signature + docstring + file path)."""
        return self.premise_index.search(
            query_text,
            top_k=top_k,
            exclude=exclude,
            hide_near_duplicates=hide_near_duplicates,
        )

    def retrieve_accepted_proofs(
        self,
        query_text: str,
        top_k: int = 3,
        exclude: Optional[Iterable[str]] = None,
        hide_near_duplicates: bool = True,
    ) -> List[Dict[str, Any]]:
        """Retrieve top-k verified accepted proofs."""
        return self.proof_index.search(
            query_text,
            top_k=top_k,
            exclude=exclude,
            hide_near_duplicates=hide_near_duplicates,
        )


def main() -> int:
    parser = argparse.ArgumentParser(
        description="Pure-Python BM25 declaration & accepted-proof index for Turing-recursive"
    )
    parser.add_argument("--root", default=None, help="Override repository root")
    parser.add_argument("--cache", default=None, help="Override BM25 cache pickle path")
    parser.add_argument("--accepted-jsonl", default=None, help="Override data/accepted.jsonl path")
    parser.add_argument("--json", action="store_true", help="Emit JSON output")
    sub = parser.add_subparsers(dest="command")

    p_build = sub.add_parser("build", help="Scan Mathlib + TuringRecursive + gemma_accepted and build BM25 index")
    p_build.add_argument("--no-write-accepted", action="store_true", help="Skip writing data/accepted.jsonl")

    p_query = sub.add_parser("query", help="Query BM25 index for top premises and accepted proofs")
    p_query.add_argument("query_text", help="Target declaration signature or search query")
    p_query.add_argument("--top-k", type=int, default=8, help="Number of premises to retrieve (default 8)")
    p_query.add_argument("--top-proofs", type=int, default=3, help="Number of accepted proofs to retrieve (default 3)")
    p_query.add_argument(
        "--exclude",
        action="append",
        default=[],
        help="Comma-separated declaration names to exclude (hides target and near duplicates)",
    )

    args = parser.parse_args()
    root = resolve_repo_root(args.root)
    cache_path = Path(args.cache) if args.cache else None
    acc_path = Path(args.accepted_jsonl) if args.accepted_jsonl else None

    if args.command == "build":
        t0 = time.time()
        idx = RepositoryIndex.build(
            repo_root=root,
            write_accepted_jsonl=not args.no_write_accepted,
            accepted_jsonl_path=acc_path,
            cache_path=cache_path,
        )
        elapsed_ms = (time.time() - t0) * 1000.0
        summary = {
            "status": "ok",
            "premises_indexed": idx.premise_index.corpus_size,
            "accepted_proofs_indexed": idx.proof_index.corpus_size,
            "elapsed_ms": round(elapsed_ms, 1),
            "accepted_jsonl": str(acc_path or RepositoryIndex.default_accepted_jsonl_path(root)),
            "cache_path": str(cache_path or RepositoryIndex.default_cache_path(root)),
        }
        if args.json:
            print(json.dumps(summary, indent=2))
        else:
            print(
                f"[OK] Built BM25 index in {elapsed_ms:.1f} ms: "
                f"{summary['premises_indexed']} premises, "
                f"{summary['accepted_proofs_indexed']} accepted proofs."
            )
        return 0

    if args.command == "query":
        idx = RepositoryIndex.load_or_build(repo_root=root, cache_path=cache_path)
        premises = idx.retrieve_premises(args.query_text, top_k=args.top_k, exclude=args.exclude)
        proofs = idx.retrieve_accepted_proofs(args.query_text, top_k=args.top_proofs, exclude=args.exclude)
        payload = {
            "query": args.query_text,
            "excluded": args.exclude,
            "premises": premises,
            "accepted_proofs": proofs,
        }
        if args.json:
            print(json.dumps(payload, indent=2))
        else:
            print(f"=== Top {len(premises)} Premises ===")
            for i, p in enumerate(premises, 1):
                print(f"{i}. {p['name']} [{p['file']}] (score={p['score']})")
                print(f"   {p['signature']}")
                if p.get("doc"):
                    print(f"   doc: {p['doc'][:120]}")
            print(f"\n=== Top {len(proofs)} Accepted Proofs ===")
            for i, p in enumerate(proofs, 1):
                print(f"{i}. {p['name']} [{p['file']}] (score={p['score']}, origin={p.get('origin')})")
                print(f"   {p['signature']} := {p['proof'][:140]}")
        return 0

    parser.print_help()
    return 0


if __name__ == "__main__":
    sys.exit(main())
