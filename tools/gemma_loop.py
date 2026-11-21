#!/usr/bin/env python3
"""
tools/gemma_loop.py — Compiler-in-the-Loop Local Prover for Turing-recursive

CLI:
  python3 tools/gemma_loop.py prove --spec specs/<name>.lean [--tier T0|T1|T2] [--max-attempts 5]
  python3 tools/gemma_loop.py daemon --queue specs/ [--once]

Fills each `sorry` declaration in a spec Lean file independently using local `gemma4:12B`,
BM25 premise + accepted-proof retrieval (`tools/index.py`), compiler feedback (`lake env lean`),
and verified outcome logging (`tools/ledger.py`).
"""

import argparse
import bisect
import json
import os
import re
import subprocess
import sys
import time
from dataclasses import dataclass
from pathlib import Path
from typing import Any, Callable, Dict, Iterable, List, Optional, Sequence, Tuple

TOOLS_DIR = Path(__file__).resolve().parent
if str(TOOLS_DIR) not in sys.path:
    sys.path.insert(0, str(TOOLS_DIR))

import index as bm25_index
import ledger
import ollama_lean4_client
import workflow_control

FORBIDDEN_TOKENS_RE = re.compile(
    r"\b(sorry|sorryAx|admit|axiom|unsafe|implemented_by|native_decide)\b"
)

TIER_COMMENT_RE = re.compile(r"--\s*tier\s*:\s*(T[012])\b", re.IGNORECASE)

MAX_PROMPT_CHARS = 8000

TACTIC_STARTERS = {
    "intro", "intros", "rintro", "exact", "refine", "apply", "rw", "rwa",
    "simp", "dsimp", "simpa", "rcases", "cases", "obtain", "induction",
    "constructor", "ext", "funext", "congr", "congrm", "ring", "omega",
    "linarith", "decide", "trivial", " contradiction", "aesop", "grind",
    "have", "suffices", "let", "change", "unfold", "split_ifs", " split",
    "first", "repeat", "try", "all_goals", "any_goals", "primrec_tac",
}

SYSTEM_RULES = (
    "You are a Lean 4 (v4.36.0, Mathlib pinned at fc4f59e5) theorem prover.\n"
    "RULES:\n"
    "1. Return ONLY a single ```lean4 ... ``` block containing the complete proved declaration, "
    "with NO prose or explanation before or after the block. If thinking mode is active, keep "
    "thinking under 3 short bullet points (<60 words) and then output the code block.\n"
    "2. Keep the declaration header and statement before `:=` BYTE-FOR-BYTE IDENTICAL to the target.\n"
    "   Never edit the theorem name, binders, type signature, or attributes.\n"
    "3. Replace `sorry` with a complete valid proof (either `:= by ...` or a term proof `:= ...`).\n"
    "4. Never use `sorry`, `admit`, `axiom`, `unsafe`, `implemented_by`, or `native_decide`.\n"
    "5. Use only real Lean 4 / Mathlib declarations (prefer the retrieved premises and examples).\n"
    "   For routine `Primrec` / `Primrec₂` / `Computable` goals, you can use `by primrec_tac` or\n"
    "   combinators (`Primrec.pair`, `Primrec.fst`, `Primrec.snd`, `Primrec.comp`, `.to₂`, `.of_eq`).\n"
    "6. Never repeat a proof that already failed in an earlier attempt."
)


@dataclass
class SpecDeclaration:
    """A single declaration extracted from a spec `.lean` file."""
    name: str
    raw_name: str
    short_name: str
    kind: str
    tier: str
    start_offset: int
    end_offset: int
    assign_offset_in_chunk: int
    statement: str          # exact bytes before top-level `:=`
    original_chunk: str     # exact bytes of the full declaration
    has_sorry: bool
    had_by_before_sorry: bool
    active_namespace: str


def sanitize_decl_filename(name: str) -> str:
    """Convert a Lean declaration name into a safe filesystem stem."""
    return re.sub(r"[^A-Za-z0-9_.-]+", "_", name).strip("_") or "decl"


def infer_tier_from_context(
    preceding_text: str,
    statement: str,
    default_tier: Optional[str] = None,
    prev_decl_end: int = 0,
) -> str:
    """
    Determine declaration tier from an explicit `-- tier: T0|T1|T2` comment directly above
    the declaration (bounded by `prev_decl_end` so earlier declarations' comments never bleed
    across declarations), CLI `--tier` override, or heuristic fallback.
    """
    header_slice = preceding_text[prev_decl_end:]
    matches = list(TIER_COMMENT_RE.finditer(header_slice))
    if matches:
        return matches[-1].group(1).upper()
    if default_tier in ("T0", "T1", "T2"):
        return default_tier
    if re.search(r"\b(Primrec|Primrec₂|Primcodable|List\.)\b", statement):
        return "T1"
    return "T1"


def parse_spec_declarations(spec_text: str, default_tier: Optional[str] = None) -> List[SpecDeclaration]:
    """Parse all top-level declarations in `spec_text` and identify which ones contain `sorry`."""
    masked = bm25_index.mask_comments_and_strings(spec_text)
    ns_timeline = bm25_index._build_namespace_timeline(masked)

    cmd_starts = [m.start() for m in bm25_index.CMD_BOUNDARY_RE.finditer(masked)]
    doc_starts = [m.start() for m in re.finditer(r"^[ \t]*/-!", spec_text, re.MULTILINE)]
    boundaries = sorted(set(cmd_starts + doc_starts + [len(spec_text)]))

    decls: List[SpecDeclaration] = []
    prev_end = 0
    for m in bm25_index.DECL_START_RE.finditer(masked):
        kind = m.group(1)
        raw_name = m.group(2)
        start = m.start()

        b_idx = bisect.bisect_right(boundaries, start)
        next_b = boundaries[b_idx] if b_idx < len(boundaries) else len(spec_text)

        chunk = spec_text[start:next_b]
        chunk_m = masked[start:next_b]

        assign_idx = bm25_index.find_top_level_assign(chunk_m)
        if assign_idx == -1 or chunk_m[assign_idx:assign_idx + 2] != ":=":
            prev_end = next_b
            continue

        stmt = chunk[:assign_idx].rstrip()
        raw_rhs = chunk[assign_idx + 2:]
        clean_rhs = bm25_index._clean_trailing_comments(raw_rhs)
        rhs_rel_end = raw_rhs.find(clean_rhs) + len(clean_rhs) if clean_rhs else len(raw_rhs.rstrip())
        actual_end = start + assign_idx + 2 + rhs_rel_end

        chunk = spec_text[start:actual_end]
        chunk_m = masked[start:actual_end]
        rhs_masked = chunk_m[assign_idx + 2:]
        has_sorry = bool(re.search(r"\b(sorry|admit)\b", rhs_masked))
        had_by = bool(re.match(r"^\s*by\b", rhs_masked))

        active_ns = bm25_index._namespace_at(ns_timeline, start)
        if active_ns and not raw_name.startswith(active_ns + "."):
            full_name = f"{active_ns}.{raw_name}"
        else:
            full_name = raw_name
        short_name = raw_name.rsplit(".", 1)[-1]

        tier = infer_tier_from_context(
            spec_text[:start],
            stmt,
            default_tier=default_tier,
            prev_decl_end=prev_end,
        )
        prev_end = actual_end
        decls.append(
            SpecDeclaration(
                name=full_name,
                raw_name=raw_name,
                short_name=short_name,
                kind=kind,
                tier=tier,
                start_offset=start,
                end_offset=actual_end,
                assign_offset_in_chunk=assign_idx,
                statement=stmt,
                original_chunk=chunk,
                has_sorry=has_sorry,
                had_by_before_sorry=had_by,
                active_namespace=active_ns,
            )
        )
    return decls


def extract_module_context(spec_text: str, up_to_offset: int) -> str:
    """Extract imports, opens, variables, namespaces, and local defs preceding `up_to_offset`."""
    prefix = spec_text[:up_to_offset]
    lines: List[str] = []
    for raw_line in prefix.splitlines():
        s = raw_line.strip()
        if not s or s.startswith("--"):
            continue
        if any(
            s.startswith(kw)
            for kw in (
                "module",
                "import ",
                "public import ",
                "open ",
                "variable ",
                "variables ",
                "universe ",
                "universes ",
                "namespace ",
                "section ",
                "end ",
                "end",
                "@[expose]",
                "public section",
                "notation",
                "local ",
                "scoped ",
                "attribute ",
                "def ",
                "abbrev ",
                "structure ",
                "inductive ",
            )
        ):
            lines.append(raw_line)
    return "\n".join(lines[-40:])


def build_prover_messages(
    decl: SpecDeclaration,
    module_context: str,
    premises: List[Dict[str, Any]],
    accepted_proofs: List[Dict[str, Any]],
    attempt: int,
    prev_candidate: str = "",
    prev_error_lines: str = "",
    prior_attempts: Optional[List[Dict[str, Any]]] = None,
) -> List[Dict[str, str]]:
    """Construct the system and user messages for `gemma4:12B`."""
    parts: List[str] = []

    if module_context.strip():
        parts.append(f"Module context (imports / opens / variables / namespace):\n```lean4\n{module_context.strip()}\n```")

    if premises:
        p_lines = []
        for i, p in enumerate(premises[:5], 1):
            doc_str = f" -- {p['doc']}" if p.get("doc") else ""
            p_lines.append(f"-- [{i}] {p['name']} ({p.get('file', '')}){doc_str}\n{p['signature']}")
        parts.append("Top retrieved premises:\n```lean4\n" + "\n".join(p_lines) + "\n```")

    if accepted_proofs:
        a_lines = []
        for i, a in enumerate(accepted_proofs[:2], 1):
            a_lines.append(f"-- Example {i}: {a['name']} ({a.get('file', '')})\n{a['signature']} :=\n  {a['proof']}")
        parts.append("Top retrieved verified proofs:\n```lean4\n" + "\n\n".join(a_lines) + "\n```")

    target_preview = f"{decl.statement} := by\n  sorry" if decl.had_by_before_sorry else f"{decl.statement} :=\n  sorry"
    parts.append(
        f"Target declaration to prove (tier {decl.tier}, attempt {attempt}):\n"
        f"```lean4\n{target_preview}\n```"
    )

    if attempt >= 2 and prev_error_lines.strip():
        if prior_attempts and len(prior_attempts) > 1:
            failed_bodies = [
                f"-- Failed attempt {a['attempt']}: {a.get('proof_body') or a.get('candidate_code', '')}"
                for a in prior_attempts
            ]
            parts.append("All previous failed attempts (DO NOT repeat any of these):\n```lean4\n" + "\n".join(failed_bodies) + "\n```")
        elif prev_candidate.strip():
            parts.append(f"Previous attempt ({attempt - 1}) code (DO NOT repeat this):\n```lean4\n{prev_candidate.strip()}\n```")
        parts.append(
            f"Compiler errors from attempt {attempt - 1} (first <= 15 lines):\n```\n{prev_error_lines.strip()}\n```\n"
            "Write a DIFFERENT proof that fixes the compiler error while keeping the declaration "
            "statement before `:=` byte-for-byte identical."
        )

    user_content = "\n\n".join(parts)
    if len(user_content) > MAX_PROMPT_CHARS:
        user_content = user_content[-MAX_PROMPT_CHARS:]

    return [
        {"role": "system", "content": SYSTEM_RULES},
        {"role": "user", "content": user_content},
    ]


def _strip_leading_attributes(stmt: str) -> str:
    """Remove leading `@[...]` attribute blocks for comparison when the model omits attributes."""
    return re.sub(r"^\s*(?:@\[[^\]]*\]\s*)+", "", stmt).strip()


def validate_and_splice_candidate(
    decl: SpecDeclaration,
    extracted_code: str,
) -> Tuple[bool, str, str]:
    """
    Validate that `extracted_code` does not alter `decl.statement` and construct the full
    declaration `<decl.statement> := <proof_body>`.
    Returns `(ok, spliced_declaration_or_reason, extracted_proof_body)`.
    """
    code = extracted_code.strip()
    if not code:
        return False, "Empty response from model.", ""

    masked = bm25_index.mask_comments_and_strings(code)
    decl_matches = list(bm25_index.DECL_START_RE.finditer(masked))

    if decl_matches:
        # Find the declaration matching our target name (or the first declaration if only one)
        chosen_match = decl_matches[0]
        for m in decl_matches:
            m_name = m.group(2)
            if m_name in (decl.raw_name, decl.name, decl.short_name):
                chosen_match = m
                break

        start = chosen_match.start()
        sub_code = code[start:]
        sub_masked = masked[start:]
        assign_idx = bm25_index.find_top_level_assign(sub_masked)
        if assign_idx == -1 or sub_masked[assign_idx:assign_idx + 2] != ":=":
            return False, "Candidate declaration is missing top-level ':='.", ""

        cand_stmt = sub_code[:assign_idx].strip()
        cand_proof = bm25_index._clean_trailing_comments(sub_code[assign_idx + 2:])

        spec_stmt = decl.statement.strip()
        spec_stmt_no_attr = _strip_leading_attributes(spec_stmt)
        cand_stmt_no_attr = _strip_leading_attributes(cand_stmt)

        norm_cand = re.sub(r"\s+", " ", cand_stmt).strip()
        norm_spec = re.sub(r"\s+", " ", spec_stmt).strip()
        norm_cand_no_attr = re.sub(r"\s+", " ", cand_stmt_no_attr).strip()
        norm_spec_no_attr = re.sub(r"\s+", " ", spec_stmt_no_attr).strip()

        # Require token/character identity of the declaration statement; splice uses exact spec_stmt bytes
        if norm_cand != norm_spec and norm_cand_no_attr != norm_spec_no_attr:
            return (
                False,
                f"Declaration statement before ':=' was modified.\n"
                f"Expected: {spec_stmt}\n"
                f"Got:      {cand_stmt}",
                cand_proof,
            )
    else:
        # Model emitted only the proof body after `:=`
        cand_proof = code
        if cand_proof.startswith(":="):
            cand_proof = cand_proof[2:].strip()
        first_word = re.split(r"[\s(;⟨]+", cand_proof, maxsplit=1)[0] if cand_proof else ""
        if (
            not cand_proof.startswith("by")
            and (decl.had_by_before_sorry or first_word in TACTIC_STARTERS)
            and first_word in TACTIC_STARTERS
        ):
            indented = "\n  ".join(cand_proof.splitlines())
            cand_proof = f"by\n  {indented}"

    if not cand_proof.strip():
        return False, "Candidate proof body is empty.", ""

    # Check that candidate proof didn't smuggle additional top-level declarations/commands
    proof_masked = bm25_index.mask_comments_and_strings(cand_proof)
    leaked = re.search(
        r"^[ \t]*(?:@\[[^\]]*\]\s*)*(?:(?:private|protected|noncomputable|scoped|local)\s+)*"
        r"(?:theorem|lemma|def|abbrev|axiom|opaque|structure|class|inductive|instance|namespace|section|end)\b",
        proof_masked,
        re.MULTILINE,
    )
    if leaked:
        cand_proof = bm25_index._clean_trailing_comments(cand_proof[:leaked.start()])

    spliced = f"{decl.statement} :=\n  {cand_proof.strip()}\n" if "\n" in cand_proof else f"{decl.statement} := {cand_proof.strip()}\n"

    # Double-check byte-identity of the spliced statement before top-level `:=`
    spliced_masked = bm25_index.mask_comments_and_strings(spliced)
    s_idx = bm25_index.find_top_level_assign(spliced_masked)
    if s_idx == -1 or spliced[:s_idx].rstrip() != decl.statement.rstrip():
        return False, "Internal splice check failed: statement before ':=' is not byte-identical.", cand_proof

    return True, spliced, cand_proof


def build_scratch_file_content(
    spec_text: str,
    all_decls: List[SpecDeclaration],
    target_decl: SpecDeclaration,
    spliced_target: str,
    accepted_replacements: Dict[int, str],
) -> str:
    """
    Construct a standalone compilable scratch `.lean` file with `spliced_target` replacing
    `target_decl`. Any OTHER unproved `sorry` declarations in the same spec file that are not
    already in `accepted_replacements` are omitted so the scratch file is 100% sorry-free
    and warning-free.
    """
    pieces: List[str] = []
    cursor = 0
    for d in all_decls:
        pieces.append(spec_text[cursor:d.start_offset])
        if d.start_offset == target_decl.start_offset:
            pieces.append(spliced_target)
        elif d.start_offset in accepted_replacements:
            pieces.append(accepted_replacements[d.start_offset])
        elif d.has_sorry:
            # Omit other unproved sorry declarations so the scratch file is completely sorry-free
            pieces.append(f"-- [gemma_loop scratch: omitted unproved {d.name}]\n")
        else:
            pieces.append(d.original_chunk)
        cursor = d.end_offset
    pieces.append(spec_text[cursor:])
    return "".join(pieces)


def run_lean_check(
    scratch_path: Path,
    repo_root: Path,
    timeout_sec: float = 300.0,
) -> Tuple[bool, int, str, float, bool]:
    """
    Run `LEAN_NUM_THREADS=2 lake env lean <scratch_path>` (single process slot) and verify:
      - exit code == 0
      - no warnings or errors in output
      - no `sorry` or forbidden tokens in comment-stripped source
    Returns `(accepted, returncode, diagnostics, lean_ms, timed_out)`.
    """
    source_text = scratch_path.read_text(encoding="utf-8", errors="replace")
    stripped = workflow_control.strip_lean_comments(source_text)
    forbidden_match = FORBIDDEN_TOKENS_RE.search(stripped)
    if forbidden_match:
        tok = forbidden_match.group(1)
        return False, 1, f"error: forbidden token '{tok}' found in candidate proof", 0.0, False

    env = os.environ.copy()
    elan_bin = os.path.expanduser("~/.elan/bin")
    env["PATH"] = f"{elan_bin}:{env.get('PATH', '')}"
    env["LEAN_NUM_THREADS"] = "2"

    t0 = time.time()
    try:
        proc = subprocess.run(
            ["lake", "env", "lean", str(scratch_path)],
            cwd=str(repo_root),
            env=env,
            capture_output=True,
            text=True,
            timeout=timeout_sec,
        )
        lean_ms = (time.time() - t0) * 1000.0
    except subprocess.TimeoutExpired as exc:
        lean_ms = (time.time() - t0) * 1000.0
        out = ((exc.stdout or "") + "\n" + (exc.stderr or "")).strip()
        return False, 124, f"timeout after {timeout_sec}s\n{out}".strip(), lean_ms, True

    combined = ((proc.stdout or "") + "\n" + (proc.stderr or "")).strip()
    has_warning = bool(re.search(r"\bwarning\s*:", combined, re.IGNORECASE))
    has_error = bool(re.search(r"\berror\s*:", combined, re.IGNORECASE))

    accepted = (proc.returncode == 0) and (not has_warning) and (not has_error)
    return accepted, proc.returncode, combined, lean_ms, False


def first_n_error_lines(diagnostics: str, max_lines: int = 15) -> str:
    """Return the first `<= max_lines` non-empty diagnostic lines."""
    lines = [ln for ln in (diagnostics or "").splitlines() if ln.strip()]
    return "\n".join(lines[:max_lines])


def prove_declaration(
    decl: SpecDeclaration,
    spec_path: Path,
    spec_text: str,
    all_decls: List[SpecDeclaration],
    accepted_replacements: Dict[int, str],
    repo_root: Path,
    idx: bm25_index.RepositoryIndex,
    max_attempts: int = 5,
    milestone: str = "W0",
    exclude: Optional[Iterable[str]] = None,
    lean_timeout: float = 300.0,
    ollama_host: str = ollama_lean4_client.DEFAULT_OLLAMA_HOST,
    ollama_model: str = ollama_lean4_client.PRIMARY_MODEL,
    ollama_timeout: float = 180.0,
    dry_run: bool = False,
    model_caller: Optional[Callable[..., Dict[str, Any]]] = None,
    lean_checker: Optional[Callable[[Path, Path, float], Tuple[bool, int, str, float, bool]]] = None,
    ledger_path: Optional[Path] = None,
) -> Dict[str, Any]:
    """
    Run up to `max_attempts` compiler-in-the-loop cycles on a single `sorry` declaration.
    Writes accepted proof to `.agents/gemma_accepted/<decl>.lean` or escalation report to
    `.agents/gemma_escalations/<decl>.json`.
    """
    scratch_dir = repo_root / ".agents" / "gemma_scratch"
    accepted_dir = repo_root / ".agents" / "gemma_accepted"
    escalations_dir = repo_root / ".agents" / "gemma_escalations"
    scratch_dir.mkdir(parents=True, exist_ok=True)
    accepted_dir.mkdir(parents=True, exist_ok=True)
    escalations_dir.mkdir(parents=True, exist_ok=True)

    safe_name = sanitize_decl_filename(decl.name)
    module_ctx = extract_module_context(spec_text, decl.start_offset)

    ex_list = list(exclude or []) + [decl.name, decl.raw_name, decl.short_name]
    clean_q_name = re.sub(r"^cal_", "", decl.name)
    query_str = f"{clean_q_name} {decl.statement}"
    premises = idx.retrieve_premises(query_str, top_k=5, exclude=ex_list)
    accepted_proofs = idx.retrieve_accepted_proofs(query_str, top_k=2, exclude=ex_list)

    caller = model_caller or ollama_lean4_client.query_ollama_chat
    checker = lean_checker or run_lean_check

    attempts_history: List[Dict[str, Any]] = []
    prev_candidate = ""
    prev_errors = ""

    for attempt in range(1, max_attempts + 1):
        # Respect pause sentinel between attempts
        if workflow_control.WorkflowController(repo_root).is_paused():
            return {
                "declaration": decl.name,
                "tier": decl.tier,
                "accepted": False,
                "paused": True,
                "attempts": attempts_history,
            }

        think = False
        msgs = build_prover_messages(
            decl=decl,
            module_context=module_ctx,
            premises=premises,
            accepted_proofs=accepted_proofs,
            attempt=attempt,
            prev_candidate=prev_candidate,
            prev_error_lines=prev_errors,
            prior_attempts=attempts_history,
        )
        prompt_text = "\n".join(m["content"] for m in msgs)

        # Locked sampling parameters per Option 1b specification
        opts = {
            "temperature": 1.0,
            "top_p": 0.95,
            "top_k": 64,
            "num_ctx": 8192,
            "num_predict": 512 if attempt >= 4 else 384,
        }

        res = caller(
            base_url=ollama_host,
            model=ollama_model,
            task_type="prove",
            messages=msgs,
            think=think,
            timeout=ollama_timeout,
            dry_run=dry_run,
            declaration=decl.name,
            record_usage=False,  # gemma_loop records verified outcome after Lean check
            milestone=milestone,
            tier=decl.tier,
            attempt=attempt,
            options_override=opts,
        )

        latency_ms = float(res.get("elapsed_ms") or 0.0)
        tokens = int(res.get("eval_count") or 0)
        raw_lean = res.get("lean_code") or ""

        if res.get("status") not in ("success", "mock"):
            err_msg = f"Ollama error: {res.get('error', 'unknown')}"
            err_class = "timeout" if "timed out" in err_msg.lower() else "other"
            ledger.append_usage_record(
                declaration=decl.name,
                milestone=milestone,
                tier=decl.tier,
                attempt=attempt,
                accepted=False,
                error_class=err_class,
                compiler_output=err_msg,
                tokens=tokens,
                latency_ms=latency_ms,
                lean_ms=0.0,
                model=res.get("model", ollama_model),
                task_type="prove",
                prompt_text=prompt_text,
                status="error",
                error=err_msg,
                ledger_path=ledger_path,
            )
            attempts_history.append({
                "attempt": attempt,
                "think": think,
                "candidate_code": raw_lean,
                "compiler_error": err_msg,
                "error_class": err_class,
                "latency_ms": latency_ms,
                "lean_ms": 0.0,
                "tokens": tokens,
                "accepted": False,
            })
            prev_candidate = raw_lean
            prev_errors = first_n_error_lines(err_msg, 15)
            continue

        valid_splice, spliced_or_err, cand_proof = validate_and_splice_candidate(decl, raw_lean)
        scratch_path = scratch_dir / f"{safe_name}_{attempt}.lean"

        if not valid_splice:
            # Write rejected candidate to scratch for auditability
            scratch_path.write_text(f"-- REJECTED BEFORE LEAN CHECK: {spliced_or_err}\n{raw_lean}\n", encoding="utf-8")
            err_msg = f"error: {spliced_or_err}"
            err_class = ledger.classify_lean_error(err_msg, accepted=False)
            ledger.append_usage_record(
                declaration=decl.name,
                milestone=milestone,
                tier=decl.tier,
                attempt=attempt,
                accepted=False,
                error_class=err_class,
                compiler_output=err_msg,
                tokens=tokens,
                latency_ms=latency_ms,
                lean_ms=0.0,
                model=res.get("model", ollama_model),
                task_type="prove",
                prompt_text=prompt_text,
                status="rejected_splice",
                error=err_msg,
                ledger_path=ledger_path,
            )
            attempts_history.append({
                "attempt": attempt,
                "think": think,
                "candidate_code": raw_lean,
                "compiler_error": err_msg,
                "error_class": err_class,
                "latency_ms": latency_ms,
                "lean_ms": 0.0,
                "tokens": tokens,
                "accepted": False,
            })
            prev_candidate = raw_lean
            prev_errors = first_n_error_lines(err_msg, 15)
            continue

        # Check for forbidden tokens in the spliced declaration before running Lean
        stripped_spliced = workflow_control.strip_lean_comments(spliced_or_err)
        forbidden = FORBIDDEN_TOKENS_RE.search(stripped_spliced)
        if not forbidden and exclude:
            stripped_proof = workflow_control.strip_lean_comments(cand_proof)
            for ex_raw in bm25_index.normalize_exclusion_set(exclude):
                # Check both qualified and last-segment identifier if >= 4 chars
                if len(ex_raw) >= 4:
                    pat = re.compile(r"(?<![A-Za-z0-9_'\.])" + re.escape(ex_raw) + r"(?![A-Za-z0-9_'\.\?])")
                    if pat.search(stripped_proof):
                        forbidden = pat.search(stripped_proof)
                        break
        if forbidden:
            tok = forbidden.group(0)
            scratch_path.write_text(spliced_or_err, encoding="utf-8")
            err_msg = f"error: forbidden token '{tok}' in candidate proof"
            ledger.append_usage_record(
                declaration=decl.name,
                milestone=milestone,
                tier=decl.tier,
                attempt=attempt,
                accepted=False,
                error_class="other",
                compiler_output=err_msg,
                tokens=tokens,
                latency_ms=latency_ms,
                lean_ms=0.0,
                model=res.get("model", ollama_model),
                task_type="prove",
                prompt_text=prompt_text,
                status="rejected_forbidden",
                error=err_msg,
                ledger_path=ledger_path,
            )
            attempts_history.append({
                "attempt": attempt,
                "think": think,
                "candidate_code": spliced_or_err.strip(),
                "compiler_error": err_msg,
                "error_class": "other",
                "latency_ms": latency_ms,
                "lean_ms": 0.0,
                "tokens": tokens,
                "accepted": False,
            })
            prev_candidate = spliced_or_err.strip()
            prev_errors = err_msg
            continue

        scratch_content = build_scratch_file_content(
            spec_text=spec_text,
            all_decls=all_decls,
            target_decl=decl,
            spliced_target=spliced_or_err,
            accepted_replacements=accepted_replacements,
        )
        scratch_path.write_text(scratch_content, encoding="utf-8")

        accepted, _rc, diagnostics, lean_ms, timed_out = checker(scratch_path, repo_root, lean_timeout)
        err_class = ledger.classify_lean_error(diagnostics, timed_out=timed_out, accepted=accepted)

        ledger.append_usage_record(
            declaration=decl.name,
            milestone=milestone,
            tier=decl.tier,
            attempt=attempt,
            accepted=accepted,
            error_class=err_class,
            compiler_output=diagnostics,
            timed_out=timed_out,
            tokens=tokens,
            latency_ms=latency_ms,
            lean_ms=lean_ms,
            model=res.get("model", ollama_model),
            task_type="prove",
            prompt_text=prompt_text,
            status="accepted" if accepted else "rejected",
            error=None if accepted else first_n_error_lines(diagnostics, 10),
            ledger_path=ledger_path,
        )

        attempts_history.append({
            "attempt": attempt,
            "think": think,
            "candidate_code": spliced_or_err.strip(),
            "proof_body": cand_proof.strip(),
            "compiler_error": "" if accepted else first_n_error_lines(diagnostics, 15),
            "error_class": err_class,
            "latency_ms": round(latency_ms, 2),
            "lean_ms": round(lean_ms, 2),
            "tokens": tokens,
            "accepted": accepted,
        })

        if accepted:
            accepted_file = accepted_dir / f"{safe_name}.lean"
            accepted_header = (
                f"-- Verified by gemma_loop.py (declaration: {decl.name}, tier: {decl.tier}, "
                f"attempt: {attempt}, spec: {spec_path.name})\n"
            )
            accepted_file.write_text(accepted_header + spliced_or_err, encoding="utf-8")
            accepted_replacements[decl.start_offset] = spliced_or_err
            return {
                "declaration": decl.name,
                "raw_name": decl.raw_name,
                "tier": decl.tier,
                "accepted": True,
                "accepted_at_attempt": attempt,
                "accepted_file": str(accepted_file),
                "spliced_declaration": spliced_or_err,
                "attempts": attempts_history,
            }

        prev_candidate = spliced_or_err.strip()
        prev_errors = first_n_error_lines(diagnostics, 15)

    # All attempts exhausted -> write escalation JSON for frontier model
    escalation_file = escalations_dir / f"{safe_name}.json"
    escalation_payload = {
        "declaration": decl.name,
        "raw_name": decl.raw_name,
        "spec_file": str(spec_path),
        "milestone": milestone,
        "tier": decl.tier,
        "statement": decl.statement,
        "max_attempts": max_attempts,
        "escalated_at": ledger.utc_now(),
        "retrieved_premises": [p["name"] for p in premises],
        "attempts": attempts_history,
    }
    escalation_file.write_text(json.dumps(escalation_payload, indent=2) + "\n", encoding="utf-8")
    return {
        "declaration": decl.name,
        "raw_name": decl.raw_name,
        "tier": decl.tier,
        "accepted": False,
        "accepted_at_attempt": None,
        "escalation_file": str(escalation_file),
        "attempts": attempts_history,
    }


def prove_spec_file(
    spec_path: Path,
    repo_root: Optional[Path] = None,
    tier_override: Optional[str] = None,
    max_attempts: int = 5,
    milestone: str = "W0",
    exclude: Optional[Iterable[str]] = None,
    lean_timeout: float = 300.0,
    ollama_host: str = ollama_lean4_client.DEFAULT_OLLAMA_HOST,
    ollama_model: str = ollama_lean4_client.PRIMARY_MODEL,
    ollama_timeout: float = 180.0,
    dry_run: bool = False,
    idx: Optional[bm25_index.RepositoryIndex] = None,
    model_caller: Optional[Callable[..., Dict[str, Any]]] = None,
    lean_checker: Optional[Callable[[Path, Path, float], Tuple[bool, int, str, float, bool]]] = None,
    ledger_path: Optional[Path] = None,
) -> Dict[str, Any]:
    """Process all `sorry` declarations in `spec_path` independently."""
    root = bm25_index.resolve_repo_root(str(repo_root) if repo_root else None)
    if workflow_control.WorkflowController(root).is_paused():
        return {"status": "paused", "spec_file": str(spec_path), "results": []}

    spec_text = spec_path.read_text(encoding="utf-8")
    all_decls = parse_spec_declarations(spec_text, default_tier=tier_override)
    sorry_decls = [d for d in all_decls if d.has_sorry]

    active_idx = idx or bm25_index.RepositoryIndex.load_or_build(repo_root=root)
    accepted_replacements: Dict[int, str] = {}
    results: List[Dict[str, Any]] = []

    for d in sorry_decls:
        if tier_override in ("T0", "T1", "T2"):
            d.tier = tier_override
        res = prove_declaration(
            decl=d,
            spec_path=spec_path,
            spec_text=spec_text,
            all_decls=all_decls,
            accepted_replacements=accepted_replacements,
            repo_root=root,
            idx=active_idx,
            max_attempts=max_attempts,
            milestone=milestone,
            exclude=exclude,
            lean_timeout=lean_timeout,
            ollama_host=ollama_host,
            ollama_model=ollama_model,
            ollama_timeout=ollama_timeout,
            dry_run=dry_run,
            model_caller=model_caller,
            lean_checker=lean_checker,
            ledger_path=ledger_path,
        )
        results.append(res)
        if res.get("paused"):
            return {"status": "paused", "spec_file": str(spec_path), "results": results}

    accepted_count = sum(1 for r in results if r.get("accepted"))
    return {
        "status": "ok",
        "spec_file": str(spec_path),
        "total_sorry_declarations": len(sorry_decls),
        "accepted_count": accepted_count,
        "escalated_count": len(sorry_decls) - accepted_count,
        "results": results,
    }


def run_daemon(
    queue_dir: Path,
    repo_root: Optional[Path] = None,
    tier_override: Optional[str] = None,
    max_attempts: int = 5,
    milestone: str = "W0",
    exclude: Optional[Iterable[str]] = None,
    poll_seconds: float = 5.0,
    once: bool = True,
    dry_run: bool = False,
) -> Dict[str, Any]:
    """Process spec `.lean` files from `queue_dir` one at a time."""
    root = bm25_index.resolve_repo_root(str(repo_root) if repo_root else None)
    idx = bm25_index.RepositoryIndex.load_or_build(repo_root=root)
    processed: List[Dict[str, Any]] = []
    seen_files: set = set()

    while True:
        if workflow_control.WorkflowController(root).is_paused():
            return {"status": "paused", "processed": processed}

        spec_files = sorted(queue_dir.glob("*.lean")) if queue_dir.is_dir() else []
        pending = [f for f in spec_files if str(f.resolve()) not in seen_files]

        for sf in pending:
            if workflow_control.WorkflowController(root).is_paused():
                return {"status": "paused", "processed": processed}
            res = prove_spec_file(
                spec_path=sf,
                repo_root=root,
                tier_override=tier_override,
                max_attempts=max_attempts,
                milestone=milestone,
                exclude=exclude,
                dry_run=dry_run,
                idx=idx,
            )
            processed.append(res)
            seen_files.add(str(sf.resolve()))
            if res.get("status") == "paused":
                return {"status": "paused", "processed": processed}

        if once:
            break
        time.sleep(poll_seconds)

    return {"status": "ok", "files_processed": len(processed), "processed": processed}


def main() -> int:
    parser = argparse.ArgumentParser(
        description="Compiler-in-the-loop local gemma4:12B prover for Turing-recursive"
    )
    parser.add_argument("--root", default=None, help="Override repository root")
    parser.add_argument("--milestone", default="W0", help="Milestone tag for usage ledger (default W0)")
    parser.add_argument("--host", default=ollama_lean4_client.DEFAULT_OLLAMA_HOST, help="Ollama host URL")
    parser.add_argument("--model", default=ollama_lean4_client.PRIMARY_MODEL, help="Ollama model name")
    parser.add_argument("--lean-timeout", type=float, default=300.0, help="Lean check timeout in seconds (default 300)")
    parser.add_argument("--ollama-timeout", type=float, default=180.0, help="Ollama request timeout in seconds")
    parser.add_argument("--exclude", action="append", default=[], help="Comma-separated declarations to exclude from BM25")
    parser.add_argument("--dry-run", action="store_true", help="Mock Ollama calls for testing")
    parser.add_argument("--json", action="store_true", help="Emit JSON output")

    sub = parser.add_subparsers(dest="command")

    p_prove = sub.add_parser("prove", help="Prove all sorry declarations in a spec Lean file")
    p_prove.add_argument("--spec", required=True, help="Path to spec Lean file (e.g. specs/<name>.lean)")
    p_prove.add_argument("--tier", choices=["T0", "T1", "T2"], default=None, help="Override declaration tier")
    p_prove.add_argument("--max-attempts", type=int, default=5, help="Max attempts per declaration (default 5)")

    p_daemon = sub.add_parser("daemon", help="Process spec files in a queue directory one at a time")
    p_daemon.add_argument("--queue", required=True, help="Directory of spec Lean files (e.g. specs/)")
    p_daemon.add_argument("--tier", choices=["T0", "T1", "T2"], default=None, help="Default tier")
    p_daemon.add_argument("--max-attempts", type=int, default=5, help="Max attempts per declaration (default 5)")
    p_daemon.add_argument("--watch", action="store_true", help="Keep polling queue directory continuously")
    p_daemon.add_argument("--poll-seconds", type=float, default=5.0, help="Polling interval when --watch is set")

    args = parser.parse_args()
    root = bm25_index.resolve_repo_root(args.root)

    if args.command == "prove":
        spec_path = Path(args.spec)
        if not spec_path.is_Absolute() if hasattr(spec_path, "is_Absolute") else not spec_path.is_absolute():
            if not spec_path.is_file() and (root / spec_path).is_file():
                spec_path = root / spec_path
        if not spec_path.is_file():
            print(f"[ERROR] Spec file not found: {args.spec}", file=sys.stderr)
            return 1
        res = prove_spec_file(
            spec_path=spec_path,
            repo_root=root,
            tier_override=args.tier,
            max_attempts=args.max_attempts,
            milestone=args.milestone,
            exclude=args.exclude,
            lean_timeout=args.lean_timeout,
            ollama_host=args.host,
            ollama_model=args.model,
            ollama_timeout=args.ollama_timeout,
            dry_run=args.dry_run,
        )
        if res.get("status") == "paused":
            print("PAUSED")
            return 42
        if args.json:
            print(json.dumps(res, indent=2))
        else:
            print(
                f"Spec {spec_path.name}: {res['accepted_count']}/{res['total_sorry_declarations']} "
                f"accepted, {res['escalated_count']} escalated."
            )
            for r in res["results"]:
                if r["accepted"]:
                    print(f"  [ACCEPTED attempt {r['accepted_at_attempt']}] {r['declaration']} -> {r['accepted_file']}")
                else:
                    print(f"  [ESCALATED] {r['declaration']} -> {r.get('escalation_file')}")
        return 0

    if args.command == "daemon":
        queue_dir = Path(args.queue)
        if not queue_dir.is_absolute() and not queue_dir.is_dir() and (root / queue_dir).is_dir():
            queue_dir = root / queue_dir
        res = run_daemon(
            queue_dir=queue_dir,
            repo_root=root,
            tier_override=args.tier,
            max_attempts=args.max_attempts,
            milestone=args.milestone,
            exclude=args.exclude,
            poll_seconds=args.poll_seconds,
            once=not args.watch,
            dry_run=args.dry_run,
        )
        if res.get("status") == "paused":
            print("PAUSED")
            return 42
        if args.json:
            print(json.dumps(res, indent=2))
        else:
            print(f"Daemon processed {res.get('files_processed', 0)} spec file(s) from {queue_dir}.")
        return 0

    parser.print_help()
    return 0


if __name__ == "__main__":
    sys.exit(main())
