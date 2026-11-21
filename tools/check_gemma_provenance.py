#!/usr/bin/env python3
"""
tools/check_gemma_provenance.py — Local-Model Provenance Gate (G8) Checker

Given a git diff range (e.g. `main...HEAD`), lists every NEW declaration whose tier is
T0 or T1 (recorded in a comment `-- tier: T0|T1|T2` placed directly above the declaration,
or inferred as T1 if absent for `Primrec`/list lemmas) and requires EITHER:
  1. `.agents/gemma_accepted/<decl>.lean`, OR
  2. `.agents/gemma_escalations/<decl>.json` with >= 5 recorded failed attempts.

Exits 0 if all T0/T1 declarations satisfy provenance, or non-zero (1) otherwise.
"""

import argparse
import json
import re
import subprocess
import sys
from pathlib import Path
from typing import Any, Dict, List, Optional, Sequence, Set, Tuple

TOOLS_DIR = Path(__file__).resolve().parent
if str(TOOLS_DIR) not in sys.path:
    sys.path.insert(0, str(TOOLS_DIR))

import gemma_loop
import index as bm25_index

TIER_COMMENT_RE = re.compile(r"--\s*tier\s*:\s*(T[012])\b", re.IGNORECASE)
PRIMREC_OR_LIST_RE = re.compile(
    r"\b(Primrec|Primrec₂|Nat\.Primrec|Primcodable|List|ListBlank)\b|list_",
)


def extract_preceding_header_window(source_text: str, decl_start: int) -> str:
    """
    Return the lines immediately above `decl_start`, stepping past any contiguous
    `@[...]` attributes and `/-- ... -/` docstring block so `-- tier: T0` works
    whether placed above or below the docstring.
    """
    prefix = source_text[:decl_start].rstrip()
    # Step past trailing attributes or docstrings to inspect up to 6 comment lines above them
    scan_pos = len(prefix)
    while scan_pos > 0:
        sub = prefix[:scan_pos].rstrip()
        if sub.endswith("-/"):
            doc_open = sub.rfind("/--")
            if doc_open != -1 and doc_open > sub.rfind("/-!"):
                scan_pos = doc_open
                continue
        lines = sub.splitlines()
        if lines and lines[-1].strip().startswith("@["):
            scan_pos = sub.rfind("\n")
            if scan_pos == -1:
                scan_pos = 0
            continue
        break
    window_start = max(0, scan_pos - 400)
    return prefix[window_start:decl_start]


def determine_declaration_tier(
    source_text: str,
    decl: gemma_loop.SpecDeclaration,
    prev_decl_end: int = 0,
) -> Optional[str]:
    """
    Return explicit tier ('T0', 'T1', 'T2') from `-- tier: T<k>` comment directly above `decl`
    (since `prev_decl_end`), or infer 'T1' if absent for `Primrec`/list lemmas; return None
    if unclassified non-Primrec/list.
    """
    window = source_text[prev_decl_end:decl.start_offset]
    matches = list(TIER_COMMENT_RE.finditer(window))
    if matches:
        return matches[-1].group(1).upper()

    combined = f"{decl.name} {decl.raw_name} {decl.statement}"
    if PRIMREC_OR_LIST_RE.search(combined):
        return "T1"
    return None


def candidate_artifact_stems(decl: gemma_loop.SpecDeclaration) -> List[str]:
    """Generate candidate filename stems for matching a declaration in gemma_accepted/escalations."""
    stems: List[str] = []
    for raw in (decl.name, decl.raw_name, decl.short_name):
        if not raw:
            continue
        for s in (gemma_loop.sanitize_decl_filename(raw), raw):
            if s and s not in stems:
                stems.append(s)
    return stems


def check_declaration_provenance(
    decl: gemma_loop.SpecDeclaration,
    tier: str,
    accepted_dir: Path,
    escalations_dir: Path,
    required_attempts: int = 5,
) -> Dict[str, Any]:
    """
    Verify provenance for a single T0/T1 declaration.
    Returns dict with `ok` (bool), `origin` ('gemma_accepted' | 'escalated' | 'missing'),
    and artifact path or error reason.
    """
    stems = candidate_artifact_stems(decl)

    # 1. Check .agents/gemma_accepted/<decl>.lean
    if accepted_dir.is_dir():
        for stem in stems:
            cand = accepted_dir / f"{stem}.lean"
            if cand.is_file():
                text = cand.read_text(encoding="utf-8", errors="replace").strip()
                if text:
                    return {
                        "declaration": decl.name,
                        "raw_name": decl.raw_name,
                        "tier": tier,
                        "ok": True,
                        "origin": "gemma_accepted",
                        "artifact": str(cand),
                        "reason": "Verified accepted proof present",
                    }

    # 2. Check .agents/gemma_escalations/<decl>.json
    if escalations_dir.is_dir():
        cand_files: List[Path] = []
        for stem in stems:
            p = escalations_dir / f"{stem}.json"
            if p.is_file() and p not in cand_files:
                cand_files.append(p)
        # Also scan all json files in escalations_dir by declaration field
        for p in sorted(escalations_dir.glob("*.json")):
            if p not in cand_files:
                cand_files.append(p)

        for p in cand_files:
            try:
                data = json.loads(p.read_text(encoding="utf-8"))
            except Exception:
                continue
            rec_names = {
                data.get("declaration", ""),
                data.get("raw_name", ""),
                data.get("declaration", "").rsplit(".", 1)[-1],
            }
            if not (rec_names & {decl.name, decl.raw_name, decl.short_name}):
                continue
            attempts = data.get("attempts", [])
            failed_attempts = [a for a in attempts if not a.get("accepted", False)]
            if len(failed_attempts) >= required_attempts:
                return {
                    "declaration": decl.name,
                    "raw_name": decl.raw_name,
                    "tier": tier,
                    "ok": True,
                    "origin": "escalated",
                    "artifact": str(p),
                    "attempts_count": len(failed_attempts),
                    "reason": f"Escalation file present with {len(failed_attempts)} recorded failed attempts",
                }
            return {
                "declaration": decl.name,
                "raw_name": decl.raw_name,
                "tier": tier,
                "ok": False,
                "origin": "insufficient_attempts",
                "artifact": str(p),
                "attempts_count": len(failed_attempts),
                "reason": (
                    f"Escalation file {p.name} has only {len(failed_attempts)} failed attempt(s); "
                    f"{required_attempts} required"
                ),
            }

    return {
        "declaration": decl.name,
        "raw_name": decl.raw_name,
        "tier": tier,
        "ok": False,
        "origin": "missing",
        "artifact": None,
        "reason": (
            f"Missing .agents/gemma_accepted/{stems[0]}.lean or "
            f".agents/gemma_escalations/{stems[0]}.json with {required_attempts} failed attempts"
        ),
    }


def find_new_declarations_between_texts(
    old_text: str,
    new_text: str,
    file_path: str = "",
) -> List[Tuple[gemma_loop.SpecDeclaration, Optional[str]]]:
    """
    Compare `old_text` and `new_text` of a Lean file and return all NEW declarations
    along with their resolved tier ('T0', 'T1', 'T2', or None).
    """
    old_decls = gemma_loop.parse_spec_declarations(old_text) if old_text.strip() else []
    old_names: Set[str] = set()
    for d in old_decls:
        old_names.add(d.name)
        old_names.add(d.raw_name)

    new_decls = gemma_loop.parse_spec_declarations(new_text)
    added: List[Tuple[gemma_loop.SpecDeclaration, Optional[str]]] = []
    prev_end = 0
    for d in new_decls:
        tier = determine_declaration_tier(new_text, d, prev_decl_end=prev_end)
        prev_end = d.end_offset
        if d.name in old_names or d.raw_name in old_names:
            continue
        added.append((d, tier))
    return added


def _git_file_at_rev(repo_root: Path, rev: str, rel_path: str) -> str:
    """Return file content at git revision `rev`, or empty string if file did not exist."""
    try:
        return subprocess.check_output(
            ["git", "-C", str(repo_root), "show", f"{rev}:{rel_path}"],
            stderr=subprocess.DEVNULL,
            text=True,
        )
    except Exception:
        return ""


def _parse_diff_range_endpoints(diff_range: str) -> Tuple[str, Optional[str]]:
    """Split a git diff range like `main...HEAD` or `main..HEAD` into `(base_rev, head_rev)`."""
    if "..." in diff_range:
        base, head = diff_range.split("...", 1)
        return base.strip() or "main", head.strip() or "HEAD"
    if ".." in diff_range:
        base, head = diff_range.split("..", 1)
        return base.strip() or "main", head.strip() or "HEAD"
    return diff_range.strip(), None


def check_git_diff_provenance(
    repo_root: Path,
    diff_range: str = "main...HEAD",
    accepted_dir: Optional[Path] = None,
    escalations_dir: Optional[Path] = None,
    required_attempts: int = 5,
    explicit_files: Optional[Sequence[str]] = None,
) -> Dict[str, Any]:
    """
    Audit all new T0/T1 declarations introduced across `diff_range` (or `explicit_files`).
    """
    acc_dir = accepted_dir or (repo_root / ".agents" / "gemma_accepted")
    esc_dir = escalations_dir or (repo_root / ".agents" / "gemma_escalations")

    base_rev, head_rev = _parse_diff_range_endpoints(diff_range)

    if explicit_files is not None:
        changed_files = [f for f in explicit_files if f.endswith(".lean")]
    else:
        try:
            out = subprocess.check_output(
                ["git", "-C", str(repo_root), "diff", "--name-only", diff_range],
                stderr=subprocess.DEVNULL,
                text=True,
            )
            changed_files = [
                ln.strip()
                for ln in out.splitlines()
                if ln.strip().endswith(".lean")
            ]
        except Exception as exc:
            return {
                "passed": False,
                "error": f"git diff failed for '{diff_range}': {exc}",
                "checked": [],
                "violations": [],
            }

    checked: List[Dict[str, Any]] = []
    skipped_t2_or_other: List[Dict[str, Any]] = []
    violations: List[Dict[str, Any]] = []

    for rel_path in changed_files:
        old_text = _git_file_at_rev(repo_root, base_rev, rel_path) if base_rev else ""
        if head_rev:
            new_text = _git_file_at_rev(repo_root, head_rev, rel_path)
            if not new_text and (repo_root / rel_path).is_file():
                new_text = (repo_root / rel_path).read_text(encoding="utf-8", errors="replace")
        else:
            full_p = repo_root / rel_path
            new_text = full_p.read_text(encoding="utf-8", errors="replace") if full_p.is_file() else ""

        if not new_text:
            continue

        added_decls = find_new_declarations_between_texts(old_text, new_text, file_path=rel_path)
        for decl, tier in added_decls:
            if tier in ("T0", "T1"):
                res = check_declaration_provenance(
                    decl=decl,
                    tier=tier,
                    accepted_dir=acc_dir,
                    escalations_dir=esc_dir,
                    required_attempts=required_attempts,
                )
                res["file"] = rel_path
                checked.append(res)
                if not res["ok"]:
                    violations.append(res)
            else:
                skipped_t2_or_other.append({
                    "declaration": decl.name,
                    "tier": tier or "unclassified",
                    "file": rel_path,
                })

    origin_counts = {
        "gemma_accepted": sum(1 for c in checked if c["origin"] == "gemma_accepted"),
        "escalated": sum(1 for c in checked if c["origin"] == "escalated"),
        "violations": len(violations),
        "t2_or_unclassified": len(skipped_t2_or_other),
    }

    return {
        "passed": len(violations) == 0,
        "diff_range": diff_range,
        "files_scanned": changed_files,
        "t0_t1_checked_count": len(checked),
        "origin_counts": origin_counts,
        "checked": checked,
        "skipped": skipped_t2_or_other,
        "violations": violations,
    }


def main() -> int:
    parser = argparse.ArgumentParser(
        description="Verify local-model (gemma4:12B) provenance for new T0/T1 Lean declarations"
    )
    parser.add_argument(
        "diff_range_pos",
        nargs="?",
        default=None,
        help="Optional positional git diff range (default: main...HEAD)",
    )
    parser.add_argument("--diff", default=None, help="Git diff range to inspect (default: main...HEAD)")
    parser.add_argument("--root", default=None, help="Override repository root")
    parser.add_argument("--accepted-dir", default=None, help="Override .agents/gemma_accepted directory")
    parser.add_argument("--escalations-dir", default=None, help="Override .agents/gemma_escalations directory")
    parser.add_argument("--required-attempts", type=int, default=5, help="Required failed attempts for escalation (default 5)")
    parser.add_argument("--files", nargs="*", default=None, help="Explicit .lean files to check instead of git diff --name-only")
    parser.add_argument("--json", action="store_true", help="Emit JSON output")

    args = parser.parse_args()
    root = bm25_index.resolve_repo_root(args.root)
    diff_range = args.diff or args.diff_range_pos or "main...HEAD"
    acc_dir = Path(args.accepted_dir) if args.accepted_dir else None
    esc_dir = Path(args.escalations_dir) if args.escalations_dir else None

    report = check_git_diff_provenance(
        repo_root=root,
        diff_range=diff_range,
        accepted_dir=acc_dir,
        escalations_dir=esc_dir,
        required_attempts=args.required_attempts,
        explicit_files=args.files,
    )

    if args.json:
        print(json.dumps(report, indent=2))
    else:
        status = "PASSED" if report.get("passed") else "FAILED"
        print(
            f"[G8 Provenance {status}] diff={diff_range} | "
            f"T0/T1 declarations checked: {report.get('t0_t1_checked_count', 0)} | "
            f"gemma_accepted: {report.get('origin_counts', {}).get('gemma_accepted', 0)} | "
            f"escalated: {report.get('origin_counts', {}).get('escalated', 0)} | "
            f"violations: {len(report.get('violations', []))}"
        )
        for c in report.get("checked", []):
            mark = "OK" if c["ok"] else "FAIL"
            print(f"  [{mark}] {c['declaration']} (tier {c['tier']}, {c['file']}): {c['reason']}")
        if report.get("error"):
            print(f"  [ERROR] {report['error']}", file=sys.stderr)

    return 0 if report.get("passed") else 1


if __name__ == "__main__":
    sys.exit(main())
