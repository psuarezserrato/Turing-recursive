#!/usr/bin/env python3
"""
tools/ledger.py — Verified Outcome Ledger for Local gemma4:12B Prover

Records every local model attempt to `.agents/gemma_usage.jsonl` with compiler-verified
`accepted` outcomes (`True`/`False`, never self-reported), classified Lean compiler errors,
token counts, model latency, and Lean verification latency. Provides per-tier,
per-milestone, and per-origin summary reporting.
"""

import argparse
import hashlib
import json
import os
import sys
from collections import Counter, defaultdict
from datetime import datetime, timezone
from pathlib import Path
from typing import Any, Dict, List, Optional

MAIN_REPO = Path("/Users/pablosuarez/Desktop/Turing-recursive")
LEDGER_REL = Path(".agents/gemma_usage.jsonl")

ERROR_CLASSES = (
    "none",
    "unknown identifier",
    "type mismatch",
    "unsolved goals",
    "timeout",
    "syntax",
    "other",
    "unverified",
)


def utc_now() -> str:
    """Return current UTC ISO-8601 timestamp."""
    return datetime.now(timezone.utc).strftime("%Y-%m-%dT%H:%M:%SZ")


def resolve_main_repo(root_override: Optional[Path] = None) -> Path:
    """Resolve the shared main repository root so usage logs stay centralized across worktrees."""
    if root_override:
        return Path(root_override).resolve()
    env_root = os.environ.get("TURING_RECURSIVE_ROOT")
    if env_root:
        return Path(env_root).resolve()
    if MAIN_REPO.is_dir():
        return MAIN_REPO
    return Path(__file__).resolve().parent.parent


def default_ledger_path(root_override: Optional[Path] = None) -> Path:
    """Return the default `.agents/gemma_usage.jsonl` path."""
    return resolve_main_repo(root_override) / LEDGER_REL


def classify_lean_error(
    compiler_output: str,
    timed_out: bool = False,
    accepted: Optional[bool] = None,
) -> str:
    """
    Classify a Lean 4 compiler diagnostic into one of:
    'none' (if accepted is True), 'unverified' (if accepted is None and no error),
    'unknown identifier', 'type mismatch', 'unsolved goals', 'timeout', 'syntax', or 'other'.
    """
    if accepted is True:
        return "none"
    if timed_out:
        return "timeout"
    text = (compiler_output or "").lower()
    if not text.strip():
        return "unverified" if accepted is None else "other"

    if "timeout" in text or "timed out" in text or "(deterministic) timeout" in text:
        return "timeout"
    if (
        "unknown identifier" in text
        or "unknown constant" in text
        or "unknown namespace" in text
        or "unknown field" in text
    ):
        return "unknown identifier"
    if (
        "type mismatch" in text
        or "application type mismatch" in text
        or "failed to synthesize" in text
        or "synthesizing" in text
    ):
        return "type mismatch"
    if "unsolved goals" in text:
        return "unsolved goals"
    if (
        "unexpected token" in text
        or "expected token" in text
        or "parse error" in text
        or "unknown tactic" in text
        or "unterminated" in text
        or "expected '" in text
        or "expected command" in text
    ):
        return "syntax"
    return "other"


def append_usage_record(
    declaration: str = "",
    milestone: str = "",
    tier: str = "unclassified",
    attempt: int = 1,
    accepted: Optional[bool] = None,
    error_class: Optional[str] = None,
    compiler_output: str = "",
    timed_out: bool = False,
    tokens: Optional[int] = None,
    latency_ms: float = 0.0,
    lean_ms: float = 0.0,
    model: str = "gemma4:12B",
    task_type: str = "prove",
    prompt_text: str = "",
    status: str = "success",
    error: Optional[str] = None,
    origin: str = "gemma",
    ledger_path: Optional[Path] = None,
) -> Dict[str, Any]:
    """
    Append a structured record to `.agents/gemma_usage.jsonl`.
    Note: `accepted` MUST be set only by an actual Lean compiler check (True/False),
    or left None for unverified standalone calls.
    """
    target_path = Path(ledger_path) if ledger_path else default_ledger_path()
    target_path.parent.mkdir(parents=True, exist_ok=True)

    resolved_error_class = error_class or classify_lean_error(
        compiler_output or (error or ""),
        timed_out=timed_out,
        accepted=accepted,
    )

    record: Dict[str, Any] = {
        "timestamp": utc_now(),
        "milestone": milestone or "",
        "declaration": declaration or "",
        "tier": tier or "unclassified",
        "attempt": int(attempt),
        "accepted": accepted if isinstance(accepted, bool) else None,
        "error_class": resolved_error_class,
        "tokens": int(tokens) if tokens is not None else 0,
        "latency_ms": round(float(latency_ms), 2),
        "lean_ms": round(float(lean_ms), 2),
        "model": model,
        "task_type": task_type,
        "origin": origin,
        "status": status,
        "prompt_sha256_16": (
            hashlib.sha256(prompt_text.encode("utf-8")).hexdigest()[:16]
            if prompt_text
            else ""
        ),
        "error": error,
    }
    with open(target_path, "a", encoding="utf-8") as f:
        f.write(json.dumps(record) + "\n")
    return record


def load_ledger(ledger_path: Optional[Path] = None) -> List[Dict[str, Any]]:
    """Read all valid JSON records from the usage ledger."""
    target_path = Path(ledger_path) if ledger_path else default_ledger_path()
    if not target_path.is_file():
        return []
    rows: List[Dict[str, Any]] = []
    with open(target_path, "r", encoding="utf-8") as f:
        for line in f:
            line = line.strip()
            if not line:
                continue
            try:
                rows.append(json.loads(line))
            except Exception:
                pass
    return rows


def _compute_group_metrics(records: List[Dict[str, Any]]) -> Dict[str, Any]:
    """Compute attempt and declaration-level pass@1, pass@5, latency, and error breakdown."""
    calls = len(records)
    verified = [r for r in records if isinstance(r.get("accepted"), bool)]
    accepted_calls = sum(1 for r in verified if r.get("accepted") is True)
    rejected_calls = sum(1 for r in verified if r.get("accepted") is False)

    by_decl: Dict[str, List[Dict[str, Any]]] = defaultdict(list)
    for r in verified:
        decl = r.get("declaration") or ""
        if decl:
            by_decl[decl].append(r)

    total_decls = len(by_decl)
    pass1_decls = 0
    pass5_decls = 0
    for decl, d_recs in by_decl.items():
        if any(r.get("accepted") is True and int(r.get("attempt", 1)) == 1 for r in d_recs):
            pass1_decls += 1
        if any(r.get("accepted") is True and int(r.get("attempt", 1)) <= 5 for r in d_recs):
            pass5_decls += 1

    tokens_list = [int(r.get("tokens") or r.get("eval_count") or 0) for r in records]
    lat_list = [float(r.get("latency_ms") or 0.0) for r in records]
    lean_list = [float(r.get("lean_ms") or 0.0) for r in verified]
    err_counts = Counter(r.get("error_class", "unverified") for r in records)

    return {
        "calls": calls,
        "verified_calls": len(verified),
        "accepted_calls": accepted_calls,
        "rejected_calls": rejected_calls,
        "call_acceptance_rate": round(accepted_calls / len(verified), 4) if verified else 0.0,
        "declarations": total_decls,
        "pass_at_1_count": pass1_decls,
        "pass_at_1": round(pass1_decls / total_decls, 4) if total_decls else 0.0,
        "pass_at_5_count": pass5_decls,
        "pass_at_5": round(pass5_decls / total_decls, 4) if total_decls else 0.0,
        "mean_tokens": round(sum(tokens_list) / len(tokens_list), 1) if tokens_list else 0.0,
        "mean_latency_ms": round(sum(lat_list) / len(lat_list), 2) if lat_list else 0.0,
        "mean_lean_ms": round(sum(lean_list) / len(lean_list), 2) if lean_list else 0.0,
        "error_classes": dict(err_counts),
    }


def summarize_ledger(
    ledger_path: Optional[Path] = None,
    repo_root: Optional[Path] = None,
) -> Dict[str, Any]:
    """Build full ledger summary with per-tier, per-milestone, and per-origin metrics."""
    rows = load_ledger(ledger_path)
    root = resolve_main_repo(repo_root)

    by_tier_rows: Dict[str, List[Dict[str, Any]]] = defaultdict(list)
    by_milestone_rows: Dict[str, List[Dict[str, Any]]] = defaultdict(list)
    by_model: Counter = Counter()
    by_task: Counter = Counter()

    for r in rows:
        tier = r.get("tier") or "unclassified"
        milestone = r.get("milestone") or "unassigned"
        by_tier_rows[tier].append(r)
        by_milestone_rows[milestone].append(r)
        by_model[r.get("model", "unknown")] += 1
        by_task[r.get("task_type", "unknown")] += 1

    overall = _compute_group_metrics(rows)
    by_tier = {t: _compute_group_metrics(recs) for t, recs in sorted(by_tier_rows.items())}
    by_milestone = {m: _compute_group_metrics(recs) for m, recs in sorted(by_milestone_rows.items())}

    # Compute counts by origin from both the ledger and .agents/gemma_{accepted,escalations}
    by_decl: Dict[str, List[Dict[str, Any]]] = defaultdict(list)
    for r in rows:
        decl = r.get("declaration") or ""
        if decl and isinstance(r.get("accepted"), bool):
            by_decl[decl].append(r)

    gemma_accepted_decls = {
        decl for decl, recs in by_decl.items() if any(r.get("accepted") is True for r in recs)
    }
    escalated_decls = {
        decl
        for decl, recs in by_decl.items()
        if decl not in gemma_accepted_decls
        and (len(recs) >= 5 or any(int(r.get("attempt", 0)) >= 5 for r in recs))
    }
    partial_failed_decls = set(by_decl.keys()) - gemma_accepted_decls - escalated_decls

    accepted_dir = root / ".agents" / "gemma_accepted"
    escalations_dir = root / ".agents" / "gemma_escalations"
    accepted_files = list(accepted_dir.glob("*.lean")) if accepted_dir.is_dir() else []
    escalation_files = list(escalations_dir.glob("*.json")) if escalations_dir.is_dir() else []

    by_origin = {
        "gemma_accepted": len(gemma_accepted_decls),
        "escalated_to_frontier": len(escalated_decls),
        "partial_failed": len(partial_failed_decls),
        "unverified_calls": sum(1 for r in rows if r.get("accepted") is None),
        "accepted_artifact_files": len(accepted_files),
        "escalation_artifact_files": len(escalation_files),
    }

    return {
        "total_calls": len(rows),
        "overall": overall,
        "by_tier": by_tier,
        "by_milestone": by_milestone,
        "by_origin": by_origin,
        "by_model": dict(by_model),
        "by_task": dict(by_task),
    }


def format_summary_text(summary: Dict[str, Any]) -> str:
    """Format ledger summary as a human-readable report."""
    lines: List[str] = []
    ov = summary["overall"]
    lines.append(
        f"Total local Ollama calls: {summary['total_calls']} "
        f"(verified: {ov['verified_calls']}, accepted: {ov['accepted_calls']}, "
        f"rejected: {ov['rejected_calls']})"
    )
    lines.append(
        f"Overall declarations: {ov['declarations']} | "
        f"pass@1: {ov['pass_at_1_count']}/{ov['declarations']} ({ov['pass_at_1']*100:.1f}%) | "
        f"pass@5: {ov['pass_at_5_count']}/{ov['declarations']} ({ov['pass_at_5']*100:.1f}%)"
    )

    lines.append("\nAcceptance per tier:")
    if not summary["by_tier"]:
        lines.append("  (none)")
    for tier, m in summary["by_tier"].items():
        lines.append(
            f"  {tier:<12} decls={m['declarations']:<3} "
            f"pass@1={m['pass_at_1_count']}/{m['declarations']} ({m['pass_at_1']*100:5.1f}%) "
            f"pass@5={m['pass_at_5_count']}/{m['declarations']} ({m['pass_at_5']*100:5.1f}%) "
            f"calls={m['calls']:<3} mean_tok={m['mean_tokens']:<6.1f} "
            f"mean_lat={m['mean_latency_ms']:<7.1f}ms mean_lean={m['mean_lean_ms']:<7.1f}ms"
        )

    lines.append("\nAcceptance per milestone:")
    if not summary["by_milestone"]:
        lines.append("  (none)")
    for ms, m in summary["by_milestone"].items():
        lines.append(
            f"  {ms:<12} decls={m['declarations']:<3} "
            f"pass@1={m['pass_at_1_count']}/{m['declarations']} ({m['pass_at_1']*100:5.1f}%) "
            f"pass@5={m['pass_at_5_count']}/{m['declarations']} ({m['pass_at_5']*100:5.1f}%) "
            f"calls={m['calls']:<3}"
        )

    lines.append("\nCounts by origin:")
    for k, v in summary["by_origin"].items():
        lines.append(f"  {k}: {v}")

    lines.append("\nError class distribution:")
    for k, v in sorted(ov["error_classes"].items()):
        lines.append(f"  {k}: {v}")
    return "\n".join(lines)


def main() -> int:
    parser = argparse.ArgumentParser(
        description="Verified outcome ledger and summary reporter for local gemma4:12B prover"
    )
    parser.add_argument("--ledger", default=None, help="Override path to gemma_usage.jsonl")
    parser.add_argument("--root", default=None, help="Override repository root")
    parser.add_argument("--json", action="store_true", help="Emit JSON output")
    sub = parser.add_subparsers(dest="command")

    p_sum = sub.add_parser("summary", help="Report acceptance per tier, per milestone, and counts by origin")
    p_sum.add_argument("--json", action="store_true", dest="sub_json", help="Emit JSON output")

    p_rec = sub.add_parser("record", help="Append a verified outcome record to the ledger")
    p_rec.add_argument("--declaration", required=True)
    p_rec.add_argument("--milestone", default="W0")
    p_rec.add_argument("--tier", default="T1")
    p_rec.add_argument("--attempt", type=int, default=1)
    p_rec.add_argument("--accepted", choices=["true", "false", "null"], default="null")
    p_rec.add_argument("--error-class", default=None)
    p_rec.add_argument("--compiler-output", default="")
    p_rec.add_argument("--tokens", type=int, default=0)
    p_rec.add_argument("--latency-ms", type=float, default=0.0)
    p_rec.add_argument("--lean-ms", type=float, default=0.0)

    args = parser.parse_args()
    ledger_path = Path(args.ledger) if args.ledger else default_ledger_path(
        Path(args.root) if args.root else None
    )

    if args.command == "record":
        acc: Optional[bool] = None
        if args.accepted == "true":
            acc = True
        elif args.accepted == "false":
            acc = False
        rec = append_usage_record(
            declaration=args.declaration,
            milestone=args.milestone,
            tier=args.tier,
            attempt=args.attempt,
            accepted=acc,
            error_class=args.error_class,
            compiler_output=args.compiler_output,
            tokens=args.tokens,
            latency_ms=args.latency_ms,
            lean_ms=args.lean_ms,
            ledger_path=ledger_path,
        )
        if args.json:
            print(json.dumps(rec, indent=2))
        else:
            print(f"Recorded {rec['declaration']} attempt {rec['attempt']} (accepted={rec['accepted']})")
        return 0

    # Default or `summary`
    summary = summarize_ledger(
        ledger_path=ledger_path,
        repo_root=Path(args.root) if args.root else None,
    )
    if args.json or getattr(args, "sub_json", False):
        print(json.dumps(summary, indent=2))
    else:
        print(format_summary_text(summary))
    return 0


if __name__ == "__main__":
    sys.exit(main())
