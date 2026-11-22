#!/usr/bin/env python3
"""
tools/workflow_control.py — Clean Pause/Resume, Status & Checkpoint Control for Turing-recursive

Manages the shared `.pause_workflow` sentinel in the main repository root so all
isolated Git worktrees and the swarm coordinator coordinate cleanly when pausing
or resuming work.
"""

import argparse
import json
import os
import re
import shutil
import subprocess
import sys
import tempfile
import threading
import uuid
from datetime import datetime, timezone
from pathlib import Path
from typing import Any, Dict, List, Optional

SENTINEL_FILENAME = ".pause_workflow"
CHECKPOINTS_REL = ".agents/checkpoints"
USAGE_LOG_REL = ".agents/gemma_usage.jsonl"

CONTRACT_FILES: Dict[str, str] = {
    "M1": "TuringRecursive/Eval.lean",
    "M2a": "TuringRecursive/ListPrimrec.lean",
    "M2": "TuringRecursive/Encoding.lean",
    "M3": "TuringRecursive/TM0Eval.lean",
    "M4": "TuringRecursive/Uniform.lean",
    "M5": "TuringRecursive/Equivalence.lean",
    "M6": "TuringRecursive/Universal.lean",
    "M7": "TuringRecursive/Stretch.lean",
}

SORRY_RE = re.compile(r"\b(sorry|admit)\b")


def strip_lean_comments(source: str) -> str:
    """Remove nested Lean block comments `/- ... -/` and line comments `-- ...`, preserving string literals."""
    out: List[str] = []
    i, n, depth = 0, len(source), 0
    while i < n:
        if depth == 0 and source[i] == "'" and (i == 0 or not (source[i - 1].isalnum() or source[i - 1] in "_'")):
            if i + 3 < n and source[i + 1] == "\\" and source[i + 3] == "'":
                out.append(source[i:i + 4])
                i += 4
                continue
            if i + 2 < n and source[i + 1] not in ("\\", "\n", "'") and source[i + 2] == "'":
                out.append(source[i:i + 3])
                i += 3
                continue
        if depth == 0 and source[i] == '"':
            out.append('"')
            i += 1
            while i < n:
                ch = source[i]
                out.append(ch)
                if ch == "\\" and i + 1 < n:
                    out.append(source[i + 1])
                    i += 2
                elif ch == '"':
                    i += 1
                    break
                else:
                    i += 1
        elif source[i:i + 2] == "/-":
            depth += 1
            i += 2
        elif depth > 0 and source[i:i + 2] == "-/":
            depth -= 1
            i += 2
        elif depth == 0 and source[i:i + 2] == "--":
            while i < n and source[i] != "\n":
                i += 1
        else:
            if depth == 0:
                out.append(source[i])
            i += 1
    return "".join(out)


def utc_now() -> str:
    """Return current UTC ISO-8601 timestamp."""
    return datetime.now(timezone.utc).strftime("%Y-%m-%dT%H:%M:%SZ")


def resolve_root(root_arg: Optional[str] = None) -> Path:
    """Resolve the repository root shared across worktrees."""
    if root_arg:
        return Path(root_arg).resolve()
    env_root = os.environ.get("TURING_RECURSIVE_ROOT")
    if env_root:
        return Path(env_root).resolve()
    here_root = Path(__file__).resolve().parent.parent
    try:
        raw = subprocess.check_output(
            ["git", "-C", str(here_root), "rev-parse", "--git-common-dir"],
            stderr=subprocess.DEVNULL,
            text=True,
            timeout=2.0,
        ).strip()
        if raw:
            p = Path(raw)
            p = (here_root / p).resolve() if not p.is_absolute() else p.resolve()
            if p.name == ".git":
                return p.parent
    except Exception:
        pass
    return here_root


class WorkflowController:
    """Atomic pause/resume sentinel, contract scanner, and checkpoint manager."""

    def __init__(self, root_dir: Optional[Path] = None):
        self.root_dir = Path(root_dir) if root_dir else resolve_root()
        self.sentinel_path = self.root_dir / SENTINEL_FILENAME
        self.checkpoints_dir = self.root_dir / CHECKPOINTS_REL
        self.usage_log_path = self.root_dir / USAGE_LOG_REL

    def is_paused(self) -> bool:
        return self.sentinel_path.is_file()

    def get_pause_data(self) -> Optional[Dict[str, Any]]:
        if not self.is_paused():
            return None
        try:
            with open(self.sentinel_path, "r", encoding="utf-8") as f:
                return json.load(f)
        except Exception as exc:
            return {"paused": True, "error": str(exc)}

    def scan_contracts(self) -> Dict[str, Any]:
        contracts: Dict[str, Any] = {}
        present = 0
        sorry_free = 0
        for cid, rel_path in CONTRACT_FILES.items():
            full = self.root_dir / rel_path
            if full.is_file():
                text = full.read_text(encoding="utf-8", errors="replace")
                lines = text.splitlines()
                sorry_count = len(SORRY_RE.findall(strip_lean_comments(text)))
                contracts[cid] = {
                    "path": rel_path,
                    "exists": True,
                    "lines": len(lines),
                    "sorry_count": sorry_count,
                }
                present += 1
                if sorry_count == 0:
                    sorry_free += 1
            else:
                contracts[cid] = {
                    "path": rel_path,
                    "exists": False,
                    "lines": 0,
                    "sorry_count": 0,
                }
        return {
            "total": len(CONTRACT_FILES),
            "present": present,
            "sorry_free": sorry_free,
            "contracts": contracts,
        }

    def gemma_stats(self) -> Dict[str, Any]:
        if not self.usage_log_path.is_file():
            return {"calls": 0, "by_model": {}}
        calls = 0
        by_model: Dict[str, int] = {}
        with open(self.usage_log_path, "r", encoding="utf-8") as f:
            for line in f:
                line = line.strip()
                if not line:
                    continue
                try:
                    rec = json.loads(line)
                    calls += 1
                    m = rec.get("model", "unknown")
                    by_model[m] = by_model.get(m, 0) + 1
                except Exception:
                    pass
        return {"calls": calls, "by_model": by_model}

    def git_worktrees(self) -> List[str]:
        try:
            out = subprocess.check_output(
                ["git", "-C", str(self.root_dir), "worktree", "list", "--porcelain"],
                stderr=subprocess.DEVNULL,
                text=True,
                timeout=3.0,
            )
            return [line[len("worktree "):] for line in out.splitlines() if line.startswith("worktree ")]
        except Exception:
            return []

    def get_status(self) -> Dict[str, Any]:
        paused = self.is_paused()
        scan = self.scan_contracts()
        return {
            "state": "PAUSED" if paused else "RUNNING",
            "paused": paused,
            "pause_info": self.get_pause_data(),
            "root_dir": str(self.root_dir),
            "timestamp": utc_now(),
            "worktrees": self.git_worktrees(),
            "gemma_usage": self.gemma_stats(),
            "summary": {
                "total": scan["total"],
                "present": scan["present"],
                "sorry_free": scan["sorry_free"],
            },
            "contracts": scan["contracts"],
        }

    def checkpoint(self, label: str = "manual") -> Dict[str, Any]:
        self.checkpoints_dir.mkdir(parents=True, exist_ok=True)
        status = self.get_status()
        stamp = datetime.now(timezone.utc).strftime("%Y%m%dT%H%M%SZ")
        safe_label = re.sub(r"[^A-Za-z0-9_.-]+", "_", label).strip("_") or "manual"
        ckpt_path = self.checkpoints_dir / f"ckpt_{stamp}_{safe_label}.json"
        record = {"label": label, "saved_at": utc_now(), "status": status}
        self._atomic_write_json(ckpt_path, record)
        record["checkpoint_path"] = str(ckpt_path)
        return record

    def pause(self, reason: str = "User requested pause", unload_ollama: bool = True) -> Dict[str, Any]:
        self.root_dir.mkdir(parents=True, exist_ok=True)
        ckpt = self.checkpoint(label="pause")
        record = {
            "paused": True,
            "paused_at": utc_now(),
            "reason": reason,
            "checkpoint_path": ckpt["checkpoint_path"],
            "ollama_unloaded": False,
        }
        if unload_ollama:
            ollama_bin = shutil.which("ollama") or ("/usr/local/bin/ollama" if os.path.isfile("/usr/local/bin/ollama") else None)
            if ollama_bin:
                try:
                    subprocess.run([ollama_bin, "stop", "gemma4:12B"], capture_output=True, timeout=5.0)
                    record["ollama_unloaded"] = True
                except Exception:
                    pass
        self._atomic_write_json(self.sentinel_path, record)
        return record

    def resume(self) -> Dict[str, Any]:
        prev = self.get_pause_data()
        if not self.is_paused():
            return {"resumed": False, "state": "RUNNING", "message": "Not currently paused."}
        try:
            self.sentinel_path.unlink()
        except FileNotFoundError:
            pass
        ollama_msg = "skipped"
        try:
            tools_dir = str(Path(__file__).resolve().parent)
            if tools_dir not in sys.path:
                sys.path.insert(0, tools_dir)
            import ollama_lean4_client
            _, ollama_msg, _ = ollama_lean4_client.ensure_ollama_daemon(autostart=True, timeout=8.0)
        except Exception as exc:
            ollama_msg = f"check error: {exc}"
        return {
            "resumed": True,
            "resumed_at": utc_now(),
            "state": "RUNNING",
            "previous_pause": prev,
            "ollama_status": ollama_msg,
        }

    def _atomic_write_json(self, dest: Path, payload: Dict[str, Any]) -> None:
        dest.parent.mkdir(parents=True, exist_ok=True)
        tmp = dest.parent / f".{dest.name}.tmp.{os.getpid()}.{threading.get_ident()}.{uuid.uuid4().hex[:8]}"
        try:
            with open(tmp, "w", encoding="utf-8") as f:
                json.dump(payload, f, indent=2)
                f.write("\n")
            tmp.replace(dest)
        except Exception:
            try:
                tmp.unlink()
            except Exception:
                pass
            raise


def run_self_tests() -> int:
    """Run isolated unit tests in a TemporaryDirectory without modifying live state."""
    with tempfile.TemporaryDirectory() as td:
        root = Path(td)
        (root / "TuringRecursive").mkdir()
        (root / "TuringRecursive" / "Eval.lean").write_text("theorem ok : True := trivial\n", encoding="utf-8")
        ctl = WorkflowController(root)
        assert not ctl.is_paused()
        st0 = ctl.get_status()
        assert st0["state"] == "RUNNING" and st0["summary"]["present"] == 1 and st0["summary"]["sorry_free"] == 1
        p = ctl.pause(reason="unit test", unload_ollama=False)
        assert p["paused"] and ctl.is_paused()
        assert (root / SENTINEL_FILENAME).is_file()
        assert Path(p["checkpoint_path"]).is_file()
        r = ctl.resume()
        assert r["resumed"] and not ctl.is_paused()
    print("workflow_control.py self-tests PASSED (5/5)")
    return 0


def main() -> int:
    parser = argparse.ArgumentParser(description="Turing-recursive workflow pause/resume/status control")
    parser.add_argument("--root", default=None, help="Override repository root")
    parser.add_argument("--json", action="store_true", help="Emit JSON output")
    sub = parser.add_subparsers(dest="cmd")

    p_pause = sub.add_parser("pause", help="Create .pause_workflow sentinel, save checkpoint, unload gemma4:12B")
    p_pause.add_argument("--reason", default="User requested pause")
    p_pause.add_argument("--keep-ollama", action="store_true", help="Do not run `ollama stop gemma4:12B`")

    sub.add_parser("resume", help="Remove .pause_workflow sentinel and verify Ollama daemon")
    sub.add_parser("status", help="Show pause state, worktrees, Gemma call count, and contract table")
    sub.add_parser("check-pause", help="Exit 42 if paused, 0 if running (for worker boundary checks)")

    p_ckpt = sub.add_parser("checkpoint", help="Save a progress snapshot JSON")
    p_ckpt.add_argument("--label", default="manual")

    sub.add_parser("test", help="Run isolated self-tests")

    args = parser.parse_args()
    if args.cmd == "test":
        return run_self_tests()

    ctl = WorkflowController(resolve_root(args.root))

    if args.cmd == "pause":
        res = ctl.pause(reason=args.reason, unload_ollama=not args.keep_ollama)
        if args.json:
            print(json.dumps(res, indent=2))
        else:
            print(f"[PAUSED] Sentinel written at {ctl.sentinel_path}")
            print(f"Reason: {res['reason']}")
            print(f"Checkpoint: {res['checkpoint_path']}")
            print(f"gemma4:12B unloaded: {res['ollama_unloaded']}")
            print(f"To resume later: python3 {ctl.root_dir}/tools/workflow_control.py resume")
        return 0

    if args.cmd == "resume":
        res = ctl.resume()
        if args.json:
            print(json.dumps(res, indent=2))
        else:
            print(f"[{res['state']}] {res.get('message', 'Sentinel cleared; ready to continue.')}")
            if "ollama_status" in res:
                print(f"Ollama: {res['ollama_status']}")
        return 0

    if args.cmd == "check-pause":
        if ctl.is_paused():
            data = ctl.get_pause_data() or {}
            print(f"PAUSED: {data.get('reason', 'paused')}")
            return 42
        print("RUNNING")
        return 0

    if args.cmd == "checkpoint":
        res = ctl.checkpoint(label=args.label)
        if args.json:
            print(json.dumps(res, indent=2))
        else:
            print(f"[CHECKPOINT] Saved {res['checkpoint_path']}")
        return 0

    # Default or `status`
    st = ctl.get_status()
    if args.json:
        print(json.dumps(st, indent=2))
    else:
        print(f"State: {st['state']} (root: {st['root_dir']})")
        if st["paused"] and st["pause_info"]:
            print(f"  Paused at: {st['pause_info'].get('paused_at')} — {st['pause_info'].get('reason')}")
        print(f"Worktrees: {len(st['worktrees'])}")
        for wt in st["worktrees"]:
            print(f"  - {wt}")
        print(f"Headless Ollama calls logged: {st['gemma_usage']['calls']} {st['gemma_usage']['by_model']}")
        print(f"Contracts ({st['summary']['present']}/{st['summary']['total']} present, {st['summary']['sorry_free']} sorry-free):")
        for cid, info in st["contracts"].items():
            mark = "OK" if info["exists"] and info["sorry_count"] == 0 else ("SORRY" if info["exists"] else "PENDING")
            print(f"  {cid:<7} [{mark:<7}] {info['path']} ({info['lines']} lines, {info['sorry_count']} sorry)")
    return 0


if __name__ == "__main__":
    sys.exit(main())
