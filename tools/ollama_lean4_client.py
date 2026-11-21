#!/usr/bin/env python3
"""
tools/ollama_lean4_client.py — Headless Local gemma4:12B Client for Lean 4

Zero-external-dependency Python 3 client talking to local Ollama
(http://localhost:11434/api/chat) for Lean 4 autoformalization, tactic synthesis,
premise selection, and proof skeletons in S4TuringPoisson.
"""

import argparse
import hashlib
import json
import os
import re
import shutil
import subprocess
import sys
import time
import urllib.error
import urllib.request
from datetime import datetime, timezone
from pathlib import Path
from typing import Any, Dict, List, Optional, Tuple

DEFAULT_OLLAMA_HOST = "http://localhost:11434"
MAIN_REPO = Path("/Users/pablosuarez/Desktop/Turing-recursive")
PRIMARY_MODEL = "gemma4:12B"
DEFAULT_CASCADE = [
    "gemma4:12B",
    "gemma-lean4:latest",
    "gemma2:9b-instruct-q5_K_M",
    "gemma2:9b",
]

DEFAULT_PROFILES: Dict[str, Dict[str, Any]] = {
    "prove": {
        "temperature": 1.0,
        "top_p": 0.95,
        "top_k": 64,
        "num_predict": 384,
        "num_ctx": 4096,
    },
    "autoformalize": {
        "temperature": 1.0,
        "top_p": 0.95,
        "top_k": 64,
        "num_predict": 768,
        "num_ctx": 4096,
    },
    "tactic": {
        "temperature": 1.0,
        "top_p": 0.95,
        "top_k": 64,
        "num_predict": 256,
        "num_ctx": 4096,
    },
    "premise": {
        "temperature": 1.0,
        "top_p": 0.95,
        "top_k": 64,
        "num_predict": 384,
        "num_ctx": 4096,
    },
    "skeleton": {
        "temperature": 1.0,
        "top_p": 0.95,
        "top_k": 64,
        "num_predict": 1024,
        "num_ctx": 4096,
    },
}


def resolve_main_repo() -> Path:
    """Resolve the shared main repository root so usage logs stay centralized across worktrees."""
    if MAIN_REPO.is_dir():
        return MAIN_REPO
    return Path(__file__).resolve().parent.parent


def load_config(config_path: Optional[str] = None) -> Dict[str, Any]:
    """Load config/ollama_gemma_config.json or return internal defaults."""
    candidates = []
    if config_path:
        candidates.append(Path(config_path))
    candidates.extend([
        Path(__file__).resolve().parent.parent / "config" / "ollama_gemma_config.json",
        resolve_main_repo() / "config" / "ollama_gemma_config.json",
    ])
    for cand in candidates:
        if cand.is_file():
            try:
                with open(cand, "r", encoding="utf-8") as f:
                    return json.load(f)
            except Exception:
                pass
    return {
        "service": {
            "default_host": DEFAULT_OLLAMA_HOST,
            "connect_timeout_seconds": 3.0,
            "request_timeout_seconds": 120.0,
            "keep_alive": 0,
        },
        "primary_model": PRIMARY_MODEL,
        "model_fallback_cascade": DEFAULT_CASCADE,
        "parameter_profiles": DEFAULT_PROFILES,
    }


ACTIVE_CONFIG = load_config()


def find_ollama_binary() -> Optional[str]:
    """Locate the ollama CLI executable."""
    candidates = [
        shutil.which("ollama"),
        "/usr/local/bin/ollama",
        "/opt/homebrew/bin/ollama",
        "/Applications/Ollama.app/Contents/Resources/ollama",
        os.path.expanduser("~/.local/bin/ollama"),
    ]
    for c in candidates:
        if c and os.path.isfile(c) and os.access(c, os.X_OK):
            return os.path.abspath(c)
    return None


def http_get_json(url: str, timeout: float = 3.0) -> Tuple[bool, Any, str]:
    """Perform a GET request returning parsed JSON."""
    req = urllib.request.Request(url, headers={"User-Agent": "S4TuringPoisson-OllamaClient/1.0"})
    try:
        with urllib.request.urlopen(req, timeout=timeout) as resp:
            if resp.status != 200:
                return False, {}, f"HTTP {resp.status}"
            return True, json.loads(resp.read().decode("utf-8")), "ok"
    except Exception as exc:
        return False, {}, str(exc)


def http_post_json(url: str, payload: Dict[str, Any], timeout: float = 120.0) -> Tuple[bool, Any, str]:
    """Perform a POST request with JSON body returning parsed JSON."""
    data = json.dumps(payload).encode("utf-8")
    req = urllib.request.Request(
        url,
        data=data,
        headers={
            "Content-Type": "application/json",
            "User-Agent": "S4TuringPoisson-OllamaClient/1.0",
        },
    )
    try:
        with urllib.request.urlopen(req, timeout=timeout) as resp:
            if resp.status != 200:
                return False, {}, f"HTTP {resp.status}"
            return True, json.loads(resp.read().decode("utf-8")), "ok"
    except urllib.error.HTTPError as exc:
        body = exc.read().decode("utf-8", errors="replace") if exc.fp else str(exc)
        return False, {}, f"HTTP {exc.code}: {body}"
    except Exception as exc:
        return False, {}, str(exc)


def is_ollama_running(base_url: str = DEFAULT_OLLAMA_HOST, timeout: float = 2.0) -> bool:
    """Return True if Ollama server responds on /api/tags."""
    ok, _, _ = http_get_json(f"{base_url.rstrip('/')}/api/tags", timeout=timeout)
    return ok


def ensure_ollama_daemon(
    base_url: str = DEFAULT_OLLAMA_HOST,
    autostart: bool = True,
    timeout: float = 12.0,
) -> Tuple[bool, str, Optional[int]]:
    """Ensure local Ollama daemon is responding, starting headless `ollama serve` if needed."""
    if is_ollama_running(base_url, timeout=2.0):
        return True, f"Ollama daemon active at {base_url}", None
    if not autostart:
        return False, f"Ollama daemon not responding at {base_url} (autostart disabled)", None
    ollama_bin = find_ollama_binary()
    if not ollama_bin:
        return False, "ollama executable not found in PATH or /usr/local/bin", None
    try:
        daemon_env = os.environ.copy()
        daemon_env["OLLAMA_NUM_PARALLEL"] = "1"
        daemon_env["OLLAMA_CONTEXT_LENGTH"] = "4096"
        proc = subprocess.Popen(
            [ollama_bin, "serve"],
            env=daemon_env,
            stdout=subprocess.DEVNULL,
            stderr=subprocess.DEVNULL,
            start_new_session=True,
            close_fds=True,
        )
    except Exception as exc:
        return False, f"Failed to start headless ollama serve: {exc}", None

    deadline = time.time() + timeout
    while time.time() < deadline:
        time.sleep(0.4)
        if is_ollama_running(base_url, timeout=1.5):
            return True, f"Started headless ollama serve (PID {proc.pid}) at {base_url}", proc.pid
    return False, f"Spawned ollama serve (PID {proc.pid}) but timed out after {timeout}s", proc.pid


def unload_model(model: str = PRIMARY_MODEL, timeout: float = 5.0) -> bool:
    """Explicitly stop/unload an Ollama model from unified RAM via `ollama stop <model>`."""
    ollama_bin = find_ollama_binary()
    if not ollama_bin:
        return False
    try:
        proc = subprocess.run([ollama_bin, "stop", model], capture_output=True, timeout=timeout)
        return proc.returncode == 0
    except Exception:
        return False


def list_installed_models(base_url: str = DEFAULT_OLLAMA_HOST, timeout: float = 3.0) -> Tuple[bool, List[Dict[str, Any]], str]:
    """Fetch installed model objects from /api/tags."""
    ok, msg, _ = ensure_ollama_daemon(base_url, autostart=True, timeout=8.0)
    if not ok:
        return False, [], msg
    ok, data, msg = http_get_json(f"{base_url.rstrip('/')}/api/tags", timeout=timeout)
    if not ok:
        return False, [], msg
    return True, data.get("models", []), "ok"


def select_model(installed: List[str], preferred: Optional[str] = None) -> Tuple[Optional[str], str]:
    """Choose requested model or first match in configured cascade (defaulting to gemma4:12B)."""
    cascade = ACTIVE_CONFIG.get("model_fallback_cascade", DEFAULT_CASCADE)
    order = ([preferred] if preferred else []) + [c for c in cascade if c != preferred]
    for target in order:
        if target in installed:
            return target, f"exact match '{target}'"
    for target in order:
        low = target.lower()
        for inst in installed:
            if inst.lower() == low or inst.lower().startswith(f"{low}:"):
                return inst, f"matched '{inst}' for '{target}'"
    if installed:
        return installed[0], f"fallback to first installed model '{installed[0]}'"
    return None, "no Ollama models installed"


def extract_lean_code(raw_text: str) -> str:
    """Extract the first ```lean4 or ```lean fenced code block, or return stripped text."""
    blocks = re.findall(r"```(?:lean4|lean)?\s*(.*?)\s*```", raw_text, re.DOTALL | re.IGNORECASE)
    if blocks:
        return blocks[0].strip()
    return raw_text.strip()


def build_messages(task_type: str, prompt: str, goal: Optional[str] = None,
                   error: Optional[str] = None, failed_tactic: Optional[str] = None) -> List[Dict[str, str]]:
    """Build system/user chat messages for the specified Lean 4 task."""
    if task_type == "autoformalize":
        sys_msg = (
            "You are an expert Lean 4 formalizer working with Mathlib v4.36.0 and TauCeti "
            "(Poisson geometry, symplectic manifolds, singular Lefschetz/wrinkled fibrations, and TM0 computability). "
            "Translate the informal statement into valid Lean 4 using snake_case for terms/theorems, "
            "UpperCamelCase for structures/classes, explicit smoothness/non-vanishing hypotheses, "
            "and enclose output in a single ```lean4 ... ``` block."
        )
        user_msg = f"Formalize in Lean 4:\n{prompt.strip()}"
    elif task_type == "tactic":
        sys_msg = (
            "You are a Lean 4 (v4.36.0 / Mathlib) tactic assistant. "
            "Given a goal state and optional compiler error, propose the minimal valid Lean 4 tactic or proof snippet. "
            "Never invent unverified lemma names; enclose code in a ```lean4 ... ``` block."
        )
        parts = []
        if goal:
            parts.append(f"Goal state:\n```lean4\n{goal.strip()}\n```")
        if failed_tactic:
            parts.append(f"Failed tactic:\n`{failed_tactic.strip()}`")
        if error:
            parts.append(f"Compiler diagnostic:\n```\n{error.strip()}\n```")
        if prompt:
            parts.append(prompt.strip())
        user_msg = "\n\n".join(parts)
    elif task_type == "premise":
        sys_msg = (
            "You are a Mathlib v4.36.0 and TauCeti premise retrieval assistant. "
            "List up to 6 likely Lean 4 / Mathlib / TauCeti declaration names and concise type hints relevant to the goal."
        )
        user_msg = f"Goal and context:\n```lean4\n{(goal or prompt).strip()}\n```"
    else:  # skeleton
        sys_msg = (
            "You are a Lean 4 mathematical architect. Decompose the theorem into 3 to 6 clean helper lemmas "
            "with valid Lean 4 signatures and short proof outlines inside a single ```lean4 ... ``` block."
        )
        user_msg = prompt.strip()
    return [
        {"role": "system", "content": sys_msg},
        {"role": "user", "content": user_msg},
    ]


def log_gemma_usage(
    model: str,
    task_type: str,
    prompt_text: str,
    elapsed_ms: float,
    status: str,
    eval_count: Optional[int] = None,
    declaration: Optional[str] = None,
    error: Optional[str] = None,
    milestone: str = "",
    tier: str = "unclassified",
    attempt: int = 1,
    accepted: Optional[bool] = None,
    error_class: Optional[str] = None,
    lean_ms: float = 0.0,
) -> None:
    """Append a structured record to <main_repo>/.agents/gemma_usage.jsonl via tools/ledger.py."""
    try:
        tools_dir = str(Path(__file__).resolve().parent)
        if tools_dir not in sys.path:
            sys.path.insert(0, tools_dir)
        import ledger
        ledger.append_usage_record(
            declaration=declaration or "",
            milestone=milestone,
            tier=tier,
            attempt=attempt,
            accepted=accepted,
            error_class=error_class,
            compiler_output=error or "",
            tokens=eval_count,
            latency_ms=elapsed_ms,
            lean_ms=lean_ms,
            model=model,
            task_type=task_type,
            prompt_text=prompt_text,
            status=status,
            error=error,
        )
    except Exception:
        pass


def query_ollama_chat(
    base_url: str,
    model: Optional[str],
    task_type: str,
    messages: List[Dict[str, str]],
    think: bool = False,
    timeout: float = 120.0,
    dry_run: bool = False,
    declaration: Optional[str] = None,
    record_usage: bool = True,
    milestone: str = "",
    tier: str = "unclassified",
    attempt: int = 1,
    options_override: Optional[Dict[str, Any]] = None,
) -> Dict[str, Any]:
    """Send a headless chat completion request to Ollama /api/chat."""
    profiles = ACTIVE_CONFIG.get("parameter_profiles", DEFAULT_PROFILES)
    opts = dict(profiles.get(task_type, DEFAULT_PROFILES.get("prove", DEFAULT_PROFILES["autoformalize"])))
    if think:
        opts["num_predict"] = 1024
    if options_override:
        opts.update(options_override)

    prompt_repr = "\n".join(m["content"] for m in messages)

    if dry_run:
        chosen = model or ACTIVE_CONFIG.get("primary_model", PRIMARY_MODEL)
        mock_raw = (
            "```lean4\n"
            "theorem dry_run_example : True := by\n"
            "  trivial\n"
            "```"
        )
        if record_usage:
            log_gemma_usage(
                chosen,
                task_type,
                prompt_repr,
                1.0,
                "mock",
                eval_count=8,
                declaration=declaration,
                milestone=milestone,
                tier=tier,
                attempt=attempt,
            )
        return {
            "status": "mock",
            "model": chosen,
            "task_type": task_type,
            "think": think,
            "elapsed_ms": 1.0,
            "eval_count": 8,
            "raw_response": mock_raw,
            "thinking": "",
            "lean_code": extract_lean_code(mock_raw),
        }

    ok, models_raw, err_msg = list_installed_models(base_url, timeout=min(timeout, 5.0))
    if not ok:
        return {"status": "error", "error": err_msg}

    installed_names = [m.get("name", "") for m in models_raw if m.get("name")]
    chosen, reason = select_model(installed_names, preferred=model)
    if not chosen:
        return {"status": "error", "error": reason}

    svc_cfg = ACTIVE_CONFIG.get("service", {})
    keep_alive = svc_cfg["keep_alive"] if "keep_alive" in svc_cfg else 0
    payload = {
        "model": chosen,
        "think": bool(think),
        "stream": False,
        "keep_alive": keep_alive,
        "options": opts,
        "messages": messages,
    }

    t0 = time.time()
    ok, resp, err = http_post_json(f"{base_url.rstrip('/')}/api/chat", payload, timeout=timeout)
    elapsed_ms = (time.time() - t0) * 1000.0
    if not ok:
        if record_usage:
            log_gemma_usage(
                chosen,
                task_type,
                prompt_repr,
                elapsed_ms,
                "error",
                declaration=declaration,
                error=err,
                milestone=milestone,
                tier=tier,
                attempt=attempt,
            )
        return {"status": "error", "model": chosen, "elapsed_ms": round(elapsed_ms, 2), "error": err}

    msg_obj = resp.get("message", {})
    raw_content = msg_obj.get("content", "") or ""
    thinking_text = msg_obj.get("thinking", "") or ""
    eval_count = resp.get("eval_count")

    lean_code = extract_lean_code(raw_content)
    if not lean_code and "```" in thinking_text:
        lean_code = extract_lean_code(thinking_text)

    if record_usage:
        log_gemma_usage(
            chosen,
            task_type,
            prompt_repr,
            elapsed_ms,
            "success",
            eval_count=eval_count,
            declaration=declaration,
            milestone=milestone,
            tier=tier,
            attempt=attempt,
        )

    return {
        "status": "success",
        "model": chosen,
        "selection_reason": reason,
        "task_type": task_type,
        "think": bool(think),
        "elapsed_ms": round(elapsed_ms, 2),
        "eval_count": eval_count,
        "raw_response": raw_content,
        "thinking": thinking_text,
        "lean_code": lean_code,
    }


def cmd_health(args: argparse.Namespace) -> int:
    """Verify headless Ollama daemon, /api/version, and primary gemma4:12B model availability."""
    ok, msg, _ = ensure_ollama_daemon(args.host, autostart=True, timeout=10.0)
    if not ok:
        print(f"[FAIL] {msg}", file=sys.stderr)
        return 1
    ok_v, ver_data, ver_msg = http_get_json(f"{args.host.rstrip('/')}/api/version", timeout=3.0)
    ok_m, models_raw, m_msg = list_installed_models(args.host, timeout=3.0)
    if not ok_m:
        print(f"[FAIL] /api/tags: {m_msg}", file=sys.stderr)
        return 1
    installed = [m.get("name", "") for m in models_raw if m.get("name")]
    chosen, reason = select_model(installed, preferred=args.model)
    result = {
        "healthy": chosen is not None,
        "host": args.host,
        "ollama_version": ver_data.get("version") if ok_v else ver_msg,
        "selected_model": chosen,
        "selection_reason": reason,
        "installed_models": installed,
    }
    if args.json:
        print(json.dumps(result, indent=2))
    else:
        print(f"[OK] {msg} (Ollama {result['ollama_version']})")
        print(f"[OK] Selected local model: {chosen} ({reason})")
    return 0 if chosen else 1


def cmd_list_models(args: argparse.Namespace) -> int:
    """List installed Ollama models."""
    ok, models_raw, msg = list_installed_models(args.host, timeout=5.0)
    if not ok:
        print(f"[ERROR] {msg}", file=sys.stderr)
        return 1
    if args.json:
        print(json.dumps(models_raw, indent=2))
        return 0
    for m in models_raw:
        size_gb = m.get("size", 0) / (1024 ** 3)
        print(f"  - {m.get('name', 'unknown')} ({size_gb:.2f} GB)")
    return 0


def cmd_run_task(args: argparse.Namespace, task_type: str) -> int:
    """Execute autoformalize / tactic / premise / skeleton / query."""
    prompt = getattr(args, "prompt", None) or getattr(args, "statement", None) or ""
    goal = getattr(args, "goal", None)
    error = getattr(args, "error", None)
    failed_tactic = getattr(args, "failed_tactic", None)
    if not prompt and not goal:
        print("[ERROR] Provide --prompt/--statement or --goal.", file=sys.stderr)
        return 1
    msgs = build_messages(task_type, prompt, goal=goal, error=error, failed_tactic=failed_tactic)
    res = query_ollama_chat(
        base_url=args.host,
        model=args.model,
        task_type=task_type,
        messages=msgs,
        think=args.think,
        timeout=args.timeout,
        dry_run=args.dry_run,
        declaration=args.declaration,
        record_usage=not args.no_log,
    )
    if args.json:
        print(json.dumps(res, indent=2))
    else:
        if res.get("status") not in ("success", "mock"):
            print(f"[ERROR] {res.get('error')}", file=sys.stderr)
            return 1
        print(res.get("lean_code", ""))
    return 0 if res.get("status") in ("success", "mock") else 1


def cmd_ledger_summary(args: argparse.Namespace) -> int:
    """Print summary statistics of local Gemma calls from .agents/gemma_usage.jsonl via tools/ledger.py."""
    tools_dir = str(Path(__file__).resolve().parent)
    if tools_dir not in sys.path:
        sys.path.insert(0, tools_dir)
    import ledger
    summary = ledger.summarize_ledger()
    if args.json:
        print(json.dumps(summary, indent=2))
    else:
        print(ledger.format_summary_text(summary))
    return 0


def cmd_test(_args: argparse.Namespace) -> int:
    """Run offline self-tests (zero network required, zero ledger side effects)."""
    assert extract_lean_code("text\n```lean4\ntheorem x : True := trivial\n```\nend") == "theorem x : True := trivial"
    assert extract_lean_code("```lean\nexact rfl\n```") == "exact rfl"
    chosen, _ = select_model(["gemma2:9b", "gemma4:12B", "gemma-lean4:latest"], preferred=None)
    assert chosen == "gemma4:12B", f"expected gemma4:12B, got {chosen}"
    chosen_ci, _ = select_model(["gemma4:12b"], preferred="gemma4:12B")
    assert chosen_ci == "gemma4:12b"
    msgs = build_messages("tactic", "prove", goal="⊢ True", error="type mismatch")
    assert len(msgs) == 2 and msgs[0]["role"] == "system" and "⊢ True" in msgs[1]["content"]
    res = query_ollama_chat(
        DEFAULT_OLLAMA_HOST, "gemma4:12B", "tactic", msgs, think=False, dry_run=True, record_usage=False
    )
    assert res["status"] == "mock" and "trivial" in res["lean_code"]
    print("ollama_lean4_client.py self-tests PASSED (5/5)")
    return 0


def main() -> int:
    common = argparse.ArgumentParser(add_help=False)
    common.add_argument("--host", default=ACTIVE_CONFIG.get("service", {}).get("default_host", DEFAULT_OLLAMA_HOST))
    common.add_argument("--model", default=ACTIVE_CONFIG.get("primary_model", PRIMARY_MODEL))
    common.add_argument("--timeout", type=float, default=float(ACTIVE_CONFIG.get("service", {}).get("request_timeout_seconds", 120.0)))
    common.add_argument("--think", action="store_true", help="Enable gemma4 thinking mode for harder decompositions")
    common.add_argument("--dry-run", action="store_true", help="Return mock response without calling Ollama")
    common.add_argument("--no-log", action="store_true", help="Skip logging to .agents/gemma_usage.jsonl")
    common.add_argument("--json", action="store_true", help="Emit JSON output")
    common.add_argument("--declaration", default=None, help="Target Lean declaration name for telemetry")

    parser = argparse.ArgumentParser(description="Headless local Ollama gemma4:12B Lean 4 helper")
    sub = parser.add_subparsers(dest="command")

    sub.add_parser("health", parents=[common]).set_defaults(func=cmd_health)
    sub.add_parser("list-models", parents=[common]).set_defaults(func=cmd_list_models)
    sub.add_parser("ledger-summary", parents=[common]).set_defaults(func=cmd_ledger_summary)
    sub.add_parser("test", parents=[common]).set_defaults(func=cmd_test)

    p_auto = sub.add_parser("autoformalize", parents=[common])
    p_auto.add_argument("statement", nargs="?", default=None)
    p_auto.add_argument("--statement", dest="prompt", default=None)
    p_auto.set_defaults(func=lambda a: cmd_run_task(a, "autoformalize"))

    p_tac = sub.add_parser("suggest-tactic", parents=[common])
    p_tac.add_argument("--goal", required=True)
    p_tac.add_argument("--error", default="")
    p_tac.add_argument("--failed-tactic", default=None)
    p_tac.add_argument("--prompt", default="")
    p_tac.set_defaults(func=lambda a: cmd_run_task(a, "tactic"))

    p_prem = sub.add_parser("premise", parents=[common])
    p_prem.add_argument("--goal", required=True)
    p_prem.add_argument("--prompt", default="")
    p_prem.set_defaults(func=lambda a: cmd_run_task(a, "premise"))

    p_skel = sub.add_parser("skeleton", parents=[common])
    p_skel.add_argument("--prompt", required=True)
    p_skel.set_defaults(func=lambda a: cmd_run_task(a, "skeleton"))

    p_query = sub.add_parser("query", parents=[common])
    p_query.add_argument("--prompt", required=True)
    p_query.add_argument("--task", choices=["autoformalize", "tactic", "premise", "skeleton"], default="tactic")
    p_query.set_defaults(func=lambda a: cmd_run_task(a, a.task))

    args = parser.parse_args()
    if not getattr(args, "func", None):
        parser.print_help()
        return 0
    return args.func(args)


if __name__ == "__main__":
    sys.exit(main())
