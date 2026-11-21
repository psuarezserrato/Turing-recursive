#!/usr/bin/env bash
# tools/collect_axioms.sh — Gate G2 Axiom & Forbidden-Token Audit + Gate G4 Wiring Audit
#
# 1. Comment-stripped token scan over TuringRecursive(.lean|/**/*.lean) reusing
#    `strip_lean_comments` from `tools/workflow_control.py` for:
#      sorry|admit|axiom|unsafe|implemented_by|native_decide|opaque|maxHeartbeats
# 2. Kernel `Lean.collectAxioms` check over every declaration in namespace `TuringRecursive`
#    (and the root) via `lake env lean tools/audit_axioms.lean`.
# 3. Optional `#audit_wiring` check via `--wiring <theorem> <req1,req2,...>`.

set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
REPO_ROOT="$(cd "${SCRIPT_DIR}/.." && pwd)"

WIRING_ROOT=""
WIRING_REQ=""
SKIP_LEAN=0
SCAN_ONLY=0
CUSTOM_FILES=()

usage() {
  cat <<'EOF'
Usage: bash tools/collect_axioms.sh [OPTIONS] [FILES...]

Options:
  --root DIR                  Override repository root
  --wiring THM REQ1,REQ2,...  Verify that REQ1,REQ2,... occur in the pruned proof closure of THM
  --scan-only, --no-lean      Run only the comment-stripped forbidden token scan (skip lake env lean)
  -h, --help                  Show this help message and exit

Checks performed:
  1. Comment-stripped regex scan (using strip_lean_comments from tools/workflow_control.py) for:
     sorry | admit | axiom | unsafe | implemented_by | native_decide | opaque | maxHeartbeats
  2. Kernel Lean.collectAxioms audit via `LEAN_NUM_THREADS=2 lake env lean tools/audit_axioms.lean`
     verifying all declarations in TuringRecursive (and root) use only
     {propext, Classical.choice, Quot.sound}.
EOF
}

while [[ $# -gt 0 ]]; do
  case "$1" in
    -h|--help)
      usage
      exit 0
      ;;
    --root)
      REPO_ROOT="$(cd "$2" && pwd)"
      shift 2
      ;;
    --wiring)
      WIRING_ROOT="$2"
      WIRING_REQ="${3:-}"
      shift 3
      ;;
    --scan-only|--no-lean)
      SKIP_LEAN=1
      SCAN_ONLY=1
      shift
      ;;
    *)
      CUSTOM_FILES+=("$1")
      shift
      ;;
  esac
done

export PATH="${HOME}/.elan/bin:${PATH}"
export LEAN_NUM_THREADS=2

# 1. Comment-stripped token scan reusing strip_lean_comments from tools/workflow_control.py
python3 - "${REPO_ROOT}" "${CUSTOM_FILES[@]+"${CUSTOM_FILES[@]}"}" <<'PY'
import re
import sys
from pathlib import Path

repo_root = Path(sys.argv[1]).resolve()
custom_files = sys.argv[2:]

tools_dir = repo_root / "tools"
if not (tools_dir / "workflow_control.py").is_file():
    tools_dir = Path(__file__).resolve().parent if "__file__" in globals() else Path.cwd() / "tools"
sys.path.insert(0, str(tools_dir))
from workflow_control import strip_lean_comments

FORBIDDEN_RE = re.compile(
    r"\b(sorry|admit|axiom|unsafe|implemented_by|native_decide|opaque|maxHeartbeats)\b"
)

target_files = []
if custom_files:
    for cf in custom_files:
        p = Path(cf)
        if not p.is_absolute():
            p = repo_root / p
        if p.is_file():
            target_files.append(p)
        elif p.is_dir():
            target_files.extend(sorted(p.rglob("*.lean")))
else:
    root_lean = repo_root / "TuringRecursive.lean"
    if root_lean.is_file():
        target_files.append(root_lean)
    pkg_dir = repo_root / "TuringRecursive"
    if pkg_dir.is_dir():
        target_files.extend(sorted(pkg_dir.rglob("*.lean")))

violations = []
for fpath in target_files:
    raw = fpath.read_text(encoding="utf-8", errors="replace")
    stripped = strip_lean_comments(raw)
    for line_no, line in enumerate(stripped.splitlines(), 1):
        for m in FORBIDDEN_RE.finditer(line):
            try:
                rel = fpath.relative_to(repo_root)
            except ValueError:
                rel = fpath
            violations.append((str(rel), line_no, m.group(1), line.strip()))

if violations:
    print(f"[FAIL] Comment-stripped token scan found {len(violations)} forbidden token(s):", file=sys.stderr)
    for rel, lno, tok, snippet in violations:
        print(f"  {rel}:{lno}: forbidden token '{tok}' -> {snippet}", file=sys.stderr)
    sys.exit(1)

print(f"[OK] Comment-stripped token scan clean across {len(target_files)} file(s).")
PY

if [[ "${SKIP_LEAN}" -eq 1 ]]; then
  exit 0
fi

cd "${REPO_ROOT}"
if [[ ! -f "${REPO_ROOT}/.lake/build/lib/lean/TuringRecursive.olean" ]]; then
  lake build TuringRecursive >/dev/null
fi
if [[ -n "${WIRING_ROOT}" ]]; then
  AUDIT_WIRING_ROOT="${WIRING_ROOT}" AUDIT_WIRING_REQUIRED="${WIRING_REQ}" \
    lake env lean "${REPO_ROOT}/tools/audit_axioms.lean"
else
  lake env lean "${REPO_ROOT}/tools/audit_axioms.lean"
fi
