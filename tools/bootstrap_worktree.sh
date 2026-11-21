#!/usr/bin/env bash
set -euo pipefail
export PATH="$HOME/.elan/bin:$HOME/.local/bin:/usr/local/bin:/opt/homebrew/bin:$PATH"
MAIN_REPO="/Users/pablosuarez/Desktop/Turing-recursive"
WORKER="${1:?Usage: bash tools/bootstrap_worktree.sh <worker-name> [base-ref]}"
BASE_REF="${2:-main}"
WT_DIR="$MAIN_REPO/.worktrees/$WORKER"
BRANCH="work/$WORKER"

mkdir -p "$MAIN_REPO/.worktrees"
LOCKDIR="$MAIN_REPO/.git/s4tp_wt.lock"
for _ in $(seq 1 50); do
  if mkdir "$LOCKDIR" 2>/dev/null; then break; fi
  sleep 0.2
done
trap 'rmdir "$LOCKDIR" 2>/dev/null || true' EXIT

if [ ! -e "$WT_DIR/.git" ]; then
  git -C "$MAIN_REPO" worktree prune
  git -C "$MAIN_REPO" worktree add -B "$BRANCH" "$WT_DIR" "$BASE_REF"
fi
rmdir "$LOCKDIR" 2>/dev/null || true
trap - EXIT

mkdir -p "$WT_DIR/.lake"
if [ ! -d "$WT_DIR/.lake/packages/TauCeti" ]; then
  echo "[bootstrap_worktree] Cloning .lake/packages via APFS CoW into $WT_DIR/.lake/packages ..."
  rm -rf "$WT_DIR/.lake/packages"
  cp -Rc "$MAIN_REPO/.lake/packages" "$WT_DIR/.lake/packages"
fi
echo "[bootstrap_worktree] Ready: $WT_DIR (branch $BRANCH)"
