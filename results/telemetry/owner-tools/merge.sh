#!/usr/bin/env bash
# merge.sh <pr> [--adjudicated] — merge one pull request through the gates.
#
# This is the file the merge daemon calls.  Until 2026-09-12 it was
# /tmp/merge-v2.sh, a path that did not exist in any snapshot while the daemon
# header still named merge.sh; the two names now describe one tracked file
# (full-speed-mode v2 design §7, work item W5, finding MT7).
#
# What it does, and nothing else:
#   1. rebases the local `main` onto github/main when it has drifted ahead,
#      stashing and restoring the working tree around it;
#   2. runs `python3 local/bin/pr_merge.py <pr> [--adjudicated]` — the ONLY
#      merge path, with its seven gates untouched.  This script has no flag
#      that can skip, weaken or fake a gate;
#   3. retries once when CI dirties the primary checkout between the stash and
#      the gate ("local changes would be overwritten by merge", 2026-09-04);
#   4. commits the telemetry the merge produced and syncs the mirror.
#
# Stash conflicts on the append-only telemetry records are resolved by union
# (the same rule W7 installs as a merge driver in .gitattributes): every line
# of HEAD, the working tree and the stash, in that order, de-duplicated.  A
# non-append-only file takes the stash version; untracked files come back from
# the stash's third parent.
#
# Exit status: 0 merged; pr_merge.py's own status otherwise (1 on a failed
# rebase).  Output of the gate run is kept at $CACHE_ROOT/daemon/merge-<pr>.out.
set -u
export PATH="$HOME/.local/bin:$HOME/.elan/bin:$PATH"

CACHE_ROOT="${MIPSTARRE_CACHE_ROOT:-$HOME/.cache/mipstarre-dev}"
CHECKOUT="${MIPSTARRE_CHECKOUT:-$HOME/MIPStarRE-qpbt}"
RUN_DIR="$CACHE_ROOT/daemon"
mkdir -p "$RUN_DIR"
cd "$CHECKOUT" || exit 1

version() {
  local v
  v="$(cat "$CACHE_ROOT/owner-bin/tools-version" 2>/dev/null | head -n 1)"
  [ -n "$v" ] || v="$(git rev-parse --short HEAD 2>/dev/null || true)"
  printf '%s\n' "${v:-unversioned}"
}
echo "tool=merge.sh version=$(version)"

[ "$#" -ge 1 ] || { echo "usage: merge.sh <pr> [--adjudicated]" >&2; exit 2; }
PR="$1"; shift
case "$PR" in ''|*[!0-9]*) echo "merge.sh: pr must be a number, got '$PR'" >&2; exit 2;; esac
OUT="$RUN_DIR/merge-$PR.out"

union() { python3 - "$1" "$2" <<'PY'
import sys, os, subprocess
f, ref = sys.argv[1], sys.argv[2]
def show(r):
    try: return subprocess.run(["git","show",f"{r}:{f}"],capture_output=True,text=True,check=True).stdout.splitlines()
    except subprocess.CalledProcessError: return []
wt = open(f).read().splitlines() if os.path.exists(f) else []
out, seen = [], set()
for v in (show("HEAD"), wt, show(ref)):
    for l in v:
        if l.startswith(("<<<<<<<", "=======", ">>>>>>>")): continue
        if l and l not in seen: seen.add(l); out.append(l)
open(f, "w").write("\n".join(out) + "\n")
PY
}
resolve_pop() {
  for f in $(git stash show --name-only 'stash@{0}'); do
    case "$f" in *.jsonl|*.md) union "$f" 'stash@{0}';; *) git show "stash@{0}:$f" > "$f" 2>/dev/null;; esac
  done
  if git rev-parse -q --verify 'stash@{0}^3' >/dev/null 2>&1; then
    for f in $(git ls-tree -r --name-only 'stash@{0}^3'); do
      if [ -e "$f" ]; then case "$f" in *.jsonl|*.md) union "$f" 'stash@{0}^3';; esac
      else mkdir -p "$(dirname "$f")"; git show "stash@{0}^3:$f" > "$f"; fi
    done
  fi
  git reset -q; git stash drop -q; echo "stash resolved (union)"
}
pop() { git stash pop -q 2>/dev/null || { echo "stash pop conflict: auto-resolving"; resolve_pop; }; }

git fetch -q github
if [ -n "$(git log --oneline github/main..main)" ]; then
  echo "local main is ahead of github/main; rebasing first"
  git stash push -q -u -m "merge.sh $PR"; git rebase -q github/main main || { echo "REBASE_FAILED"; exit 1; }; pop
  local/bin/github-sync.sh >/dev/null 2>&1 || true
fi
RC=1
for attempt in 1 2 3; do
  STASHED=0
  if [ -n "$(git status --porcelain)" ]; then git stash push -q -u -m "merge.sh $PR telemetry" && STASHED=1; fi
  python3 local/bin/pr_merge.py "$PR" "$@" > "$OUT" 2>&1; RC=$?; cat "$OUT"
  [ "$STASHED" -eq 1 ] && pop
  if [ "$RC" -ne 0 ] && grep -q "would be overwritten by merge" "$OUT"; then echo "primary dirtied during the gate; retry $attempt"; git merge --abort 2>/dev/null; sleep 5; continue; fi
  break
done
[ "$RC" -eq 0 ] || { echo "MERGE_FAILED rc=$RC"; exit "$RC"; }
git fetch -q github
if ! git merge-base --is-ancestor github/main main; then git stash push -q -u -m "merge.sh $PR post"; git rebase -q github/main main; pop; fi
if [ -n "$(git status --porcelain -- results/telemetry)" ]; then
  git add results/telemetry && git commit -q -m "chore(telemetry): records around PR $PR merge" && echo "telemetry $(git rev-parse --short HEAD)"
fi
local/bin/github-sync.sh 2>&1 | tail -1
git update-ref refs/remotes/origin/main "$(git rev-parse github/main)"
echo "github/main $(git rev-parse --short github/main) local main $(git rev-parse --short main)"
