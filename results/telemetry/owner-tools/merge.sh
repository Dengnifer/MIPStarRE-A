#!/usr/bin/env bash
# merge.sh <pr> [--adjudicated] — operator merge: stash live telemetry so the
# primary is clean, run the gate, then reapply and commit telemetry ON TOP of
# the merged main (committing it first diverges local main; 2026-09-04 lesson),
# push, refresh the origin/main alias.
set -u
export PATH="$HOME/.local/bin:$HOME/.elan/bin:$PATH"
cd "$HOME/MIPStarRE-qpbt" || exit 1
PR="$1"; shift
git fetch -q github
if [ -n "$(git log --oneline github/main..main)" ]; then
  echo "local main is ahead of github/main; rebasing first"
  git stash push -q -u -m "merge.sh $PR" && git rebase -q github/main main && git stash pop -q || { echo "REBASE_FAILED"; exit 1; }
  local/bin/github-sync.sh >/dev/null 2>&1 || true
fi
STASHED=0
if [ -n "$(git status --porcelain)" ]; then git stash push -q -u -m "merge.sh $PR telemetry" && STASHED=1; fi
python3 local/bin/pr_merge.py "$PR" "$@"; RC=$?
if [ "$STASHED" -eq 1 ]; then git stash pop -q || echo "STASH_POP_CONFLICT (resolve by hand)"; fi
[ "$RC" -eq 0 ] || { echo "MERGE_FAILED rc=$RC"; exit "$RC"; }
git fetch -q github
if ! git merge-base --is-ancestor github/main main; then git stash push -q -u -m "merge.sh $PR post" && git rebase -q github/main main && git stash pop -q; fi
if [ -n "$(git status --porcelain -- results/telemetry)" ]; then
  git add results/telemetry && git commit -q -m "chore(telemetry): records around PR $PR merge" && echo "telemetry $(git rev-parse --short HEAD)"
fi
local/bin/github-sync.sh 2>&1 | tail -1
git update-ref refs/remotes/origin/main "$(git rev-parse github/main)"
echo "github/main $(git rev-parse --short github/main) local main $(git rev-parse --short main)"
