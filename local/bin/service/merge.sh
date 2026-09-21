#!/usr/bin/env bash
# merge.sh <pr> [--adjudicated] — run the repository's merge gate (local/bin/pr_merge.py)
# on one PR with the primary checkout parked safely: telemetry rows that other tools
# appended meanwhile are stashed, the gate runs, the stash comes back (unioning
# append-only .jsonl/.md files on conflict), and the result is published.
#
# Two rules are load-bearing and both were paid for:
#   * push_guarded: pop ONLY a stash THIS invocation pushed.  An unguarded
#     `stash push; rebase; pop` finds no stash to create on a clean tree and then pops
#     whatever old stash sat on top of the shared checkout — it once cut a source file
#     down to fourteen lines.  Old stashes in a shared checkout are dangerous.
#   * the gate is retried when CI dirtied the primary between the stash and the gate
#     ("local changes would be overwritten by merge").
#
# Provenance: kit-src/tmp-scripts/merge-v2.sh (repository path hard-coded).
set -u
KIT_SERVICE_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd -P)"
# shellcheck source=/dev/null
. "$KIT_SERVICE_DIR/service-lib.sh"
cd "$KIT_REPO_ROOT" || exit 1

PR="${1:?usage: merge.sh <pr> [--adjudicated]}"; shift
BASE="${KIT_BASE_BRANCH:-main}"
OUT_DIR="$KIT_LANE_DIR"; mkdir -p "$OUT_DIR"
OUT="$OUT_DIR/pr$PR.gate.out"

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
        if l.startswith(("<<<<<<<", "|||||||", "=======", ">>>>>>>")): continue
        if l and l not in seen: seen.add(l); out.append(l)
open(f, "w").write("\n".join(out) + "\n")
PY
}

resolve_pop() {
  for f in $(git stash show --name-only 'stash@{0}'); do
    case "$f" in *.jsonl|*.md) union "$f" 'stash@{0}';; *) git show "stash@{0}:$f" > "$f" 2>/dev/null;; esac
  done
  # A `stash push -u` keeps the untracked files in a third parent.
  if git rev-parse -q --verify 'stash@{0}^3' >/dev/null 2>&1; then
    for f in $(git ls-tree -r --name-only 'stash@{0}^3'); do
      if [ -e "$f" ]; then case "$f" in *.jsonl|*.md) union "$f" 'stash@{0}^3';; esac
      else mkdir -p "$(dirname "$f")"; git show "stash@{0}^3:$f" > "$f"; fi
    done
  fi
  git reset -q; git stash drop -q; echo "stash resolved (union)"
}
pop() { git stash pop -q 2>/dev/null || { echo "stash pop conflict: auto-resolving"; resolve_pop; }; }
# Returns success only when this invocation actually created a stash entry.
push_guarded() { local a b; a=$(git stash list | wc -l); git stash push -q -u -m "$1" >/dev/null 2>&1 || true; b=$(git stash list | wc -l); [ "$b" -gt "$a" ]; }

git fetch -q github
if [ -n "$(git log --oneline "github/$BASE..$BASE")" ]; then
  echo "local $BASE is ahead of github/$BASE; rebasing first"
  P=0; push_guarded "merge.sh $PR" && P=1
  git rebase -q "github/$BASE" "$BASE" || { echo "REBASE_FAILED"; [ "$P" -eq 1 ] && pop; exit 1; }
  [ "$P" -eq 1 ] && pop
  local/bin/github-sync.sh "$BASE" >/dev/null 2>&1 || true
fi

RC=1
for attempt in 1 2 3; do
  STASHED=0
  if [ -n "$(git status --porcelain)" ]; then push_guarded "merge.sh $PR telemetry" && STASHED=1; fi
  python3 local/bin/pr_merge.py "$PR" "$@" > "$OUT" 2>&1; RC=$?; cat "$OUT"
  [ "$STASHED" -eq 1 ] && pop
  if [ "$RC" -ne 0 ] && grep -q "would be overwritten by merge" "$OUT"; then
    echo "primary dirtied during the gate; retry $attempt"; git merge --abort 2>/dev/null; sleep 5; continue
  fi
  break
done
[ "$RC" -eq 0 ] || { echo "MERGE_FAILED rc=$RC"; exit "$RC"; }

git fetch -q github
if ! git merge-base --is-ancestor "github/$BASE" "$BASE"; then
  P=0; push_guarded "merge.sh $PR post" && P=1
  git rebase -q "github/$BASE" "$BASE"
  [ "$P" -eq 1 ] && pop
fi
if [ -n "$(git status --porcelain -- results/telemetry)" ]; then
  git add results/telemetry && git commit -q -m "chore(telemetry): records around PR $PR merge" \
    && echo "telemetry $(git rev-parse --short HEAD)"
fi
local/bin/github-sync.sh "$BASE" 2>&1 | tail -1
echo "github/$BASE $(git rev-parse --short "github/$BASE") local $BASE $(git rev-parse --short "$BASE")"
