#!/usr/bin/env bash
# claude-lane-prep.sh N SLUG [BASE_BRANCH] — prepare a worktree for a Claude (Fable 5.1) prover
# that works over ssh from the owner's machine: branch from github/main (or BASE_BRANCH for a
# stacked packet), warm from the hot cache, write the task file, and append a start record to
# results/telemetry/owner-sessions.jsonl (these sessions bypass dispatch.sh, so they are logged
# here instead of sessions.jsonl). Prints the worktree path.
set -u
export PATH="$HOME/.local/bin:$HOME/.elan/bin:$PATH"
N=$1; SLUG=$2; BASE=${3:-github/main}
P="$HOME/MIPStarRE-qpbt"; BR="issue-$N-$SLUG"; W="$P/.worktrees/$BR"
STATE="$HOME/.cache/mipstarre-dev/watchdog/lanes"; mkdir -p "$STATE"
cd "$P" || exit 1
git fetch -q github
if [ ! -d "$W" ]; then
  git show-ref --quiet "refs/heads/$BR" || git branch -q "$BR" "$BASE"
  git worktree add -q "$W" "$BR" || { echo "worktree add failed"; exit 1; }
fi
local/bin/worktree-setup.sh "$W" >/dev/null 2>&1 || echo "warm finished with warnings"
[ -L "$W/.lake/packages" ] || bash /tmp/migrate-packages.sh "$W" >/dev/null 2>&1 || true
TASK="$STATE/$N.task.md"
{
  echo "----- ISSUE #$N -----"
  gh issue view "$N" --json title,body --jq '"# "+.title+"\n\n"+.body'
  [ -f "$STATE/$N.repair.md" ] && { echo; echo "----- NOTE FROM THE OPERATOR -----"; cat "$STATE/$N.repair.md"; }
} > "$TASK"
printf '{"name":"claude-prover-%s-%s","role":"prover","model":"claude-fable-5-1","issue":%s,"worktree":"%s","base":"%s","start":"%s","status":"running"}\n' "$N" "$(date -u +%Y%m%dT%H%MZ)" "$N" "$W" "$BASE" "$(date -u +%FT%TZ)" >> "$P/results/telemetry/owner-sessions.jsonl"
echo "$W"
