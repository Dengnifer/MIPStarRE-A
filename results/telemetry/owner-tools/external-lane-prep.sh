#!/usr/bin/env bash
# external-lane-prep.sh <issue> <slug> [base-ref] — prepare a worktree for a prover that
# is NOT dispatched through local/bin/dispatch.sh (a second model family, a session run by
# hand, a person).  Branch from the integration branch (or from base-ref for a stacked
# packet), warm the worktree from the shared cache, write the task file, and append a
# start row to results/telemetry/owner-sessions.jsonl — these sessions bypass dispatch.sh,
# so they are recorded there instead of sessions.jsonl.  Prints the worktree path.
# Finish with external-lane-finish.sh, which closes the row and runs the lane tail.
# Model name: $KIT_EXTERNAL_MODEL, default "external".
# Provenance: the origin's owner-tools/claude-lane-prep.sh (checkout path, cache directory
# and one model id hard-coded).
set -u
HERE="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd -P)"
SERVICE="$HERE/../../../local/bin/service"
# shellcheck source=/dev/null
. "$SERVICE/service-lib.sh"

N="${1:?usage: external-lane-prep.sh <issue> <slug> [base-ref]}"
SLUG="${2:?usage: external-lane-prep.sh <issue> <slug> [base-ref]}"
BASE="${3:-github/${KIT_BASE_BRANCH:-main}}"
MODEL="${KIT_EXTERNAL_MODEL:-external}"
P="$KIT_REPO_ROOT"; BR="issue-$N-$SLUG"; W="$P/.worktrees/$BR"
STATE="$KIT_LANE_DIR"; mkdir -p "$STATE"
cd "$P" || exit 1
git fetch -q github

if [ ! -d "$W" ]; then
  git show-ref --quiet "refs/heads/$BR" || git branch -q "$BR" "$BASE"
  git worktree add -q "$W" "$BR" || { echo "worktree add failed"; exit 1; }
fi
local/bin/worktree-setup.sh "$W" >/dev/null 2>&1 || echo "warm finished with warnings"
MIGRATE="$HERE/migrate-packages.sh"
[ -L "$W/.lake/packages" ] || { [ -x "$MIGRATE" ] && bash "$MIGRATE" "$W" >/dev/null 2>&1; } || true

TASK="$STATE/$N.task.md"
{
  echo "----- ISSUE #$N -----"
  gh issue view "$N" --json title,body --jq '"# "+.title+"\n\n"+.body'
  [ -f "$STATE/$N.repair.md" ] && { echo; echo "----- NOTE FROM THE OPERATOR -----"; cat "$STATE/$N.repair.md"; }
} > "$TASK"
printf '{"name":"external-prover-%s-%s","role":"prover","model":"%s","issue":%s,"worktree":"%s","base":"%s","start":"%s","status":"running"}\n' \
  "$N" "$(date -u +%Y%m%dT%H%MZ)" "$MODEL" "$N" "$W" "$BASE" "$(date -u +%FT%TZ)" \
  >> "$P/results/telemetry/owner-sessions.jsonl"
echo "$W"
