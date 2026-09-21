#!/usr/bin/env bash
# external-lane-finish.sh <issue> <slug> <done|blocked|failed> [tokens] — close the
# owner-sessions row an external prover opened with external-lane-prep.sh and, when the
# status is `done`, run the lane tail on its worktree (merge the base in, build, push,
# open the PR, CI, review) through local/bin/service/lane.sh with SKIP_DISPATCH=1.
# Provenance: the origin's owner-tools/claude-lane-finish.sh (checkout path, cache
# directory, one model id and the /tmp path of the lane runner hard-coded).
set -u
HERE="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd -P)"
SERVICE="$HERE/../../../local/bin/service"
# shellcheck source=/dev/null
. "$SERVICE/service-lib.sh"

N="${1:?usage: external-lane-finish.sh <issue> <slug> <status> [tokens]}"
SLUG="${2:?usage: external-lane-finish.sh <issue> <slug> <status> [tokens]}"
STATUS="${3:?usage: external-lane-finish.sh <issue> <slug> <status> [tokens]}"
TOKENS="${4:-null}"
MODEL="${KIT_EXTERNAL_MODEL:-external}"
BASE="${KIT_BASE_BRANCH:-main}"
P="$KIT_REPO_ROOT"; BR="issue-$N-$SLUG"; W="$P/.worktrees/$BR"
cd "$P" || exit 1

START=$(grep "\"issue\":$N," results/telemetry/owner-sessions.jsonl 2>/dev/null | tail -1 \
        | grep -o '"start":"[^"]*"' | cut -d'"' -f4)
if [ -n "$START" ]; then WALL=$(( $(date +%s) - $(date -d "$START" +%s) )); else START=""; WALL=0; fi
printf '{"name":"external-prover-%s","role":"prover","model":"%s","issue":%s,"worktree":"%s","start":"%s","end":"%s","wall_s":%s,"status":"%s","tokens":%s,"commits":%s}\n' \
  "$N" "$MODEL" "$N" "$W" "$START" "$(date -u +%FT%TZ)" "$WALL" "$STATUS" "$TOKENS" \
  "$(git -C "$W" rev-list --count "github/$BASE..HEAD" 2>/dev/null || echo 0)" \
  >> results/telemetry/owner-sessions.jsonl
[ "$STATUS" = done ] || exit 0
LANE_BRANCH="$BR" SKIP_DISPATCH=1 exec bash "$SERVICE/lane.sh" "$N" "$SLUG" prover
