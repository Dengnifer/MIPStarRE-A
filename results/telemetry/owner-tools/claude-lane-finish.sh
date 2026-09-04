#!/usr/bin/env bash
# claude-lane-finish.sh N SLUG STATUS [TOKENS] — close the owner-sessions record for a Claude
# prover and run the lane tail (merge main, build, push, PR, CI, review) on its worktree.
set -u
export PATH="$HOME/.cache/mipstarre-dev/owner-bin:$HOME/.local/bin:$HOME/.elan/bin:$PATH"
N=$1; SLUG=$2; STATUS=$3; TOKENS=${4:-null}
P="$HOME/MIPStarRE-qpbt"; BR="issue-$N-$SLUG"; W="$P/.worktrees/$BR"
STATE="$HOME/.cache/mipstarre-dev/watchdog/lanes"
cd "$P" || exit 1
START=$(grep "\"issue\":$N," results/telemetry/owner-sessions.jsonl | tail -1 | grep -o '"start":"[^"]*"' | cut -d'"' -f4)
WALL=$(( $(date +%s) - $(date -d "$START" +%s) ))
printf '{"name":"claude-prover-%s","role":"prover","model":"claude-fable-5-1","issue":%s,"worktree":"%s","start":"%s","end":"%s","wall_s":%s,"status":"%s","tokens":%s,"commits":%s}\n' "$N" "$N" "$W" "$START" "$(date -u +%FT%TZ)" "$WALL" "$STATUS" "$TOKENS" "$(git -C "$W" rev-list --count github/main..HEAD)" >> results/telemetry/owner-sessions.jsonl
[ "$STATUS" = done ] || exit 0
LANE_BRANCH=$BR SKIP_DISPATCH=1 exec bash /tmp/lane-v10.sh "$N" "$SLUG" prover
