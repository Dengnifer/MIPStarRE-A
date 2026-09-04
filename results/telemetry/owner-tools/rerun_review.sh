#!/usr/bin/env bash
# rerun_review.sh <pr> — run review.sh for a PR once fewer than MAX_CODEX codex sessions are live.
set -u
export PATH="$HOME/.cache/mipstarre-dev/owner-bin:$HOME/.local/bin:$HOME/.elan/bin:$PATH"
PR="$1"; MAX_CODEX="${MAX_CODEX:-7}"
cap() { if [ -n "${MAX_CODEX_FIXED:-}" ]; then echo "$MAX_CODEX_FIXED"; return; fi; b=$(pgrep -fa codex | grep "MIPStarRE-auto\|/tmp/qpbt-" | grep -o "\-C /[^ ]*" | sort -u | wc -l); b=$((b+1)); c=$((9-b)); [ "$c" -lt 4 ] && c=4; echo "$c"; }
L="$HOME/.cache/mipstarre-dev/watchdog/lanes"; mkdir -p "$L"; rm -f "$L/pr$PR.review.done"
cd "$HOME/MIPStarRE-qpbt" || exit 1
live() { pgrep -fa 'codex exec' | grep -o '\-C [^ ]*' | sort -u | wc -l; }
exec 9>"$HOME/.cache/mipstarre-dev/watchdog/launch.lock"; flock 9
for _ in $(seq 1 720); do [ "$(live)" -lt "$(cap)" ] && break; sleep 30; done
echo "== $(date -u +%FT%TZ) review.sh $PR (live sessions before: $(live))"
local/bin/review.sh "$PR" & RPID=$!; sleep 25; flock -u 9; wait "$RPID"; echo "REVIEW_EXIT=$?"
H=$(gh pr view "$PR" --json headRefOid --jq .headRefOid)
gh api "repos/Dengnifer/MIPStarRE-A/commits/$H/status" --jq '.statuses[] | select(.context|endswith("summary")) | .context+" "+.state+" "+(.description // "")'
touch "$L/pr$PR.review.done"
