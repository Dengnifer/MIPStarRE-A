#!/usr/bin/env bash
# rerun_review.sh <pr> — run review.sh for a PR once fewer than MAX_CODEX codex sessions are live.
set -u
export PATH="$HOME/.local/bin:$HOME/.elan/bin:$PATH"
PR="$1"; MAX_CODEX="${MAX_CODEX:-5}"
L="$HOME/.cache/mipstarre-dev/watchdog/lanes"; mkdir -p "$L"; rm -f "$L/pr$PR.review.done"
cd "$HOME/MIPStarRE-qpbt" || exit 1
live() { pgrep -fa 'codex exec' | grep -o '\-C [^ ]*' | sort -u | wc -l; }
for _ in $(seq 1 720); do [ "$(live)" -lt "$MAX_CODEX" ] && break; sleep 30; done
echo "== $(date -u +%FT%TZ) review.sh $PR (live sessions before: $(live))"
local/bin/review.sh "$PR"; echo "REVIEW_EXIT=$?"
H=$(gh pr view "$PR" --json headRefOid --jq .headRefOid)
gh api "repos/Dengnifer/MIPStarRE-A/commits/$H/status" --jq '.statuses[] | select(.context|endswith("summary")) | .context+" "+.state+" "+(.description // "")'
touch "$L/pr$PR.review.done"
