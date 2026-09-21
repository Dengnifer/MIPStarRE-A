#!/usr/bin/env bash
# rerun_review.sh <pr> — run local/bin/review.sh for one PR as soon as a worker slot is
# free, then print the summary statuses on the PR's head.  Useful when a review died or
# a head moved; the lane runner does this by itself.
# Provenance: the origin's owner-tools/rerun_review.sh (checkout path, cache directory
# and repository slug hard-coded).
set -u
HERE="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd -P)"
SERVICE="$HERE/../../../local/bin/service"
# shellcheck source=/dev/null
. "$SERVICE/service-lib.sh"
cd "$KIT_REPO_ROOT" || exit 1

PR="${1:?usage: rerun_review.sh <pr>}"
mkdir -p "$KIT_LANE_DIR"; rm -f "$KIT_LANE_DIR/pr$PR.review.done"
kit_wait_for_slot
kit_log "review.sh $PR (live sessions before: $(kit_live_workers))"
local/bin/review.sh "$PR" & RPID=$!
sleep 25; flock -u 9; wait "$RPID"; echo "REVIEW_EXIT=$?"
H=$(gh pr view "$PR" --json headRefOid --jq .headRefOid)
SLUG="$(kit_slug)" && gh api "repos/$SLUG/commits/$H/status" \
  --jq '.statuses[] | select(.context|endswith("summary")) | .context+" "+.state+" "+(.description // "")'
touch "$KIT_LANE_DIR/pr$PR.review.done"
