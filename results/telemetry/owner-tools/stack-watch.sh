#!/usr/bin/env bash
# stack-watch.sh — reviews of STACKED PRs are wasted while their base PR is still open
# (the diff carries the base's files too).  The registry <state>/lanes/stacks holds one
# line "issue:slug:base-branch" per stacked packet.  Every five minutes this checks each
# entry: once the base branch's head is contained in the integration branch, it re-runs
# the lane tail WITH review on the stacked branch and drops the entry.
# Stop it by removing its entries, or kill it by its pid.
# Provenance: the origin's owner-tools/stack-watch.sh (checkout path, cache directory and
# the /tmp path of the lane runner hard-coded).
set -u
HERE="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd -P)"
SERVICE="$HERE/../../../local/bin/service"
# shellcheck source=/dev/null
. "$SERVICE/service-lib.sh"
cd "$KIT_REPO_ROOT" || exit 1
BASE="${KIT_BASE_BRANCH:-main}"
L="$KIT_LANE_DIR"

while true; do
  [ -s "$L/stacks" ] || { sleep 300; continue; }
  git fetch -q github
  while IFS=: read -r N SLUG STACK_BASE; do
    [ -n "$N" ] || continue
    BH=$(git rev-parse --verify -q "refs/heads/$STACK_BASE" || git rev-parse --verify -q "refs/remotes/github/$STACK_BASE") || continue
    [ -n "$BH" ] || continue
    if git merge-base --is-ancestor "$BH" "github/$BASE"; then
      kit_log "base $STACK_BASE is merged; re-running the lane tail with review for #$N"
      grep -v "^$N:" "$L/stacks" > "$L/stacks.tmp"; mv "$L/stacks.tmp" "$L/stacks"
      rm -f "$L/$N.done" "$L/$N.needs-attention"
      LANE_BRANCH="issue-$N-$SLUG" SKIP_DISPATCH=1 setsid nohup bash "$SERVICE/lane.sh" "$N" "$SLUG" prover \
        > "$L/$N.lane.log" 2>&1 < /dev/null &
    fi
  done < "$L/stacks"
  sleep 300
done
