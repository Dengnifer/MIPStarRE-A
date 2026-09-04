#!/usr/bin/env bash
# stack-watch.sh — reviews of STACKED PRs are wasted while their base PR is open (the diff
# contains the base's files). Registry $L/stacks holds lines "issue:slug:base-branch". Every
# 5 min: for each entry whose base branch head is now contained in github/main, run the lane
# tail WITH review on the stacked branch (merge main, build, push, CI, review) and drop the entry.
export PATH="$HOME/.cache/mipstarre-dev/owner-bin:$HOME/.local/bin:$HOME/.elan/bin:$PATH"
L=$HOME/.cache/mipstarre-dev/watchdog/lanes
cd "$HOME/MIPStarRE-qpbt" || exit 1
while true; do
  [ -e "$L/stacks" ] || { sleep 300; continue; }
  git fetch -q github
  while IFS=: read -r N SLUG BASE; do
    [ -n "$N" ] || continue
    BH=$(git rev-parse --verify -q "refs/heads/$BASE" || git rev-parse --verify -q "refs/remotes/github/$BASE")
    [ -n "$BH" ] || continue
    if git merge-base --is-ancestor "$BH" github/main; then
      echo "== $(date -u +%FT%TZ) base $BASE merged; re-running lane tail with review for #$N"
      grep -v "^$N:" "$L/stacks" > "$L/stacks.tmp"; mv "$L/stacks.tmp" "$L/stacks"
      rm -f "$L/$N.done" "$L/$N.needs-attention"
      LANE_BRANCH="issue-$N-$SLUG" SKIP_DISPATCH=1 setsid nohup bash /tmp/lane-v13.sh "$N" "$SLUG" prover > "$L/$N.lane.log" 2>&1 < /dev/null &
    fi
  done < "$L/stacks"
  sleep 300
done
