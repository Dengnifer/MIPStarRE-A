#!/usr/bin/env bash
# merge-chain.sh PR:ISSUE:BRANCH ... — serial fresh-base refresh + merge of review-clean PRs.
# Each merge invalidates every other PR's fresh-base gate, so the chain refreshes one PR
# (merge main -> build -> push -> CI -> carried review) and merges it before the next.
export PATH="$HOME/.cache/mipstarre-dev/owner-bin:$HOME/.local/bin:$HOME/.elan/bin:$PATH"
L=~/.cache/mipstarre-dev/watchdog/lanes
cd ~/MIPStarRE-qpbt || exit 1
rm -f "$L/chain.done" "$L/chain.needs-attention"
for spec in "$@"; do
  PR=${spec%%:*}; rest=${spec#*:}; N=${rest%%:*}; BR=${rest#*:}; SLUG=${BR#issue-*-}; SLUG=${SLUG#0*-}
  echo "== $(date -u +%FT%TZ) chain: PR $PR issue $N branch $BR"
  git fetch -q github
  H=$(gh pr view "$PR" --json headRefOid --jq .headRefOid)
  if ! git merge-base --is-ancestor github/main "$H"; then
    rm -f "$L/$N.done" "$L/$N.needs-attention"
    LANE_BRANCH=$BR SKIP_DISPATCH=1 bash /tmp/lane-v8.sh "$N" "$SLUG" prover > "$L/$N.lane.log" 2>&1
    [ -e "$L/$N.done" ] || { echo "refresh lane failed for PR $PR"; tail -3 "$L/$N.lane.log"; touch "$L/chain.needs-attention"; exit 1; }
  fi
  bash /tmp/merge.sh "$PR" > "$L/pr$PR.merge.log" 2>&1 || { echo "merge failed for PR $PR"; grep -v "^MIPStarRE pre-\|^hint" "$L/pr$PR.merge.log" | tail -4; touch "$L/chain.needs-attention"; exit 1; }
  grep -v "^MIPStarRE pre-\|^hint" "$L/pr$PR.merge.log" | tail -2
done
touch "$L/chain.done"
