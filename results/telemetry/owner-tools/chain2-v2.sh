#!/usr/bin/env bash
# chain2.sh — after merge-chain finishes: refresh + adjudicate + merge PRs 92, 42, 79 in order.
# 42/79 first take the merge-budget hook from main (their branches carry the old hook).
export MAX_CODEX="${MAX_CODEX:-7}"
export PATH="$HOME/.cache/mipstarre-dev/owner-bin:$HOME/.local/bin:$HOME/.elan/bin:$PATH"
L=~/.cache/mipstarre-dev/watchdog/lanes
cd ~/MIPStarRE-qpbt || exit 1
while [ ! -e "$L/chain.done" ] && [ ! -e "$L/chain.needs-attention" ]; do sleep 60; done
rm -f "$L/chain2.done" "$L/chain2.needs-attention"
step() { # PR ISSUE BRANCH TEMPLATE
  PR=$1; N=$2; BR=$3; T=$4; SLUG=${BR#issue-*-}; SLUG=${SLUG#0*-}; W=.worktrees/$BR
  echo "== $(date -u +%FT%TZ) chain2: PR $PR issue $N"
  git fetch -q github
  [ "$(gh pr view "$PR" --json state --jq .state)" = "MERGED" ] && { echo "PR $PR already merged"; return 0; }
  if [ -d "$W" ] && ! git -C "$W" diff --quiet github/main -- .githooks/pre-commit; then
    git -C "$W" checkout github/main -- .githooks/pre-commit && git -C "$W" commit -qm "chore(hooks): take the merge-budget exemption from main" || { echo "hook sync failed"; touch "$L/chain2.needs-attention"; exit 1; }
  fi
  rm -f "$L/$N.done" "$L/$N.needs-attention"
  LANE_BRANCH=$BR SKIP_DISPATCH=1 bash /tmp/lane-v9.sh "$N" "$SLUG" prover > "$L/$N.lane.log" 2>&1
  [ -e "$L/$N.done" ] || { echo "refresh lane failed for PR $PR"; tail -3 "$L/$N.lane.log"; touch "$L/chain2.needs-attention"; exit 1; }
  H=$(gh pr view "$PR" --json headRefOid --jq .headRefOid)
  sed "s/__HEAD__/$H/" "$T" > "/tmp/adjudication-$PR.md"
  gh api "repos/Dengnifer/MIPStarRE-A/issues/$PR/comments" -F body=@"/tmp/adjudication-$PR.md" --jq .html_url
  bash /tmp/merge.sh "$PR" --adjudicated > "$L/pr$PR.merge.log" 2>&1 || { echo "merge failed for PR $PR"; grep -v "^MIPStarRE pre-\|^hint" "$L/pr$PR.merge.log" | tail -4; touch "$L/chain2.needs-attention"; exit 1; }
  grep -v "^MIPStarRE pre-\|^hint" "$L/pr$PR.merge.log" | tail -2
}
step 92 91 issue-91-hook-merge-exempt /tmp/adjudication-92-template.md
step 42 8 issue-0008-gh-common-review-replace /tmp/adjudication-42-template.md
step 79 60 issue-60-third-round-refusal /tmp/adjudication-79-template2.md
touch "$L/chain2.done"
