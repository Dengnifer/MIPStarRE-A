#!/usr/bin/env bash
# merge-daemon.sh — continuous merge queue (owner tool, 2026-09-04). Every 3 minutes: find open
# PRs that are CI-green and review-clean on their exact head (or listed in ADJ with an
# adjudication template), skip PRs whose lane is still running, refresh stale ones onto main
# one at a time (lane-v9 SKIP_DISPATCH: merge main, build, push, CI, carried review), post the
# adjudication for ADJ PRs, merge with merge-v2.sh, then rescan (main moved). Stop with
# `touch ~/.cache/mipstarre-dev/watchdog/daemon/stop`. A failed PR is retried after 2 h.
export MAX_CODEX="${MAX_CODEX:-7}"
export PATH="$HOME/.cache/mipstarre-dev/owner-bin:$HOME/.local/bin:$HOME/.elan/bin:$PATH"
L=$HOME/.cache/mipstarre-dev/watchdog/lanes; D=$HOME/.cache/mipstarre-dev/watchdog/daemon; mkdir -p "$D"
cd "$HOME/MIPStarRE-qpbt" || exit 1
ADJ=" 92 42 79 "
log() { echo "== $(date -u +%FT%TZ) $*"; }
status_of() { gh api "repos/Dengnifer/MIPStarRE-A/commits/$1/status" --jq '[.statuses[] | select(.context|endswith("summary")) | .context[6:]+"="+.state]|join(" ")'; }
unresolved_of() { gh api "repos/Dengnifer/MIPStarRE-A/pulls/$1/reviews" --jq ".[] | select(.body|contains(\"head=$2\")) | .body" | grep -c '^- \[ \]'; }
while true; do
  [ -e "$D/stop" ] && { log "stop file present; exiting"; exit 0; }
  git fetch -q github
  for PR in $(gh pr list --state open --limit 100 --json number --jq '.[].number' | sort -n); do
    [ -e "$D/stop" ] && break
    if [ -e "$D/pr$PR.failed" ] && [ "$(( $(date +%s) - $(stat -c %Y "$D/pr$PR.failed") ))" -lt 7200 ]; then continue; fi
    BR=$(gh pr view "$PR" --json headRefName --jq .headRefName); H=$(gh pr view "$PR" --json headRefOid --jq .headRefOid)
    N=$(echo "$BR" | sed -E 's/^issue-0*([0-9]+)-.*/\1/'); SLUG=${BR#issue-*-}; SLUG=${SLUG#0*-}
    [[ "$N" =~ ^[0-9]+$ ]] || continue
    pgrep -f "^bash /tmp/lane-v[0-9].sh $N " > /dev/null && continue
    S=$(status_of "$H"); echo "$S" | grep -q "ci/summary=success" || continue
    U=$(unresolved_of "$PR" "$H"); MODE=clean
    if ! echo "$S" | grep -q "review/summary=success" || [ "$U" != "0" ]; then
      echo "$ADJ" | grep -q " $PR " || continue
      MODE=adj
    fi
    log "PR $PR ($BR @ ${H:0:7}) merge candidate ($MODE)"
    if ! git merge-base --is-ancestor github/main "$H"; then
      W=.worktrees/$BR
      if [ "$MODE" = adj ] && [ -d "$W" ] && ! git -C "$W" diff --quiet github/main -- .githooks/pre-commit; then
        git -C "$W" checkout github/main -- .githooks/pre-commit && git -C "$W" commit -qm "chore(hooks): take the merge-budget exemption from main"
      fi
      rm -f "$L/$N.done" "$L/$N.needs-attention"
      LANE_BRANCH=$BR SKIP_DISPATCH=1 bash /tmp/lane-v9.sh "$N" "$SLUG" prover > "$L/$N.lane.log" 2>&1
      [ -e "$L/$N.done" ] || { log "refresh failed for PR $PR"; tail -2 "$L/$N.lane.log"; touch "$D/pr$PR.failed"; continue; }
      H=$(gh pr view "$PR" --json headRefOid --jq .headRefOid); S=$(status_of "$H")
      if [ "$MODE" = clean ] && { ! echo "$S" | grep -q "review/summary=success" || [ "$(unresolved_of "$PR" "$H")" != "0" ]; }; then log "review not clean on the refreshed head of PR $PR"; continue; fi
    fi
    ARGS=()
    if [ "$MODE" = adj ]; then
      T=$(ls /tmp/adjudication-$PR-template*.md 2>/dev/null | tail -1); [ -n "$T" ] || { log "no adjudication template for PR $PR"; continue; }
      sed "s/__HEAD__/$H/" "$T" > "/tmp/adjudication-$PR.md"
      gh api "repos/Dengnifer/MIPStarRE-A/issues/$PR/comments" -F body=@"/tmp/adjudication-$PR.md" --jq .html_url
      ARGS=(--adjudicated)
    fi
    if bash /tmp/merge-v2.sh "$PR" "${ARGS[@]}" > "$L/pr$PR.merge.log" 2>&1; then
      log "merged PR $PR"; grep -v "^MIPStarRE pre-\|^hint\|^Blueprint" "$L/pr$PR.merge.log" | tail -2; rm -f "$D/pr$PR.failed"; echo "$PR" >> "$D/merged"
      break
    else
      log "merge failed for PR $PR"; grep -v "^MIPStarRE pre-\|^hint\|^Blueprint" "$L/pr$PR.merge.log" | tail -3; touch "$D/pr$PR.failed"
    fi
  done
  sleep 180
done
