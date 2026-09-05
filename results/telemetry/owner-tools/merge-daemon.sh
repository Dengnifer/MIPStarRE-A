#!/usr/bin/env bash
# merge-daemon-v3.sh — merge queue with PARALLEL refreshes (owner tool, 2026-09-04).
# Loop: collect every open PR that is CI-green and review-clean on its head (or in ADJ with a
# template) and has no running lane; refresh ALL stale candidates concurrently (up to 4 lanes:
# merge main, incremental build, push, CI, carried review); then merge the first candidate that is
# fresh and clean (ADJ: post the adjudication for the head first); rescan. Stop with
# `touch ~/.cache/mipstarre-dev/watchdog/daemon/stop`. A failed PR is retried after 2 h.
export MAX_CODEX="${MAX_CODEX:-7}"
export PATH="$HOME/.cache/mipstarre-dev/owner-bin:$HOME/.local/bin:$HOME/.elan/bin:$PATH"
L=$HOME/.cache/mipstarre-dev/watchdog/lanes; D=$HOME/.cache/mipstarre-dev/watchdog/daemon; mkdir -p "$D"
cd "$HOME/MIPStarRE-qpbt" || exit 1
ADJ=" $(cat "$D/adj-list" 2>/dev/null || echo 92 42 79) "
PAR=4
log() { echo "== $(date -u +%FT%TZ) $*"; }
status_of() { gh api "repos/Dengnifer/MIPStarRE-A/commits/$1/status" --jq '[.statuses[] | select(.context|endswith("summary")) | .context[6:]+"="+.state]|join(" ")'; }
unresolved_of() { gh api "repos/Dengnifer/MIPStarRE-A/pulls/$1/reviews" --jq ".[] | select(.body|contains(\"head=$2\")) | .body" | grep -c '^- \[ \]'; }
clean_on() { S=$(status_of "$2"); echo "$S" | grep -q "ci/summary=success" || return 1; echo "$S" | grep -q "review/summary=success" || return 1; [ "$(unresolved_of "$1" "$2")" = "0" ]; }
refresh() { # PR N BR SLUG MODE
  local PR=$1 N=$2 BR=$3 SLUG=$4 MODE=$5 W=.worktrees/$3
  if [ "$MODE" = adj ] && [ -d "$W" ] && git show github/main:.githooks/pre-commit | grep -q MERGE_HEAD && ! git -C "$W" show HEAD:.githooks/pre-commit | grep -q MERGE_HEAD; then
    git -C "$W" checkout github/main -- .githooks/pre-commit && git -C "$W" commit -qm "chore(hooks): take the merge-budget exemption from main"
  fi
  rm -f "$L/$N.done" "$L/$N.needs-attention"
  LANE_BRANCH=$BR SKIP_DISPATCH=1 bash /tmp/lane-v12.sh "$N" "$SLUG" prover > "$L/$N.lane.log" 2>&1
  [ -e "$L/$N.done" ] || { log "refresh failed for PR $PR"; tail -2 "$L/$N.lane.log"; touch "$D/pr$PR.failed"; return 1; }
}
while true; do
  [ -e "$D/stop" ] && { log "stop file present; exiting"; exit 0; }
  git fetch -q github
  CANDS=()
  for PR in $(gh pr list --state open --limit 100 --json number --jq '.[].number' | sort -n); do
    if [ -e "$D/pr$PR.failed" ] && [ "$(( $(date +%s) - $(stat -c %Y "$D/pr$PR.failed") ))" -lt 7200 ]; then continue; fi
    BR=$(gh pr view "$PR" --json headRefName --jq .headRefName); H=$(gh pr view "$PR" --json headRefOid --jq .headRefOid)
    N=$(echo "$BR" | sed -E 's/^issue-0*([0-9]+)-.*/\1/'); SLUG=${BR#issue-*-}; SLUG=${SLUG#0*-}
    [[ "$N" =~ ^[0-9]+$ ]] || continue
    pgrep -f "^bash /tmp/lane-v[0-9]+.sh $N " > /dev/null && continue
    S=$(status_of "$H"); echo "$S" | grep -q "ci/summary=success" || continue
    MODE=clean
    if ! clean_on "$PR" "$H"; then echo "$ADJ" | grep -q " $PR " || continue; MODE=adj; fi
    CANDS+=("$PR:$N:$BR:$SLUG:$MODE:$H")
  done
  if [ "${#CANDS[@]}" -eq 0 ]; then sleep 120; continue; fi
  log "candidates: $(printf '%s ' "${CANDS[@]}" | sed -E 's/:[^ ]*//g')"
  # phase A: refresh every stale candidate, up to PAR at a time
  RUNNING=0
  for c in "${CANDS[@]}"; do
    IFS=: read -r PR N BR SLUG MODE H <<< "$c"
    git merge-base --is-ancestor github/main "$H" && continue
    log "refreshing PR $PR ($BR)"
    refresh "$PR" "$N" "$BR" "$SLUG" "$MODE" &
    RUNNING=$((RUNNING+1)); [ "$RUNNING" -ge "$PAR" ] && { wait -n; RUNNING=$((RUNNING-1)); }
  done
  wait
  # phase B: merge the first fresh, clean candidate
  git fetch -q github
  for c in "${CANDS[@]}"; do
    IFS=: read -r PR N BR SLUG MODE H0 <<< "$c"
    [ -e "$D/stop" ] && break
    [ "$(gh pr view "$PR" --json state --jq .state)" = "OPEN" ] || continue
    H=$(gh pr view "$PR" --json headRefOid --jq .headRefOid)
    git merge-base --is-ancestor github/main "$H" || { log "PR $PR still stale after refresh"; continue; }
    ARGS=()
    if [ "$MODE" = adj ]; then
      T=$(ls /tmp/adjudication-$PR-template*.md 2>/dev/null | tail -1); [ -n "$T" ] || { log "no adjudication template for PR $PR"; continue; }
      sed "s/__HEAD__/$H/" "$T" > "/tmp/adjudication-$PR.md"
      gh api "repos/Dengnifer/MIPStarRE-A/issues/$PR/comments" -F body=@"/tmp/adjudication-$PR.md" --jq .html_url
      ARGS=(--adjudicated)
    else
      clean_on "$PR" "$H" || { log "PR $PR not clean on its refreshed head"; continue; }
    fi
    if bash /tmp/merge-v2.sh "$PR" "${ARGS[@]}" > "$L/pr$PR.merge.log" 2>&1; then
      log "merged PR $PR"; grep -v "^MIPStarRE pre-\|^hint\|^Blueprint" "$L/pr$PR.merge.log" | tail -2; rm -f "$D/pr$PR.failed"; echo "$PR" >> "$D/merged"
      break
    else
      log "merge failed for PR $PR"; grep -v "^MIPStarRE pre-\|^hint\|^Blueprint" "$L/pr$PR.merge.log" | tail -3; touch "$D/pr$PR.failed"
    fi
  done
  sleep 30
done
