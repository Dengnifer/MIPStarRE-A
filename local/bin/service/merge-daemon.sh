#!/usr/bin/env bash
# merge-daemon.sh — the merge queue.  One scan per loop (daemon-scan.py, one GraphQL
# call) gives every open PR with its head; a candidate is CI-green and review-clean at
# that head (or listed in <daemon>/adj-list with an adjudication template) and has no
# running lane.  Fresh candidates — the integration branch is an ancestor, or has only
# advanced through passive telemetry records — merge at once, one after another, with
# freshness re-checked after each merge.  Stale candidates get a DETACHED refresh lane
# (merge the base, incremental build, push, CI, carried review), at most PAR at a time,
# tracked by <daemon>/pr<N>.refreshing; the loop never waits for one.  A staged reviewed
# train takes over the loop for one pass.  Stop with `touch <daemon>/stop`.
#
# Rules paid for in incidents:
#   * A failed PR is not retried for two hours (<daemon>/pr<N>.failed).
#   * Never pkill by substring: the lane check uses an anchored pgrep with a bracket in
#     the pattern so it cannot match itself, and refresh subshells share this daemon's
#     command line — stop the daemon through its pid file, never through pgrep.
#   * Telemetry is committed right BEFORE a merge attempt (merge gate 2 needs a clean
#     primary) and again after (the base moved anyway), at most one idle batch an hour.
#   * A refused train leaves <daemon>/train-approved.running.json behind and the daemon
#     exits: reconciliation is train-recover.sh, never history surgery.
#
# Environment: PAR (detached refreshes, default 0 = reviewed mode), KIT_BASE_BRANCH.
# Provenance: kit-src/tmp-scripts/merge-daemon-v9k-cpa.sh, hard-coded to one repository,
# one cache directory, one repository slug and /tmp script paths.
set -u
KIT_SERVICE_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd -P)"
# shellcheck source=/dev/null
. "$KIT_SERVICE_DIR/service-lib.sh"
cd "$KIT_REPO_ROOT" || exit 1

SLUG="$(kit_slug)" || { echo "merge-daemon: no GitHub slug (set project.github_slug)" >&2; exit 2; }
BASE="${KIT_BASE_BRANCH:-main}"
L="$KIT_LANE_DIR"; D="$KIT_DAEMON_DIR"; mkdir -p "$L" "$D" "$D/cache"
PAR="${PAR:-0}"
[ "$PAR" = 0 ] || { echo "the reviewed daemon requires PAR=0" >&2; exit 1; }
echo $$ > "$D/daemon.pid"   # restart with: kill "$(cat <daemon>/daemon.pid)"
log() { kit_log "$*"; }

status_of() { timeout 60 gh api "repos/$SLUG/commits/$1/status" \
  --jq '[.statuses[] | select(.context|endswith("summary")) | .context[6:]+"="+.state]|join(" ")' 2>/dev/null; }
unresolved_of() { timeout 60 gh api "repos/$SLUG/pulls/$1/reviews" \
  --jq ".[] | select(.body|contains(\"head=$2\")) | .body" 2>/dev/null | grep -c '^- \[ \]'; }
clean_on() { local S; S=$(status_of "$2")
  echo "$S" | grep -q "ci/summary=success" || return 1
  echo "$S" | grep -q "review/summary=success" || return 1
  [ "$(unresolved_of "$1" "$2")" = "0" ]; }
head_of() { timeout 60 gh pr view "$1" --repo "$SLUG" --json headRefOid,state \
  --jq 'select(.state=="OPEN") | .headRefOid' 2>/dev/null; }
# Freshness is the merged gate-2b predicate, imported from the repository's own merge
# gate so the daemon and the gate can never disagree.
fresh() { python3 -c "import sys; from pathlib import Path; sys.path.insert(0, 'local/bin'); import pr_merge; sys.exit(0 if pr_merge.head_is_fresh(Path('.'), sys.argv[1], sys.argv[2]) else 1)" "github/$BASE" "$1" 2>/dev/null; }
lane_running() { pgrep -f "^bash $KIT_SERVICE_DIR/lan[e].sh $1 " > /dev/null; }

refreshing_count() { local n=0 f pid
  for f in "$D"/pr*.refreshing; do
    [ -e "$f" ] || continue
    pid=$(cat "$f" 2>/dev/null)
    if [ -n "$pid" ] && kill -0 "$pid" 2>/dev/null; then n=$((n+1)); else rm -f "$f"; fi
  done; echo "$n"; }

launch_refresh() { # PR ISSUE BRANCH SLUG MODE
  local PR=$1 N=$2 BR=$3 WSLUG=$4 MODE=$5
  rm -f "$L/$N.done" "$L/$N.needs-attention"
  ( LANE_BRANCH=$BR SKIP_DISPATCH=1 setsid bash "$KIT_SERVICE_DIR/lane.sh" "$N" "$WSLUG" prover \
      > "$L/$N.lane.log" 2>&1 < /dev/null
    if [ -e "$L/$N.done" ]; then
      echo "== $(date -u +%FT%TZ) refresh done for PR $PR" >> "$D/refresh.log"
      echo "$PR:$N:$MODE" >> "$D/refresh-done.queue"
    else
      echo "== $(date -u +%FT%TZ) refresh failed for PR $PR: $(tail -n 1 "$L/$N.lane.log")" >> "$D/refresh.log"
      touch "$D/pr$PR.failed"
    fi
    rm -f "$D/pr$PR.refreshing" ) &
  echo $! > "$D/pr$PR.refreshing"
  log "refreshing PR $PR ($BR) detached, pid $(cat "$D/pr$PR.refreshing")"
}

try_merge() { # PR ISSUE MODE HEAD
  local PR=$1 N=$2 MODE=$3 H=$4 ARGS=() T
  if [ "$MODE" = adj ]; then
    T=$(ls "$D"/adjudication-"$PR"-template*.md 2>/dev/null | tail -1)
    [ -n "$T" ] || { log "no adjudication template for PR $PR in $D"; return 1; }
    sed "s/__HEAD__/$H/" "$T" > "$D/adjudication-$PR.md"
    timeout 60 gh api "repos/$SLUG/issues/$PR/comments" -F body=@"$D/adjudication-$PR.md" --jq .html_url
    ARGS=(--adjudicated)
  else
    clean_on "$PR" "$H" || { log "PR $PR not clean on head ${H:0:8}"; return 1; }
  fi
  if bash "$KIT_SERVICE_DIR/merge.sh" "$PR" "${ARGS[@]}" > "$L/pr$PR.merge.log" 2>&1; then
    log "merged PR $PR"; tail -2 "$L/pr$PR.merge.log"
    rm -f "$D/pr$PR.failed"; echo "$PR" >> "$D/merged"
    commit_telemetry "batch after the PR $PR merge"
    return 0
  fi
  log "merge failed for PR $PR"; tail -3 "$L/pr$PR.merge.log"; touch "$D/pr$PR.failed"; return 1
}

commit_telemetry() { # subject tail
  [ -n "$(git status --porcelain -- results/telemetry)" ] || return 0
  git add results/telemetry \
    && git commit -qm "chore(telemetry): $1" >/dev/null 2>&1 \
    && git push -q github "$BASE" >/dev/null 2>&1 \
    && log "telemetry committed: $1"; }

log "merge daemon up: $SLUG base $BASE state $D"
while true; do
  [ -e "$D/train-approved.running.json" ] && {
    log "a reviewed train needs reconciliation ($D/train-approved.running.json); exiting (run train-recover.sh)"; exit 1; }
  [ -e "$D/stop" ] && { log "stop file present; exiting"; exit 0; }
  git fetch -q github 2>/dev/null

  # Fast path: a PR whose refresh just finished is merged before the scan, so a later
  # merge in this same pass cannot make it stale again.
  if [ -s "$D/refresh-done.queue" ]; then
    Q=$(cat "$D/refresh-done.queue"); : > "$D/refresh-done.queue"
    while IFS=: read -r PR N MODE; do
      [ -n "$PR" ] || continue
      H=$(head_of "$PR"); [ -n "$H" ] || continue
      if fresh "$H"; then
        log "fast path: PR $PR refreshed and fresh"
        commit_telemetry "records before PR $PR merge"
        try_merge "$PR" "$N" "$MODE" "$H" && git fetch -q github 2>/dev/null
      else
        log "fast path: PR $PR refreshed but already stale"
      fi
    done <<< "$Q"
  fi

  CANDS=()
  SCAN=$(timeout 150 python3 "$KIT_SERVICE_DIR/daemon-scan.py" "$D/adj-list" 2>>"$D/scan.err") \
    || { log "scan failed (see $D/scan.err); retry in 60 s"; sleep 60; continue; }
  while IFS=: read -r PR N BR WSLUG MODE H; do
    [ -n "$PR" ] || continue
    if [ -e "$D/pr$PR.failed" ] && [ "$(( $(date +%s) - $(stat -c %Y "$D/pr$PR.failed") ))" -lt 7200 ]; then continue; fi
    lane_running "$N" && continue
    [ -e "$D/pr$PR.refreshing" ] && kill -0 "$(cat "$D/pr$PR.refreshing" 2>/dev/null)" 2>/dev/null && continue
    CANDS+=("$PR:$N:$BR:$WSLUG:$MODE:$H")
  done <<< "$SCAN"
  if [ "${#CANDS[@]}" -eq 0 ]; then sleep 90; continue; fi
  log "candidates: $(printf '%s ' "${CANDS[@]}" | sed -E 's/:[^ ]*//g')| refreshing: $(refreshing_count)"

  # A staged reviewed train owns the whole pass.
  if [ -f "$D/train-approved.json" ]; then
    if [ "$(refreshing_count)" -ne 0 ]; then log "reviewed train held: a refresh is still running"; sleep 45; continue; fi
    mv "$D/train-approved.json" "$D/train-approved.running.json" || { log "train admission rename failed"; exit 1; }
    if printf '%s\n' "${CANDS[@]}" | python3 "$KIT_REPO_ROOT/local/bin/daemon_train.py" \
        --repo-root "$KIT_REPO_ROOT" --batch-file "$D/train-approved.running.json" >> "$D/train.log" 2>&1; then
      mv "$D/train-approved.running.json" "$D/train-approved.done.json" \
        || { log "train completed but the receipt rename failed; reconcile by hand"; exit 1; }
      log "reviewed train completed; the published manifest names the actual members ($D/train.log)"
    else
      log "reviewed train refused or incomplete ($D/train.log); no automatic retry"
      exit 1
    fi
    continue
  fi

  # Phase B: merge every fresh candidate, re-fetching after each (a merge stales the rest).
  MERGED_ONE=0
  for c in "${CANDS[@]}"; do
    IFS=: read -r PR N BR WSLUG MODE H <<< "$c"
    [ -e "$D/stop" ] && break
    git fetch -q github 2>/dev/null
    H=$(head_of "$PR"); [ -n "$H" ] || continue
    fresh "$H" || continue
    commit_telemetry "records before PR $PR merge"
    try_merge "$PR" "$N" "$MODE" "$H" && MERGED_ONE=1
  done

  # Phase A: detached refreshes for stale candidates, up to PAR at a time.
  git fetch -q github 2>/dev/null
  for c in "${CANDS[@]}"; do
    IFS=: read -r PR N BR WSLUG MODE H <<< "$c"
    [ "$(refreshing_count)" -ge "$PAR" ] && break
    [ -e "$D/pr$PR.refreshing" ] && continue
    lane_running "$N" && continue
    H=$(head_of "$PR"); [ -n "$H" ] || continue
    fresh "$H" && continue
    launch_refresh "$PR" "$N" "$BR" "$WSLUG" "$MODE"
  done

  # At most one idle telemetry batch an hour, measured from the last commit that
  # touched results/telemetry.
  LASTS=$(git log -1 --format=%ct -- results/telemetry 2>/dev/null || echo 0)
  if [ -n "$(git status --porcelain -- results/telemetry)" ] \
     && [ "$(( $(date +%s) - LASTS ))" -gt 3600 ] && [ "$(refreshing_count)" -eq 0 ]; then
    commit_telemetry "hourly batch"
  fi
  [ "$MERGED_ONE" = 1 ] && sleep 10 || sleep 45
done
