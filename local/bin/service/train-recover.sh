#!/usr/bin/env bash
# train-recover.sh — recover after the merge daemon exited on a refused or incomplete
# reviewed train.  Model-free and safe by construction: it aborts unless the daemon is
# dead, no train process runs, and every dirty or unpublished path is under
# results/telemetry.  Then it folds pending records into one commit, publishes the base
# branch, verifies remote == local, moves train-approved.running.json aside as
# train-approved.refused-<timestamp>.json (the operating session re-stages a batch in its
# own quiet window) and restarts the daemon.
#
# Recovery is never history surgery: nothing here rewrites, resets or force-pushes.
#
# Exit codes: 0 recovered, 2 nothing to do (the daemon is alive), 3 not safe yet,
# 4 non-record content in the way (a person must look), 5 publication failed.
# Provenance: kit-src/tmp-scripts/meta-train-recover-takeover.sh, hard-coded to one
# repository path, one cache directory and one dated daemon log name.
set -u
KIT_SERVICE_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd -P)"
# shellcheck source=/dev/null
. "$KIT_SERVICE_DIR/service-lib.sh"
cd "$KIT_REPO_ROOT" || exit 1

D="$KIT_DAEMON_DIR"; BASE="${KIT_BASE_BRANCH:-main}"
LOG="${KIT_DAEMON_LOG:-$KIT_LANE_DIR/merge-daemon.log}"
mkdir -p "$D" "$KIT_LANE_DIR"
log() { kit_log "$*"; kit_plog "train-recover: $*"; }

P=$(cat "$D/daemon.pid" 2>/dev/null || true)
[ -n "$P" ] && kill -0 "$P" 2>/dev/null && { echo "the daemon ($P) is alive: nothing to recover"; exit 2; }
# Anchored on this repository (see records.sh): another project's train is not ours.
pgrep -f "$KIT_REPO_ROOT/local/bin/(pr_train|daemon_train)[.]py" >/dev/null && { echo "a train process of this repository is still running"; exit 3; }

git fetch -q github "$BASE"
DIRTY=$(git status --porcelain | awk '{print $NF}' | grep -v "^results/telemetry/" || true)
[ -z "$DIRTY" ] || { echo "ABORT: dirty path outside results/telemetry:"; echo "$DIRTY"; exit 4; }
UNPUB=$(git diff --name-only "github/$BASE...$BASE" | grep -v "^results/telemetry/" || true)
[ -z "$UNPUB" ] || { echo "ABORT: unpublished content outside results/telemetry:"; echo "$UNPUB"; exit 4; }

if [ -n "$(git status --porcelain)" ]; then
  git add results/telemetry && git commit -qm "chore(telemetry): records after a refused train" \
    && log "folded pending record rows"
fi
if [ "$(git rev-parse "$BASE")" != "$(git rev-parse "github/$BASE")" ]; then
  bash local/bin/github-sync.sh "$BASE" 2>&1 | tail -n 3
  git fetch -q github "$BASE"
fi
[ "$(git rev-parse "$BASE")" = "$(git rev-parse "github/$BASE")" ] \
  || { echo "ABORT: local $BASE != github/$BASE after publication"; exit 5; }

TS=$(date -u +%Y%m%dT%H%M%SZ)
if [ -e "$D/train-approved.running.json" ]; then
  mv "$D/train-approved.running.json" "$D/train-approved.refused-$TS.json"
  log "the refused batch is kept as train-approved.refused-$TS.json (re-stage it in a quiet window)"
fi
rm -f "$D/stop"
PAR=0 setsid nohup bash "$KIT_SERVICE_DIR/merge-daemon.sh" >> "$LOG" 2>&1 < /dev/null &
sleep 3
log "daemon restarted pid $(cat "$D/daemon.pid" 2>/dev/null); $BASE $(git rev-parse --short "$BASE") published and clean"
tail -n 6 "$D/train.log" 2>/dev/null | cut -c1-200
