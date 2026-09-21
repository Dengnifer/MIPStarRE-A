#!/usr/bin/env bash
# stage-when-quiet.sh PR PR [PR...] — wait for the quiet window, publish records, stage
# the train.  A train needs the primary checkout untouched for its whole run, so this
# waits (at most KIT_QUIET_WAIT_MINUTES, default 20) until no local/bin/ci.sh run is in
# flight, then commits and publishes pending records so the primary is clean, and only
# then hands the members to stage-train.py.
# Provenance: kit-src/tmp-scripts/meta-stage-when-quiet.sh.
set -u
KIT_SERVICE_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd -P)"
# shellcheck source=/dev/null
. "$KIT_SERVICE_DIR/service-lib.sh"
cd "$KIT_REPO_ROOT" || exit 1
export PYTHONDONTWRITEBYTECODE=1

[ "$#" -ge 2 ] || { echo "usage: stage-when-quiet.sh PR PR [PR...]" >&2; exit 2; }
TICKS=$(( ${KIT_QUIET_WAIT_MINUTES:-20} * 4 ))
for _ in $(seq 1 "$TICKS"); do pgrep -f "local/bin/ci[.]sh" >/dev/null || break; sleep 15; done
bash "$KIT_SERVICE_DIR/records.sh" "records before the train" | tail -n 1
raw=$(python3 "$KIT_SERVICE_DIR/stage-train.py" "$@" 2>&1); rc=$?
out=$(printf '%s\n' "$raw" | tail -n 3 | tr '\n' ' ' | cut -c1-300)
echo "$out"
kit_plog "stage-when-quiet $*: $out"
exit "$rc"
