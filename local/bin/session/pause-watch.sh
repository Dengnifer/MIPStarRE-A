#!/usr/bin/env bash
# pause-watch.sh — watch for the two markers that mean "stop now" and act on
# them: `cutoff` (the key watch proved the main session's key is dead) and
# `pause-now` (the operator wrote it).  It calls pause.sh now, once.
#
# Provenance: the origin project's meta-pause-watch.sh.  It exists because the
# thing that decides to stop (the key watch) must not be the thing that stops
# everything: a guard lives outside what it guards.
#
#   pause-watch.sh [--interval S] [--once] [--dry-run]
#   stop it with: touch "$KIT_STATE_DIR/pause-watch.stop"
set -u
. "$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)/lib.sh"

INTERVAL="${KIT_PAUSE_WATCH_INTERVAL:-30}"; ONCE=0
while [ $# -gt 0 ]; do
  case "$1" in
    --interval) INTERVAL="${2:?}"; shift 2 ;;
    --once) ONCE=1; shift ;;
    --dry-run) KIT_DRY_RUN=1; ONCE=1; shift ;;
    -h|--help) sed -n '1,12p' "$0" >&2; exit 3 ;;
    *) printf 'pause-watch.sh: unknown argument %s\n' "$1" >&2; exit 3 ;;
  esac
done
kit_state_dir
kit_is_dry || echo $$ > "$KIT_STATE_DIR/pause-watch.pid"
kit_log "pause watch started (pid $$): triggers are $KIT_STATE_DIR/cutoff and $KIT_STATE_DIR/pause-now"

while true; do
  [ -e "$KIT_STATE_DIR/pause-watch.stop" ] && { kit_log "pause watch: stop file; exiting"; exit 0; }
  if [ ! -e "$KIT_STATE_DIR/paused" ]; then
    if [ -e "$KIT_STATE_DIR/cutoff" ]; then
      bash "$KIT_SESSION_DIR/pause.sh" now --reason "cutoff marker: $(head -c 120 "$KIT_STATE_DIR/cutoff" | tr '\n' ' ')"
    elif [ -e "$KIT_STATE_DIR/pause-now" ]; then
      bash "$KIT_SESSION_DIR/pause.sh" now --reason "pause-now marker: $(head -c 120 "$KIT_STATE_DIR/pause-now" | tr '\n' ' ')"
    fi
  fi
  [ "$ONCE" = 1 ] && exit 0
  sleep "$INTERVAL"
done
