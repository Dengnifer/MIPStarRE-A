#!/usr/bin/env bash
# capacityd.sh — run local/bin/capacity_controller.py tick every 60 s.
# Usage: bash results/telemetry/owner-tools/capacityd.sh [--once]
# Stop it by touching $W/capacity/capacityd.stop (the loop exits within one tick) or by
# killing the pid in $W/capacity/capacityd.pid. This is the whole supervisor: a while/sleep
# loop with a stop file. Anything more is the "hardening the hardening" pattern that cost
# this project 17 hours on 2026-09-01 (design full-speed-v2 §9 item 7).
# A failing tick is logged and retried on the next tick; the controller leaves the cap files
# untouched when its inputs are malformed, so a bad run-mode.json never zeroes capacity.
set -u
export PATH="$HOME/.cache/mipstarre-dev/owner-bin:$HOME/.local/bin:$PATH"
ROOT="${MIPSTARRE_CHECKOUT:-$HOME/MIPStarRE-qpbt}"
W="${MIPSTARRE_CACHE_ROOT:-$HOME/.cache/mipstarre-dev}/watchdog"
C="$W/capacity"; STOP="$C/capacityd.stop"; LOG="$C/capacityd.log"; INTERVAL="${CAPACITY_TICK_S:-60}"
mkdir -p "$C" || exit 1
echo "tool=capacityd.sh version=$(git -C "$ROOT" rev-parse --short HEAD 2>/dev/null || echo unknown) started $(date -u +%FT%TZ)" >>"$LOG"
# The stop file is kept across restarts, as the merge daemon's is: the resume path removes it.
[ -e "$STOP" ] && { echo "$(date -u +%FT%TZ) stop file present; remove $STOP to start" >>"$LOG"; exit 0; }
echo $$ >"$C/capacityd.pid"
while true; do
  [ -e "$STOP" ] && { echo "$(date -u +%FT%TZ) stop file present; exiting" >>"$LOG"; break; }
  python3 "$ROOT/local/bin/capacity_controller.py" tick >>"$LOG" 2>&1 ||
    echo "$(date -u +%FT%TZ) tick failed rc=$? (cap files untouched; retrying in ${INTERVAL}s)" >>"$LOG"
  [ "${1:-}" = "--once" ] && break
  sleep "$INTERVAL"
done
rm -f "$C/capacityd.pid"
