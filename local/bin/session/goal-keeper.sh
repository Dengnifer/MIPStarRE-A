#!/usr/bin/env bash
# goal-keeper.sh — keep the main session's goal loop running and its turns short.
#
# Provenance: the origin project's goal-keeper-v3.sh.  Every cycle it looks at
# the last four non-empty pane lines and does one of three things: resume a
# stalled or paused goal, set the goal again on a session that went idle without
# one, or press Escape once on a turn that has run longer than the turn limit
# (codex keeps its work and queued messages then land).  Unlike the original it
# has NO built-in goal: the goal text comes only from the state directory, so a
# keeper can never re-send another project's goal.
#
#   goal-keeper.sh [--interval S] [--turn-max M] [--once] [--dry-run]
#   stop it with:  touch "$KIT_STATE_DIR/goal-keeper.stop"
set -u
. "$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)/lib.sh"

INTERVAL="${KIT_KEEPER_INTERVAL:-120}"
TURN_MAX="$KIT_TURN_MAX"
ONCE=0
while [ $# -gt 0 ]; do
  case "$1" in
    --interval) INTERVAL="${2:?}"; shift 2 ;;
    --turn-max) TURN_MAX="${2:?}"; shift 2 ;;
    --once) ONCE=1; shift ;;
    --dry-run) KIT_DRY_RUN=1; ONCE=1; shift ;;
    -h|--help) sed -n '1,14p' "$0" >&2; exit 3 ;;
    *) printf 'goal-keeper.sh: unknown argument %s\n' "$1" >&2; exit 3 ;;
  esac
done
kit_state_dir
[ -f "$KIT_STATE_DIR/turn-max" ] && TURN_MAX="$(cat "$KIT_STATE_DIR/turn-max")"
GOAL_FILE="$KIT_STATE_DIR/goal-text"
SAY="${KIT_SAY:-$KIT_SESSION_DIR/say.sh}"
LOG="$KIT_STATE_DIR/goal-keeper.log"
klog() { printf '%s %s\n' "$(kit_now)" "$*" >> "$LOG"; kit_is_dry && printf '%s\n' "$*"; return 0; }

kit_is_dry || echo $$ > "$KIT_STATE_DIR/goal-keeper.pid"
klog "goal-keeper started (pid $$): interval ${INTERVAL}s, turn limit ${TURN_MAX}m, goal file $GOAL_FILE"
[ -s "$GOAL_FILE" ] || klog "WARNING: $GOAL_FILE is missing or empty; an idle session will NOT be given a goal (there is no built-in goal)"

LAST_ESCAPE=0
while true; do
  [ -e "$KIT_STATE_DIR/goal-keeper.stop" ] && { klog "stop file; exiting"; exit 0; }

  PANE="$(kit_pane -S -6 | grep -v '^[[:space:]]*$' | tail -n 4)"
  DECISION=none

  if printf '%s\n' "$PANE" | grep -q -E "Goal (stalled|paused)"; then
    DECISION=resume
    if kit_is_dry; then klog "would send /goal resume"; else
      bash "$SAY" --mode idle --timeout 300 "/goal resume" >> "$LOG" 2>&1 && klog "resumed the goal"
    fi
  elif kit_status_line_seen "$(printf '%s\n' "$PANE" | tail -n 1)" \
       && ! printf '%s\n' "$PANE" | grep -q -E "Pursuing goal|Goal \((paused|stalled|active)\)" \
       && ! printf '%s\n' "$PANE" | grep -q -E "$KIT_BUSY_RE"; then
    if [ -s "$GOAL_FILE" ]; then
      DECISION=set-goal
      if kit_is_dry; then klog "would set the goal from $GOAL_FILE"; else
        bash "$SAY" --mode idle --timeout 300 --file "$GOAL_FILE" >> "$LOG" 2>&1 \
          && klog "set the goal on a goal-less idle session"
      fi
    else
      DECISION=no-goal-text
      klog "the session is idle without a goal, but $GOAL_FILE is empty: nothing sent"
    fi
  fi

  MINUTES="$(printf '%s\n' "$PANE" | grep -o -E "Working \([0-9]+m" | grep -o -E "[0-9]+" | tail -n 1 || true)"
  if [ -n "${MINUTES:-}" ] && [ "$MINUTES" -ge "$TURN_MAX" ] \
     && [ $(( $(date +%s) - LAST_ESCAPE )) -gt "${KIT_KEEPER_ESCAPE_GAP:-600}" ]; then
    DECISION="$DECISION+escape"
    if kit_is_dry; then klog "would interrupt a ${MINUTES}-minute turn (limit ${TURN_MAX})"; else
      tmux send-keys -t "$KIT_TMUX" Escape
      LAST_ESCAPE=$(date +%s)
      klog "interrupted a ${MINUTES}-minute turn (limit ${TURN_MAX})"
    fi
  fi

  [ "${KIT_KEEPER_PRINT_DECISION:-0}" = 1 ] && printf 'decision=%s\n' "$DECISION"
  [ "$ONCE" = 1 ] && exit 0
  sleep "$INTERVAL"
done
