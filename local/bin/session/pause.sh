#!/usr/bin/env bash
# pause.sh — stop the project, in one of two ways.
#
#   pause.sh graceful <epoch> [--reason TEXT]
#       A LANDING.  Nothing is killed.  At the given time the merge queue is
#       told to stop after the job it is running, and the between-turn loop is
#       told to stop.  Work already running finishes by itself.  Use this for
#       "wind down by <time>".
#
#   pause.sh now [--reason TEXT] [--wait-minutes N]
#       The HARD variant, and it says so.  Worker caps go to 0, the goal keeper
#       and the key watch are stopped, the merge queue is told to stop and is
#       given up to N minutes to finish a running job, and the main session's
#       TUI is closed — politely first (/quit, then Ctrl-C), and only if it
#       still will not go, with a signal.  A turn in flight is lost.
#
#   pause.sh status     what is paused, cut off, or armed
#
# Provenance: the origin project's meta-pause-lib.sh (pause_all), its hard
# pause-now script and its graceful retire timer, merged into one tool with the
# difference between them spelled out, because using the hard one for a landing
# was the mistake that made the distinction worth a script.
set -u
. "$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)/lib.sh"

usage() { sed -n '1,20p' "$0" >&2; exit 3; }

ACTION="${1-}"; [ $# -gt 0 ] && shift
REASON=""; WAIT_MIN="${KIT_PAUSE_TRAIN_WAIT_MIN:-30}"; EPOCH=""
while [ $# -gt 0 ]; do
  case "$1" in
    --reason) REASON="${2:?}"; shift 2 ;;
    --wait-minutes) WAIT_MIN="${2:?}"; shift 2 ;;
    --dry-run) KIT_DRY_RUN=1; shift ;;
    -h|--help) usage ;;
    -*) usage ;;
    *) if [ -z "$EPOCH" ]; then EPOCH="$1"; shift; else usage; fi ;;
  esac
done
kit_state_dir
DAEMON_DIR="$KIT_DAEMON_DIR"

landing() { # kills nothing
  local why="${1:-operator asked for a graceful landing}"
  if kit_is_dry; then
    printf 'DRY landing: touch %s and %s; kill nothing\n' "$DAEMON_DIR/stop" "$KIT_STATE_DIR/auto-merge.stop"
    return 0
  fi
  mkdir -p "$DAEMON_DIR" 2>/dev/null || true
  touch "$DAEMON_DIR/stop" "$KIT_STATE_DIR/auto-merge.stop"
  kit_log "GRACEFUL LANDING: $why — the merge queue and the between-turn loop will stop after the job they are running. Nothing was killed; work in flight finishes."
}

hard_pause() {
  local why="${1:-operator asked for a full stop}"
  if [ -e "$KIT_STATE_DIR/paused" ]; then
    kit_log "pause now: already paused ($(head -c 160 "$KIT_STATE_DIR/paused"))"; return 0
  fi
  printf 'This is the HARD pause: a turn in flight is lost. For a landing that kills nothing, use: pause.sh graceful <epoch>\n'
  if kit_is_dry; then
    printf 'DRY hard pause: write %s, caps 0, stop the goal keeper and key watch,\n' "$KIT_STATE_DIR/paused"
    printf 'DRY   touch %s and wait up to %s minutes for a running job,\n' "$DAEMON_DIR/stop" "$WAIT_MIN"
    printf 'DRY   then close the main TUI (/quit, Ctrl-C, signal as the last resort)\n'
    return 0
  fi
  printf '%s %s\n' "$(kit_now)" "$why" > "$KIT_STATE_DIR/paused"
  printf '0\n' > "$KIT_STATE_DIR/max-codex-primary"
  printf '0\n' > "$KIT_STATE_DIR/max-codex-second"
  printf '0\n' > "$KIT_STATE_DIR/max-codex"
  kit_log "PAUSE (hard): $why — worker caps 0"
  kit_daemon_stop goal-keeper >/dev/null 2>&1 || true
  touch "$KIT_STATE_DIR/goal-keeper.stop"     # latched until a resume clears it
  kit_daemon_stop key-watch >/dev/null 2>&1 || true
  touch "$KIT_STATE_DIR/key-watch.stop"
  kit_log "goal keeper and key watch stopped"
  mkdir -p "$DAEMON_DIR" 2>/dev/null || true
  touch "$DAEMON_DIR/stop"
  local p i
  p="$(cat "$DAEMON_DIR/daemon.pid" 2>/dev/null || true)"
  for i in $(seq 1 $(( WAIT_MIN * 6 ))); do
    [ -n "$p" ] && kill -0 "$p" 2>/dev/null || break
    sleep 10
  done
  if [ -n "$p" ] && kill -0 "$p" 2>/dev/null; then
    kit_log "the merge queue (pid $p) is still busy after ${WAIT_MIN} min; left running with its stop file in place"
  else
    kit_log "the merge queue stopped"
  fi
  # the TUI: ask, then interrupt, and only then signal
  if [ -n "$(kit_main_pid)" ]; then
    timeout "${KIT_PAUSE_QUIT_TIMEOUT:-480}" bash "${KIT_SAY:-$KIT_SESSION_DIR/say.sh}" --mode interrupt --grace 240 "/quit" 2>/dev/null | tail -n 1
    for i in $(seq 1 45); do [ -n "$(kit_main_pid)" ] || break; sleep 2; done
  fi
  if [ -n "$(kit_main_pid)" ]; then
    tmux send-keys -t "$KIT_TMUX" C-c; sleep 1; tmux send-keys -t "$KIT_TMUX" C-c
    for i in $(seq 1 15); do [ -n "$(kit_main_pid)" ] || break; sleep 2; done
  fi
  if [ -n "$(kit_main_pid)" ]; then kill -TERM "$(kit_main_pid)" 2>/dev/null; sleep 10; fi
  if [ -n "$(kit_main_pid)" ]; then
    kill -KILL "$(kit_main_pid)" 2>/dev/null; sleep 2
    kit_log "the main TUI had to be killed (it would not quit)"
  else
    kit_log "the main TUI quit"
  fi
  tmux send-keys -t "$KIT_TMUX" C-u 2>/dev/null || true
  kit_issue_comment "**Paused $(date -u +%H:%MZ)** — $why

Stopped: the main session, the goal keeper, the key watch and the merge queue. Nothing restarts by itself; a resume is an explicit step." >/dev/null
  kit_log "PAUSED: $why"
}

case "$ACTION" in
  graceful)
    case "$EPOCH" in ''|*[!0-9]*) printf 'pause.sh graceful needs a unix epoch: pause.sh graceful $(date -d "+2 hours" +%%s)\n' >&2; exit 3 ;; esac
    NOW="$(date +%s)"
    if [ "$EPOCH" -le "$NOW" ]; then
      landing "${REASON:-graceful landing, time already reached}"
    else
      bash "$KIT_SESSION_DIR/timer.sh" "$EPOCH" --name landing --detach -- \
        bash "$KIT_SESSION_DIR/pause.sh" graceful "$NOW" --reason "${REASON:-scheduled graceful landing}"
      if kit_is_dry; then
        printf 'DRY a graceful landing WOULD be armed for epoch %s (%s minutes from now); nothing is armed\n' \
          "$EPOCH" "$(( (EPOCH - NOW) / 60 ))"
      else
        kit_log "graceful landing armed for epoch $EPOCH ($(( (EPOCH - NOW) / 60 )) minutes from now): ${REASON:-scheduled graceful landing}. Nothing will be killed; cancel with: timer.sh stop landing"
      fi
    fi
    ;;
  now) hard_pause "${REASON:-operator asked for a full stop}" ;;
  status)
    printf 'paused:   %s\n' "$([ -e "$KIT_STATE_DIR/paused" ] && head -c 200 "$KIT_STATE_DIR/paused" || echo 'no')"
    printf 'cutoff:   %s\n' "$([ -e "$KIT_STATE_DIR/cutoff" ] && head -c 200 "$KIT_STATE_DIR/cutoff" || echo 'no')"
    printf 'pause-now:%s\n' "$([ -e "$KIT_STATE_DIR/pause-now" ] && head -c 200 "$KIT_STATE_DIR/pause-now" || echo ' no')"
    printf 'landing:  %s\n' "$([ -e "$KIT_STATE_DIR/timer-landing.pid" ] && echo "armed (pid $(cat "$KIT_STATE_DIR/timer-landing.pid"))" || echo 'not armed')"
    ;;
  *) usage ;;
esac
