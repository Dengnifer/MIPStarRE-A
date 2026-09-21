#!/usr/bin/env bash
# standdown.sh — hand the main session over without interrupting it.
#
# Provenance: the origin project's graceful stand-down script and its message.
# Nothing is killed and no turn is cut short: the goal keeper is stopped so no
# goal is re-sent, the stand-down text is QUEUED (paste + Tab) so it arrives at
# the end of the turn that is running, and the session is closed only after it
# has written its done marker and gone idle.
#
#   standdown.sh [--minutes N] [--reason TEXT] [--next-layout TEXT]
#                [--message FILE] [--dry-run]
#
#   exit 0 the session stood down and the TUI is closed
#   exit 4 the text could not be queued      exit 5 no done marker in time
set -u
. "$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)/lib.sh"

MINUTES="${KIT_STANDDOWN_MINUTES:-45}"
REASON="the operator is handing this project to a new main session"
NEXT_LAYOUT="a new main session starts right after this one is closed"
MESSAGE=""
while [ $# -gt 0 ]; do
  case "$1" in
    --minutes) MINUTES="${2:?}"; shift 2 ;;
    --reason) REASON="${2:?}"; shift 2 ;;
    --next-layout) NEXT_LAYOUT="${2:?}"; shift 2 ;;
    --message) MESSAGE="${2:?}"; shift 2 ;;
    --dry-run) KIT_DRY_RUN=1; shift ;;
    -h|--help) sed -n '1,15p' "$0" >&2; exit 3 ;;
    *) printf 'standdown.sh: unknown argument %s\n' "$1" >&2; exit 3 ;;
  esac
done
kit_state_dir

DONE_MARKER="$KIT_STATE_DIR/main-standdown.done"
HANDOFF="$KIT_STATE_DIR/handoff.md"
TEMPLATE="${KIT_STANDDOWN_TEMPLATE:-$KIT_REPO_ROOT/local/templates/standdown.md}"
HANDOVER_TEMPLATE="$KIT_REPO_ROOT/local/templates/handover-section.md"
if [ -n "$KIT_PROGRESS_ISSUE" ]; then
  PROGRESS_NOTE="Post one comment on the progress issue ($KIT_GITHUB_SLUG#$KIT_PROGRESS_ISSUE): that the main session is handing over, and the one sentence a reader needs to know where the work stands."
else
  PROGRESS_NOTE="No progress issue is configured for this project, so there is nothing to post; skip this step."
fi

RENDERED=""
if [ -n "$MESSAGE" ]; then
  [ -r "$MESSAGE" ] || kit_die "standdown.sh: cannot read $MESSAGE"
  RENDERED="$MESSAGE"
else
  RENDERED="$(mktemp "${TMPDIR:-/tmp}/kit-standdown.XXXXXX")"
  trap 'rm -f "$RENDERED"' EXIT
  kit_render "$TEMPLATE" "$RENDERED" \
    "REASON=$REASON" "NEXT_LAYOUT=$NEXT_LAYOUT" "DEADLINE_MIN=$MINUTES" \
    "DONE_MARKER=$DONE_MARKER" "HANDOFF_FILE=$HANDOFF" \
    "HANDOVER_TEMPLATE=$HANDOVER_TEMPLATE" "PROGRESS_NOTE=$PROGRESS_NOTE" \
    "RECORDS_CMD=${KIT_RECORDS_CMD:-local/bin/service/records.sh}" \
    || kit_die "standdown.sh: could not render $TEMPLATE"
fi

if kit_is_dry; then
  printf 'DRY stand-down: queue this text for the main session, wait up to %s minutes for %s, then /quit the idle TUI\n' "$MINUTES" "$DONE_MARKER"
  printf -- '--- message ---\n'
  cat "$RENDERED"
  printf -- '--- end ---\n'
  exit 0
fi

kit_daemon_stop goal-keeper >/dev/null 2>&1 || true
touch "$KIT_STATE_DIR/goal-keeper.stop"   # latched: no goal is re-sent into a session that is standing down
rm -f "$DONE_MARKER"

if [ -z "$(kit_main_pid)" ]; then
  kit_log "stand-down: no main TUI is running; nothing to hand over"
  exit 0
fi
kit_log "STAND-DOWN: $REASON — the goal keeper is stopped and the stand-down text is being queued"

RC=0
bash "${KIT_SAY:-$KIT_SESSION_DIR/say.sh}" --mode queue --file "$RENDERED" || RC=$?
if [ "$RC" != 0 ]; then
  kit_log "stand-down: the text could not be delivered (say.sh exit $RC); the session was NOT closed"
  exit 4
fi

for _i in $(seq 1 $(( MINUTES * 6 ))); do
  [ -e "$DONE_MARKER" ] && break
  [ -z "$(kit_main_pid)" ] && break
  sleep 10
done
if [ ! -e "$DONE_MARKER" ]; then
  kit_log "stand-down: no done marker after ${MINUTES} minutes (or the TUI is gone); NOT closing the session — look at the pane"
  exit 5
fi
kit_log "stand-down: the main session reported done"

# let the turn that wrote the marker end, then close the idle session
for _i in $(seq 1 60); do kit_busy || break; sleep 5; done
tmux send-keys -t "$KIT_TMUX" C-u
tmux send-keys -t "$KIT_TMUX" "/quit" Enter; sleep 3
[ -n "$(kit_main_pid)" ] && tmux send-keys -t "$KIT_TMUX" Enter
for _i in $(seq 1 30); do [ -z "$(kit_main_pid)" ] && break; sleep 2; done
if [ -z "$(kit_main_pid)" ]; then
  kit_log "stand-down complete: the main TUI is closed. Nothing was killed."
  exit 0
fi
kit_log "stand-down: the main session reported done but its TUI is still running; it was left alone (do not kill it blindly)"
exit 5
