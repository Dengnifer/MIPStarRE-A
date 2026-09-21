#!/usr/bin/env bash
# say.sh — deliver one message to the main session's TUI in tmux, in one of the
# three ways that work: when it is idle, by interrupting it, or by queueing the
# text for the end of the running turn.
#
# Provenance: the origin project's owner-say.sh (idle), owner-say-v3.sh
# (Escape + /goal resume) and the paste/Tab queueing of its stand-down script,
# merged into one tool.  Long texts always go through a tmux buffer, because a
# long paste becomes an attachment ("Pasted Content") that one Enter does not
# always submit; that is why Enter is pressed again while the attachment is
# still visible.
#
#   say.sh --mode idle|interrupt|queue (--file F | TEXT) [--timeout S] [--grace S]
#
#   exit 0  delivered          exit 4  could not confirm the text was queued
#   exit 1  never went idle    exit 6  sent, but an attachment is still in the composer
set -u
. "$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)/lib.sh"

usage() { cat >&2 <<'EOF'
usage: say.sh --mode idle|interrupt|queue (--file FILE | TEXT) [options]
  --mode idle        wait until the session is idle, then paste and submit
  --mode interrupt   Escape a running turn first, then as idle, then "/goal resume"
  --mode queue       paste and press Tab; the text lands at the end of the turn
  --file FILE        read the message from FILE (always used for long texts)
  --timeout S        how long to wait for an idle session (default 1800)
  --grace S          --mode interrupt: wait this long for a natural idle (default 120)
  --dry-run          print what would be sent; touch no tmux session
EOF
exit 3; }

MODE=""; FILE=""; TEXT=""; TIMEOUT=1800; GRACE=120
while [ $# -gt 0 ]; do
  case "$1" in
    --mode) MODE="${2:?}"; shift 2 ;;
    --file) FILE="${2:?}"; shift 2 ;;
    --timeout) TIMEOUT="${2:?}"; shift 2 ;;
    --grace) GRACE="${2:?}"; shift 2 ;;
    --dry-run) KIT_DRY_RUN=1; shift ;;
    -h|--help) usage ;;
    --) shift; TEXT="${1-}"; shift || true ;;
    -*) usage ;;
    *) TEXT="$1"; shift ;;
  esac
done
case "$MODE" in idle|interrupt|queue) ;; *) usage ;; esac
[ -n "$FILE" ] || [ -n "$TEXT" ] || usage
[ -z "$FILE" ] || [ -r "$FILE" ] || kit_die "say.sh: cannot read $FILE"

# Long or multi-line text is pasted from a file through a tmux buffer; a short
# one-liner (a slash command, a nudge) is typed directly.
TMPFILE=""
cleanup() { [ -n "$TMPFILE" ] && rm -f "$TMPFILE"; }
trap cleanup EXIT
USE_BUFFER=0
if [ -n "$FILE" ]; then
  USE_BUFFER=1
else
  case "$TEXT" in *$'\n'*) USE_BUFFER=1 ;; esac
  [ "${#TEXT}" -gt 200 ] && USE_BUFFER=1
  if [ "$USE_BUFFER" = 1 ]; then
    TMPFILE="$(mktemp "${TMPDIR:-/tmp}/kit-say.XXXXXX")"
    printf '%s' "$TEXT" > "$TMPFILE"; FILE="$TMPFILE"
  fi
fi

DESC="${FILE:-$(printf '%s' "$TEXT" | head -c 60)}"

if kit_is_dry; then
  printf 'DRY say --mode %s to tmux session %s: %s\n' "$MODE" "$KIT_TMUX" "$DESC"
  [ -n "$FILE" ] && printf 'DRY first line: %s\n' "$(head -n 1 "$FILE" | cut -c1-120)"
  exit 0
fi

paste_it() {
  if [ "$USE_BUFFER" = 1 ]; then
    tmux load-buffer -b kitsay "$FILE"
    tmux paste-buffer -b kitsay -t "$KIT_TMUX"
  else
    tmux send-keys -t "$KIT_TMUX" -l "$TEXT"
  fi
  sleep 2
}

attachment_visible() { kit_pane_tail 6 | grep -q "Pasted Content"; }

submit_it() { # Enter, then Enter again while the attachment is still in the composer
  local i
  tmux send-keys -t "$KIT_TMUX" Enter; sleep "${KIT_SAY_SETTLE:-6}"
  for i in 1 2 3; do
    kit_busy && return 0
    attachment_visible || return 0
    tmux send-keys -t "$KIT_TMUX" Enter; sleep "${KIT_SAY_SETTLE:-6}"
  done
  kit_busy && return 0
  attachment_visible && return 6
  return 0
}

clear_prefilled_composer() { # something was typed but never submitted: send it first
  kit_pane_tail 4 | grep -q -F "$KIT_COMPOSER_PLACEHOLDER" && return 0
  tmux send-keys -t "$KIT_TMUX" Enter; sleep 8
  kit_wait_idle "$TIMEOUT" || return 1
  return 0
}

INTERRUPTED=0
case "$MODE" in
  idle)
    kit_wait_idle "$TIMEOUT" 10 || { echo "not idle after ${TIMEOUT}s; nothing sent"; exit 1; }
    clear_prefilled_composer || { echo "composer submitted but the session did not go idle again; nothing sent"; exit 1; }
    ;;
  interrupt)
    if ! kit_wait_idle "$GRACE" 5; then
      tmux send-keys -t "$KIT_TMUX" Escape; INTERRUPTED=1
      kit_wait_idle "${KIT_SAY_AFTER_ESCAPE:-400}" 5 || { echo "not idle after Escape; nothing sent"; exit 1; }
    fi
    clear_prefilled_composer || { echo "composer submitted but the session did not go idle again; nothing sent"; exit 1; }
    ;;
  queue)
    : # queueing needs no idle session; that is the point of it
    ;;
esac

paste_it

if [ "$MODE" = queue ]; then
  if ! kit_busy; then
    # nothing is running, so there is nothing to queue behind: submit it
    rc=0; submit_it || rc=$?
    echo "submitted at $(date -u +%H:%MZ) (the session was idle, nothing to queue behind)"
    exit "$rc"
  fi
  for i in 1 2 3; do
    tmux send-keys -t "$KIT_TMUX" Tab; sleep "${KIT_SAY_TAB_SETTLE:-3}"
    if kit_pane_tail 8 | grep -q -F "${KIT_QUEUE_MARK:-Queued follow-up inputs}"; then
      echo "queued at $(date -u +%H:%MZ) (delivered at the end of the running turn)"
      exit 0
    fi
  done
  echo "pressed Tab three times but '${KIT_QUEUE_MARK:-Queued follow-up inputs}' never appeared; check the composer"
  exit 4
fi

rc=0; submit_it || rc=$?
if [ "$rc" = 6 ]; then
  echo "sent at $(date -u +%H:%MZ) but an attachment is still in the composer; press Enter in the pane"
else
  echo "sent at $(date -u +%H:%MZ) (interrupted=$INTERRUPTED)"
fi

if [ "$INTERRUPTED" = 1 ] && [ "$rc" != 6 ]; then
  kit_wait_idle "${KIT_SAY_RESUME_WAIT:-900}" 5 || true
  tmux send-keys -t "$KIT_TMUX" -l "/goal resume"; sleep 1
  tmux send-keys -t "$KIT_TMUX" Enter
  echo "goal resumed at $(date -u +%H:%MZ)"
fi
exit "$rc"
