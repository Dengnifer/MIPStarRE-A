#!/usr/bin/env bash
# owner-say.sh — deliver ONE message to the main codex session in tmux (design §2 Item 7).
# The single tool that replaces the /tmp v3 (escape-and-resume) / v4 (wait-for-idle) fork.
#
# Usage: owner-say.sh --mode idle|interrupt|terminal [--timeout N] [--dry-run] TEXT
#
#   idle       wait up to --timeout (default 1800 s) for the session to go idle, then send.
#              Never interrupts a turn.  Exit 1 if it never goes idle.
#   interrupt  wait up to --timeout (default 120 s) for idle; otherwise press Escape, wait
#              for idle, send, and then "/goal resume".  For nudges that must not wait for
#              a long turn to end.
#   terminal   the closing order.  Write watchdog/goal-hold FIRST, then Escape if needed,
#              send, and do NOT resume.  On 2026-09-12 the terminal stop order went out at
#              08:19Z and the same script resumed the goal at 08:24Z; goal-hold is what
#              stops goal-keeper.sh from doing that.
#
# THE IDLE RULE (v4, kept verbatim): idleness is judged on the LAST FOUR non-empty lines of
# the pane only.  v2 scanned the whole pane and a stale "esc to interrupt" line in the
# scrollback kept it waiting for 20 minutes (2026-09-12 04:01Z-04:21Z).
#
# Environment: MIPSTARRE_TMUX_SESSION (default qpbt), MIPSTARRE_REPO_ROOT,
#              MIPSTARRE_CACHE_ROOT.
# Exit codes: 0 sent · 1 not idle / not sent · 2 usage · 3 no tmux session
set -u

PROG="owner-say.sh"
CACHE_ROOT="${MIPSTARRE_CACHE_ROOT:-$HOME/.cache/mipstarre-dev}"
W="$CACHE_ROOT/watchdog"
OWNER_BIN="${MIPSTARRE_OWNER_BIN:-$CACHE_ROOT/owner-bin}"
S="${MIPSTARRE_TMUX_SESSION:-qpbt}"

MODE=""; TIMEOUT=""; DRY=0; TEXT=""
while [ "$#" -gt 0 ]; do
  case "$1" in
    --mode) MODE="${2:-}"; shift ;;
    --mode=*) MODE="${1#--mode=}" ;;
    --timeout) TIMEOUT="${2:-}"; shift ;;
    --timeout=*) TIMEOUT="${1#--timeout=}" ;;
    --dry-run) DRY=1 ;;
    -h|--help) sed -n '2,25p' "$0" | sed 's/^# \{0,1\}//'; exit 0 ;;
    --) shift; TEXT="${1:-}"; break ;;
    -*) echo "$PROG: unknown option '$1'" >&2; exit 2 ;;
    *) TEXT="$1" ;;
  esac
  shift
done

case "$MODE" in
  idle|interrupt|terminal) ;;
  *) echo "$PROG: --mode must be idle, interrupt or terminal" >&2; exit 2 ;;
esac
[ -n "$TEXT" ] || { echo "$PROG: no message text" >&2; exit 2; }
case "$TEXT" in
  *$'\n'*) echo "$PROG: the message must be a single line (tmux send-keys submits on newline)" >&2; exit 2 ;;
esac
if [ -z "$TIMEOUT" ]; then
  case "$MODE" in idle) TIMEOUT=1800 ;; *) TIMEOUT=120 ;; esac
fi
case "$TIMEOUT" in ''|*[!0-9]*) echo "$PROG: --timeout must be a whole number of seconds" >&2; exit 2 ;; esac

ROOT="${MIPSTARRE_REPO_ROOT:-}"
if [ -z "$ROOT" ] && [ -r "$OWNER_BIN/repo-root" ]; then ROOT="$(cat "$OWNER_BIN/repo-root")"; fi
if [ -z "$ROOT" ]; then ROOT="$HOME/MIPStarRE-qpbt"; fi
# the pane's status line shows the session's directory as "~/<name>"
PANE_DIR=" · ${ROOT/#$HOME/\~}"

VERSION="$(sed -n 's/^short=//p' "$OWNER_BIN/tools-version" 2>/dev/null | head -n 1)"
echo "tool=$PROG version=${VERSION:-unreleased}"

tail4() { tmux capture-pane -p -t "$S" 2>/dev/null | grep -v '^[[:space:]]*$' | tail -n 4; }
idle() {
  local p; p="$(tail4)"
  printf '%s\n' "$p" | grep -qF "$PANE_DIR" || return 1
  printf '%s\n' "$p" | grep -q -E "esc to interrupt|Working \(" && return 1
  return 0
}
send_line() { tmux send-keys -t "$S" -l "$1"; sleep 1; tmux send-keys -t "$S" Enter; }

if [ "$DRY" -eq 1 ]; then
  echo "$PROG: [dry-run] mode=$MODE timeout=${TIMEOUT}s session=$S hold=$([ "$MODE" = terminal ] && echo yes || echo no)"
  echo "$PROG: [dry-run] would send: $TEXT"
  exit 0
fi

tmux has-session -t "$S" 2>/dev/null || { echo "$PROG: no tmux session '$S'" >&2; exit 3; }

# terminal: the hold goes down BEFORE the message, so the keeper cannot win a race with it.
if [ "$MODE" = terminal ]; then
  mkdir -p "$W"
  printf '%s owner-say --mode terminal\n' "$(date -u +%FT%TZ)" > "$W/goal-hold"
  echo "$PROG: watchdog/goal-hold written; goal-keeper.sh will not resume the goal"
fi

t=0
until idle; do
  sleep 5; t=$((t + 5))
  [ "$t" -ge "$TIMEOUT" ] && break
done

INTERRUPTED=0
if ! idle; then
  if [ "$MODE" = idle ]; then
    echo "$PROG: not idle after ${TIMEOUT}s; not sent" >&2; exit 1
  fi
  tmux send-keys -t "$S" Escape; INTERRUPTED=1
  u=0
  until idle; do
    sleep 5; u=$((u + 5))
    if [ "$u" -ge 400 ]; then echo "$PROG: not idle 400 s after Escape; not sent" >&2; exit 1; fi
  done
fi

# a half-typed composer swallows the message; submit whatever is in it first
if ! tail4 | grep -q "Ask Codex to do anything"; then
  tmux send-keys -t "$S" Enter; sleep 8
  u=0
  until idle; do
    sleep 5; u=$((u + 5))
    if [ "$u" -ge 180 ]; then echo "$PROG: composer submitted but not idle again; not sent" >&2; exit 1; fi
  done
fi

send_line "$TEXT"; sleep 2
echo "$PROG: sent at $(date -u +%H:%MZ) after ${t}s (mode=$MODE interrupted=$INTERRUPTED)"

if [ "$MODE" = interrupt ] && [ "$INTERRUPTED" = 1 ]; then
  u=0
  until idle; do
    sleep 5; u=$((u + 5))
    [ "$u" -ge 900 ] && break
  done
  send_line "/goal resume"
  echo "$PROG: goal resumed at $(date -u +%H:%MZ)"
fi
exit 0
