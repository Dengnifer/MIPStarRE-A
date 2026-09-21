#!/usr/bin/env bash
# status.sh — one screen: what is running, which key, which caps, which goal,
# what stopped it, and the last few things that happened.
#
# Provenance: the questions the origin project's operator had to answer by hand
# from six different files every time it came back to the machine.
#
#   status.sh [--events N]
set -u
. "$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)/lib.sh"

EVENTS="${1:-}"; [ "$EVENTS" = "--events" ] && EVENTS="${2:-10}" || EVENTS=10
W="$KIT_STATE_DIR"

read_or() { [ -s "$W/$1" ] && head -c "${2:-120}" "$W/$1" | tr '\n' ' ' || printf '%s' "${3:-—}"; }
alive() { local p; p="$(cat "$W/$1.pid" 2>/dev/null || true)"
  if [ -n "$p" ] && kill -0 "$p" 2>/dev/null; then printf 'running (pid %s)' "$p"; else printf 'not running'; fi; }

printf 'project      %s   track %s   repo %s\n' "$KIT_NAME" "$KIT_TRACK" "$KIT_REPO_ROOT"
printf 'github       %s   progress issue %s\n' "$KIT_GITHUB_SLUG" "${KIT_PROGRESS_ISSUE:-none}"
printf 'state dir    %s\n' "$W"
printf '\n'

MPID="$(kit_main_pid)"
printf 'main session %s (tmux session "%s")\n' "$([ -n "$MPID" ] && printf 'running (pid %s)' "$MPID" || printf 'NOT running')" "$KIT_TMUX"
printf 'key          %s   caps primary %s / second %s / total %s\n' \
  "$(read_or main-key 40 "$KIT_MAIN_KEY")" "$(read_or max-codex-primary 8 0)" \
  "$(read_or max-codex-second 8 0)" "$(read_or max-codex 8 0)"
printf 'goal keeper  %s   turn limit %s min\n' "$(alive goal-keeper)" "$(read_or turn-max 8 "$KIT_TURN_MAX")"
printf 'key watch    %s\n' "$(alive key-watch)"
printf 'pause watch  %s\n' "$(alive pause-watch)"
DPID="$(cat "$KIT_DAEMON_DIR/daemon.pid" 2>/dev/null || true)"
printf 'merge queue  %s%s\n' \
  "$([ -n "$DPID" ] && kill -0 "$DPID" 2>/dev/null && printf 'running (pid %s)' "$DPID" || printf 'not running')" \
  "$([ -e "$KIT_DAEMON_DIR/stop" ] && printf '  [stop file present]' || printf '')"
# The shim's fallback guard (written by local/bin/service/keyrot-install.sh, never here):
# with it on, a worker that finds no free rotation slot refuses to start on ~/.codex.
printf 'default home %s\n' \
  "$([ -e "$W/no-default-home" ] && printf 'REFUSED as a fallback (no-default-home: %s)' "$(head -c 130 "$W/no-default-home" | tr '\n' ' ')" || printf 'usable as a fallback')"
printf 'worker models%s\n' \
  "$([ -s "$W/models-allowed" ] && printf ' %s' "$(tr '\n' ' ' < "$W/models-allowed")" || printf ' any (no allowlist)')"
printf '\n'

printf 'paused       %s\n' "$(read_or paused 160 no)"
printf 'cutoff       %s\n' "$(read_or cutoff 160 no)"
printf 'pause-now    %s\n' "$(read_or pause-now 160 no)"
if [ -n "$(ls -A "$W/key-disabled" 2>/dev/null || true)" ]; then
  printf 'retired keys\n'
  for f in "$W/key-disabled"/*; do [ -e "$f" ] || continue; printf '  %-12s %s\n' "$(basename "$f")" "$(head -c 130 "$f" | tr '\n' ' ')"; done
else
  printf 'retired keys none\n'
fi
printf '\n'

if [ -s "$W/goal-text" ]; then
  printf 'goal (%s bytes, first line)\n  %s\n' "$(wc -c < "$W/goal-text" | tr -d ' ')" "$(head -n 1 "$W/goal-text" | cut -c1-150)"
else
  printf 'goal         none set (%s is empty)\n' "$W/goal-text"
fi
printf 'handoff      %s\n' "$([ -s "$W/handoff.md" ] && printf '%s (%s lines)' "$W/handoff.md" "$(wc -l < "$W/handoff.md" | tr -d ' ')" || printf 'none')"
printf '\n'

printf 'last %s events\n' "$EVENTS"
if [ -s "$W/events-meta.log" ]; then tail -n "$EVENTS" "$W/events-meta.log" | cut -c1-170 | sed 's/^/  /'
else printf '  (none)\n'; fi

if [ -n "$MPID" ]; then
  printf '\nlast pane lines\n'
  kit_pane_tail 4 | cut -c1-170 | sed 's/^/  /'
fi
