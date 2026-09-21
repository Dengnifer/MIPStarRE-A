#!/usr/bin/env bash
# timer.sh — run one command at a wall-clock time, on this host.
#
# Provenance: the origin project's host-side resume and retire timers.  The lesson
# they exist for: timers and one-shot jobs scheduled inside a chat session did
# not fire, while a plain detached loop with a pid file and a stop file on the
# host always did.  Anything that must happen at a time uses this.
#
#   timer.sh <epoch> -- <command...>   [--name N] [--detach] [--poll S]
#   timer.sh list                      the timers that exist
#   timer.sh stop <name>               cancel one (the command never runs)
#
# A time in the past runs the command immediately.
set -u
. "$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)/lib.sh"

usage() { sed -n '1,17p' "$0" >&2; exit 3; }

case "${1-}" in
  list)
    kit_state_dir
    found=0
    for f in "$KIT_STATE_DIR"/timer-*.pid; do
      [ -e "$f" ] || continue
      n="$(basename "$f" .pid)"; n="${n#timer-}"; p="$(cat "$f" 2>/dev/null || true)"
      printf '%-24s pid %-8s %s  %s\n' "$n" "${p:-?}" \
        "$(kill -0 "${p:-0}" 2>/dev/null && echo running || echo gone)" \
        "$(head -n 1 "$KIT_STATE_DIR/timer-$n.log" 2>/dev/null | cut -c1-90)"
      found=1
    done
    [ "$found" = 0 ] && printf 'no timers\n'
    exit 0 ;;
  stop)
    NAME="${2:?usage: timer.sh stop <name>}"
    kit_state_dir
    touch "$KIT_STATE_DIR/timer-$NAME.stop"
    p="$(cat "$KIT_STATE_DIR/timer-$NAME.pid" 2>/dev/null || true)"
    [ -n "$p" ] && kill "$p" 2>/dev/null
    printf 'timer %s cancelled\n' "$NAME"
    exit 0 ;;
esac

END=""; NAME=""; DETACH=0; POLL="${KIT_TIMER_POLL:-20}"; CMD=()
while [ $# -gt 0 ]; do
  case "$1" in
    --name) NAME="${2:?}"; shift 2 ;;
    --detach) DETACH=1; shift ;;
    --poll) POLL="${2:?}"; shift 2 ;;
    --dry-run) KIT_DRY_RUN=1; shift ;;
    -h|--help) usage ;;
    --) shift; CMD=("$@"); break ;;
    *) if [ -z "$END" ]; then END="$1"; shift; else usage; fi ;;
  esac
done
case "$END" in ''|*[!0-9]*) usage ;; esac
[ "${#CMD[@]}" -gt 0 ] || usage
[ -n "$NAME" ] || NAME="at-$END"

kit_state_dir
PIDF="$KIT_STATE_DIR/timer-$NAME.pid"
STOPF="$KIT_STATE_DIR/timer-$NAME.stop"
LOGF="$KIT_STATE_DIR/timer-$NAME.log"

if kit_is_dry; then
  printf 'DRY timer %s: at %s (%s, in %ss) run: %s\n' "$NAME" "$END" \
    "$(date -u -d "@$END" +%FT%TZ 2>/dev/null || date -u -r "$END" +%FT%TZ 2>/dev/null || echo '?')" \
    "$(( END - $(date +%s) ))" "${CMD[*]}"
  exit 0
fi

if [ "$DETACH" = 1 ]; then
  rm -f "$STOPF"
  setsid nohup "$0" "$END" --name "$NAME" --poll "$POLL" -- "${CMD[@]}" >> "$LOGF" 2>&1 < /dev/null &
  sleep 1
  printf 'timer %s armed (pid %s); cancel with: timer.sh stop %s\n' "$NAME" "$(cat "$PIDF" 2>/dev/null || echo '?')" "$NAME"
  exit 0
fi

rm -f "$STOPF"
echo $$ > "$PIDF"
printf '%s timer %s armed for epoch %s: %s\n' "$(kit_now)" "$NAME" "$END" "${CMD[*]}" >> "$LOGF"
while [ "$(date +%s)" -lt "$END" ]; do
  [ -e "$STOPF" ] && { printf '%s timer %s cancelled\n' "$(kit_now)" "$NAME" >> "$LOGF"; exit 0; }
  sleep "$POLL"
done
[ -e "$STOPF" ] && { printf '%s timer %s cancelled\n' "$(kit_now)" "$NAME" >> "$LOGF"; exit 0; }
kit_log "timer $NAME fired: ${CMD[*]}"
rc=0; "${CMD[@]}" >> "$LOGF" 2>&1 || rc=$?
kit_log "timer $NAME: the command exited $rc"
exit "$rc"
