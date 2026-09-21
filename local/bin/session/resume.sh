#!/usr/bin/env bash
# resume.sh — bring the project back up on a key, in the order that works.
#
# Provenance: the origin project's resume script.  The order is the content:
# probe the key BEFORE anything is started (a main session on a dead key looks
# idle and burns a night), only then clear the stop markers, set the worker
# caps, start the watchers and the merge queue, write down in the handoff what
# the layout now is, and start the main session last.
#
# It does NOT touch $KIT_STATE_DIR/no-default-home: whether a worker may fall back
# to the default CODEX_HOME is a property of the machine's shim installation, and
# local/bin/service/keyrot-install.sh is the one place that decides it (it writes
# the file when the default home is not one of the keys in local/project.json).
# status.sh shows the resulting state.
#
#   resume.sh [--key K] [--lanes N] [--delegates N] [--briefing F] [--goal F]
#             [--reason TEXT] [--default-permissions] [--no-tui] [--dry-run]
#
#   exit 0 up   exit 75 the key did not answer (nothing was started or cleared)
set -u
. "$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)/lib.sh"

KEY="$KIT_MAIN_KEY"; LANES="$KIT_LANES"; DELEGATES="$KIT_MAIN_DELEGATES"
BRIEFING=""; GOAL=""; REASON="the operator resumed the project"; NO_TUI=0; PERMS=()
while [ $# -gt 0 ]; do
  case "$1" in
    --key) KEY="${2:?}"; shift 2 ;;
    --lanes) LANES="${2:?}"; shift 2 ;;
    --delegates) DELEGATES="${2:?}"; shift 2 ;;
    --briefing) BRIEFING="${2:?}"; shift 2 ;;
    --goal) GOAL="${2:?}"; shift 2 ;;
    --reason) REASON="${2:?}"; shift 2 ;;
    --default-permissions) PERMS+=(--default-permissions); shift ;;
    --no-tui) NO_TUI=1; shift ;;
    --dry-run) KIT_DRY_RUN=1; shift ;;
    -h|--help) sed -n '1,20p' "$0" >&2; exit 3 ;;
    *) printf 'resume.sh: unknown argument %s\n' "$1" >&2; exit 3 ;;
  esac
done
kit_state_dir

# --- 1. the probe gate: nothing is touched until the key answers ------------
PROBE_OUT="$(bash "$KIT_SESSION_DIR/probe-key.sh" "$KEY" 2>&1)"; PROBE_RC=$?
printf '%s\n' "$PROBE_OUT" | tail -n 1
if [ "$PROBE_RC" != 0 ]; then
  kit_log "resume: key '$KEY' did not answer (probe-key.sh exit $PROBE_RC) — nothing was started, no marker was cleared"
  exit 75
fi

if kit_is_dry; then
  printf 'DRY resume on key %s: caps %s/0/%s, %s native delegate(s)\n' "$KEY" "$LANES" "$LANES" "$DELEGATES"
  printf 'DRY clear: paused, cutoff, pause-now, key-disabled/main, key-disabled/%s, the stop files\n' "$KEY"
  printf 'DRY start: key-watch.sh, pause-watch.sh, %s\n' "$KIT_REPO_ROOT/local/bin/service/merge-daemon.sh"
  printf 'DRY append a handover section to %s\n' "$KIT_STATE_DIR/handoff.md"
  [ "$NO_TUI" = 1 ] && printf 'DRY --no-tui: the main session is NOT started\n' \
    || printf 'DRY then: main-tui.sh start --key %s --delegates %s\n' "$KEY" "$DELEGATES"
  exit 0
fi

# --- 2. markers and caps ----------------------------------------------------
printf '%s\n' "$KEY" > "$KIT_STATE_DIR/main-key"
rm -f "$KIT_STATE_DIR/paused" "$KIT_STATE_DIR/cutoff" "$KIT_STATE_DIR/pause-now" \
      "$KIT_STATE_DIR/goal-keeper.stop" "$KIT_STATE_DIR/key-watch.stop" \
      "$KIT_STATE_DIR/pause-watch.stop" "$KIT_DAEMON_DIR/stop" "$KIT_STATE_DIR/auto-merge.stop"
# Only the key we just probed is brought back, and only because a human ran
# this command: the key watch never un-retires a key by itself.
for f in "$KIT_STATE_DIR/key-disabled/main" "$KIT_STATE_DIR/key-disabled/$KEY"; do
  [ -e "$f" ] && { kit_log "resume: clearing the retirement of $(basename "$f") — its probe answered HTTP 200"; rm -f "$f"; }
done
printf '%s\n' "$LANES" > "$KIT_STATE_DIR/max-codex-primary"
printf '0\n' > "$KIT_STATE_DIR/max-codex-second"
printf '%s\n' "$LANES" > "$KIT_STATE_DIR/max-codex"
# the main session's key never doubles as a worker-rotation key
if [ -d "$KIT_CACHE_ROOT/keyrot/$KEY" ]; then
  mkdir -p "$KIT_CACHE_ROOT/keyrot-off" 2>/dev/null || true
  mv "$KIT_CACHE_ROOT/keyrot/$KEY" "$KIT_CACHE_ROOT/keyrot-off/$KEY" 2>/dev/null || true
  kit_log "resume: key '$KEY' carries the main session, so it was taken out of the worker rotation"
fi
kit_log "resume: main key '$KEY', worker caps $LANES/0/$LANES, $DELEGATES native delegate(s) — $REASON"

# --- 3. the watchers and the merge queue ------------------------------------
kit_daemon_start key-watch -- bash "$KIT_SESSION_DIR/key-watch.sh" watch
kit_daemon_start pause-watch -- bash "$KIT_SESSION_DIR/pause-watch.sh"
MERGE_DAEMON="$KIT_REPO_ROOT/local/bin/service/merge-daemon.sh"
if [ -x "$MERGE_DAEMON" ] || [ -r "$MERGE_DAEMON" ]; then
  DPID="$(cat "$KIT_DAEMON_DIR/daemon.pid" 2>/dev/null || true)"
  if [ -n "$DPID" ] && kill -0 "$DPID" 2>/dev/null; then
    printf 'merge queue already running (pid %s)\n' "$DPID"
  else
    ( cd "$KIT_REPO_ROOT" && setsid nohup bash "$MERGE_DAEMON" >> "$KIT_STATE_DIR/merge-daemon.log" 2>&1 < /dev/null & )
    sleep 3
    printf 'merge queue started (pid %s)\n' "$(cat "$KIT_DAEMON_DIR/daemon.pid" 2>/dev/null || echo '?')"
  fi
else
  kit_log "resume: $MERGE_DAEMON is not present; the merge queue was not started"
fi

# --- 4. the handoff section -------------------------------------------------
HANDOFF="$KIT_STATE_DIR/handoff.md"
SECTION="$(mktemp "${TMPDIR:-/tmp}/kit-handover.XXXXXX")"
if kit_render "$KIT_REPO_ROOT/local/templates/handover-section.md" "$SECTION" \
     "TIMESTAMP=$(kit_now)" "TITLE=RESUMED on key '$KEY'" "REASON=$REASON" \
     "LAYOUT=main session on key '$KEY' with $DELEGATES native delegate(s); worker caps $LANES/0/$LANES"; then
  printf '\n' >> "$HANDOFF"; cat "$SECTION" >> "$HANDOFF"
  kit_log "resume: a handover section was appended to $HANDOFF (fill it in; it is never committed)"
fi
rm -f "$SECTION"

# --- 5. the main session ----------------------------------------------------
if [ "$NO_TUI" = 1 ]; then
  kit_log "resume: --no-tui, so the main session was not started; run main-tui.sh start when you are ready"
  exit 0
fi
ARGS=(start --key "$KEY" --delegates "$DELEGATES")
[ -n "$BRIEFING" ] && ARGS+=(--briefing "$BRIEFING")
[ -n "$GOAL" ] && ARGS+=(--goal "$GOAL")
exec bash "$KIT_SESSION_DIR/main-tui.sh" "${ARGS[@]}" ${PERMS[@]+"${PERMS[@]}"}
