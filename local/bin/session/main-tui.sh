#!/usr/bin/env bash
# main-tui.sh — start (or relaunch) the project's MAIN codex session in tmux,
# brief it, give it its goal and start the goal keeper.
#
# Provenance: the origin project's meta-start-*-main.sh and its full-access
# relaunch script, generalized.  The order matters and is the lesson of several
# lost hours: probe the key first (a session started on a dead key looks idle),
# never start a second TUI over a running one, quit an old one politely before
# replacing it, and verify that both the briefing and the goal were SUBMITTED —
# a long paste becomes an attachment that one Enter does not always send.
#
#   main-tui.sh start|relaunch [--key K] [--delegates N] [--briefing F]
#                              [--goal F] [--default-permissions]
#                              [--model M] [--effort E] [--sub-effort E] [--dry-run]
#
#   exit 0 up      exit 3 a main TUI is already running (or would not quit)
#   exit 4 the TUI did not come up   exit 6 briefing or goal not confirmed
#   exit 75 the key did not answer HTTP 200
set -u
. "$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)/lib.sh"

# ---------------------------------------------------------------- internal exec
# Invoked inside the tmux pane; keeps every codex flag in one place so the
# command line typed into the pane stays short.
if [ "${1-}" = "__exec" ]; then
  # The KIT_EXEC_* names are deliberately not the configured ones: config.sh is
  # authoritative for those and would overwrite what this launch line chose.
  export PATH="$HOME/.elan/bin:$HOME/.local/bin:$PATH"
  command -v codex >/dev/null 2>&1 || { printf 'main-tui.sh: codex is not on PATH\n' >&2; exit 127; }
  EX_DELEGATES="${KIT_EXEC_DELEGATES:-$KIT_MAIN_DELEGATES}"
  EX_MODEL="${KIT_EXEC_MODEL:-$KIT_MAIN_MODEL}"
  EX_EFFORT="${KIT_EXEC_EFFORT:-$KIT_MAIN_EFFORT}"
  EX_SUB_EFFORT="${KIT_EXEC_SUB_EFFORT:-}"
  ARGS=( -C "$KIT_REPO_ROOT" )
  if [ "${KIT_FULL_ACCESS:-1}" = 1 ]; then
    ARGS+=( --sandbox danger-full-access -c 'approval_policy="never"' )
  fi
  if [ "$EX_DELEGATES" -ge 1 ]; then
    ARGS+=( -c 'features.multi_agent=true' -c 'features.expose_spawn_agent_model_overrides=true'
            -c "agents.max_concurrent_threads_per_session=$EX_DELEGATES" -c 'agents.max_depth=1' )
    [ -n "$EX_SUB_EFFORT" ] && ARGS+=( -c "multi_agent_reasoning_effort=\"$EX_SUB_EFFORT\"" )
  else
    ARGS+=( -c 'features.multi_agent=false' -c 'agents.max_concurrent_threads_per_session=1' )
  fi
  [ -n "$EX_EFFORT" ] && ARGS+=( -c "model_reasoning_effort=\"$EX_EFFORT\"" )
  [ -n "$EX_MODEL" ] && ARGS+=( -m "$EX_MODEL" )
  PROMPT="You are the MAIN SESSION of this project. Read, in order:
local/personas/main.md (your persona), local/README.md, AGENTS.md. The
operator will send a briefing and then invoke /goal; treat both as
authoritative for state and next steps. Your working directory is the
repository root: $KIT_REPO_ROOT — all workflow tools are invoked as
local/bin/<tool> from there."
  cd "$KIT_REPO_ROOT" || exit 1
  exec codex "${ARGS[@]}" "$PROMPT"
fi

# ---------------------------------------------------------------- arguments
ACTION="${1-}"; shift || true
case "$ACTION" in start|relaunch) ;; *) sed -n '1,22p' "$0" >&2; exit 3 ;; esac

KEY="$KIT_MAIN_KEY"; DELEGATES="$KIT_MAIN_DELEGATES"; BRIEFING=""; GOAL=""
FULL_ACCESS=1; SUB_EFFORT="${KIT_MAIN_SUB_EFFORT:-}"
while [ $# -gt 0 ]; do
  case "$1" in
    --key) KEY="${2:?}"; shift 2 ;;
    --delegates) DELEGATES="${2:?}"; shift 2 ;;
    --briefing) BRIEFING="${2:?}"; shift 2 ;;
    --goal) GOAL="${2:?}"; shift 2 ;;
    --model) KIT_MAIN_MODEL="${2:?}"; shift 2 ;;
    --effort) KIT_MAIN_EFFORT="${2:?}"; shift 2 ;;
    --sub-effort) SUB_EFFORT="${2:?}"; shift 2 ;;
    --default-permissions) FULL_ACCESS=0; shift ;;
    --dry-run) KIT_DRY_RUN=1; shift ;;
    -h|--help) sed -n '1,22p' "$0" >&2; exit 3 ;;
    *) printf 'main-tui.sh: unknown argument %s\n' "$1" >&2; exit 3 ;;
  esac
done
kit_state_dir
HOME_DIR="$(kit_key_home "$KEY")"
SAY="${KIT_SAY:-$KIT_SESSION_DIR/say.sh}"

# ---------------------------------------------------------------- 1. probe gate
# A key that does not answer must never carry a main session: the TUI comes up,
# every turn fails, and the session looks idle to everything that watches it.
PROBE_OUT="$(bash "$KIT_SESSION_DIR/probe-key.sh" "$KEY" 2>&1)"; PROBE_RC=$?
printf '%s\n' "$PROBE_OUT" | tail -n 1
if [ "$PROBE_RC" = 0 ]; then
  kit_log "main-tui $ACTION: key '$KEY' answered HTTP 200"
else
  kit_log "main-tui $ACTION: key '$KEY' did NOT answer (probe-key.sh exit $PROBE_RC) — nothing was started"
  exit 75
fi

# ---------------------------------------------------------------- 2. one TUI only
RUNNING="$(kit_main_pid)"
if [ -n "$RUNNING" ]; then
  if [ "$ACTION" != relaunch ]; then
    kit_log "main-tui start: a main TUI is already running (pid $RUNNING); use 'relaunch' to replace it"
    exit 3
  fi
  kit_log "main-tui relaunch: asking the running TUI (pid $RUNNING) to quit"
  if ! kit_is_dry; then
    tmux send-keys -t "$KIT_TMUX" C-u
    tmux send-keys -t "$KIT_TMUX" "/quit" Enter
    for _i in $(seq 1 "${KIT_QUIT_WAIT:-20}"); do [ -z "$(kit_main_pid)" ] && break; sleep 2; done
    if [ -n "$(kit_main_pid)" ]; then   # polite interrupt, still not a kill
      tmux send-keys -t "$KIT_TMUX" C-c; sleep 1; tmux send-keys -t "$KIT_TMUX" C-c
      for _i in $(seq 1 "${KIT_QUIT_WAIT:-15}"); do [ -z "$(kit_main_pid)" ] && break; sleep 2; done
    fi
    if [ -n "$(kit_main_pid)" ]; then
      kit_log "main-tui relaunch: the running TUI would not quit; NOTHING was changed (do not kill it blindly: it may be mid-turn)"
      exit 3
    fi
    sleep 3
  fi
fi
# a keeper of the old session must not re-send a goal into the new one
kit_daemon_stop goal-keeper >/dev/null 2>&1 || true

# ---------------------------------------------------------------- 3. the key home
# codex's own update check steals the first keystrokes of a fresh TUI.
if [ -f "$HOME_DIR/config.toml" ] && ! grep -q '^[[:space:]]*check_for_update_on_startup' "$HOME_DIR/config.toml"; then
  if kit_is_dry; then printf 'DRY set check_for_update_on_startup=false in the key home config.toml\n'
  else sed -i '1i check_for_update_on_startup = false' "$HOME_DIR/config.toml"; fi
fi

# ---------------------------------------------------------------- 4. goal text
if [ -n "$GOAL" ]; then
  [ -r "$GOAL" ] || kit_die "main-tui: cannot read the goal file $GOAL"
  kit_is_dry || cp -f "$GOAL" "$KIT_STATE_DIR/goal-text"
fi
[ -s "$KIT_STATE_DIR/goal-text" ] || kit_log "main-tui $ACTION: WARNING — $KIT_STATE_DIR/goal-text is empty; the session will get no goal"

# ---------------------------------------------------------------- 5. the TUI
LAUNCH="cd $KIT_REPO_ROOT && CODEX_HOME=$HOME_DIR KIT_FULL_ACCESS=$FULL_ACCESS"
LAUNCH="$LAUNCH KIT_EXEC_DELEGATES=$DELEGATES"
[ -n "$KIT_MAIN_MODEL" ] && LAUNCH="$LAUNCH KIT_EXEC_MODEL=$KIT_MAIN_MODEL"
[ -n "$KIT_MAIN_EFFORT" ] && LAUNCH="$LAUNCH KIT_EXEC_EFFORT=$KIT_MAIN_EFFORT"
[ -n "$SUB_EFFORT" ] && LAUNCH="$LAUNCH KIT_EXEC_SUB_EFFORT=$SUB_EFFORT"
LAUNCH="$LAUNCH bash local/bin/session/main-tui.sh __exec"

if kit_is_dry; then
  printf 'DRY tmux session: %s (window size %sx%s, cwd %s)\n' "$KIT_TMUX" "${KIT_TMUX_WIDTH:-220}" "${KIT_TMUX_HEIGHT:-50}" "$KIT_REPO_ROOT"
  printf 'DRY launch command: %s\n' "$LAUNCH"
  printf 'DRY permissions: %s\n' "$([ "$FULL_ACCESS" = 1 ] && echo 'full access (--sandbox danger-full-access, approval_policy=never)' || echo 'codex defaults (the owner grants full access in the TUI)')"
  printf 'DRY delegates: %s%s\n' "$DELEGATES" "$([ "$DELEGATES" -ge 1 ] && echo '' || echo ' (multi_agent off)')"
  printf 'DRY briefing: %s\n' "${BRIEFING:-<none>}"
  printf 'DRY goal: %s\n' "$KIT_STATE_DIR/goal-text"
  printf 'DRY then: start the goal keeper\n'
  exit 0
fi

tmux has-session -t "$KIT_TMUX" 2>/dev/null \
  || tmux new-session -d -s "$KIT_TMUX" -x "${KIT_TMUX_WIDTH:-220}" -y "${KIT_TMUX_HEIGHT:-50}" -c "$KIT_REPO_ROOT"
tmux send-keys -t "$KIT_TMUX" C-u
tmux send-keys -t "$KIT_TMUX" "$LAUNCH" Enter
for _i in $(seq 1 "${KIT_TUI_WAIT:-120}"); do
  kit_pane | grep -q -F "$KIT_COMPOSER_PLACEHOLDER" && break
  sleep 2
done
sleep 8
PID="$(kit_main_pid)"
[ -n "$PID" ] || { kit_log "main-tui $ACTION: the TUI did not start"; kit_pane_tail 6 | cut -c1-170; exit 4; }
kit_log "main-tui $ACTION: TUI up (pid $PID) on key '$KEY', $([ "$FULL_ACCESS" = 1 ] && echo 'full access' || echo 'codex default permissions'), $DELEGATES native delegate(s)"

# ---------------------------------------------------------------- 6. brief + goal
RC=0
send_and_verify() { # file, label
  local f="$1" label="$2" out rc=0
  out="$(bash "$SAY" --mode idle --timeout "${KIT_SAY_TIMEOUT:-900}" --file "$f")" || rc=$?
  printf '%s: %s\n' "$label" "$out"
  if [ "$rc" != 0 ]; then
    kit_log "main-tui $ACTION: the $label was NOT confirmed submitted ($out) — look at the pane"
    return 6
  fi
  return 0
}
if [ -n "$BRIEFING" ]; then
  [ -r "$BRIEFING" ] || kit_die "main-tui: cannot read the briefing file $BRIEFING"
  send_and_verify "$BRIEFING" briefing || RC=6
  for _i in $(seq 1 90); do kit_busy || break; sleep 10; done
  sleep 3
fi
if [ -s "$KIT_STATE_DIR/goal-text" ]; then
  send_and_verify "$KIT_STATE_DIR/goal-text" goal || RC=6
fi

# ---------------------------------------------------------------- 7. the keeper
kit_daemon_start goal-keeper -- bash "$KIT_SESSION_DIR/goal-keeper.sh"
kit_log "main-tui $ACTION: briefed, goal sent, goal keeper running"
kit_pane_tail 5 | cut -c1-170
exit "$RC"
