#!/usr/bin/env bash
# goal-keeper.sh — keep the main session's goal loop running, its turns short, and its
# inbox drained (design §2 Items 2 and 7).  Runs as a host loop with a 2-minute tick.
#
# Every tick:
#   (a) "Goal stalled" / "Goal paused" in the last four non-empty lines -> "/goal resume"
#   (b) idle with no goal at all -> set the cycle goal, rendered from run_mode.py
#   (c) a turn running longer than TURN_MAX minutes -> one Escape (codex keeps its work and
#       the queued owner messages land), at most once per 10 minutes
#   (d) drain watchdog/main-inbox/: every file in it is delivered with owner-say.sh in
#       --mode interrupt, so a dispatch nudge never waits for a 25-minute turn to end
#
# It does NOTHING while watchdog/goal-hold exists.  That file is written by
# `owner-say.sh --mode terminal` and removed by owner-resume.sh: on 2026-09-12 the owner's
# terminal stop order at 08:19Z was undone by an automatic goal resume at 08:24Z.
#
# Nothing in this file names a cap, an issue number or a turn limit: the goal text comes
# from `run_mode.py show --oneline` and TURN_MAX from `run_mode.py get turn_max_min`, so the
# keeper can no longer repeat a stale "primary 0, second 22, total 22" for hours.
#
# Stop with: touch ~/.cache/mipstarre-dev/watchdog/goal-keeper.stop
# Inbox file format: the message, one line.  An optional first line "#mode: idle|interrupt|
# terminal" chooses the delivery mode (default interrupt).  Delivered files move to
# main-inbox/sent/.
set -u

PROG="goal-keeper.sh"
CACHE_ROOT="${MIPSTARRE_CACHE_ROOT:-$HOME/.cache/mipstarre-dev}"
W="$CACHE_ROOT/watchdog"
OWNER_BIN="${MIPSTARRE_OWNER_BIN:-$CACHE_ROOT/owner-bin}"
S="${MIPSTARRE_TMUX_SESSION:-qpbt}"
LOG="${MIPSTARRE_KEEPER_LOG:-$W/goal-keeper.log}"
INBOX="$W/main-inbox"
TICK="${MIPSTARRE_KEEPER_TICK:-120}"
ONCE=0
[ "${1:-}" = "--once" ] && ONCE=1

ROOT="${MIPSTARRE_REPO_ROOT:-}"
if [ -z "$ROOT" ] && [ -r "$OWNER_BIN/repo-root" ]; then ROOT="$(cat "$OWNER_BIN/repo-root")"; fi
if [ -z "$ROOT" ]; then ROOT="$HOME/MIPStarRE-qpbt"; fi
RUN_MODE="${MIPSTARRE_RUN_MODE:-$ROOT/local/bin/run_mode.py}"
SAY="${MIPSTARRE_OWNER_SAY:-$OWNER_BIN/owner-say.sh}"
PANE_DIR=" · ${ROOT/#$HOME/\~}"

VERSION="$(sed -n 's/^short=//p' "$OWNER_BIN/tools-version" 2>/dev/null | head -n 1)"
mkdir -p "$W" "$INBOX/sent"
log() { printf '%s %s\n' "$(date -u +%FT%TZ)" "$*" >> "$LOG"; }
echo "tool=$PROG version=${VERSION:-unreleased}"
log "tool=$PROG version=${VERSION:-unreleased} tick=${TICK}s"

rm_get() { # rm_get KEY fallback
  local out=""
  out="$(python3 "$RUN_MODE" get "$1" 2>/dev/null)" || out=""
  out="$(printf '%s' "$out" | head -n 1 | tr -d '\r')"
  if [ -n "$out" ]; then printf '%s\n' "$out"; else printf '%s\n' "$2"; fi
}

mode_oneline() { # the run's caps/issues/speed on ONE line, for the goal text
  local out=""
  out="$(python3 "$RUN_MODE" show --oneline 2>/dev/null | head -n 1 | tr -d '\r')" || out=""
  if [ -z "$out" ]; then
    out="speed=$(rm_get speed unknown) floor=$(rm_get floor unknown) progress=#$(rm_get progress_issue unknown) estimate=#$(rm_get estimate_issue unknown)"
  fi
  printf '%s\n' "$out"
}

goal_text() {
  printf '%s' "/goal Operate track A continuously as the main session by the cycle in local/personas/main.md: every turn run bash results/telemetry/owner-tools/status-snapshot.sh --prs, dispatch DETACHED workers through local/bin/dispatch.sh for every actionable line, keep the live worker count at or above the occupancy floor and refill immediately when it drops, record telemetry, one progress comment per stage boundary, end the turn; never spawn native sub-agents; never do multi-minute work yourself; never merge by hand; critical path first; stop only when the owner says so or the formalization is complete. Current run mode: $(mode_oneline)"
}

pane() { tmux capture-pane -p -t "$S" -S -6 2>/dev/null | grep -v '^[[:space:]]*$' | tail -n 4; }

deliver() { # deliver <mode> <text>  -> owner-say.sh, logged
  bash "$SAY" --mode "$1" --timeout 300 "$2" >> "$LOG" 2>&1
}

drain_inbox() {
  local f base mode text
  for f in "$INBOX"/*; do
    [ -f "$f" ] || continue
    base="$(basename "$f")"
    case "$base" in sent) continue ;; esac
    mode=interrupt
    case "$(head -n 1 "$f")" in
      '#mode:'*) mode="$(head -n 1 "$f" | sed 's/^#mode:[[:space:]]*//')"; text="$(sed -n '2,$p' "$f" | tr '\n' ' ')" ;;
      *) text="$(tr '\n' ' ' < "$f")" ;;
    esac
    text="$(printf '%s' "$text" | sed 's/[[:space:]]*$//')"
    [ -n "$text" ] || { mv "$f" "$INBOX/sent/$(date -u +%Y%m%dT%H%M%SZ)-empty-$base"; continue; }
    if deliver "$mode" "$text"; then
      log "inbox: delivered $base (mode=$mode)"
      mv "$f" "$INBOX/sent/$(date -u +%Y%m%dT%H%M%SZ)-$base"
    else
      log "inbox: delivery of $base failed; keeping it for the next tick"
    fi
  done
}

echo $$ > "$W/goal-keeper.pid"
LAST_ESC=0
HELD=0
while true; do
  if [ -e "$W/goal-keeper.stop" ]; then log "stop file; exiting"; exit 0; fi

  if [ -e "$W/goal-hold" ]; then
    if [ "$HELD" -eq 0 ]; then log "goal-hold present ($(head -n 1 "$W/goal-hold" 2>/dev/null)); keeping hands off"; HELD=1; fi
    [ "$ONCE" -eq 1 ] && exit 0
    sleep "$TICK"; continue
  fi
  if [ "$HELD" -eq 1 ]; then log "goal-hold gone; keeping again"; HELD=0; fi

  P="$(pane)"
  TURN_MAX="$(rm_get turn_max_min 25)"
  case "$TURN_MAX" in ''|*[!0-9]*) TURN_MAX=25 ;; esac

  if printf '%s\n' "$P" | grep -q -E "Goal (stalled|paused)"; then
    deliver interrupt "/goal resume" && log "resumed the goal"
  elif printf '%s\n' "$P" | tail -n 1 | grep -qF "$PANE_DIR" \
     && ! printf '%s\n' "$P" | grep -q -E "Pursuing goal|Goal (paused|stalled|active)" \
     && ! printf '%s\n' "$P" | grep -q "esc to interrupt"; then
    deliver idle "$(goal_text)" && log "set the goal on a goal-less idle session"
  fi

  M="$(printf '%s\n' "$P" | grep -o -E "Working \(([0-9]+)m" | grep -o -E "[0-9]+" | tail -n 1)"
  if [ -n "$M" ] && [ "$M" -ge "$TURN_MAX" ] && [ $(( $(date +%s) - LAST_ESC )) -gt 600 ]; then
    tmux send-keys -t "$S" Escape
    LAST_ESC=$(date +%s)
    log "interrupted a ${M}-minute turn (turn_max_min=$TURN_MAX)"
  fi

  drain_inbox

  [ "$ONCE" -eq 1 ] && exit 0
  sleep "$TICK"
done
