#!/usr/bin/env bash
# owner-pause.sh — pause track A within the owner's deadline (design §5).  The ONE pause
# script: it replaces /tmp/owner-pause.sh, owner-pause-v2.sh, owner-pause-fast.sh and
# final-pause.sh, whose chain hard-coded a timestamp, edited the crontab three times in
# sequence without a backup (wiping it once through a sed delimiter bug), and clobbered the
# saved caps by writing them after the caps had already been zeroed.
#
# Usage: owner-pause.sh [--deadline 15m] [--reason "..."] [--dry-run]
#
#   --deadline   total budget from the owner's word.  Default: run.pause_deadline_min from
#                the run brief.  Accepts 15m, 900s or a bare number of minutes.
#   --reason     one line recorded in pause-state.json, stages.jsonl and the event entry.
#   --dry-run    print the phase plan and the computed deadline; touch nothing.
#
# Phases, as offsets from the owner's word (T0 = now):
#   T+0:00  stop admission   run_mode.py pause (caps to 0; the pre-pause caps are saved
#                            inside capacity/state.json, not in a second file a later phase
#                            can clobber) and touch watchdog/drain
#   T+0:30  release waiters  account_router.reserve sees watchdog/drain and exits cleanly,
#                            so queued dispatches release THEMSELVES (49 waiters at 06:38Z
#                            on 2026-09-12 were killed instead).  Stop the keeper, the merge
#                            daemon, stack-watch and capacityd (stop files kept) by stop
#                            file and by a VERIFIED pid — a paused pipeline has no daemons.
#   T+1:00  one message      exactly one owner-say.sh --mode terminal: closing progress
#                            comment + handoff, no prose on the estimate issue, no
#                            auto-resume (watchdog/goal-hold is written by owner-say.sh).
#   T+2:00  crontab          back up `crontab -l` VERBATIM, failing the phase if it returns
#                            nothing, then install the paused crontab from a file under $W.
#   D-2:00  kill leftovers   anchored patterns only, SIGTERM then SIGKILL after 20 s.
#                            Partial work stays in the worker's worktree; never `git clean`.
#   D-0:01  confirm/record   confirm "Goal paused" in the pane, write pause-state.json,
#                            append stages.jsonl and an events.d/ entry, commit and publish
#                            through checked-push.sh.  One minute BEFORE the deadline, so a
#                            publish that takes a few seconds still finishes inside it.
#
# watchdog/pause-state.json is the single record owner-resume.sh reads.  No literal
# timestamp, cap, issue number or deadline appears anywhere in this file.
#
# Exit codes: 0 paused · 2 usage · 3 a phase failed (the pause continues; the failure is
# printed, recorded in pause-state.json under "phase_failures" and left for the operator)
set -u

PROG="owner-pause.sh"
CACHE_ROOT="${MIPSTARRE_CACHE_ROOT:-$HOME/.cache/mipstarre-dev}"
W="$CACHE_ROOT/watchdog"
D="$W/daemon"
L="$W/lanes"
OWNER_BIN="${MIPSTARRE_OWNER_BIN:-$CACHE_ROOT/owner-bin}"
S="${MIPSTARRE_TMUX_SESSION:-qpbt}"

DEADLINE_ARG=""; REASON=""; DRY=0
while [ "$#" -gt 0 ]; do
  case "$1" in
    --deadline) DEADLINE_ARG="${2:-}"; shift ;;
    --deadline=*) DEADLINE_ARG="${1#--deadline=}" ;;
    --reason) REASON="${2:-}"; shift ;;
    --reason=*) REASON="${1#--reason=}" ;;
    --dry-run) DRY=1 ;;
    -h|--help) sed -n '2,40p' "$0" | sed 's/^# \{0,1\}//'; exit 0 ;;
    *) echo "$PROG: unknown argument '$1'" >&2; exit 2 ;;
  esac
  shift
done

ROOT="${MIPSTARRE_REPO_ROOT:-}"
if [ -z "$ROOT" ] && [ -r "$OWNER_BIN/repo-root" ]; then ROOT="$(cat "$OWNER_BIN/repo-root")"; fi
if [ -z "$ROOT" ]; then ROOT="$HOME/MIPStarRE-qpbt"; fi
RUN_MODE="${MIPSTARRE_RUN_MODE:-$ROOT/local/bin/run_mode.py}"
SAY="${MIPSTARRE_OWNER_SAY:-$OWNER_BIN/owner-say.sh}"
CRONS="${MIPSTARRE_INSTALL_CRONS:-$OWNER_BIN/install-crons.sh}"
PANE_DIR=" · ${ROOT/#$HOME/\~}"

VERSION="$(sed -n 's/^short=//p' "$OWNER_BIN/tools-version" 2>/dev/null | head -n 1)"
echo "tool=$PROG version=${VERSION:-unreleased}"

log() { printf '== %s %s\n' "$(date -u +%FT%TZ)" "$*"; }
FAILURES=""
fail_phase() { FAILURES="$FAILURES${FAILURES:+; }$1"; echo "$PROG: PHASE FAILED: $1" >&2; }

rm_get() { # rm_get KEY fallback
  local out=""
  out="$(python3 "$RUN_MODE" get "$1" 2>/dev/null)" || out=""
  out="$(printf '%s' "$out" | head -n 1 | tr -d '\r')"
  if [ -n "$out" ]; then printf '%s\n' "$out"; else printf '%s\n' "$2"; fi
}
have_run_mode() { [ -r "$RUN_MODE" ]; }

# --- the deadline ------------------------------------------------------------------------
DEADLINE_MIN="$(rm_get pause_deadline_min 15)"
if [ -n "$DEADLINE_ARG" ]; then
  case "$DEADLINE_ARG" in
    *m) DEADLINE_MIN="${DEADLINE_ARG%m}" ;;
    *s) DEADLINE_MIN="$(( ${DEADLINE_ARG%s} / 60 ))"; [ "$DEADLINE_MIN" -lt 1 ] && DEADLINE_MIN=1 ;;
    *) DEADLINE_MIN="$DEADLINE_ARG" ;;
  esac
fi
case "$DEADLINE_MIN" in ''|*[!0-9]*) echo "$PROG: bad deadline '$DEADLINE_ARG'" >&2; exit 2 ;; esac
[ "$DEADLINE_MIN" -ge 1 ] || { echo "$PROG: the deadline must be at least one minute" >&2; exit 2; }
DEADLINE_S=$((DEADLINE_MIN * 60))

# Phase offsets in seconds from the owner's word.  EVERY offset is clamped to the deadline,
# in order: a deadline shorter than the nominal plan collapses the later phases onto it
# rather than running past it, because "within 15 minutes" is the owner's whole instruction.
clamp() { if [ "$1" -gt "$DEADLINE_S" ]; then printf '%s\n' "$DEADLINE_S"; else printf '%s\n' "$1"; fi; }
P_ADMISSION=0
P_RELEASE="$(clamp 30)"
P_MESSAGE="$(clamp 60)"
P_CRONTAB="$(clamp 120)"
P_KILL=$((DEADLINE_S - 120))
[ "$P_KILL" -lt $((P_CRONTAB + 30)) ] && P_KILL=$((P_CRONTAB + 30))
P_KILL="$(clamp "$P_KILL")"
P_RECORD="$DEADLINE_S"
# The confirm/record phase runs a minute BEFORE the deadline, not on it: it ends with a
# checked-push.sh publish, and a publish started at T+deadline returns after it.  "Paused
# within 15 minutes" is the owner's whole instruction, so the last phase finishes inside it.
P_PUBLISH=$((P_RECORD - 60))
[ "$P_PUBLISH" -lt $((P_KILL + 25)) ] && P_PUBLISH=$((P_KILL + 25))
P_PUBLISH="$(clamp "$P_PUBLISH")"
COLLAPSED=0
[ "$P_CRONTAB" -lt 120 ] && COLLAPSED=1

T0="$(date +%s)"
hhmm() { printf '%d:%02d' $(( $1 / 60 )) $(( $1 % 60 )); }

# --- the single record ------------------------------------------------------------------
# watchdog/pause-state.json is what owner-resume.sh restores FROM, so it is written twice:
# a provisional copy as soon as the caps are known (a pause that dies mid-way still leaves
# the one number the resume cannot reconstruct) and the complete one after the telemetry is
# published, so it also carries the phases that failed at the very end.
STATE="$W/pause-state.json"
CAPS_JSON="{}"; CAPS_SRC="unknown"; SPEED="unknown"; CADENCE=0
CRON_BAK=""; CRON_SHA=""; CRON_PAUSED_SHA=""; DAEMON_PAR=""; MAIN_GOAL="unknown"
RUN_MODE_JSON="{}"; MEASURED_JSON="{}"
write_state() { # write_state <status>; every value goes through argv, never through the
                # program text: --reason is owner-supplied and may contain quotes
  python3 - "$STATE" "$1" "${VERSION:-unreleased}" "$CAPS_SRC" "$SPEED" "$CADENCE" \
    "$CRON_BAK" "$CRON_SHA" "$CRON_PAUSED_SHA" "$DAEMON_PAR" "$MAIN_GOAL" "$REASON" \
    "$DEADLINE_MIN" "$FAILURES" "$CAPS_JSON" "$RUN_MODE_JSON" "$MEASURED_JSON" <<'PY'
import datetime, json, sys

(out, status, version, caps_source, speed, cadence, cron_bak, cron_sha, cron_paused_sha,
 par, main_goal, reason, deadline_min, failures, caps, run_mode, measured) = sys.argv[1:18]


def as_json(text, default):
    try:
        value = json.loads(text)
    except Exception:
        return default
    return default if value in (None, "") else value


def as_int(text, default=None):
    text = (text or "").strip()
    return int(text) if text.isdigit() else default


state = {
    "schema": "mipstarre-pause-state/1",
    "status": status,
    "tools_version": version.strip(),
    "caps": as_json(caps, {}),
    "caps_source": caps_source.strip(),
    "speed": speed.strip(),
    "estimate_cadence_min": as_int(cadence, 0),
    "crontab_backup": cron_bak.strip() or None,
    "crontab_sha256": cron_sha.strip() or None,
    "crontab_paused_sha256": cron_paused_sha.strip() or None,
    "daemon_par": as_int(par),
    "run_mode": as_json(run_mode, {}),
    "measured_limits": as_json(measured, {}),
    "main_goal": main_goal.strip(),
    "reason": reason.strip() or None,
    "deadline_min": as_int(deadline_min, 0),
    "phase_failures": [f for f in failures.split("; ") if f.strip()],
    "paused_at": datetime.datetime.now(datetime.timezone.utc).strftime("%Y-%m-%dT%H:%M:%SZ"),
}
with open(out + ".tmp", "w", encoding="utf-8") as fh:
    fh.write(json.dumps(state, indent=1, sort_keys=True) + "\n")
import os
os.replace(out + ".tmp", out)
PY
}

plan() {
  printf 'phase plan (deadline %s min = T+%s from the owner word):\n' \
    "$DEADLINE_MIN" "$(hhmm "$DEADLINE_S")"
  printf '  T+%-6s stop admission   run_mode.py pause; touch watchdog/drain\n' "$(hhmm $P_ADMISSION)"
  printf '  T+%-6s release waiters  drain check releases queued dispatches; stop keeper, merge daemon, stack-watch and capacityd (stop files kept)\n' "$(hhmm $P_RELEASE)"
  printf '  T+%-6s one message      owner-say.sh --mode terminal (no auto-resume, goal-hold written)\n' "$(hhmm $P_MESSAGE)"
  printf '  T+%-6s crontab          backup crontab -l verbatim, install the paused crontab from a file under $W\n' "$(hhmm $P_CRONTAB)"
  printf '  T+%-6s kill leftovers   anchored patterns, SIGTERM then SIGKILL after 20 s; partial work stays in the worktrees\n' "$(hhmm $P_KILL)"
  printf '  T+%-6s confirm/record   confirm the paused goal, write pause-state.json, append telemetry, commit and push\n' "$(hhmm $P_PUBLISH)"
  printf 'last phase T+%s <= deadline T+%s (the publish is started before the deadline, not on it)\n' \
    "$(hhmm "$P_PUBLISH")" "$(hhmm "$DEADLINE_S")"
  if [ "$COLLAPSED" -eq 1 ]; then
    printf 'NOTE: the deadline is shorter than the nominal plan, so the later phases are\n'
    printf '      clamped onto it; the main session gets almost no time for its closing report.\n'
  fi
}

if [ "$DRY" -eq 1 ]; then
  plan
  echo "run-mode: $([ -r "$RUN_MODE" ] && echo "$RUN_MODE" || echo 'NOT FOUND — caps would be zeroed directly and flagged in pause-state.json')"
  echo "reason: ${REASON:-(none given)}"
  echo "$PROG: [dry-run] nothing was stopped, written or sent"
  exit 0
fi

mkdir -p "$W" "$D" "$L"
if ! mkdir "$W/owner-pause.lock" 2>/dev/null; then
  echo "$PROG: another pause is running ($W/owner-pause.lock); refusing" >&2; exit 2
fi
trap 'rmdir "$W/owner-pause.lock" 2>/dev/null || true' EXIT

wait_until() { # wait_until <offset seconds from T0>
  local target=$(( T0 + $1 )) now
  while :; do
    now="$(date +%s)"
    [ "$now" -ge "$target" ] && return 0
    sleep 5
  done
}

# Signal a pid ONLY when it is still the process the file names.  ghz is a
# 128-core host shared with other users' jobs, so a recycled pid is a real
# possibility and an unverified `kill "$(cat …)"` can stop someone else's work.
kill_recorded() { # kill_recorded <pid file> <substring the cmdline must contain> <label>
  local file="$1" want="$2" label="$3" pid cmd
  pid="$(cat "$file" 2>/dev/null || true)"
  case "${pid:-}" in ''|*[!0-9]*) return 1 ;; esac
  kill -0 "$pid" 2>/dev/null || { log "$label: pid $pid is already gone"; return 1; }
  cmd="$(tr '\0' ' ' < "/proc/$pid/cmdline" 2>/dev/null || ps -o args= -p "$pid" 2>/dev/null || true)"
  case "$cmd" in
    *"$want"*) kill "$pid" 2>/dev/null && log "$label: SIGTERM to pid $pid"; return 0 ;;
    *) log "$label: pid $pid is NOT $want (it runs '${cmd:0:60}'); not signalled"; return 1 ;;
  esac
}

plan
log "pause started (deadline T+$(hhmm "$DEADLINE_S"))${REASON:+ — $REASON}"

# --- T+0:00 stop admission ------------------------------------------------------------------
# The caps are read BEFORE anything is paused.  The 2026-09-12 chain wrote its caps record
# AFTER a phase had already zeroed the live files, so the resume would have restored zeros.
caps_from_live() { # last resort, and still taken before the zeroing below
  python3 - "$W" <<'PY'
import json, pathlib, sys
w = pathlib.Path(sys.argv[1]); out = {}
for f in sorted(w.glob("max-codex-*")):
    try:
        out[f.name.replace("max-codex-", "")] = int(f.read_text().strip() or 0)
    except Exception:
        pass
print(json.dumps(out))
PY
}

RUN_MODE_OK=1
CAPS_SRC="run-mode"
if have_run_mode; then
  CAPS_JSON="$(python3 "$RUN_MODE" show --json 2>/dev/null | python3 -c '
import json,sys
try: m = json.load(sys.stdin)
except Exception: print("{}"); raise SystemExit(0)
caps = m.get("caps") or {}
print(json.dumps(caps))' 2>/dev/null)" || CAPS_JSON="{}"
  if [ "$CAPS_JSON" = "{}" ] || [ -z "$CAPS_JSON" ]; then
    ACCTS="$(python3 "$RUN_MODE" get accounts 2>/dev/null || true)"
    CAPS_JSON="$(for a in $ACCTS; do printf '%s=%s\n' "$a" "$(rm_get "cap.$a" 0)"; done | python3 -c '
import sys,json
print(json.dumps({k: int(v) for k, v in (l.strip().split("=",1) for l in sys.stdin if "=" in l)}))')"
  fi
  if python3 "$RUN_MODE" pause; then
    log "admission stopped: run_mode.py pause (caps 0, pre-pause caps inside capacity/state.json)"
  else
    RUN_MODE_OK=0; fail_phase "run_mode.py pause failed"
  fi
else
  RUN_MODE_OK=0
  echo "$PROG: no run_mode.py at $RUN_MODE; zeroing the derived cap files directly" >&2
fi
if [ "$CAPS_JSON" = "{}" ] || [ -z "$CAPS_JSON" ]; then
  CAPS_JSON="$(caps_from_live)"
  CAPS_SRC="live cap files, read before the zeroing"
  log "caps for the record taken from the live files ($CAPS_JSON)"
fi
if [ "$RUN_MODE_OK" -eq 0 ]; then
  for f in "$W"/max-codex-* "$W/max-codex"; do
    [ -e "$f" ] || continue
    printf '0\n' > "$f"
  done
  log "admission stopped: derived cap files zeroed (run-mode record incomplete)"
fi
date -u +%FT%TZ > "$W/drain"
log "watchdog/drain written: the router releases queued reservations itself"
SPEED="$(rm_get speed unknown)"
RUN_MODE_JSON="$(python3 "$RUN_MODE" show --json 2>/dev/null || echo '{}')"
write_state pausing
log "provisional pause-state.json written with the pre-pause caps ($CAPS_JSON)"

# --- T+0:30 release waiters, stop the loops ---------------------------------------------------
wait_until "$P_RELEASE"
WAITERS="$(pgrep -fc 'python3 [^ ]*account_router\.py' 2>/dev/null || true)"; WAITERS="${WAITERS:-0}"
log "waiting dispatches at the drain: $WAITERS (they exit themselves; none is killed here)"
touch "$W/goal-keeper.stop"
kill_recorded "$W/goal-keeper.pid" goal-keeper "goal keeper" || true
touch "$D/stop"
kill_recorded "$D/daemon.pid" merge-daemon "merge daemon" || true
touch "$W/stack-watch.stop"
for p in $(pgrep -f '^bash [^ ]*stack-watch(-v[0-9]+)?\.sh' 2>/dev/null || true); do kill "$p" 2>/dev/null; done
# capacityd too: a paused pipeline has NO daemons running.  Without this the
# controller keeps ticking every 60 s through the pause, and because a recovering
# endpoint is handled before the paused test it could raise a cap while
# state.json says paused.  The stop file is kept; owner-resume.sh removes it.
mkdir -p "$W/capacity"
touch "$W/capacity/capacityd.stop"
kill_recorded "$W/capacity/capacityd.pid" capacityd "capacity controller" || true
log "keeper stopped, merge daemon stopped (stop file KEPT), stack-watch stopped, capacityd stopped (stop file KEPT)"

# --- T+1:00 the one terminal message ------------------------------------------------------------
wait_until "$P_MESSAGE"
MSG="OWNER (pause): stop dispatching now and start nothing new. Post ONE closing progress comment on the progress issue and write results/telemetry/owner-handoffs/<date>-main.md from the committed TEMPLATE.md, with every number measured by you (status-snapshot.sh, gh) and not copied from this message. Do NOT post prose on the estimate issue. Then run /goal pause and stay idle. Workers still running at the deadline are stopped by the operator; their partial work stays in their worktrees."
if bash "$SAY" --mode terminal --timeout 120 "$MSG"; then
  log "closing order delivered (terminal mode: no auto-resume, watchdog/goal-hold written)"
else
  fail_phase "the terminal message could not be delivered"
fi

# --- T+2:00 crontab ---------------------------------------------------------------------------------
wait_until "$P_CRONTAB"
CRONTAB_BIN="${MIPSTARRE_CRONTAB:-crontab}"
CRON_BAK=""
CRON_SHA=""
CRON_PAUSED_SHA=""
sha_of_stdin() { python3 -c 'import hashlib,sys;print(hashlib.sha256(sys.stdin.buffer.read()).hexdigest())'; }
CRON_LIVE="$("$CRONTAB_BIN" -l 2>/dev/null || true)"
if [ -z "$CRON_LIVE" ]; then
  fail_phase "crontab -l returned nothing; no backup taken and no crontab installed"
else
  CRON_BAK="$W/crontab.$(date -u +%Y%m%dT%H%M%SZ).bak"
  printf '%s\n' "$CRON_LIVE" > "$CRON_BAK"
  CRON_SHA="$(printf '%s\n' "$CRON_LIVE" | sha_of_stdin)"
  log "crontab backed up verbatim to $CRON_BAK ($CRON_SHA)"
  if [ -x "$CRONS" ]; then
    if bash "$CRONS" --paused; then
      log "paused crontab installed from a file under \$W"
      CRON_PAUSED_SHA="$("$CRONTAB_BIN" -l 2>/dev/null | sha_of_stdin)"
    else
      fail_phase "install-crons.sh --paused failed; the live crontab is unchanged"
    fi
  else
    fail_phase "no install-crons.sh at $CRONS; the live crontab is unchanged"
  fi
fi

# --- D-2:00 kill the leftovers ----------------------------------------------------------------------
wait_until "$P_KILL"
PATTERNS='^bash [^ ]*lane\.sh( |$)
^bash [^ ]*lane-v[0-9]+\.sh( |$)
^bash [^ ]*autofix\.sh( |$)
^bash [^ ]*autofix-loop\.sh( |$)
^bash [^ ]*fix-lane\.sh( |$)
^bash [^ ]*conflict-resolve\.sh( |$)
^bash [^ ]*dispatch\.sh( |$)
^python3 [^ ]*account_router\.py
^bash [^ ]*capacityd\.sh( |$)
^node [^ ]*codex(\.js)?( |$).* exec( |$)'
n=0
while IFS= read -r pat; do
  [ -n "$pat" ] || continue
  for p in $(pgrep -f "$pat" 2>/dev/null || true); do
    kill "$p" 2>/dev/null && n=$((n + 1))
  done
done <<EOF
$PATTERNS
EOF
log "SIGTERM sent to $n leftover processes (anchored patterns only)"
sleep 20
m=0
while IFS= read -r pat; do
  [ -n "$pat" ] || continue
  for p in $(pgrep -f "$pat" 2>/dev/null || true); do
    kill -9 "$p" 2>/dev/null && m=$((m + 1))
  done
done <<EOF
$PATTERNS
EOF
log "SIGKILL sent to $m survivors; partial work stays in the workers' worktrees (never git clean)"

# --- D-0:01 confirm and record ------------------------------------------------------------------
wait_until "$P_PUBLISH"
MAIN_GOAL="unknown"
if tmux has-session -t "$S" 2>/dev/null; then
  PANE="$(tmux capture-pane -p -t "$S" 2>/dev/null | grep -v '^[[:space:]]*$' | tail -n 4)"
  if ! printf '%s\n' "$PANE" | grep -q "Goal paused"; then
    tmux send-keys -t "$S" Escape; sleep 10
    tmux send-keys -t "$S" -l "/goal pause"; sleep 1; tmux send-keys -t "$S" Enter; sleep 5
    PANE="$(tmux capture-pane -p -t "$S" 2>/dev/null | grep -v '^[[:space:]]*$' | tail -n 4)"
  fi
  MAIN_GOAL="$(printf '%s\n' "$PANE" | grep -o -E "Goal paused|Pursuing goal|Goal stalled" | head -n 1)"
  MAIN_GOAL="${MAIN_GOAL:-unknown}"
  printf '%s\n' "$PANE" | grep -q "Goal paused" || fail_phase "the pane does not confirm 'Goal paused' (it reads: $MAIN_GOAL)"
else
  fail_phase "no tmux session '$S' to confirm the paused goal"
fi
log "main goal state: $MAIN_GOAL"

CADENCE="$(rm_get estimate_cadence_min 0)"
DAEMON_PAR="$(cat "$D/par" 2>/dev/null || true)"
MEASURED_JSON="$(cat "$W/capacity/limit-estimate.json" 2>/dev/null || echo '{}')"

NOTE="owner pause within the ${DEADLINE_MIN}-minute deadline${REASON:+: $REASON}; admission stopped and drain set, keeper/merge daemon/stack-watch stopped, one terminal message sent, paused crontab installed (backup ${CRON_BAK:-none}), leftovers stopped at the deadline; resume only on the owner's word with owner-resume.sh"
python3 - "$ROOT/results/telemetry/stages.jsonl" "$NOTE" <<'PY'
import datetime, json, sys
row = {"ts": datetime.datetime.now().astimezone().strftime("%Y-%m-%dT%H:%M:%S%z"),
       "stage": "operator", "event": "pause", "note": sys.argv[2]}
with open(sys.argv[1], "a", encoding="utf-8") as fh:
    fh.write(json.dumps(row) + "\n")
PY

EV_DIR="$ROOT/results/telemetry/events.d"
mkdir -p "$EV_DIR"
EV="$EV_DIR/$(date -u +%F)-operator.md"
{
  printf -- '- %s PAUSE (owner word, %s-minute deadline). Admission stopped through run-mode; queued\n' \
    "$(date -u +%H:%MZ)" "$DEADLINE_MIN"
  printf -- '  dispatches released themselves at the drain; keeper, merge daemon (stop file kept) and stack-watch\n'
  printf -- '  stopped; one terminal message asked for the closing progress comment and the handoff; the paused\n'
  printf -- '  crontab was installed from a file under $W after a verbatim backup; leftover workers were stopped\n'
  printf -- '  at the deadline and their partial work stays in their worktrees. Record: watchdog/pause-state.json.\n'
  [ -n "$FAILURES" ] && printf -- '  Phase failures: %s.\n' "$FAILURES"
  [ -n "$REASON" ] && printf -- '  Reason given: %s.\n' "$REASON"
} >> "$EV"

BR="$(git -C "$ROOT" rev-parse --abbrev-ref HEAD 2>/dev/null || echo unknown)"
if [ "$BR" = main ]; then
  git -C "$ROOT" add results/telemetry/stages.jsonl "$EV" >/dev/null 2>&1
  git -C "$ROOT" commit -qm "chore(telemetry): owner pause of track A" \
    -- results/telemetry/stages.jsonl "$EV" 2>&1 | tail -n 1
  if [ -x "$ROOT/local/bin/checked-push.sh" ]; then
    "$ROOT/local/bin/checked-push.sh" --repo-root "$ROOT" github refs/heads/main:refs/heads/main \
      || fail_phase "checked-push.sh could not publish the pause telemetry (it stays committed locally)"
  else
    fail_phase "no checked-push.sh; the pause telemetry stays committed locally"
  fi
else
  fail_phase "the primary checkout is on '$BR', not main; the pause telemetry stays uncommitted"
fi

# the complete record LAST, so it also carries the phases that failed while publishing
write_state paused
log "pause-state.json written ($STATE)"

log "paused at $(date -u +%FT%TZ) ($(( ($(date +%s) - T0) / 60 )) min after the word)"
if [ -n "$FAILURES" ]; then echo "$PROG: phases that failed: $FAILURES" >&2; exit 3; fi
exit 0
