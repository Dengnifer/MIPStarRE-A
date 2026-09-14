#!/usr/bin/env bash
# owner-pause.sh — pause track A within the owner's deadline (design §5).  The ONE pause
# script: it replaces /tmp/owner-pause.sh, owner-pause-v2.sh, owner-pause-fast.sh and
# final-pause.sh, whose chain hard-coded a timestamp, edited the crontab three times in
# sequence without a backup (wiping it once through a sed delimiter bug), and clobbered the
# saved caps by writing them after the caps had already been zeroed.
#
# Usage: owner-pause.sh [--cutoff] [--deadline 15m] [--reason "..."] [--dry-run]
#
#   --cutoff     the FIRST owner word: stop admission and nothing else.  Caps to 0,
#                watchdog/drain, queued dispatches release themselves, no process is
#                signalled and the daemons keep running, so work already in flight
#                finishes and still merges.  It may be given long before the pause.
#   --deadline   total budget from the owner's PAUSE word.  Default: run.pause_deadline_min
#                from the run brief.  Accepts 15m, 900s or a bare number of minutes.
#   --reason     one line recorded in pause-state.json, stages.jsonl and the event entry.
#   --dry-run    print the phase plan, the landing rule and the recorded thresholds;
#                touch nothing.
#
# Phases, as offsets from the owner's pause word (T0 = now):
#   T+0:00  stop admission   run_mode.py pause (caps to 0; the pre-pause caps are saved
#                            inside capacity/state.json, not in a second file a later phase
#                            can clobber), touch watchdog/drain and watchdog/paused, and
#                            snapshot the merge daemon's failed markers BEFORE the daemon is
#                            stopped — afterwards nothing can write one, so a snapshot taken
#                            later cannot tell a kill-caused marker from a real verdict
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
#   D-land  landing          pause_landing.py classifies every live codex session by role
#                            and elapsed time and stops the YOUNG ones only.  Partial work
#                            stays in the worker's worktree; never `git clean`.
#   D-last  last call        the mature reviewers that did not finish and the checkpointed
#                            writers are stopped: one SIGTERM pass over the phase (the
#                            dispatcher AND the codex process it owns), ONE grace, then
#                            SIGKILL to the survivors — the sleep is per phase, not per
#                            session, so the landing cannot cost grace x sessions and run
#                            past the deadline.  The anchored pattern table then sweeps the
#                            leftovers no registry row names.
#   D-0:01  confirm/record   confirm "Goal paused" in the pane, write pause-state.json,
#                            append stages.jsonl and an events.d/ entry, commit and publish
#                            through checked-push.sh.  One minute BEFORE the deadline, so a
#                            publish that takes a few seconds still finishes inside it.
#
# The landing is age-based, not a blanket kill.  A codex session has already paid for its
# input and its reasoning, so killing it throws that away and the resume pays again: on
# 2026-09-12 seventeen sessions died mid-work.  Young sessions have little sunk cost and
# stop at once; a mature reviewer usually finishes, so it runs to the last call and is then
# restarted from scratch; a mature writer is checkpointed — worktree untouched, thread id
# and step recorded — and stopped only at the last call.  Every threshold comes from
# local/capacity-policy.json through pause_landing.py; none is written here.
#
# watchdog/pause-state.json is the single record owner-resume.sh reads, and the landing
# manifest under its "landing" key is what turns that resume into a resume of the WORK.
# No literal timestamp, cap, issue number or deadline appears anywhere in this file.
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

DEADLINE_ARG=""; REASON=""; DRY=0; CUTOFF=0
while [ "$#" -gt 0 ]; do
  case "$1" in
    --cutoff) CUTOFF=1 ;;
    --deadline) DEADLINE_ARG="${2:-}"; shift ;;
    --deadline=*) DEADLINE_ARG="${1#--deadline=}" ;;
    --reason) REASON="${2:-}"; shift ;;
    --reason=*) REASON="${1#--reason=}" ;;
    --dry-run) DRY=1 ;;
    -h|--help) sed -n '2,60p' "$0" | sed 's/^# \{0,1\}//'; exit 0 ;;
    *) echo "$PROG: unknown argument '$1'" >&2; exit 2 ;;
  esac
  shift
done

ROOT="${MIPSTARRE_REPO_ROOT:-}"
if [ -z "$ROOT" ] && [ -r "$OWNER_BIN/repo-root" ]; then ROOT="$(cat "$OWNER_BIN/repo-root")"; fi
if [ -z "$ROOT" ]; then ROOT="$HOME/MIPStarRE-qpbt"; fi
RUN_MODE="${MIPSTARRE_RUN_MODE:-$ROOT/local/bin/run_mode.py}"
LANDING="${MIPSTARRE_PAUSE_LANDING:-$ROOT/local/bin/pause_landing.py}"
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

# --- the landing thresholds ----------------------------------------------------------------
# Every number of the landing lives in local/capacity-policy.json and is answered by
# pause_landing.py, which carries the same values as documented fallbacks.  Nothing is
# written here: a threshold in this file is exactly the literal PR #552 forbids.
CUTOFF_FILE="$W/cutoff"
LANDING_OK=0
THRESHOLDS=""
if [ -r "$LANDING" ] && THRESHOLDS="$(python3 "$LANDING" thresholds 2>/dev/null)" \
   && [ -n "$THRESHOLDS" ]; then
  LANDING_OK=1
fi
pl_get() { # pl_get KEY fallback — the same shape as rm_get above.  The home of every
           # value is local/capacity-policy.json ("landing"), read through
           # pause_landing.py; the fallback applies only when that module cannot run at
           # all.  The fallbacks below are deliberate and are not a second home for the
           # numbers: scripts/tests/test_pause_landing.py asserts that each one equals
           # the matching value in pause_landing.DEFAULTS, so a threshold can still only
           # be CHANGED in the policy file.  A fallback that silently differed is how the
           # degraded path would schedule a different plan from the briefed one.
  local out
  out="$(printf '%s\n' "$THRESHOLDS" | sed -n "s/^$1  *//p" | head -n 1)"
  if [ -n "$out" ]; then printf '%s\n' "$out"; else printf '%s\n' "$2"; fi
}
LAND_LEAD_S="$(pl_get landing_lead_s 180)"
LAST_CALL_S="$(pl_get last_call_s 90)"
GRACE_S="$(pl_get grace_s 20)"
YOUNG_MIN="$(pl_get young_max_min 5)"
CUTOFF_LEAD_MIN="$(pl_get cutoff_lead_min 10)"
THRESHOLD_SRC="$(printf '%s\n' "$THRESHOLDS" | sed -n 's/^source  *//p' | head -n 1)"

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
P_LAND=$((DEADLINE_S - LAND_LEAD_S))
[ "$P_LAND" -lt $((P_CRONTAB + 30)) ] && P_LAND=$((P_CRONTAB + 30))
P_LAND="$(clamp "$P_LAND")"
P_LAST=$((DEADLINE_S - LAST_CALL_S))
[ "$P_LAST" -lt $((P_LAND + 5)) ] && P_LAST=$((P_LAND + 5))
P_LAST="$(clamp "$P_LAST")"
P_RECORD="$DEADLINE_S"
# The confirm/record phase runs a minute BEFORE the deadline, not on it: it ends with a
# checked-push.sh publish, and a publish started at T+deadline returns after it.  "Paused
# within 15 minutes" is the owner's whole instruction, so the last phase finishes inside it.
P_PUBLISH=$((P_RECORD - 60))
[ "$P_PUBLISH" -lt $((P_LAST + 5)) ] && P_PUBLISH=$((P_LAST + 5))
P_PUBLISH="$(clamp "$P_PUBLISH")"
COLLAPSED=0
[ "$P_CRONTAB" -lt 120 ] && COLLAPSED=1

T0="$(date +%s)"
hhmm() { printf '%d:%02d' $(( $1 / 60 )) $(( $1 % 60 )); }

# --- the single record ------------------------------------------------------------------
# watchdog/pause-state.json is what owner-resume.sh restores FROM, so it is written twice:
# a provisional copy as soon as the caps are known (a pause that dies mid-way still leaves
# the one number the resume cannot reconstruct) and the complete one after the telemetry is
# published, so it also carries the phases that failed at the very end.  The landing
# manifest is merged into the same file by pause_landing.py, under "landing".
STATE="$W/pause-state.json"
CAPS_JSON="{}"; CAPS_SRC="unknown"; SPEED="unknown"; CADENCE=0
CRON_BAK=""; CRON_SHA=""; CRON_PAUSED_SHA=""; DAEMON_PAR=""; MAIN_GOAL="unknown"
RUN_MODE_JSON="{}"; MEASURED_JSON="{}"; CUTOFF_AT=""
write_state() { # write_state <status>; every value goes through argv, never through the
                # program text: --reason is owner-supplied and may contain quotes
  python3 - "$STATE" "$1" "${VERSION:-unreleased}" "$CAPS_SRC" "$SPEED" "$CADENCE" \
    "$CRON_BAK" "$CRON_SHA" "$CRON_PAUSED_SHA" "$DAEMON_PAR" "$MAIN_GOAL" "$REASON" \
    "$DEADLINE_MIN" "$FAILURES" "$CAPS_JSON" "$RUN_MODE_JSON" "$MEASURED_JSON" \
    "$CUTOFF_AT" <<'PY'
import datetime, json, sys

(out, status, version, caps_source, speed, cadence, cron_bak, cron_sha, cron_paused_sha,
 par, main_goal, reason, deadline_min, failures, caps, run_mode, measured,
 cutoff_at) = sys.argv[1:19]


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
    "cutoff_at": cutoff_at.strip() or None,
    "deadline_min": as_int(deadline_min, 0),
    "phase_failures": [f for f in failures.split("; ") if f.strip()],
    "paused_at": datetime.datetime.now(datetime.timezone.utc).strftime("%Y-%m-%dT%H:%M:%SZ"),
}
# The landing manifest is owned by pause_landing.py and merged into this same file;
# a rewrite here must never drop it.  Nor may a later write LOWER the recorded caps:
# after a cutoff the live cap files are 0 by design, and a pause word that recorded
# those zeros is a resume with no admission at all.
try:
    with open(out, encoding="utf-8") as handle:
        previous = json.load(handle)
except Exception:
    previous = None
if isinstance(previous, dict):
    if isinstance(previous.get("landing"), dict):
        state["landing"] = previous["landing"]
    was = previous.get("caps") if isinstance(previous.get("caps"), dict) else {}
    now = state["caps"] if isinstance(state["caps"], dict) else {}
    kept = any(isinstance(v, int) and v > 0 for v in was.values())
    if kept and not any(isinstance(v, int) and v > 0 for v in now.values()):
        state["caps"] = was
        state["caps_source"] = previous.get("caps_source") or caps_source.strip()
        state["caps_kept_from"] = previous.get("paused_at")
with open(out + ".tmp", "w", encoding="utf-8") as fh:
    fh.write(json.dumps(state, indent=1, sort_keys=True) + "\n")
import os
os.replace(out + ".tmp", out)
PY
}

landing_rule() {
  printf 'landing rule (thresholds from %s):\n' "${THRESHOLD_SRC:-pause_landing.py (unavailable)}"
  printf '  young (< %s min elapsed)   stopped at the landing phase: little sunk cost\n' \
    "$YOUNG_MIN"
  printf '  mature reviewer           runs until the last call, then restarted from scratch\n'
  printf '  mature writer             checkpointed (worktree, thread id and step recorded),\n'
  printf '                            stopped at the last call, resumed on its own thread\n'
  printf '  every stop                SIGTERM to the dispatcher AND the codex it owns, one\n'
  printf '                            %s s grace for the whole phase, then SIGKILL to the\n' \
    "$GRACE_S"
  printf '                            survivors — and only to a pid whose command line still\n'
  printf '                            names the recorded session (an unreadable one is spared)\n'
  if [ "$LANDING_OK" -eq 0 ]; then
    printf 'NOTE: %s is not readable; nothing can be classified and the landing\n' "$LANDING"
    printf '      degrades to the anchored pattern sweep at the last call.\n'
  fi
}

plan() {
  printf 'phase plan (deadline %s min = T+%s from the owner word):\n' \
    "$DEADLINE_MIN" "$(hhmm "$DEADLINE_S")"
  printf '  T+%-6s stop admission   run_mode.py pause; touch watchdog/drain and watchdog/paused; snapshot the daemon failure markers\n' "$(hhmm $P_ADMISSION)"
  printf '  T+%-6s release waiters  drain check releases queued dispatches; stop keeper, merge daemon, stack-watch and capacityd (stop files kept)\n' "$(hhmm $P_RELEASE)"
  printf '  T+%-6s one message      owner-say.sh --mode terminal (no auto-resume, goal-hold written)\n' "$(hhmm $P_MESSAGE)"
  printf '  T+%-6s crontab          backup crontab -l verbatim, install the paused crontab from a file under $W\n' "$(hhmm $P_CRONTAB)"
  printf '  T+%-6s landing          record the manifest, stop the young only, then read the heads statuses\n' "$(hhmm "$P_LAND")"
  printf '  T+%-6s last call        stop every session still pending (one TERM pass, one grace, then KILL), then the anchored pattern sweep\n' "$(hhmm "$P_LAST")"
  printf '  T+%-6s confirm/record   confirm the paused goal, write pause-state.json, append telemetry, commit and push\n' "$(hhmm "$P_PUBLISH")"
  printf 'last phase T+%s <= deadline T+%s (the publish is started before the deadline, not on it)\n' \
    "$(hhmm "$P_PUBLISH")" "$(hhmm "$DEADLINE_S")"
  if [ -r "$CUTOFF_FILE" ]; then
    printf 'a cutoff is already in force since %s: admission has been closed and the\n' \
      "$(head -n 1 "$CUTOFF_FILE" 2>/dev/null)"
    printf 'sessions still running are the ones that did not finish in that window.\n'
  else
    printf 'no cutoff was given first, so this pause degrades to the landing rule alone.\n'
  fi
  if [ "$COLLAPSED" -eq 1 ]; then
    printf 'NOTE: the deadline is shorter than the nominal plan, so the later phases are\n'
    printf '      clamped onto it; the main session gets almost no time for its closing report.\n'
  fi
  landing_rule
}

cutoff_plan() {
  printf 'cutoff plan (the first owner word; no deadline, no process is signalled):\n'
  printf '  stop admission   run_mode.py pause (caps to 0, pre-pause caps saved in the run mode)\n'
  printf '  drain            touch watchdog/drain; queued dispatches release THEMSELVES\n'
  printf '  daemons          left running, so work already in flight finishes and still merges\n'
  printf '  record           watchdog/cutoff and pause-state.json with status "cutoff"\n'
  printf '  message          one owner-say.sh --mode interrupt: start nothing new, finish what runs\n'
  printf 'the pause word follows whenever the owner gives it; %s minutes of lead is what the\n' \
    "$CUTOFF_LEAD_MIN"
  printf 'policy asks for, and it is what lets the mature sessions finish on their own.\n'
}

if [ "$DRY" -eq 1 ]; then
  if [ "$CUTOFF" -eq 1 ]; then cutoff_plan; else plan; fi
  echo "run-mode: $([ -r "$RUN_MODE" ] && echo "$RUN_MODE" || echo 'NOT FOUND — caps would be zeroed directly and flagged in pause-state.json')"
  echo "landing:  $([ "$LANDING_OK" -eq 1 ] && echo "$LANDING" || echo "NOT USABLE at $LANDING")"
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
    *) log "$label: pid $pid is NOT $want (it runs '${cmd:0:60}'); not signalled" ; return 1 ;;
  esac
}

# --- the admission stop, shared by both owner words ------------------------------------------
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

stop_admission() {
  RUN_MODE_OK=1
  CAPS_SRC="run-mode"
  if have_run_mode; then
    # `show --json` has no top-level `caps`: the live ones are under `derived`,
    # and once a pause (a cutoff, hours earlier) has zeroed them the ones worth
    # restoring are in `saved_caps`.  Reading the live files at this point is how
    # a pause word after a cutoff recorded `primary 0, second 0` as the caps to
    # restore and made owner-resume.sh's fallback resume the run with no
    # admission at all.
    CAPS_JSON="$(python3 "$RUN_MODE" show --json 2>/dev/null | python3 -c '
import json,sys
try: m = json.load(sys.stdin)
except Exception: print("{}"); raise SystemExit(0)
saved = m.get("saved_caps") if isinstance(m.get("saved_caps"), dict) else None
caps = saved or m.get("caps") or (m.get("derived") or {}).get("caps") or {}
caps = {k: v for k, v in caps.items() if isinstance(v, int) and not isinstance(v, bool)}
# All-zero is not a record worth restoring; fall through to the other readers.
print(json.dumps(caps if any(v > 0 for v in caps.values()) else {}))' 2>/dev/null)" \
      || CAPS_JSON="{}"
    if { [ "$CAPS_JSON" = "{}" ] || [ -z "$CAPS_JSON" ]; } && [ ! -r "$CUTOFF_FILE" ]; then
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
  if { [ "$CAPS_JSON" = "{}" ] || [ -z "$CAPS_JSON" ]; } && [ ! -r "$CUTOFF_FILE" ]; then
    CAPS_JSON="$(caps_from_live)"
    CAPS_SRC="live cap files, read before the zeroing"
    log "caps for the record taken from the live files ($CAPS_JSON)"
  elif [ "$CAPS_JSON" = "{}" ] || [ -z "$CAPS_JSON" ]; then
    # A cutoff zeroed the live files hours ago, so reading them now would record
    # zeros as the caps to restore.  write_state keeps the caps the cutoff's own
    # record already carries rather than lowering them.
    CAPS_SRC="the cutoff's own record (the live files are zero by design)"
    log "a cutoff is in force; the caps already recorded in $STATE are kept"
  fi
  if [ "$RUN_MODE_OK" -eq 0 ]; then
    for f in "$W"/max-codex-* "$W/max-codex"; do
      [ -e "$f" ] || continue
      printf '0\n' > "$f"
    done
    log "admission stopped: derived cap files zeroed (run-mode record incomplete)"
  fi
  date -u +%FT%TZ > "$W/drain"
  # Both markers, always together.  owner-resume.sh's post-condition requires
  # watchdog/paused as the proof that the admission pause it is clearing was a
  # real one; nothing wrote it, so the check failed on every clean pause/resume
  # pair, the resume exited 5 before section 6 and the whole work resume was
  # unreachable in production while its unit tests passed.
  date -u +%FT%TZ > "$W/paused"
  log "watchdog/drain and watchdog/paused written: the router releases queued reservations itself"
  SPEED="$(rm_get speed unknown)"
  RUN_MODE_JSON="$(python3 "$RUN_MODE" show --json 2>/dev/null || echo '{}')"
}

# --- the cutoff word: admission only ---------------------------------------------------------
# No kill, no crontab change and no stopped daemon.  Everything in flight finishes, the
# merge daemon still merges what passes, and the pause word can come minutes or hours later
# to a pipeline with almost nothing left to land.
cutoff_expired() { # the recorded cutoff is older than the lead the policy asks for
  local since age
  since="$(head -n 1 "$CUTOFF_FILE" 2>/dev/null)" || return 1
  age="$(python3 - "$since" "$CUTOFF_LEAD_MIN" <<'PY' 2>/dev/null || echo 0
import datetime, sys
try:
    then = datetime.datetime.strptime(sys.argv[1].strip(), "%Y-%m-%dT%H:%M:%SZ")
except Exception:
    raise SystemExit(0)
now = datetime.datetime.now(datetime.timezone.utc).replace(tzinfo=None)
print(1 if (now - then).total_seconds() > int(sys.argv[2]) * 60 else 0)
PY
)"
  [ "${age:-0}" = 1 ]
}

if [ "$CUTOFF" -eq 1 ]; then
  stop_admission
  # A marker that survived a whole cutoff window is not a cutoff still in force:
  # the pause word never came, the main session has moved on (or been replaced),
  # and staying silent leaves it dispatching into refused reservations.  The
  # resume removes the marker, so a fresh cutoff always speaks.
  if [ -r "$CUTOFF_FILE" ] && ! cutoff_expired; then
    log "a cutoff was already in force since $(head -n 1 "$CUTOFF_FILE" 2>/dev/null); admission re-asserted, no second message"
  else
    [ -r "$CUTOFF_FILE" ] && log "the recorded cutoff is older than ${CUTOFF_LEAD_MIN} min; re-asserting it with a fresh message"
    date -u +%FT%TZ > "$CUTOFF_FILE"
    MSG="OWNER (cutoff): admission is closed. Start NOTHING new — no lane, no dispatch, no review — and let everything already running finish; the daemons keep running so finished work still merges. Do not post a closing report yet: the pause word has not been given."
    if [ -x "$SAY" ] || [ -r "$SAY" ]; then
      bash "$SAY" --mode interrupt --timeout 120 "$MSG" || \
        fail_phase "the cutoff message could not be delivered (admission is closed either way)"
    fi
  fi
  CUTOFF_AT="$(head -n 1 "$CUTOFF_FILE" 2>/dev/null)"
  write_state cutoff
  log "cutoff recorded ($STATE); no process was signalled and no daemon was stopped"
  if [ -n "$FAILURES" ]; then echo "$PROG: phases that failed: $FAILURES" >&2; exit 3; fi
  exit 0
fi

plan
log "pause started (deadline T+$(hhmm "$DEADLINE_S"))${REASON:+ — $REASON}"
[ -r "$CUTOFF_FILE" ] && CUTOFF_AT="$(head -n 1 "$CUTOFF_FILE" 2>/dev/null)"

# --- T+0:00 stop admission ------------------------------------------------------------------
stop_admission
write_state pausing
log "provisional pause-state.json written with the pre-pause caps ($CAPS_JSON)"
# The failed-marker snapshot belongs HERE, before the merge daemon is stopped in
# the next phase: the daemon is the only writer of watchdog/daemon/pr<N>.failed,
# so a snapshot taken at the landing phase can never contain a marker the pause
# caused, and "clear the kill-caused markers" would be dead code on every pause.
if [ "$LANDING_OK" -eq 1 ]; then
  if MARKERS_OUT="$(python3 "$LANDING" markers --state "$STATE" 2>&1)"; then
    log "pre-pause marker snapshot: $MARKERS_OUT"
  else
    fail_phase "pause_landing.py markers failed (${MARKERS_OUT:-unknown}); a kill-caused failed marker cannot be told from a verdict"
  fi
fi

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
MSG="OWNER (pause): stop dispatching now and start nothing new. Post ONE closing progress comment on the progress issue and write results/telemetry/owner-handoffs/<date>-main.md from the committed TEMPLATE.md, with every number measured by you (status-snapshot.sh, gh) and not copied from this message. Do NOT post prose on the estimate issue. Then run /goal pause and stay idle. Workers still running are landed by age: young sessions stop now, mature reviewers run to the last minute, and mature provers are checkpointed in their worktrees and resumed on their own threads."
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

# --- D-land: classify, then stop the young ONLY ------------------------------------------------------
# The manifest is written first and to the same record owner-resume.sh reads, so a landing
# that dies between the two phases still leaves the thread ids, worktrees and lane steps
# behind — the one thing a resume cannot reconstruct from a dead process.
wait_until "$P_LAND"
# `|| fail_phase` on a PIPELINE reads the status of its LAST command, so a `| sed`
# made every landing phase look successful and no failure ever reached
# pause-state.json.  PIPESTATUS[0] is the one that matters here.
land_phase() { # land_phase <now|last>
  python3 "$LANDING" land --phase "$1" | sed 's/^/   /'
  [ "${PIPESTATUS[0]}" -eq 0 ] || fail_phase "pause_landing.py land --phase $1 failed"
}
if [ "$LANDING_OK" -eq 1 ]; then
  # --no-github first: the status reads are bounded but not free, and the young
  # must be stopped inside the landing window, not after it.  The statuses are
  # read once the young are down, and the resume re-reads them anyway.
  if MANIFEST_OUT="$(python3 "$LANDING" manifest --cutoff-at "$CUTOFF_AT" --no-github 2>&1 >/dev/null)"; then
    log "landing manifest written into $STATE"
  else
    fail_phase "pause_landing.py manifest failed: ${MANIFEST_OUT:-unknown}"
  fi
  land_phase now
  log "young sessions stopped; mature reviewers and checkpointed writers still running"
  python3 "$LANDING" statuses 2>&1 | sed 's/^/   /' || true
else
  fail_phase "no usable $LANDING; nothing could be classified and no manifest was written"
fi

# --- D-last: the last call ---------------------------------------------------------------------------
wait_until "$P_LAST"
if [ "$LANDING_OK" -eq 1 ]; then
  land_phase last
fi
# The anchored sweep is the LEFTOVER pass, not the landing: it stops the lane runners and
# the helper loops no registry row names.  Every classified codex session has already been
# handled above by its own rule, so this no longer decides anything about a paid session.
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
sleep "$GRACE_S"
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

NOTE="owner pause within the ${DEADLINE_MIN}-minute deadline${REASON:+: $REASON}; admission stopped and drain set, keeper/merge daemon/stack-watch stopped, one terminal message sent, paused crontab installed (backup ${CRON_BAK:-none}), workers landed by age with the manifest in pause-state.json; resume the work with owner-resume.sh on the owner's word"
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
  printf -- '  crontab was installed from a file under $W after a verbatim backup; the landing stopped the young\n'
  printf -- '  sessions first and the mature ones at the last call, and their partial work stays in their\n'
  printf -- '  worktrees. Record: watchdog/pause-state.json, with the lanes, the stopped sessions and the\n'
  printf -- '  failed markers under "landing".\n'
  [ -n "$CUTOFF_AT" ] && printf -- '  A cutoff was in force since %s.\n' "$CUTOFF_AT"
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
