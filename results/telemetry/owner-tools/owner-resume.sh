#!/usr/bin/env bash
# owner-resume.sh — resume track A, on the owner's explicit word only (design §5).
#
# It restores FROM watchdog/pause-state.json AND NOTHING ELSE.  The 2026-09-12 resume
# script guessed instead: it un-commented the crontab with
#     sed -E 's#^\#PAUSED-2026[0-9]{4} ##'
# which would have resurrected the watchdog / astra-poll / heartbeat rows deliberately
# commented out since 2026-09-09, it hard-coded "primary 5 / second 39 / total 44" into the
# resume message (already wrong by 04:58Z on the day it ran), and it restored caps from a
# caps-before-pause file that a later phase could — and did — overwrite with zeros.
#
# Usage: owner-resume.sh [--dry-run] [--force-crontab] [--state FILE]
#   --dry-run        print what would be restored and check nothing is missing; touch nothing
#   --force-crontab  install the recorded backup even though the live crontab was edited
#                    during the pause (the difference is printed either way)
#   --state FILE     use FILE instead of watchdog/pause-state.json
#
# Post-condition check, loud on failure: every cap file exists, is numeric and nonzero for
# an enabled account, no account is "down", the capacity controller and the merge daemon are
# running, and watchdog/drain is gone.  A resume that leaves no controller running is a run
# whose caps can never move again, so it is an exit-5 failure, not a silent success.
#
# Exit codes: 0 resumed · 2 usage · 3 no usable pause record · 4 the crontab was edited
#             during the pause and --force-crontab was not given · 5 the post-condition
#             check failed (the run is NOT healthy; read the printed lines)
set -u

PROG="owner-resume.sh"
CACHE_ROOT="${MIPSTARRE_CACHE_ROOT:-$HOME/.cache/mipstarre-dev}"
W="$CACHE_ROOT/watchdog"
D="$W/daemon"
L="$W/lanes"
OWNER_BIN="${MIPSTARRE_OWNER_BIN:-$CACHE_ROOT/owner-bin}"
S="${MIPSTARRE_TMUX_SESSION:-qpbt}"

DRY=0; FORCE_CRON=0; STATE="$W/pause-state.json"
while [ "$#" -gt 0 ]; do
  case "$1" in
    --dry-run) DRY=1 ;;
    --force-crontab) FORCE_CRON=1 ;;
    --state) STATE="${2:-}"; shift ;;
    --state=*) STATE="${1#--state=}" ;;
    -h|--help) sed -n '2,28p' "$0" | sed 's/^# \{0,1\}//'; exit 0 ;;
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
CRONTAB_BIN="${MIPSTARRE_CRONTAB:-crontab}"

VERSION="$(sed -n 's/^short=//p' "$OWNER_BIN/tools-version" 2>/dev/null | head -n 1)"
echo "tool=$PROG version=${VERSION:-unreleased}"
log() { printf '== %s %s\n' "$(date -u +%FT%TZ)" "$*"; }

[ -r "$STATE" ] || {
  echo "$PROG: no pause record at $STATE." >&2
  echo "$PROG: owner-pause.sh writes it; without it there is nothing to restore FROM and" >&2
  echo "$PROG: this script will not guess caps, a speed tier or a crontab." >&2
  exit 3
}

field() { # field <dotted.path> [fallback] — one scalar out of the pause record
  python3 - "$STATE" "$1" "${2-}" <<'PY'
import json, sys
state = json.load(open(sys.argv[1], encoding="utf-8"))
node = state
for part in sys.argv[2].split("."):
    if isinstance(node, dict) and part in node:
        node = node[part]
    else:
        node = None
        break
print(sys.argv[3] if node in (None, "") else node)
PY
}

PAUSED_AT="$(field paused_at unknown)"
SPEED="$(field speed unknown)"
CRON_BAK="$(field crontab_backup)"
CRON_SHA="$(field crontab_sha256)"
CRON_PAUSED_SHA="$(field crontab_paused_sha256)"
PAR="$(field daemon_par)"
CAPS_SOURCE="$(field caps_source unknown)"
log "resuming from $STATE (paused at $PAUSED_AT, speed $SPEED, caps from $CAPS_SOURCE)"

CAPS_LINES="$(python3 - "$STATE" <<'PY'
import json, sys
state = json.load(open(sys.argv[1], encoding="utf-8"))
for name, value in sorted((state.get("caps") or {}).items()):
    print(f"{name} {value}")
PY
)"
if [ -z "$CAPS_LINES" ]; then
  echo "$PROG: the pause record carries no caps; refusing to resume with a guess" >&2
  exit 3
fi
echo "$PROG: caps to restore:"; printf '%s\n' "$CAPS_LINES" | sed 's/^/  /'

if [ "$DRY" -eq 1 ]; then
  echo "$PROG: [dry-run] would: run_mode.py resume; install $CRON_BAK verbatim;"
  echo "$PROG: [dry-run]        restart capacityd, merge daemon (PAR=${PAR:-daemon default}), stack-watch, keeper;"
  echo "$PROG: [dry-run]        remove watchdog/{drain,goal-hold,paused} and the stop files;"
  echo "$PROG: [dry-run]        send one resume message rendered from run_mode.py show."
  [ -n "$CRON_BAK" ] && [ ! -r "$CRON_BAK" ] && echo "$PROG: [dry-run] WARNING: $CRON_BAK is missing" >&2
  exit 0
fi

cd "$ROOT" 2>/dev/null || { echo "$PROG: cannot enter $ROOT" >&2; exit 3; }

# --- 0. preconditions, checked BEFORE anything is restored ---------------------------------
# A refusal here must leave the paused state exactly as it was, not half-resumed.
sha_of() { python3 -c 'import hashlib,sys;print(hashlib.sha256(open(sys.argv[1],"rb").read()).hexdigest())' "$1"; }
CRON_OK=0
if [ -z "$CRON_BAK" ]; then
  echo "$PROG: the pause recorded no crontab backup; the live crontab will be left alone" >&2
elif [ ! -r "$CRON_BAK" ]; then
  echo "$PROG: the recorded backup $CRON_BAK is gone; the live crontab will be left alone" >&2
else
  BAK_SHA="$(sha_of "$CRON_BAK")"
  if [ -n "$CRON_SHA" ] && [ "$BAK_SHA" != "$CRON_SHA" ]; then
    echo "$PROG: $CRON_BAK has changed since the pause ($BAK_SHA != $CRON_SHA); refusing" >&2
    echo "$PROG: nothing was restored." >&2
    exit 4
  fi
  LIVE_SHA="$("$CRONTAB_BIN" -l 2>/dev/null | python3 -c 'import hashlib,sys;print(hashlib.sha256(sys.stdin.buffer.read()).hexdigest())')"
  if [ -n "$CRON_PAUSED_SHA" ] && [ "$LIVE_SHA" != "$CRON_PAUSED_SHA" ]; then
    echo "$PROG: the live crontab is not the one the pause installed." >&2
    echo "$PROG: live $LIVE_SHA, paused $CRON_PAUSED_SHA — someone edited it during the pause." >&2
    echo "$PROG: difference (live vs the backup that would be restored):" >&2
    "$CRONTAB_BIN" -l 2>/dev/null | diff - "$CRON_BAK" | sed 's/^/  /' >&2 || true
    if [ "$FORCE_CRON" -eq 0 ]; then
      echo "$PROG: re-run with --force-crontab to install the backup anyway. Nothing was restored." >&2
      exit 4
    fi
    echo "$PROG: --force-crontab given; installing the recorded backup over those edits" >&2
  fi
  CRON_OK=1
fi

git fetch -q github 2>/dev/null || true

# --- 1. caps and speed, through run-mode --------------------------------------------------
if [ -r "$RUN_MODE" ] && python3 "$RUN_MODE" resume; then
  log "run_mode.py resume: caps and speed restored, AIMD re-enters at the saved value"
else
  echo "$PROG: run_mode.py resume unavailable or failed; writing the recorded caps into the" >&2
  echo "$PROG: derived cap files directly (they are the router's admission input)." >&2
  total=0
  printf '%s\n' "$CAPS_LINES" | while read -r name value; do
    case "$value" in ''|*[!0-9]*) echo "$PROG: recorded cap for $name is not numeric ('$value'); skipped" >&2; continue ;; esac
    printf '%s\n' "$value" > "$W/max-codex-$name"
  done
  total="$(printf '%s\n' "$CAPS_LINES" | awk '$2 ~ /^[0-9]+$/ { s += $2 } END { print s + 0 }')"
  printf '%s\n' "$total" > "$W/max-codex"
  log "cap files written from the record (total $total)"
fi

# --- 2. the crontab, verbatim, never by sed ------------------------------------------------
# No `sed -E 's#^\#PAUSED-2026[0-9]{4} ##'`: un-commenting would resurrect the watchdog,
# astra-poll and heartbeat rows that have been deliberately off since 2026-09-09.
if [ "$CRON_OK" -eq 1 ]; then
  if [ -x "$CRONS" ]; then
    bash "$CRONS" --restore "$CRON_BAK" || echo "$PROG: restoring the crontab failed" >&2
  else
    "$CRONTAB_BIN" "$CRON_BAK" && log "crontab restored verbatim from $CRON_BAK"
  fi
fi

# --- 3. clear the pause markers and restart the loops ---------------------------------------
rm -f "$D/stop" "$W/goal-keeper.stop" "$W/stack-watch.stop" "$W/capacity/capacityd.stop" \
      "$W/paused" "$W/drain" "$W/goal-hold"
log "drain, goal-hold and the stop files cleared (capacityd.stop included)"

mkdir -p "$L" "$W/capacity"
# capacityd FIRST: without a running controller nothing writes the cap files again, there
# is no AIMD, no 5xx trip and no half-open probe, and the caps stay frozen at whatever the
# resume restored — the 2026-09-12 situation that was recovered by hand.  capacityd.sh
# takes a lock, so starting one that is already running is a no-op.
if [ -x "$OWNER_BIN/capacityd.sh" ]; then
  setsid nohup bash "$OWNER_BIN/capacityd.sh" >> "$W/capacity/capacityd.out" 2>&1 < /dev/null &
  sleep 1
  log "capacity controller restarted (pid $(cat "$W/capacity/capacityd.pid" 2>/dev/null || echo '?'))"
else
  echo "$PROG: no capacityd.sh in $OWNER_BIN; the capacity controller is NOT running." >&2
  echo "$PROG: run results/telemetry/owner-tools/install.sh --start-loops." >&2
fi
if [ -x "$OWNER_BIN/merge-daemon.sh" ]; then
  if [ -n "$PAR" ]; then export PAR; fi
  setsid nohup bash "$OWNER_BIN/merge-daemon.sh" >> "$L/daemon.log" 2>&1 < /dev/null &
  sleep 1
  log "merge daemon restarted (PAR=${PAR:-daemon default}, pid $(cat "$D/daemon.pid" 2>/dev/null || echo '?'))"
else
  echo "$PROG: no merge-daemon.sh in $OWNER_BIN; run install.sh" >&2
fi
if [ -x "$OWNER_BIN/stack-watch.sh" ]; then
  pgrep -f "^bash $OWNER_BIN/stack-watch.sh" >/dev/null 2>&1 || {
    setsid nohup bash "$OWNER_BIN/stack-watch.sh" >> "$L/stack-watch.log" 2>&1 < /dev/null &
    log "stack-watch restarted"; }
fi
if [ -x "$OWNER_BIN/goal-keeper.sh" ]; then
  setsid nohup bash "$OWNER_BIN/goal-keeper.sh" > /dev/null 2>&1 < /dev/null &
  sleep 1
  log "goal keeper restarted (pid $(cat "$W/goal-keeper.pid" 2>/dev/null || echo '?'))"
fi

# --- 4. one resume message, rendered from run-mode ------------------------------------------
ONELINE="$(python3 "$RUN_MODE" show --oneline 2>/dev/null | head -n 1 | tr -d '\r')" || ONELINE=""
if [ -z "$ONELINE" ]; then
  ONELINE="$(printf '%s\n' "$CAPS_LINES" | awk '{printf "%s=%s ", $1, $2}')speed=$SPEED"
fi
MSG="OWNER (resume): the pause is over; the run mode is $ONELINE. Read local/personas/main.md and the last comments on the progress issue, run status-snapshot.sh --prs, dispatch detached workers through local/bin/dispatch.sh until the live count reaches the occupancy floor, and resume the cycle. Every number you report must be measured by you, not copied from this message."
if tmux has-session -t "$S" 2>/dev/null; then
  bash "$SAY" --mode interrupt --timeout 300 "$MSG" || echo "$PROG: the resume message was not delivered" >&2
else
  echo "$PROG: no tmux session '$S'; start the main session with local/bin/main-session.sh" >&2
fi

# --- 5. the post-condition check, loud ---------------------------------------------------------
RC=0
for f in "$W"/max-codex-*; do
  [ -e "$f" ] || { echo "$PROG: POST-CONDITION: no per-account cap file under $W" >&2; RC=5; break; }
  v="$(cat "$f" 2>/dev/null || true)"
  name="$(basename "$f")"; name="${name#max-codex-}"
  case "$v" in ''|*[!0-9]*) echo "$PROG: POST-CONDITION: $f is not numeric ('$v')" >&2; RC=5; continue ;; esac
  # `enabled.<account>` is run_mode's spelling (PER_ACCOUNT_KEYS), and it answers
  # yes/no, never true/false.  `account.<name>.enabled` raises and exits 2, so the
  # old `|| echo true` fallback fired on every account and the comparison against
  # `false` could never be true: a briefed `enabled: false` account (the supported
  # replacement for `echo 0 > max-codex-primary`) tripped this check on a healthy
  # resume and the script exited 5 RESUME INCOMPLETE.
  enabled="$(python3 "$RUN_MODE" get "enabled.$name" 2>/dev/null || echo unknown)"
  if [ "$enabled" != no ] && [ "$v" = 0 ]; then
    echo "$PROG: POST-CONDITION: $name is enabled ($enabled) but its cap is 0" >&2; RC=5
  fi
  health="$(python3 -c '
import json,sys
try: print(json.load(open(sys.argv[1], encoding="utf-8")).get("health", "unknown"))
except Exception: print("unknown")' "$W/capacity/health-$name.json" 2>/dev/null || echo unknown)"
  if [ "$health" = down ]; then echo "$PROG: POST-CONDITION: account $name is down" >&2; RC=5; fi
  printf '  %-10s cap %s health %s enabled %s\n' "$name" "$v" "$health" "$enabled"
done
CAPD_PID="$(cat "$W/capacity/capacityd.pid" 2>/dev/null || true)"
if [ -e "$W/capacity/capacityd.stop" ]; then
  echo "$PROG: POST-CONDITION: watchdog/capacity/capacityd.stop still exists" >&2; RC=5
elif [ -z "$CAPD_PID" ] || ! kill -0 "$CAPD_PID" 2>/dev/null; then
  echo "$PROG: POST-CONDITION: no capacity controller is running (capacityd.pid '${CAPD_PID:-none}')" >&2
  echo "$PROG: without it the caps never move again: no AIMD, no 5xx trip, no probe." >&2
  RC=5
else
  printf '  %-10s pid %s (60 s tick)\n' capacityd "$CAPD_PID"
fi
DAEMON_PID="$(cat "$D/daemon.pid" 2>/dev/null || true)"
if [ -z "$DAEMON_PID" ] || ! kill -0 "$DAEMON_PID" 2>/dev/null; then
  echo "$PROG: POST-CONDITION: no merge daemon is running (daemon.pid '${DAEMON_PID:-none}')" >&2
  RC=5
fi
# The PATH shim refuses every CODEX_HOME other than ~/.codex while
# watchdog/account-mode says `primary` (or is absent, which reads the same), so
# an enabled second account plus `primary` is a key with a cap and nowhere to
# dispatch — the idle-slot failure of 2026-09-12 intervention 2, invisible
# except as deaths in the AIMD.  run_mode.py derives the file from
# accounts[].enabled on apply, pause and resume; this checks that it landed.
AM="$(cat "$W/account-mode" 2>/dev/null || echo absent)"
AM_WANT="$(python3 "$RUN_MODE" get account_mode 2>/dev/null || echo unknown)"
if [ "$AM_WANT" != unknown ] && [ "$AM" != "$AM_WANT" ]; then
  echo "$PROG: POST-CONDITION: $W/account-mode is '$AM', and accounts[].enabled derives '$AM_WANT'" >&2
  echo "$PROG: with 'primary' the codex shim exits 4 for every non-default CODEX_HOME:" >&2
  echo "$PROG: an enabled second account would hold a cap and dispatch nowhere." >&2
  echo "$PROG: fix with: python3 $RUN_MODE resume   (it writes the file)" >&2
  RC=5
else
  printf '  %-10s %s (derived from accounts[].enabled)\n' account-mode "$AM"
fi
if [ -e "$W/drain" ]; then echo "$PROG: POST-CONDITION: watchdog/drain still exists" >&2; RC=5; fi
if [ -e "$W/goal-hold" ]; then echo "$PROG: POST-CONDITION: watchdog/goal-hold still exists" >&2; RC=5; fi
if [ ! -s "$W/max-codex" ]; then echo "$PROG: POST-CONDITION: $W/max-codex is missing or empty" >&2; RC=5; fi

python3 - "$ROOT/results/telemetry/stages.jsonl" "$PAUSED_AT" "$ONELINE" <<'PY'
import datetime, json, sys
row = {"ts": datetime.datetime.now().astimezone().strftime("%Y-%m-%dT%H:%M:%S%z"),
       "stage": "operator", "event": "resume",
       "note": ("owner resume from watchdog/pause-state.json (paused at %s): caps, speed and "
                "crontab restored verbatim from the record, daemon/stack-watch/keeper restarted, "
                "one resume message rendered from run-mode (%s)" % (sys.argv[2], sys.argv[3]))}
with open(sys.argv[1], "a", encoding="utf-8") as fh:
    fh.write(json.dumps(row) + "\n")
PY
BR="$(git -C "$ROOT" rev-parse --abbrev-ref HEAD 2>/dev/null || echo unknown)"
if [ "$BR" = main ]; then
  git -C "$ROOT" commit -qm "chore(telemetry): resume of track A (owner word)" \
    -- results/telemetry/stages.jsonl 2>&1 | tail -n 1
  if [ -x "$ROOT/local/bin/checked-push.sh" ]; then
    "$ROOT/local/bin/checked-push.sh" --repo-root "$ROOT" github refs/heads/main:refs/heads/main \
      || echo "$PROG: the resume telemetry stays committed locally" >&2
  fi
fi

if [ "$RC" -ne 0 ]; then
  echo "$PROG: RESUME INCOMPLETE — the post-condition check failed; fix the lines above" >&2
  exit "$RC"
fi
log "resumed at $(date -u +%FT%TZ)"
exit 0
