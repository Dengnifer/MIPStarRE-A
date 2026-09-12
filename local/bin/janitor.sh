#!/usr/bin/env bash
#
# Usage: local/bin/janitor.sh [--dry-run] [--pass NAME]... [--list-passes]
#                             [--no-lock] [--report PATH] [--help]
#
# The self-repair pass.  ONE idempotent sweep, safe to run from cron or from the
# merge daemon's loop, that turns every terminal state the pipeline can reach
# into either a repair or a reported line.  Everything it does is selected by a
# record field — a session status, a marker's reason string, a PR state, a spool
# deadline — and never by a date glob or a filename digit filter.  The
# 2026-09-12 recovery script globbed `*20260912*.jsonl` and matched
# `/[0-9]{3}\.needs-attention$` with `-mmin -15`, so lanes below 100 and the 1xxx
# lanes were never repaired and a marker missed by one poll was never picked up
# again.  Nothing here has an age filter or a digit-count filter.
#
# The five passes, each independently guarded (one failing pass never aborts the
# others; a GitHub error is reported and retried next pass, never converted into
# a local success):
#
#   dead-sessions   results/telemetry/sessions.jsonl rows whose last status is
#                   `active` and whose process is gone.  When the capture ends in
#                   an exhausted reconnect, a 5xx or a concurrency refusal the
#                   same role is re-dispatched on the same PR and the same head,
#                   at most twice per (pr, role, head_sha), ledger
#                   $CACHE_ROOT/watchdog/janitor/retries.jsonl.  A capture that
#                   ends cleanly is NEVER re-dispatched.  The abandoned row is
#                   marked `failed` so telemetry stops showing it live.
#                   This is the recovery path for the 25 reviews that were re-run
#                   by hand after the 503 outage: review.sh retries only a
#                   pre-model death (ended-started < 15 s and tokens 0), so a
#                   reviewer that dies after twenty minutes at
#                   "Reconnecting... 5/5" leaves the PR pending forever.
#                   SCOPE: only a role with a re-dispatch entry point is
#                   re-dispatched, and today that is `reviewer` alone
#                   (review.sh, exact head, verdict supersedes).  A dead prover,
#                   orc or fixer is marked `failed` with a `residue` field in
#                   $CACHE_ROOT/watchdog/janitor/actions.jsonl and is the owning
#                   session's to re-plan; `local/bin/ready_report.py` counts
#                   those rows PER ROLE into the hourly comment on the progress
#                   issue, so the unrepaired remainder reaches the owner's
#                   channel instead of a local log.
#   parked-lanes    every $CACHE_ROOT/watchdog/lanes/*.needs-attention, no digit
#                   filter and no age filter.  The recorded reason is classified;
#                   `merge` and `build` go to fix-lane.sh with the committed
#                   brief, at most twice per lane; every other class stays parked
#                   and appears in the report.
#   superseded-prs  local/bin/pr_janitor.py (empty three-dot diff AND head
#                   reachable from github/main; one idempotent marker comment;
#                   never closes an issue).
#   stale-lanes     lane state for lanes whose PR is closed or merged is deleted
#                   (20 stale 1xxx lanes were left behind on 2026-09-12).
#   spool-expiry    $CACHE_ROOT/watchdog/capacity/spool/*.json entries past the
#                   run's dispatch_cutoff are dropped, so a spool that outlives a
#                   run cannot re-launch stale work.
#   owner-accounts  `ACCOUNTS: <name> ceiling=<n> [reserved=<n>]
#                   [enabled=true|false]` comments on the owner inbox issue are
#                   applied to the live accounts file and answered with one
#                   `applied:` / `rejected:` reply per comment
#                   (local/bin/accounts_inbox.py).  ONLY comments written by the
#                   repository owner login are applied; the author check, the
#                   parsing and the validation live in that tool and in
#                   local/bin/accounts_file.py, never here.  It is the owner's
#                   channel for a ceiling change when they are away from a
#                   shell: on 2026-09-12 every such change was a message to a
#                   session that had to be idle to receive it.
#
# The janitor repairs; it never merges, never pushes, never closes an issue and
# never touches a gate.  Repairs are dispatched through fix-lane.sh ->
# dispatch.sh (agents never invoke codex directly) and the lane tail is
# relaunched through the repository's own local/bin/lane.sh.
#
# Runner: results/telemetry/owner-tools/merge-daemon.sh calls this once every
# `janitor_interval_s` (daemon.conf), detached and bounded; the sweep takes its
# own lock, so an overlapping call exits instead of doubling up.  Nothing else
# runs it: a checkout whose merge daemon is not running has no self-repair.
#
# Output: one line per action on stdout, the same lines in
# $CACHE_ROOT/watchdog/janitor/report.md (the operator's log of the sweep; the
# hourly readiness report does NOT read it — it reports merges and readiness
# from daemon state) and one append-only JSONL row per action in
# $CACHE_ROOT/watchdog/janitor/{retries,repairs,actions,closures}.jsonl.
#
# Exit codes: 0 all passes completed; 1 at least one pass failed (the others
# still ran); 2 usage/environment error.
#
# Environment:
#   MIPSTARRE_CACHE_ROOT             override ~/.cache/mipstarre-dev
#   MIPSTARRE_REPO_ROOT              override the checkout (default: this file's)
#   MIPSTARRE_JANITOR_RETRY_CAP      re-dispatches per (pr, role, head)  [2]
#   MIPSTARRE_JANITOR_REPAIR_CAP     repairs per lane                    [2]
#   MIPSTARRE_JANITOR_STALE_S        a dead session's capture must be this old
#                                    before it is judged abandoned       [900]
#   MIPSTARRE_JANITOR_LANE_KEEP_S    lane state younger than this is never
#                                    deleted                             [3600]
#   MIPSTARRE_JANITOR_REDISPATCH_ROLES  roles the janitor may re-dispatch
#                                    automatically; only a role with an entry
#                                    point below may be listed    [reviewer]
#   MIPSTARRE_JANITOR_CLASSIFIER     auto | builtin  (auto prefers telemetry.py's
#                                    classify-failure when it exists)    [auto]
#   MIPSTARRE_JANITOR_SOURCE_ONLY=1  define the functions and return; run nothing
#                                    (used by scripts/tests/test_janitor_classify.py)

set -uo pipefail

PROG="janitor.sh"

SCRIPT_DIR="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd)"
REPO_ROOT="${MIPSTARRE_REPO_ROOT:-$(cd -- "$SCRIPT_DIR/../.." && pwd)}"
CACHE_ROOT="${MIPSTARRE_CACHE_ROOT:-$HOME/.cache/mipstarre-dev}"
W="$CACHE_ROOT/watchdog"
L="$W/lanes"
D="$W/daemon"
J="$W/janitor"
SPOOL="$W/capacity/spool"
SESSIONS="${MIPSTARRE_SESSIONS_JSONL:-$REPO_ROOT/results/telemetry/sessions.jsonl}"

RETRY_CAP="${MIPSTARRE_JANITOR_RETRY_CAP:-2}"
REPAIR_CAP="${MIPSTARRE_JANITOR_REPAIR_CAP:-2}"
STALE_S="${MIPSTARRE_JANITOR_STALE_S:-900}"
LANE_KEEP_S="${MIPSTARRE_JANITOR_LANE_KEEP_S:-3600}"
REDISPATCH_ROLES="${MIPSTARRE_JANITOR_REDISPATCH_ROLES:-reviewer}"
CLASSIFIER="${MIPSTARRE_JANITOR_CLASSIFIER:-auto}"
BASE_REF="${MIPSTARRE_BASE_REF:-github/main}"

DRY_RUN=0
USE_LOCK=1
REPORT_FILE=""
PASS_FAILURES=0

ALL_PASSES="dead-sessions parked-lanes superseded-prs stale-lanes spool-expiry owner-accounts"
SELECTED="$ALL_PASSES"

# Report lines are collected in a file, not a variable: each pass runs in its own
# subshell so that one failing pass cannot abort the others, and a variable would
# not survive that boundary.
REPORT_SPOOL="${MIPSTARRE_JANITOR_REPORT_SPOOL:-$J/.report-lines.$$}"

# --------------------------------------------------------------- small helpers

now() { date -u +%FT%TZ; }

log() { printf '== %s %s\n' "$(now)" "$*"; }

# A reported line: printed, kept for report.md, and never silent.
report() {
  printf '%s\n' "$*"
  mkdir -p "$(dirname "$REPORT_SPOOL")" 2>/dev/null || return 0
  printf '%s\n' "$*" >> "$REPORT_SPOOL" 2>/dev/null || true
}

json_row() {
  python3 -c 'import json,sys; print(json.dumps(dict(zip(sys.argv[1::2], sys.argv[2::2])), ensure_ascii=False))' "$@"
}

# Append-only JSONL under the cache root.  One short line per append, written
# with a single write(2), which is atomic for a line this size; the janitor also
# holds its own lock, so two passes never interleave.
ledger_append() {
  local file="$1"; shift
  mkdir -p "$(dirname "$file")" 2>/dev/null || return 1
  printf '%s\n' "$(json_row "$@")" >> "$file"
}

# Count attempt rows in a ledger for one key.  Field-based, never a date glob.
ledger_count() {
  JAN_LEDGER="$1" JAN_KEY="$2" python3 - <<'PY'
import json, os
path, key, total = os.environ["JAN_LEDGER"], os.environ["JAN_KEY"], 0
try:
    with open(path, encoding="utf-8", errors="replace") as handle:
        for line in handle:
            line = line.strip()
            if not line:
                continue
            try:
                row = json.loads(line)
            except ValueError:
                continue
            if isinstance(row, dict) and row.get("key") == key and row.get("event") == "attempt":
                total += 1
except FileNotFoundError:
    pass
print(total)
PY
}

retry_key() { printf 'pr%s:%s:%s\n' "$1" "$2" "$3"; }

# Exit 0 while another attempt is allowed.  The cap is on attempts, not on
# successes: a re-dispatch that dies again counts.
retry_allow() {
  local key="$1" seen
  seen="$(ledger_count "$J/retries.jsonl" "$key")"
  [ "${seen:-0}" -lt "$RETRY_CAP" ]
}

# The `attempt` rows of the repair ledger are written by fix-lane.sh — the one
# entry point both the merge daemon and this janitor use — so a lane repaired
# twice by the daemon is at its cap here too, and a repair that died before it
# reached the worktree still counts.
repair_allow() {
  local lane="$1" seen
  seen="$(ledger_count "$J/repairs.jsonl" "lane:$lane")"
  [ "${seen:-0}" -lt "$REPAIR_CAP" ]
}

# --------------------------------------------------- classification (pure)

# classify_reason TEXT -> the class of a parked lane, from the reason the lane
# runner recorded in <N>.needs-attention.  The strings are lane.sh's own fail()
# messages; order matters, the most specific first.
classify_reason() {
  local text="$1"
  case "$text" in
    *"left paths missing that main carries"*|*"merge_loss_guard"*) echo "merge-loss" ;;
    *"merging github/main conflicted"*|*"merge conflicted"*|*"CONFLICT"*) echo "merge" ;;
    *"lake build before push failed"*|*"lake build of changed modules failed"*|\
    *"lake build"*failed*|*"build failed"*) echo "build" ;;
    *"pre-push gate failed"*|*"gate failed"*) echo "gate" ;;
    *"no commits ahead"*) echo "no-commits" ;;
    *"left uncommitted changes"*|*"uncommitted worker changes"*) echo "dirty-worktree" ;;
    *"worktree-mismatch"*|*"worktree holds"*|*"different branch than the PR"*) echo "worktree-mismatch" ;;
    *"no-slot"*|*"no free slot"*|*"no account slot"*) echo "no-slot" ;;
    *"pr_open failed"*|*"pr_open.py"*failed*) echo "pr-open" ;;
    *) echo "unknown" ;;
  esac
}

# Only these two classes have a repair brief; everything else stays parked and
# is reported for the operator.
repairable_class() {
  case "$1" in merge|build) return 0 ;; *) return 1 ;; esac
}

# capture_class FILE -> how a captured `codex exec --json` stream ended.
#   clean               a completed turn is the last event   -> never re-dispatch
#   reconnect-exhausted "Reconnecting... N/N" (the retry budget ran out)
#   endpoint-5xx        503/502/500 from the endpoint
#   concurrency-limit   the provider refused the session (concurrency / 429)
#   empty               no capture, or an empty one
#   unknown             anything else -> reported, never re-dispatched
capture_class_builtin() {
  local file="$1" last=""
  [ -n "$file" ] && [ -s "$file" ] || { echo "empty"; return 0; }
  last="$(grep -v '^[[:space:]]*$' "$file" 2>/dev/null | tail -n 1)"
  # A clean end wins over anything earlier in the stream: a session that
  # reconnected once and then finished its turn is not a failure.
  case "$last" in
    *'"type":"turn.completed"'*|*'"type": "turn.completed"'*|\
    *'"type":"thread.completed"'*|*'"type": "thread.completed"'*|\
    *'"type":"session.completed"'*|*'"type": "session.completed"'*|\
    *'"type":"response.completed"'*|*'"type": "response.completed"'*)
      echo "clean"; return 0 ;;
  esac
  if grep -qE 'Reconnecting\.\.\.? ([0-9]+)/\1' "$file" 2>/dev/null; then
    echo "reconnect-exhausted"; return 0
  fi
  if grep -qE '50[0-9] (Service Unavailable|Bad Gateway|Internal Server Error)|HTTP 5[0-9][0-9]|"status": ?5[0-9][0-9]' "$file" 2>/dev/null; then
    echo "endpoint-5xx"; return 0
  fi
  if grep -qiE 'concurrency limit|too many requests|429|rate.?limit' "$file" 2>/dev/null; then
    echo "concurrency-limit"; return 0
  fi
  echo "unknown"
}

# `auto` prefers telemetry.py's classify-failure (W2) when that subcommand
# exists, so there is one classifier for the whole pipeline; it falls back to the
# builtin patterns above when it does not, and whenever it errors.
capture_class() {
  local file="$1" out=""
  if [ "$CLASSIFIER" = builtin ] || [ ! -f "$SCRIPT_DIR/telemetry.py" ]; then
    capture_class_builtin "$file"; return 0
  fi
  if python3 "$SCRIPT_DIR/telemetry.py" classify-failure --help >/dev/null 2>&1; then
    out="$(python3 "$SCRIPT_DIR/telemetry.py" classify-failure "$file" \
            --field failure_class 2>/dev/null | tail -n 1)"
    case "$out" in
      endpoint_5xx|endpoint-5xx) echo "endpoint-5xx"; return 0 ;;
      concurrency_limit|concurrency-limit|refused) echo "concurrency-limit"; return 0 ;;
      retries_exhausted|reconnect_exhausted) echo "reconnect-exhausted"; return 0 ;;
      none|clean|completed) echo "clean"; return 0 ;;
    esac
  fi
  capture_class_builtin "$file"
}

# A dead session is re-dispatched only for these classes.
redispatchable_class() {
  case "$1" in reconnect-exhausted|endpoint-5xx|concurrency-limit) return 0 ;; *) return 1 ;; esac
}

# Only a role whose re-dispatch is a pure re-run of the same work may be
# automated.  `reviewer` is exactly that: review.sh reviews the PR's exact head
# and its verdict supersedes, so a re-run cannot duplicate work.  A prover's
# unfinished packet is re-planned by its owning session (events.md 2026-09-12
# 06:38Z: "Meta owns failed reviewer retries"), so every other role is reported,
# not re-dispatched, unless an operator widens this list deliberately.
role_redispatchable() {
  local role="$1" allowed
  for allowed in $REDISPATCH_ROLES; do
    [ "$role" = "$allowed" ] && return 0
  done
  return 1
}

# lane_id_of PATH -> the lane number of any $L/<N>.<suffix> file.  Every number
# is accepted: lane 7 and lane 1342 are equally real (the /tmp poll's
# /[0-9]{3}\.needs-attention$ filter is exactly what left them unrepaired).
lane_id_of() {
  local base id
  base="$(basename -- "$1")"
  id="${base%%.*}"
  case "$id" in ''|*[!0-9]*) return 1 ;; esac
  printf '%s\n' "$id"
}

# Every marker, no -mmin window: a marker missed by one poll must still be seen.
list_lane_markers() {
  local file
  [ -d "$L" ] || return 0
  for file in "$L"/*.needs-attention; do
    [ -e "$file" ] || continue
    printf '%s\n' "$file"
  done
}

# spool_is_expired FILE CUTOFF_ISO -> exit 0 when the entry may not be launched.
# An entry is expired when its own deadline has passed or when the run's
# dispatch_cutoff has.  An unparsable entry is NOT expired (it is reported).
spool_is_expired() {
  JAN_FILE="$1" JAN_CUTOFF="${2:-}" python3 - <<'PY'
import json, os, sys
from datetime import datetime, timezone

def parse(value):
    if not value:
        return None
    text = str(value).strip().replace("Z", "+00:00")
    try:
        stamp = datetime.fromisoformat(text)
    except ValueError:
        return None
    return stamp if stamp.tzinfo else stamp.replace(tzinfo=timezone.utc)

try:
    entry = json.load(open(os.environ["JAN_FILE"], encoding="utf-8"))
except Exception:
    sys.exit(1)
now = datetime.now(timezone.utc)
cutoff = parse(os.environ.get("JAN_CUTOFF"))
deadline = parse(entry.get("deadline") if isinstance(entry, dict) else None)
sys.exit(0 if ((deadline and deadline <= now) or (cutoff and cutoff <= now)) else 1)
PY
}

# The run's dispatch cutoff, from run-mode (W1) and then from the mode file.
dispatch_cutoff() {
  local value=""
  if [ -x "$SCRIPT_DIR/run_mode.py" ] || [ -f "$SCRIPT_DIR/run_mode.py" ]; then
    value="$(python3 "$SCRIPT_DIR/run_mode.py" get dispatch_cutoff 2>/dev/null | tail -n 1)"
  fi
  if [ -z "$value" ] && [ -s "$W/run-mode.json" ]; then
    value="$(JAN_MODE="$W/run-mode.json" python3 - <<'PY'
import json, os
try:
    mode = json.load(open(os.environ["JAN_MODE"], encoding="utf-8"))
    value = (mode.get("run") or {}).get("dispatch_cutoff") or ""
except Exception:
    value = ""
print(value if isinstance(value, str) else "")
PY
)"
  fi
  case "$value" in
    ""|null|"until my word") printf '' ;;
    *) printf '%s' "$value" ;;
  esac
}

# --------------------------------------------------------------- process probes

process_matches() { pgrep -f "$1" >/dev/null 2>&1; }

# setsid detaches a launched worker from this pass's session so a cron timeout
# cannot take its children down; where it does not exist, nohup alone is used.
DETACH=""
command -v setsid >/dev/null 2>&1 && DETACH="setsid"

lane_is_running() {
  local lane="$1"
  process_matches "lane\.sh $lane( |$)" && return 0
  process_matches "lane-v[0-9]*\.sh $lane( |$)" && return 0
  return 1
}

fixer_is_running() {
  process_matches "fix-lane\.sh $1( |$)"
}

fix_lane_cmd() {
  local installed="$CACHE_ROOT/owner-bin/fix-lane.sh"
  local checked_out="$REPO_ROOT/results/telemetry/owner-tools/fix-lane.sh"
  if [ -f "$installed" ]; then printf '%s\n' "$installed"
  elif [ -f "$checked_out" ]; then printf '%s\n' "$checked_out"
  else return 1; fi
}

daemon_scan_cmd() {
  local installed="${MIPSTARRE_OWNER_BIN:-$CACHE_ROOT/owner-bin}/daemon-scan.py"
  local checked_out="$REPO_ROOT/results/telemetry/owner-tools/daemon-scan.py"
  if [ -r "$installed" ]; then printf '%s\n' "$installed"
  elif [ -r "$checked_out" ]; then printf '%s\n' "$checked_out"
  else return 1; fi
}

# The daemon's failure marker, written by the daemon's own writer.  A marker is a
# JSON record {pr, head, ts, class, reason, attempts, lane_log} whose class decides
# the backoff; a bare `touch` produces an empty file that daemon-scan.py degrades to
# class `infra`, and the infra backoff clears it after five minutes — so the "hold
# this PR while it is being repaired" marker would expire while the repair runs.
# There is deliberately NO `touch` fallback: no marker at all is honest, an
# unclassed one is a five-minute lie.
write_repair_marker() { # write_repair_marker PR LANE JANITOR_CLASS REASON
  local pr="$1" lane="$2" cls="$3" reason="$4" scan head version
  case "$cls" in
    merge) cls=conflict ;;
    build) cls=build ;;
    *) report "janitor: refusing to write a marker for PR $pr: class '$cls' is not repairable"
       return 1 ;;
  esac
  scan="$(daemon_scan_cmd)" || {
    report "janitor: no daemon-scan.py; PR $pr is repaired WITHOUT a failure marker"
    return 1; }
  head="$(timeout 60 gh pr view "$pr" --json headRefOid --jq .headRefOid 2>/dev/null </dev/null || true)"
  version="$(head -n 1 "${MIPSTARRE_OWNER_BIN:-$CACHE_ROOT/owner-bin}/tools-version" 2>/dev/null | tr -d '\n')"
  timeout 60 python3 "$scan" marker-write --path "$D/pr$pr.failed" --pr "$pr" \
    --head "${head:-}" --class "$cls" --reason "${reason:0:200}" \
    --lane-log "$L/$lane.lane.log" --tools-version "${version:-uninstalled}" \
    >/dev/null 2>&1 && return 0
  report "janitor: daemon-scan.py marker-write failed for PR $pr (class $cls)"
  return 1
}

# --------------------------------------------------------------- GitHub reads

# One open PR for a branch, or empty.  Reads are wrapped so a GitHub failure is a
# reported blank, never a wrong decision (the caller skips the lane).
pr_for_branch() {
  local branch="$1"
  timeout 60 python3 "$SCRIPT_DIR/gh_common.py" pr-for-branch "$branch" 2>/dev/null \
    | python3 -c 'import json,sys
try:
    row = json.load(sys.stdin)
except Exception:
    row = None
print(row["number"] if isinstance(row, dict) and row.get("number") else "")'
}

# The state of the newest PR for a branch in ANY state: open | closed | merged | "".
pr_state_for_branch() {
  local branch="$1" slug
  slug="$(timeout 60 python3 "$SCRIPT_DIR/gh_common.py" repo-slug 2>/dev/null | tail -n 1)"
  [ -n "$slug" ] || return 0
  JAN_SLUG="$slug" JAN_BRANCH="$branch" JAN_BIN="$SCRIPT_DIR" timeout 90 python3 - <<'PY'
import os, sys
sys.path.insert(0, os.environ["JAN_BIN"])
import urllib.parse
try:
    import gh_common
    owner = os.environ["JAN_SLUG"].split("/")[0]
    head = urllib.parse.quote(f"{owner}:{os.environ['JAN_BRANCH']}", safe=":")
    rows = gh_common.api(f"pulls?state=all&head={head}", paginate=True) or []
except Exception:
    print("")
    raise SystemExit(0)
rows.sort(key=lambda row: int(row.get("number") or 0))
if not rows:
    print("")
else:
    row = rows[-1]
    state = "merged" if row.get("merged_at") else (row.get("state") or "")
    print(f"{row.get('number')} {state}")
PY
}

# --------------------------------------------------- branch of a lane

# Resolved from the record, in order: the marker's worktree path, a recorded
# branch file, the lane's task header, the operator's dispatch record.  Never
# guessed from the lane number (lane id and issue number disagree by design for
# the 1xxx lanes the 2026-09-12 run created).
lane_branch() {
  local lane="$1" branch="" text=""
  if [ -s "$L/$lane.branch" ]; then
    branch="$(head -n 1 "$L/$lane.branch")"
  fi
  if [ -z "$branch" ] && [ -s "$L/$lane.needs-attention" ]; then
    text="$(grep -o '\.worktrees/[^ ]*' "$L/$lane.needs-attention" | head -n 1)"
    branch="${text#.worktrees/}"
  fi
  if [ -z "$branch" ] && [ -s "$L/$lane.task.md" ]; then
    branch="$(sed -n 's/.*(branch \([^)]*\)).*/\1/p' "$L/$lane.task.md" | head -n 1)"
  fi
  if [ -z "$branch" ] && [ -s "$W/meta-dispatched.txt" ]; then
    branch="$(awk -v lane="$lane" '$1=="lane" && $2==lane {print $5; exit}' "$W/meta-dispatched.txt")"
  fi
  if [ -z "$branch" ] && [ -s "$L/$lane.lane.log" ]; then
    text="$(grep -o '\.worktrees/[^ ]*' "$L/$lane.lane.log" | head -n 1)"
    branch="${text#.worktrees/}"
  fi
  printf '%s\n' "${branch%/}"
}

# =========================================================== pass 1: sessions

# Emits one row per abandoned `active` session, fields separated by US (\037):
#   name role pr issue head worktree capture account reason
# The separator is deliberately NOT a tab: `read` collapses runs of IFS
# whitespace, so two empty fields in a row would shift every later column.
dead_session_rows() {
  JAN_SESSIONS="$SESSIONS" JAN_CACHE="$CACHE_ROOT" JAN_REPO="$REPO_ROOT" \
  JAN_STALE_S="$STALE_S" JAN_DRY="$DRY_RUN" JAN_BIN="$SCRIPT_DIR" python3 - <<'PY'
import json, os, subprocess, sys, time
from pathlib import Path

sys.path.insert(0, os.environ["JAN_BIN"])

cache = Path(os.environ["JAN_CACHE"])
repo = Path(os.environ["JAN_REPO"])
stale_s = float(os.environ.get("JAN_STALE_S") or 900)
dry_run = os.environ.get("JAN_DRY") == "1"
registry = Path(os.environ["JAN_SESSIONS"])

accounts_dir = cache / "accounts"


def router_live_pids() -> set:
    """Live dispatcher pids, through the router's own reaper when not dry-running."""
    pids = set()
    if not accounts_dir.is_dir():
        return pids
    if not dry_run:
        try:
            import account_router
            for account in accounts_dir.iterdir():
                if account.is_dir():
                    pids |= account_router.live_pids(account)
            return pids
        except Exception:
            pass
    for account in accounts_dir.iterdir():
        if not account.is_dir():
            continue
        for marker in account.iterdir():
            if marker.name.isdecimal() and int(marker.name) > 0:
                pids.add(int(marker.name))
    return pids


def pid_alive(pid: int) -> bool:
    try:
        os.kill(pid, 0)
    except ProcessLookupError:
        return False
    except PermissionError:
        return True
    except OSError:
        return True
    return True


def pgrep(pattern: str) -> bool:
    return subprocess.run(["pgrep", "-f", pattern],
                          capture_output=True, text=True).returncode == 0


def rows_by_name(path: Path) -> dict:
    """Last row per session name wins: the registry is append-only and a later
    line supersedes an earlier one (meta.md, 'Two memory disciplines')."""
    latest = {}
    try:
        handle = path.open(encoding="utf-8", errors="replace")
    except FileNotFoundError:
        return latest
    with handle:
        for line in handle:
            line = line.strip()
            if not line:
                continue
            try:
                row = json.loads(line)
            except ValueError:
                continue
            if isinstance(row, dict) and row.get("name"):
                latest[row["name"]] = row
    return latest


def capture_of(row):
    candidates = []
    raw = row.get("capture")
    if raw:
        path = Path(raw)
        candidates.append(path if path.is_absolute() else repo / path)
    name = row.get("name") or ""
    if name:
        candidates.append(cache / "sessions" / f"{name}.jsonl")
        candidates.append(repo / "results" / "telemetry" / "sessions" / f"{name}.jsonl")
    for candidate in candidates:
        try:
            if candidate.is_file():
                return candidate
        except OSError:
            continue
    return None


SEP = "\x1f"


def clean(value) -> str:
    text = str(value if value is not None else "")
    for bad in ("\t", "\n", "\r", SEP):
        text = text.replace(bad, " ")
    return text


live = router_live_pids()
now = time.time()
for name, row in sorted(rows_by_name(registry).items()):
    if row.get("status") != "active":
        continue
    capture = capture_of(row)
    pid = row.get("pid") or row.get("dispatch_pid")
    reason = ""
    try:
        pid = int(pid) if pid is not None else None
    except (TypeError, ValueError):
        pid = None
    if pid is not None:
        if pid in live or pid_alive(pid):
            continue
        reason = f"pid {pid} is gone"
    else:
        # No pid on the row: the dispatcher that owns the capture is the
        # process to look for, and the capture must also have gone quiet.
        if capture is not None and pgrep(str(capture)):
            continue
        if pgrep(f"[ =]{name}( |$)"):
            continue
        try:
            age = now - capture.stat().st_mtime if capture is not None else stale_s + 1
        except OSError:
            age = stale_s + 1
        if age < stale_s:
            continue
        reason = f"no live process and the capture has been quiet for {int(age)}s"
    print(SEP.join(clean(value) for value in (
        name, row.get("role") or "", row.get("pr") or "", row.get("issue") or "",
        row.get("head") or row.get("head_sha") or "", row.get("worktree") or "",
        str(capture) if capture else "", row.get("account") or "", reason)))
PY
}

mark_session_failed() {
  local name="$1" note="$2"
  [ "$DRY_RUN" -eq 1 ] && return 0
  python3 "$SCRIPT_DIR/telemetry.py" --repo-root "$REPO_ROOT" session-status \
    --name "$name" --status failed --registry "$SESSIONS" \
    --note "janitor: $note" >/dev/null 2>&1
}

pass_dead_sessions() {
  local name role pr issue head worktree capture account reason class key seen cmd log_file
  local rows
  rows="$(dead_session_rows)" || { report "janitor: dead-sessions: cannot read $SESSIONS"; return 1; }
  [ -n "$rows" ] || { report "janitor: dead-sessions: none"; return 0; }
  while IFS=$'\037' read -r name role pr issue head worktree capture account reason; do
    [ -n "$name" ] || continue
    class="$(capture_class "$capture")"
    if ! redispatchable_class "$class"; then
      report "janitor: dead session $name (role ${role:-?}, pr ${pr:-none}): $reason; capture ended '$class' -> not re-dispatched, marked failed"
      mark_session_failed "$name" "$reason; capture ended $class; not re-dispatched"
      ledger_append "$J/actions.jsonl" ts "$(now)" pass dead-sessions action mark-failed \
        session "$name" role "$role" pr "$pr" issue "$issue" account "$account" \
        worktree "$worktree" capture_class "$class" reason "$reason" \
        residue capture-ended-cleanly dry_run "$DRY_RUN"
      continue
    fi
    if [ -z "$pr" ]; then
      report "janitor: dead session $name (role ${role:-?}): capture ended '$class' but the row carries no PR -> reported, marked failed"
      mark_session_failed "$name" "$reason; capture ended $class; no PR on the row"
      ledger_append "$J/actions.jsonl" ts "$(now)" pass dead-sessions action mark-failed \
        session "$name" role "$role" pr "$pr" issue "$issue" account "$account" \
        worktree "$worktree" capture_class "$class" reason "$reason" \
        residue no-pr-on-the-row dry_run "$DRY_RUN"
      continue
    fi
    if ! role_redispatchable "$role"; then
      report "janitor: dead session $name (role ${role:-?}, PR $pr): capture ended '$class' -> reported for the owning session (role not in MIPSTARRE_JANITOR_REDISPATCH_ROLES)"
      mark_session_failed "$name" "$reason; capture ended $class; role $role is not auto-re-dispatched"
      # The residue the janitor does NOT repair.  Only `reviewer` has an entry
      # point whose re-run is a pure re-run (review.sh, exact head); a dead
      # prover, orc or fixer is the owning session's to re-plan.  That is a
      # deliberate scope, not an omission — but on 2026-09-12 roughly ninety
      # sessions died across all roles and the residue existed only in a local
      # report file nothing read, so the meta re-dispatched them by hand.  This
      # row is what `ready_report.py` counts per role into the hourly comment.
      ledger_append "$J/actions.jsonl" ts "$(now)" pass dead-sessions action mark-failed \
        session "$name" role "$role" pr "$pr" issue "$issue" account "$account" \
        worktree "$worktree" capture_class "$class" reason "$reason" \
        residue role-not-auto-re-dispatched dry_run "$DRY_RUN"
      continue
    fi
    if [ -z "$head" ]; then
      head="$(timeout 60 python3 "$SCRIPT_DIR/gh_common.py" pr-view "$pr" 2>/dev/null \
        | python3 -c 'import json,sys
try:
    print((json.load(sys.stdin).get("head") or {}).get("sha") or "")
except Exception:
    print("")')"
    fi
    if [ -z "$head" ]; then
      report "janitor: dead session $name (PR $pr): head SHA unknown (GitHub read failed) -> left for the next pass"
      continue
    fi
    key="$(retry_key "$pr" "$role" "$head")"
    if ! retry_allow "$key"; then
      seen="$(ledger_count "$J/retries.jsonl" "$key")"
      report "janitor: dead session $name (PR $pr, $role, head ${head:0:12}): re-dispatch cap reached ($seen/$RETRY_CAP) -> stays reported"
      mark_session_failed "$name" "$reason; capture ended $class; retry cap $RETRY_CAP reached"
      ledger_append "$J/actions.jsonl" ts "$(now)" pass dead-sessions action mark-failed \
        session "$name" role "$role" pr "$pr" issue "$issue" account "$account" \
        worktree "$worktree" capture_class "$class" reason "$reason" \
        residue retry-cap-reached dry_run "$DRY_RUN"
      continue
    fi
    if process_matches "review\.sh $pr( |$)"; then
      report "janitor: dead session $name (PR $pr): a $role is already running for that PR -> nothing dispatched"
      mark_session_failed "$name" "$reason; capture ended $class; a live $role already covers PR $pr"
      continue
    fi
    if [ "$DRY_RUN" -eq 1 ]; then
      # A dry run must not consume the retry budget, so nothing is appended here.
      report "janitor: dead session $name (PR $pr, $role, head ${head:0:12}): would re-dispatch (dry run)"
      continue
    fi
    log_file="$L/pr$pr.$role-rerun.log"
    cmd="$REPO_ROOT/local/bin/review.sh"
    if [ ! -x "$cmd" ]; then
      report "janitor: dead session $name (PR $pr): $cmd missing -> reported, nothing dispatched"
      continue
    fi
    # The ledger row is written BEFORE the launch: a janitor that dies between
    # the two must not forget that an attempt was made.
    mark_session_failed "$name" "$reason; capture ended $class; re-dispatched on head ${head:0:12}"
    ledger_append "$J/retries.jsonl" ts "$(now)" key "$key" event attempt action redispatch \
      session "$name" role "$role" pr "$pr" issue "$issue" head "$head" \
      account "$account" worktree "$worktree" capture_class "$class" reason "$reason"
    ( cd "$REPO_ROOT" && MIPSTARRE_CACHE_ROOT="$CACHE_ROOT" \
        $DETACH nohup "$cmd" "$pr" > "$log_file" 2>&1 < /dev/null & )
    report "janitor: dead session $name (PR $pr, $role, head ${head:0:12}) ended '$class' -> re-dispatched, log $log_file"
    ledger_append "$J/actions.jsonl" ts "$(now)" pass dead-sessions action redispatch \
      session "$name" role "$role" pr "$pr" head "$head" capture_class "$class" log "$log_file"
  done <<EOF
$rows
EOF
  return 0
}

# =========================================================== pass 2: lanes

pass_parked_lanes() {
  local marker lane text class branch pr fixer mode seen
  local found=0
  while IFS= read -r marker; do
    [ -n "$marker" ] || continue
    found=1
    if ! lane="$(lane_id_of "$marker")"; then
      report "janitor: parked lane: $marker has no lane number -> reported, untouched"
      continue
    fi
    text="$(tr '\n' ' ' < "$marker" 2>/dev/null)"
    class="$(classify_reason "$text")"
    branch="$(lane_branch "$lane")"
    if ! repairable_class "$class"; then
      report "janitor: lane $lane parked (class $class${branch:+, branch $branch}) -> stays parked: ${text:0:120}"
      continue
    fi
    if lane_is_running "$lane"; then
      report "janitor: lane $lane parked (class $class) but a lane process is running -> left alone"
      continue
    fi
    if [ -z "$branch" ]; then
      report "janitor: lane $lane parked (class $class) but its branch could not be resolved from the record -> stays parked"
      continue
    fi
    pr="$(pr_for_branch "$branch")"
    if [ -z "$pr" ]; then
      report "janitor: lane $lane parked (class $class, branch $branch) has no open PR -> stays parked (see the stale-lanes pass)"
      continue
    fi
    if fixer_is_running "$pr"; then
      report "janitor: lane $lane parked (class $class, PR $pr): a repair is already running -> left alone"
      continue
    fi
    if ! repair_allow "$lane"; then
      seen="$(ledger_count "$J/repairs.jsonl" "lane:$lane")"
      report "janitor: lane $lane parked (class $class, PR $pr): repair cap reached ($seen/$REPAIR_CAP) -> stays parked for the operator"
      continue
    fi
    if ! fixer="$(fix_lane_cmd)"; then
      report "janitor: lane $lane parked (class $class, PR $pr): no fix-lane.sh installed or in the checkout -> stays parked"
      continue
    fi
    mode="$class"
    if [ "$DRY_RUN" -eq 1 ]; then
      report "janitor: lane $lane parked (class $class, PR $pr, branch $branch): would run $fixer $pr $lane $branch $mode (dry run)"
      continue
    fi
    # A CLASSED marker, written the way the daemon writes one.  A bare `touch`
    # leaves an empty file that daemon-scan.py's load_marker degrades to class
    # `infra`, whose five-minute backoff clears it — so the "hold this PR while
    # it is repaired" marker would last five minutes and the daemon would queue
    # the PR back into the repair that is still running.
    write_repair_marker "$pr" "$lane" "$class" "$text"
    ledger_append "$J/actions.jsonl" ts "$(now)" pass parked-lanes action repair lane "$lane" \
      pr "$pr" branch "$branch" class "$class" tool "$fixer"
    ( cd "$REPO_ROOT" \
      && MIPSTARRE_REPO_ROOT="$REPO_ROOT" MIPSTARRE_CACHE_ROOT="$CACHE_ROOT" \
         $DETACH nohup bash "$fixer" "$pr" "$lane" "$branch" "$mode" \
        > "$L/$lane.fix.launch.log" 2>&1 < /dev/null & )
    report "janitor: lane $lane parked (class $class, PR $pr, branch $branch) -> $mode repair dispatched"
  done <<EOF
$(list_lane_markers)
EOF
  [ "$found" -eq 1 ] || report "janitor: parked-lanes: none"
  return 0
}

# =========================================================== pass 3: PRs

pass_superseded_prs() {
  local args=() out rc
  [ -f "$SCRIPT_DIR/pr_janitor.py" ] || { report "janitor: superseded-prs: pr_janitor.py missing"; return 1; }
  args=(--repo-root "$REPO_ROOT" --base "$BASE_REF" --report "$J/superseded.md")
  [ "$DRY_RUN" -eq 1 ] && args+=(--dry-run)
  out="$(timeout 900 python3 "$SCRIPT_DIR/pr_janitor.py" "${args[@]}" 2>&1)"
  rc=$?
  while IFS= read -r line; do
    [ -n "$line" ] && report "$line"
  done <<EOF
$out
EOF
  return "$rc"
}

# =========================================================== pass 4: lane state

pass_stale_lanes() {
  local lane branch state pr_state pr_number file newest
  local seen="" removed=0 examined=0
  [ -d "$L" ] || { report "janitor: stale-lanes: no lane state"; return 0; }
  for file in "$L"/*; do
    [ -e "$file" ] || continue
    lane="$(lane_id_of "$file")" || continue
    case " $seen " in *" $lane "*) continue ;; esac
    seen="$seen $lane"
    examined=$((examined + 1))
    if lane_is_running "$lane"; then
      continue
    fi
    # Freshness is the age of the YOUNGEST file of the lane: state a lane still
    # writes is never deleted, whatever the PR says.
    newest="$(python3 - "$L" "$lane" <<'PY'
import os, sys, time
directory, lane = sys.argv[1], sys.argv[2]
ages = []
for name in os.listdir(directory):
    if name.split(".")[0] == lane:
        try:
            ages.append(time.time() - os.path.getmtime(os.path.join(directory, name)))
        except OSError:
            pass
print(int(min(ages)) if ages else 0)
PY
)"
    if [ "${newest:-0}" -lt "$LANE_KEEP_S" ]; then
      continue
    fi
    branch="$(lane_branch "$lane")"
    if [ -z "$branch" ]; then
      report "janitor: lane $lane has stale state but no resolvable branch -> kept, reported"
      continue
    fi
    pr_state="$(pr_state_for_branch "$branch")"
    pr_number="${pr_state%% *}"
    state="${pr_state##* }"
    if [ -z "$pr_state" ] || [ -z "$pr_number" ]; then
      report "janitor: lane $lane ($branch): no PR found for the branch -> lane state kept, reported"
      continue
    fi
    case "$state" in
      closed|merged) ;;
      *) continue ;;
    esac
    if [ "$DRY_RUN" -eq 1 ]; then
      report "janitor: lane $lane ($branch): PR $pr_number is $state -> would delete $(ls "$L/$lane".* 2>/dev/null | wc -l | tr -d ' ') lane state file(s) (dry run)"
      continue
    fi
    ledger_append "$J/actions.jsonl" ts "$(now)" pass stale-lanes action delete-lane-state \
      lane "$lane" branch "$branch" pr "$pr_number" pr_state "$state" \
      files "$(ls "$L/$lane".* 2>/dev/null | tr '\n' ' ')"
    rm -f "$L/$lane".*
    removed=$((removed + 1))
    report "janitor: lane $lane ($branch): PR $pr_number is $state -> lane state deleted"
  done
  report "janitor: stale-lanes: $examined lane(s) examined, $removed cleared (state younger than ${LANE_KEEP_S}s is never touched)"
  return 0
}

# =========================================================== pass 5: spool

pass_spool_expiry() {
  local cutoff file dropped=0 kept=0
  [ -d "$SPOOL" ] || { report "janitor: spool-expiry: no spool"; return 0; }
  cutoff="$(dispatch_cutoff)"
  for file in "$SPOOL"/*.json; do
    [ -e "$file" ] || continue
    if spool_is_expired "$file" "$cutoff"; then
      if [ "$DRY_RUN" -eq 1 ]; then
        report "janitor: spool entry $(basename "$file") is past the dispatch cutoff -> would drop (dry run)"
      else
        ledger_append "$J/actions.jsonl" ts "$(now)" pass spool-expiry action drop-spool-entry \
          entry "$(basename "$file")" cutoff "${cutoff:-none}"
        rm -f "$file"
        report "janitor: spool entry $(basename "$file") is past the dispatch cutoff ${cutoff:-(entry deadline)} -> dropped"
      fi
      dropped=$((dropped + 1))
    else
      kept=$((kept + 1))
    fi
  done
  report "janitor: spool-expiry: $dropped dropped, $kept kept (cutoff ${cutoff:-none})"
  return 0
}

# =================================================== pass 6: owner accounts

pass_owner_accounts() {
  local args=() out rc
  [ -f "$SCRIPT_DIR/accounts_inbox.py" ] || {
    report "janitor: owner-accounts: accounts_inbox.py missing"; return 1; }
  [ "$DRY_RUN" -eq 1 ] && args+=(--dry-run)
  # Bounded like every other GitHub read here: a slow API delays one pass and
  # never holds the janitor's lock while the daemon waits to call it again.
  out="$(timeout 300 python3 "$SCRIPT_DIR/accounts_inbox.py" "${args[@]}" 2>&1)"
  rc=$?
  while IFS= read -r line; do
    [ -n "$line" ] && report "$line"
  done <<EOF
$out
EOF
  return "$rc"
}

# =========================================================== driver

run_pass() {
  local name="$1" fn="$2" rc=0
  case " $SELECTED " in *" $name "*) ;; *) return 0 ;; esac
  log "pass $name: start"
  ( "$fn" ); rc=$?
  if [ "$rc" -ne 0 ]; then
    PASS_FAILURES=$((PASS_FAILURES + 1))
    report "janitor: pass $name FAILED (rc=$rc); the other passes still ran"
  fi
  log "pass $name: done (rc=$rc)"
  return 0
}

version() {
  if [ -s "$CACHE_ROOT/owner-bin/tools-version" ]; then
    head -n 1 "$CACHE_ROOT/owner-bin/tools-version"
  else
    git -C "$REPO_ROOT" describe --always --dirty 2>/dev/null || echo unknown
  fi
}

usage() { sed -n '2,60p' "${BASH_SOURCE[0]}" | sed 's/^# \{0,1\}//'; }

main() {
  local chosen=""
  while [ $# -gt 0 ]; do
    case "$1" in
      --dry-run) DRY_RUN=1 ;;
      --no-lock) USE_LOCK=0 ;;
      --report) shift; REPORT_FILE="${1:-}" ;;
      --pass) shift; chosen="$chosen ${1:-}" ;;
      --list-passes) printf '%s\n' $ALL_PASSES; return 0 ;;
      -h|--help) usage; return 0 ;;
      *) printf '%s: unknown argument %s\n' "$PROG" "$1" >&2; return 2 ;;
    esac
    shift
  done
  if [ -n "$chosen" ]; then
    local pass
    for pass in $chosen; do
      case " $ALL_PASSES " in
        *" $pass "*) ;;
        *) printf '%s: unknown pass %s (have: %s)\n' "$PROG" "$pass" "$ALL_PASSES" >&2; return 2 ;;
      esac
    done
    SELECTED="$chosen"
  fi

  [ -d "$REPO_ROOT/local/bin" ] || { printf '%s: %s is not a checkout\n' "$PROG" "$REPO_ROOT" >&2; return 2; }
  mkdir -p "$J" "$L" "$D" "$CACHE_ROOT/locks" || { printf '%s: cannot create runtime state under %s\n' "$PROG" "$W" >&2; return 2; }

  if [ "$USE_LOCK" -eq 1 ] && command -v flock >/dev/null 2>&1; then
    exec 9>"$CACHE_ROOT/locks/janitor.lock"
    if ! flock -n 9; then
      log "another janitor pass is running; this one exits (idempotent by design)"
      return 0
    fi
  fi

  printf 'tool=%s version=%s\n' "$PROG" "$(version)"
  log "janitor start (repo $REPO_ROOT, cache $CACHE_ROOT, passes:$SELECTED, dry_run=$DRY_RUN)"

  run_pass dead-sessions  pass_dead_sessions
  run_pass parked-lanes   pass_parked_lanes
  run_pass superseded-prs pass_superseded_prs
  run_pass stale-lanes    pass_stale_lanes
  run_pass spool-expiry   pass_spool_expiry
  run_pass owner-accounts pass_owner_accounts

  {
    printf '# janitor report %s\n\n' "$(now)"
    if [ -s "$REPORT_SPOOL" ]; then sed 's/^/- /' "$REPORT_SPOOL"; else printf -- '- nothing to report\n'; fi
  } > "$J/report.md.tmp" 2>/dev/null && mv -f "$J/report.md.tmp" "$J/report.md" 2>/dev/null
  rm -f "$REPORT_SPOOL"
  if [ -n "$REPORT_FILE" ]; then
    cp -f "$J/report.md" "$REPORT_FILE" 2>/dev/null || true
  fi

  log "janitor done ($PASS_FAILURES failed pass(es); report $J/report.md)"
  [ "$PASS_FAILURES" -eq 0 ] || return 1
  return 0
}

if [ "${MIPSTARRE_JANITOR_SOURCE_ONLY:-0}" != "1" ]; then
  main "$@"
  exit $?
fi
