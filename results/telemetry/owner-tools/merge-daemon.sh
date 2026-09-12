#!/usr/bin/env bash
# merge-daemon.sh — the merge queue for Dengnifer/MIPStarRE-A (owner tool).
#
# Promoted from /tmp/merge-daemon-v9h.sh, 2026-09-12, at its honest name and
# with the self-repair of full-speed-mode v2 §3.2-§3.5 (work item W5).  Gate
# behaviour is unchanged: this loop merges ONLY through local/bin/pr_merge.py
# and has no flag that can skip, weaken or fake one of its seven gates.
#
# One loop:
#   * PAR = clamp(1, floor((nproc - load1) / cores_per_build), free_slots),
#     recomputed every loop and logged with its inputs, so other users' load on
#     the shared host throttles us instead of the owner typing PAR=8;
#   * a PR whose refresh just finished is merged before the scan, so a later
#     merge cannot invalidate it (v9c fast path);
#   * one GraphQL call (daemon-scan.py) gives every open PR with its head, its
#     candidate mode and whether it is retirable;
#   * retirable PRs (head already on main, or an empty three-dot diff) go to
#     local/bin/pr_janitor.py and never enter a candidate list;
#   * fresh candidates are merged one after another, re-checking freshness
#     after each merge (gate 2b invalidates the others);
#   * stale candidates get a detached refresh lane (local/bin/lane.sh); a
#     branch may hold at most one lane and one fix loop;
#   * a refresh that ends without the lane's .done marker writes a CLASSED
#     marker.  conflict and build markers go to the janitor's repair entry
#     point (fix-lane.sh), one attempt per (PR, head); infra failures are
#     retried, not repaired; the lane tail is relaunched only when the
#     worktree is clean and not mid-merge.  Refreshes and repairs share one
#     PAR budget, so repairs cannot starve merges.
#
# Failure markers are JSON records with a class and a reason, and clear on an
# observable change — the head moved, the repair finished, the recorded reason
# is gone from a dry run, or a newer installed tools-version supersedes them —
# never on elapsed time alone, except the two classes whose backoff IS the
# documented retry (infra 5 min, preflight 15 min).  See daemon-scan.py for
# the table.  On 2026-09-12 05:44Z eleven unrelated PRs stayed blocked by 2 h
# `touch`ed markers after the systemic lane bugs had been fixed, and were
# freed by hand with `rm` and with `( sleep 1500; rm -f ... )`.
#
# Usage: merge-daemon.sh [--once] [--dry-run] [--help]
#   --once     run a single loop and exit
#   --dry-run  implies --once: take the scan from $MIPSTARRE_DAEMON_SCAN_FIXTURE
#              (or skip it), compute and log PAR, print the plan, change
#              nothing.  Used by scripts/tests/test_daemon_marker_classes.py.
# Stop a running daemon with `touch $CACHE_ROOT/watchdog/daemon/stop`, or
# `kill "$(cat $CACHE_ROOT/watchdog/daemon/daemon.pid)"` — never pgrep-kill it,
# the refresh subshells share its cmdline.
#
# Knobs: results/telemetry/owner-tools/daemon.conf (environment wins over the
# file).  Runtime state: $CACHE_ROOT/watchdog/daemon — never committed.
#
# shellcheck disable=SC2154  # the lower-case knobs come from daemon.conf
set -u

PROG="merge-daemon.sh"
SELF_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"

DRY=0; ONCE=0
while [ "$#" -gt 0 ]; do
  case "$1" in
    --once) ONCE=1 ;;
    --dry-run) DRY=1; ONCE=1 ;;
    -h|--help) sed -n '2,49p' "${BASH_SOURCE[0]}" | sed 's/^# \{0,1\}//'; exit 0 ;;
    *) printf '%s: unknown argument %s\n' "$PROG" "$1" >&2; exit 2 ;;
  esac
  shift
done

CACHE_ROOT="${MIPSTARRE_CACHE_ROOT:-$HOME/.cache/mipstarre-dev}"
OWNER_BIN="${MIPSTARRE_OWNER_BIN:-$CACHE_ROOT/owner-bin}"
CONF="${MIPSTARRE_DAEMON_CONF:-$SELF_DIR/daemon.conf}"
[ -r "$CONF" ] || CONF="$OWNER_BIN/daemon.conf"

log() { printf '== %s %s\n' "$(date -u +%FT%TZ)" "$*"; }
note() { printf '%s: %s\n' "$PROG" "$*" >&2; }

if [ ! -r "$CONF" ]; then
  log "refusing to start: no daemon.conf (looked in $SELF_DIR and $OWNER_BIN)"
  exit 3
fi
# shellcheck source=/dev/null
. "$CONF"

CHECKOUT="${MIPSTARRE_CHECKOUT:-${checkout:-$HOME/MIPStarRE-qpbt}}"
export PATH="$OWNER_BIN:$HOME/.local/bin:$HOME/.elan/bin:$PATH"
L="$CACHE_ROOT/watchdog/lanes"; D="$CACHE_ROOT/watchdog/daemon"
mkdir -p "$D" "$D/cache" "$D/repair" "$D/state" "$D/seen" "$L"
cd "$CHECKOUT" || { note "no checkout at $CHECKOUT"; exit 2; }

dep_path() {
  case "$1" in
    lane.sh) printf '%s\n' "$CHECKOUT/local/bin/lane.sh" ;;
    *) if [ -r "$OWNER_BIN/$1" ]; then printf '%s\n' "$OWNER_BIN/$1"
       else printf '%s\n' "$SELF_DIR/$1"; fi ;;
  esac
}
SCAN_PY="$(dep_path daemon-scan.py)"
MERGE_SH="$(dep_path merge.sh)"
FIX_LANE="$(dep_path fix-lane.sh)"
LANE_SH="$(dep_path lane.sh)"
RESOLVE_SH="$CHECKOUT/local/bin/worktree_resolve.sh"
JANITOR_PY="$CHECKOUT/local/bin/pr_janitor.py"
TAB="$(printf '\t')"

sha256_of() {
  sha256sum "$1" 2>/dev/null | cut -d' ' -f1 || shasum -a 256 "$1" 2>/dev/null | cut -d' ' -f1
}
tools_version() { head -n 1 "$OWNER_BIN/tools-version" 2>/dev/null | tr -d '\n'; }
tools_epoch() {
  # install.sh stamps an ISO-8601 timestamp into tools-version; a numeric
  # comparison is what makes "newer" honest, the string is the fallback.
  local iso
  iso="$(tools_version | grep -oE '[0-9]{4}-[0-9]{2}-[0-9]{2}T[0-9:]{8}Z' | head -n 1)"
  [ -n "$iso" ] || return 0
  date -u -d "$iso" +%s 2>/dev/null || true
}
TOOLS_VERSION="$(tools_version)"; [ -n "$TOOLS_VERSION" ] || TOOLS_VERSION="uninstalled"
TOOLS_TS="$(tools_epoch)"
MERGE_TREE_OK=0
git merge-tree -h 2>&1 | grep -q -- '--write-tree' && MERGE_TREE_OK=1
log "tool=$PROG version=$TOOLS_VERSION checkout=$CHECKOUT conf=$CONF"

# --------------------------------------------------------------------- deps
progress_note() {
  local body="$1" issue=""
  issue="$(python3 "$CHECKOUT/local/bin/run_mode.py" get progress_issue 2>/dev/null || true)"
  case "$issue" in
    ''|*[!0-9]*) log "progress note (no progress issue configured): $body"; return 0 ;;
  esac
  if [ "$DRY" = 1 ]; then log "would post to #$issue: $body"; return 0; fi
  printf '%s\n' "$body" | timeout 60 gh api "repos/${repo}/issues/$issue/comments" \
    -F body=@- --jq .html_url >/dev/null 2>&1 || log "progress note to #$issue failed"
}

verify_deps() {
  local manifest="$OWNER_BIN/manifest.sha256" bad=0 dep path want have
  for dep in $daemon_deps lane.sh; do
    path="$(dep_path "$dep")"
    [ -r "$path" ] || { note "missing dependency: $dep ($path)"; bad=1; }
  done
  [ -r "$RESOLVE_SH" ] || { note "missing dependency: worktree_resolve.sh ($RESOLVE_SH)"; bad=1; }
  if [ -r "$manifest" ]; then
    for dep in $daemon_deps; do
      path="$(dep_path "$dep")"; [ -r "$path" ] || continue
      want="$(awk -v n="$dep" '$NF ~ ("(^|/)" n "$") { print $1; exit }' "$manifest")"
      if [ -z "$want" ]; then note "dependency $dep is not listed in $manifest"; bad=1; continue; fi
      have="$(sha256_of "$path")"
      [ "$want" = "$have" ] || { note "dependency $dep does not match its manifest hash"; bad=1; }
    done
  elif [ "${require_manifest:-1}" = 1 ]; then
    note "no installer manifest at $manifest; run results/telemetry/owner-tools/install.sh"
    bad=1
  else
    log "no installer manifest; running uninstalled (require_manifest=0)"
  fi
  return "$bad"
}

if [ "$DRY" != 1 ] && ! verify_deps; then
  progress_note "merge-daemon.sh refused to start at $(date -u +%FT%TZ): an installed dependency is missing or its hash does not match the installer manifest (details in the daemon log). No pull request was touched; re-run results/telemetry/owner-tools/install.sh."
  log "refusing to start: dependency check failed"
  exit 3
fi

# ------------------------------------------------------------------ records
LATENCY_FILE="${merge_latency_file:-}"
if [ -z "$LATENCY_FILE" ]; then
  # One writer per path: the flat file only once the union merge driver (W7)
  # is in effect for results/telemetry, a dated file until then (design §3.7).
  if git check-attr merge -- results/telemetry/events.md 2>/dev/null | grep -q 'merge: union'; then
    LATENCY_FILE="results/telemetry/merge-latency.jsonl"
  else
    LATENCY_FILE="results/telemetry/merge-latency-$(date -u +%F).jsonl"
  fi
fi

PAR=1; PAR_INPUTS="not computed"
mark_event() { # PR HEAD EVENT [CLASS] [REASON]
  local pr="$1" head="$2" event="$3" cls="${4:-}" reason="${5:-}" now last secs
  now="$(date +%s)"; last="$(cat "$D/state/$pr.ts" 2>/dev/null || echo "$now")"
  secs=$(( now - last )); printf '%s\n' "$now" > "$D/state/$pr.ts"
  if [ "$DRY" = 1 ]; then log "would record latency pr=$pr event=$event"; return 0; fi
  python3 "$SCAN_PY" latency --file "$LATENCY_FILE" --pr "$pr" --head "$head" \
    --event "$event" --class "$cls" --reason "$reason" --seconds "$secs" --par "$PAR" \
    >/dev/null 2>&1 || log "latency row failed for PR $pr"
}

marker_class() {
  python3 -c 'import json,sys
try: print(json.load(open(sys.argv[1])).get("class","infra"))
except Exception: print("infra")' "$1" 2>/dev/null || printf 'infra\n'
}

fresh() { # HEAD — the merged gate-2b predicate (PR 499 / #498), unchanged
  python3 -c 'import sys
from pathlib import Path
sys.path.insert(0, "local/bin")
import pr_merge
sys.exit(0 if pr_merge.head_is_fresh(Path("."), sys.argv[1], sys.argv[2]) else 1)' \
    "$base_ref" "$1" 2>/dev/null
}

# -------------------------------------------------------------- parallelism
free_slots() {
  local out
  if [ -n "${MIPSTARRE_DAEMON_FREE_SLOTS:-}" ]; then printf '%s\n' "$MIPSTARRE_DAEMON_FREE_SLOTS"; return; fi
  out="$(python3 "$SCAN_PY" slots --cache-root "$CACHE_ROOT" --checkout "$CHECKOUT" 2>/dev/null)" || out=""
  set -- ${out:-0 0 0}
  printf '%s\n' "${1:-0}"
}
compute_par() {
  local nproc load1 free
  nproc="${MIPSTARRE_DAEMON_NPROC:-$(nproc 2>/dev/null || echo 8)}"
  load1="${MIPSTARRE_DAEMON_LOAD1:-$(cut -d' ' -f1 /proc/loadavg 2>/dev/null || echo 0)}"
  free="$(free_slots)"
  PAR="$(python3 "$SCAN_PY" par --nproc "$nproc" --load1 "$load1" \
          --cores-per-build "$cores_per_build" --free-slots "$free" 2>/dev/null || echo 1)"
  PAR_INPUTS="nproc=$nproc load1=$load1 cores_per_build=$cores_per_build free_slots=$free"
}

count_pidfiles() { # suffix
  local n=0 f pid
  for f in "$D"/pr*."$1"; do
    [ -e "$f" ] || continue
    pid="$(cat "$f" 2>/dev/null)"
    if [ -n "$pid" ] && kill -0 "$pid" 2>/dev/null; then n=$(( n + 1 )); else rm -f "$f"; fi
  done
  printf '%s\n' "$n"
}
DRY_LAUNCHED=0
in_flight() { printf '%s\n' "$(( $(refreshing_count) + $(repairing_count) + DRY_LAUNCHED ))"; }
refreshing_count() { count_pidfiles refreshing; }
repairing_count() { count_pidfiles repairing; }
lane_running() { pgrep -f "lane(-v[0-9]+)?\.sh 0*$1 " >/dev/null 2>&1; }
busy_on() { # PR N — one lane and one fix loop per branch, never two
  local pr="$1" n="$2" pid
  pid="$(cat "$D/pr$pr.refreshing" 2>/dev/null || true)"
  [ -n "$pid" ] && kill -0 "$pid" 2>/dev/null && return 0
  pid="$(cat "$D/pr$pr.repairing" 2>/dev/null || true)"
  [ -n "$pid" ] && kill -0 "$pid" 2>/dev/null && return 0
  lane_running "$n"
}

# ------------------------------------------------------------------ markers
classify_lane() { # N -> "CLASS<TAB>REASON"
  python3 "$SCAN_PY" classify "$L/$1.needs-attention" "$L/$1.lane.log" --source lane 2>/dev/null \
    || printf 'infra%sunreadable lane log\n' "$TAB"
}
marker_write() { # PR HEAD CLASS REASON LOG
  python3 "$SCAN_PY" marker-write --path "$D/pr$1.failed" --pr "$1" --head "$2" \
    --class "$3" --reason "$4" --lane-log "$5" --tools-version "$TOOLS_VERSION" \
    ${TOOLS_TS:+--tools-ts "$TOOLS_TS"} >/dev/null 2>&1 \
    || { log "marker write failed for PR $1"; : > "$D/pr$1.failed"; }
}
repair_state_of() { # PR HEAD
  local pr="$1" head="$2" pid used
  pid="$(cat "$D/pr$pr.repairing" 2>/dev/null || true)"
  if [ -n "$pid" ] && kill -0 "$pid" 2>/dev/null; then printf 'running\n'; return; fi
  rm -f "$D/pr$pr.repairing" 2>/dev/null || true
  if [ -e "$D/pr$pr.repair-done" ]; then printf 'done\n'; return; fi
  used="$(cat "$D/repair/$pr-$head" 2>/dev/null || echo 0)"
  if [ "$used" -ge "$repair_attempts_per_head" ]; then printf 'exhausted\n'; else printf 'none\n'; fi
}
conflict_gone() { # HEAD — the dry run of the failing step for class conflict
  [ "$MERGE_TREE_OK" = 1 ] || return 1
  git rev-parse -q --verify "$1^{commit}" >/dev/null 2>&1 || return 1
  git merge-tree --write-tree "$base_ref" "$1" >/dev/null 2>&1
}
marker_blocks() { # PR N BR HEAD -> 0 blocked (MARKER_DECISION set), 1 clear
  local pr="$1" head="$4" state cls out rc
  MARKER_DECISION=""
  [ -e "$D/pr$pr.failed" ] || return 1
  state="$(repair_state_of "$pr" "$head")"
  cls="$(marker_class "$D/pr$pr.failed")"
  local extra=()
  if [ "$cls" = conflict ] && conflict_gone "$head"; then extra=(--reason-gone); fi
  out="$(python3 "$SCAN_PY" marker-check --path "$D/pr$pr.failed" --head "$head" \
          --tools-version "$TOOLS_VERSION" ${TOOLS_TS:+--tools-ts "$TOOLS_TS"} \
          --repair-state "$state" --backoff-infra "$backoff_infra_s" \
          --backoff-preflight "$backoff_preflight_s" \
          --infra-max-attempts "$infra_max_attempts" \
          ${extra[@]+"${extra[@]}"} 2>/dev/null)"
  rc=$?
  MARKER_DECISION="$out"
  [ "$rc" = 0 ] && return 0
  rm -f "$D/pr$pr.failed" "$D/pr$pr.repair-done"
  log "cleared the failure marker of PR $pr: ${out:-no marker}"
  return 1
}

# --------------------------------------------------------- lanes and repairs
worktree_ready() { # BRANCH — clean and not mid-merge (an absent one is fine:
  # the lane creates it).  Resolved registry-first, exactly as the lane does,
  # so the daemon never judges a directory that holds another branch.
  local wt rc gd
  if [ -r "$RESOLVE_SH" ]; then
    wt="$(bash "$RESOLVE_SH" --root "$CHECKOUT" "$1" 2>/dev/null)"
    rc=$?
    [ "$rc" = 4 ] && return 0
    [ "$rc" = 0 ] && [ -n "$wt" ] || return 1
  else
    wt="$CHECKOUT/.worktrees/$1"
    [ -e "$wt/.git" ] || return 0
  fi
  gd="$(git -C "$wt" rev-parse --git-dir 2>/dev/null)" || return 1
  case "$gd" in /*) ;; *) gd="$wt/$gd" ;; esac
  [ -e "$gd/MERGE_HEAD" ] && return 1
  [ -z "$(git -C "$wt" status --porcelain 2>/dev/null | grep -v '^?? ')" ]
}

launch_refresh() { # PR N BR SLUG MODE HEAD
  local PR="$1" N="$2" BR="$3" SLUG="$4" MODE="$5" H="$6"
  if ! worktree_ready "$BR"; then
    log "refresh held for PR $PR: worktree $BR is dirty or mid-merge"
    return 1
  fi
  if [ "$DRY" = 1 ]; then log "would refresh PR $PR ($BR) mode=$MODE par=$PAR"; return 0; fi
  rm -f "$L/$N.done" "$L/$N.needs-attention"
  mark_event "$PR" "$H" refresh_start
  ( LANE_BRANCH="$BR" SKIP_DISPATCH=1 setsid bash "$LANE_SH" "$N" "$SLUG" prover \
        > "$L/$N.lane.log" 2>&1 < /dev/null
    if [ -e "$L/$N.done" ]; then
      printf '== %s refresh done for PR %s\n' "$(date -u +%FT%TZ)" "$PR" >> "$D/refresh.log"
      printf '%s:%s:%s\n' "$PR" "$N" "$MODE" >> "$D/refresh-done.queue"
      rm -f "$D/pr$PR.failed" "$D/pr$PR.repair-done"
    else
      cr="$(classify_lane "$N")"; cls="${cr%%${TAB}*}"; reason="${cr#*${TAB}}"
      printf '== %s refresh failed for PR %s [%s] %s\n' "$(date -u +%FT%TZ)" "$PR" "$cls" "$reason" >> "$D/refresh.log"
      marker_write "$PR" "$H" "$cls" "$reason" "$L/$N.lane.log"
      mark_event "$PR" "$H" failed "$cls" "$reason"
    fi
    rm -f "$D/pr$PR.refreshing" ) &
  echo $! > "$D/pr$PR.refreshing"
  log "refreshing PR $PR ($BR) detached, pid $(cat "$D/pr$PR.refreshing") par=$PAR"
}

launch_repair() { # PR N BR HEAD CLASS
  local PR="$1" N="$2" BR="$3" H="$4" CLS="$5" mode=merge ledger used
  [ "$CLS" = build ] && mode=build
  [ -r "$FIX_LANE" ] || { log "no repair entry point at $FIX_LANE; PR $PR stays parked"; return 1; }
  ledger="$D/repair/$PR-$H"
  used="$(cat "$ledger" 2>/dev/null || echo 0)"
  if [ "$used" -ge "$repair_attempts_per_head" ]; then
    log "repair budget spent for PR $PR head ${H:0:8} (class $CLS)"; return 1
  fi
  if [ "$DRY" = 1 ]; then log "would repair PR $PR ($BR) mode=$mode"; return 0; fi
  printf '%s\n' "$(( used + 1 ))" > "$ledger"
  rm -f "$D/pr$PR.repair-done"
  ( timeout "$repair_timeout_s" bash "$FIX_LANE" "$PR" "$N" "$BR" "$mode" >> "$L/$N.fix.log" 2>&1
    printf '== %s repair (%s) for PR %s exited %s\n' "$(date -u +%FT%TZ)" "$mode" "$PR" "$?" >> "$L/$N.fix.log"
    touch "$D/pr$PR.repair-done"
    rm -f "$D/pr$PR.repairing" ) &
  echo $! > "$D/pr$PR.repairing"
  log "repairing PR $PR ($BR) mode=$mode, pid $(cat "$D/pr$PR.repairing")"
}

try_merge() { # PR N MODE HEAD
  local PR="$1" N="$2" MODE="$3" H="$4" T cr cls reason
  local ARGS=()
  if [ "$MODE" = adj ]; then
    T="$(ls "$D"/adjudication-"$PR"-template*.md 2>/dev/null | tail -1)"
    [ -n "$T" ] || T="$(ls "$CHECKOUT"/results/telemetry/owner-tools/adjudication-"$PR"-template*.md 2>/dev/null | tail -1)"
    [ -n "$T" ] || { log "no adjudication template for PR $PR"; return 1; }
    if [ "$DRY" = 1 ]; then log "would post the adjudication for PR $PR and merge"; return 0; fi
    sed "s/__HEAD__/$H/" "$T" > "$D/adjudication-$PR.md"
    timeout 60 gh api "repos/${repo}/issues/$PR/comments" -F body=@"$D/adjudication-$PR.md" --jq .html_url
    ARGS=(--adjudicated)
  fi
  if [ "$DRY" = 1 ]; then log "would merge PR $PR (mode $MODE, head ${H:0:8})"; return 0; fi
  if bash "$MERGE_SH" "$PR" ${ARGS[@]+"${ARGS[@]}"} > "$L/pr$PR.merge.log" 2>&1; then
    log "merged PR $PR"
    grep -v "^MIPStarRE pre-\|^hint\|^Blueprint" "$L/pr$PR.merge.log" | tail -2
    rm -f "$D/pr$PR.failed" "$D/pr$PR.repair-done"; printf '%s\n' "$PR" >> "$D/merged"
    mark_event "$PR" "$H" merged
    # v9e: pending telemetry is committed AFTER a merge (main moved anyway); a
    # commit before the merge tripped gate 2b for PR 359.
    if [ -n "$(git status --porcelain -- results/telemetry)" ]; then
      git add results/telemetry &&
        git commit -qm "chore(telemetry): batch after the PR $PR merge" >/dev/null 2>&1 &&
        git push -q github main >/dev/null 2>&1 && log "telemetry batch committed after PR $PR"
    fi
    return 0
  fi
  log "merge failed for PR $PR"
  grep -v "^MIPStarRE pre-\|^hint\|^Blueprint" "$L/pr$PR.merge.log" | tail -3
  cr="$(python3 "$SCAN_PY" classify "$L/pr$PR.merge.log" --source merge 2>/dev/null \
        || printf 'gate%smerge failed\n' "$TAB")"
  cls="${cr%%${TAB}*}"; reason="${cr#*${TAB}}"
  marker_write "$PR" "$H" "$cls" "$reason" "$L/pr$PR.merge.log"
  mark_event "$PR" "$H" failed "$cls" "$reason"
  return 1
}

# --------------------------------------------------------------- retirement
retire_pr() { # PR HEAD
  local PR="$1" stamp="$D/state/$1.retire" age
  if [ -e "$stamp" ]; then
    age=$(( $(date +%s) - $(stat -c %Y "$stamp" 2>/dev/null || echo 0) ))
    [ "$age" -lt "$retire_retry_s" ] && return 0
  fi
  touch "$stamp"
  if [ "$DRY" = 1 ]; then log "would hand PR $PR to pr_janitor.py (superseded)"; return 0; fi
  if [ -r "$JANITOR_PY" ]; then
    if python3 "$JANITOR_PY" --pr "$PR" >> "$D/retire.log" 2>&1; then
      log "retired PR $PR (nothing left against main); the janitor closed it"
      printf '%s\n' "$PR" >> "$D/retired"
    else
      log "pr_janitor.py declined PR $PR (see daemon/retire.log)"
    fi
  else
    log "pr_janitor.py is not installed; PR $PR is retirable and stays open"
  fi
}

gc_lane_state() { # open lane numbers as words
  local open=" $* " f n pr
  for f in "$L"/*.done; do
    [ -e "$f" ] || continue
    n="$(basename "$f" .done)"
    case "$open" in *" $n "*) continue ;; esac
    lane_running "$n" && continue
    [ -e "$L/$n.needs-attention" ] && continue
    pr="$(sed -n 's/.*PR=\([0-9][0-9]*\).*/\1/p' "$f" | head -n 1)"
    [ -n "$pr" ] || continue
    if [ "$DRY" = 1 ]; then log "would drop lane state $n (PR $pr no longer open)"; continue; fi
    rm -f "$L/$n".done "$L/$n".thread "$L/$n".task.md "$L/$n".pr.md \
          "$L/$n".dispatch.log "$L/$n".build.log "$L/$n".ci.log "$L/$n".review.log
    log "dropped lane state for $n (PR $pr no longer open)"
  done
}

report_markers() { # every live marker with its reason, one line each
  local lines
  lines="$(python3 "$SCAN_PY" marker-list --dir "$D" --json-out "$D/markers.json" 2>/dev/null)"
  if [ -n "$lines" ]; then
    log "live failure markers:"
    printf '%s\n' "$lines" | while IFS= read -r line; do log "  $line"; done
  else
    log "live failure markers: none"
  fi
}

# ------------------------------------------------------------------- loop
[ "$DRY" = 1 ] || echo $$ > "$D/daemon.pid"
LAST_REPORT=0
while true; do
  [ -e "$D/stop" ] && { log "stop file present; exiting"; exit 0; }
  [ -e "$D/adj-list" ] || : > "$D/adj-list"
  [ "$DRY" = 1 ] || git fetch -q github 2>/dev/null
  compute_par
  log "scan start: par=$PAR ($PAR_INPUTS) refreshing=$(refreshing_count) repairing=$(repairing_count)"

  # fast path: a PR whose refresh just finished is merged before the scan
  if [ -s "$D/refresh-done.queue" ]; then
    Q="$(cat "$D/refresh-done.queue")"; : > "$D/refresh-done.queue"
    while IFS=: read -r PR N MODE; do
      [ -n "${PR:-}" ] || continue
      H="$(timeout 60 gh pr view "$PR" --json headRefOid,state --jq 'select(.state=="OPEN") | .headRefOid' 2>/dev/null </dev/null)"
      [ -n "$H" ] || continue
      mark_event "$PR" "$H" refresh_end
      if fresh "$H"; then
        log "fast path: PR $PR refreshed and fresh"
        try_merge "$PR" "$N" "$MODE" "$H" && git fetch -q github 2>/dev/null
      else
        log "fast path: PR $PR refreshed but already stale"
      fi
    done <<< "$Q"
  fi

  # -------------------------------------------------------------- the scan
  if [ -n "${MIPSTARRE_DAEMON_SCAN_FIXTURE:-}" ]; then
    SCAN="$(cat "$MIPSTARRE_DAEMON_SCAN_FIXTURE")"
  elif [ "$DRY" = 1 ]; then
    SCAN=""
  else
    SCAN="$(timeout "$scan_timeout_s" python3 "$SCAN_PY" scan --adj-list "$D/adj-list" \
             --repo "$repo" --base "$base_ref" --all 2>>"$D/scan.err")" || {
      log "scan failed (see daemon/scan.err); retry in ${scan_fail_sleep_s}s"
      [ "$ONCE" = 1 ] && exit 1
      sleep "$scan_fail_sleep_s"; continue; }
  fi

  CANDS=(); REPAIRS=(); OPEN_LANES=""
  while IFS=: read -r PR N BR SLUG MODE H; do
    [ -n "${PR:-}" ] || continue
    case "${N:--}" in -) ;; *) OPEN_LANES="$OPEN_LANES $N" ;; esac
    case "$MODE" in
      retire) retire_pr "$PR" "$H"; continue ;;
      offconv) log "PR $PR branch '$BR' is off-convention; no lane is launched for it"; continue ;;
      skip) continue ;;
    esac
    busy_on "$PR" "$N" && continue
    if marker_blocks "$PR" "$N" "$BR" "$H"; then
      log "PR $PR held by its failure marker: $MARKER_DECISION"
      # A conflict or build marker whose repair has not run yet is not a
      # merge candidate but IS a repair candidate; both draw on the PAR
      # budget below, so repairs can never starve merges.
      case "$MARKER_DECISION" in
        "block awaiting-repair"*) REPAIRS+=("$PR:$N:$BR:$SLUG:$MODE:$H") ;;
      esac
      continue
    fi
    CANDS+=("$PR:$N:$BR:$SLUG:$MODE:$H")
    [ -e "$D/seen/$PR-$H.ready" ] || { touch "$D/seen/$PR-$H.ready"; mark_event "$PR" "$H" ready "$MODE"; }
  done <<< "$SCAN"

  gc_lane_state $OPEN_LANES

  if [ "$(( $(date +%s) - LAST_REPORT ))" -ge "$report_interval_s" ]; then
    report_markers; LAST_REPORT="$(date +%s)"
  fi

  if [ "${#CANDS[@]}" -eq 0 ] && [ "${#REPAIRS[@]}" -eq 0 ]; then
    [ "$ONCE" = 1 ] && exit 0
    sleep "$idle_sleep_s"; continue
  fi
  log "candidates: $(printf '%s ' ${CANDS[@]+"${CANDS[@]}"} | sed -E 's/:[^ ]*//g')| repairs: $(printf '%s ' ${REPAIRS[@]+"${REPAIRS[@]}"} | sed -E 's/:[^ ]*//g')| par=$PAR ($PAR_INPUTS)"

  # phase B: merge every fresh candidate, re-fetching after each merge
  MERGED_ONE=0
  for c in ${CANDS[@]+"${CANDS[@]}"}; do
    IFS=: read -r PR N BR SLUG MODE H <<< "$c"
    [ -e "$D/stop" ] && break
    if [ "$DRY" = 1 ]; then log "would test freshness of PR $PR and merge it when fresh"; continue; fi
    git fetch -q github 2>/dev/null
    H="$(timeout 60 gh pr view "$PR" --json headRefOid,state --jq 'select(.state=="OPEN") | .headRefOid' 2>/dev/null </dev/null)"
    [ -n "$H" ] || continue
    fresh "$H" || continue
    try_merge "$PR" "$N" "$MODE" "$H" && MERGED_ONE=1
  done

  # phase A: repairs first, then refreshes, sharing ONE PAR budget
  [ "$DRY" = 1 ] || git fetch -q github 2>/dev/null
  DRY_LAUNCHED=0
  for c in ${REPAIRS[@]+"${REPAIRS[@]}"}; do
    IFS=: read -r PR N BR SLUG MODE H <<< "$c"
    [ "$(in_flight)" -ge "$PAR" ] && break
    [ "$(repairing_count)" -ge "$repair_max_concurrent" ] && break
    busy_on "$PR" "$N" && continue
    launch_repair "$PR" "$N" "$BR" "$H" "$(marker_class "$D/pr$PR.failed")" \
      && DRY_LAUNCHED=$(( DRY_LAUNCHED + DRY ))
  done
  for c in ${CANDS[@]+"${CANDS[@]}"}; do
    IFS=: read -r PR N BR SLUG MODE H <<< "$c"
    [ "$(in_flight)" -ge "$PAR" ] && break
    busy_on "$PR" "$N" && continue
    if [ "$DRY" != 1 ]; then
      H="$(timeout 60 gh pr view "$PR" --json headRefOid,state --jq 'select(.state=="OPEN") | .headRefOid' 2>/dev/null </dev/null)"
      [ -n "$H" ] || continue
      fresh "$H" && continue
    fi
    launch_refresh "$PR" "$N" "$BR" "$SLUG" "$MODE" "$H" && DRY_LAUNCHED=$(( DRY_LAUNCHED + DRY ))
  done

  # v9f: the daemon owns telemetry commits; when nothing merged for an hour,
  # commit pending telemetry now (one refresh may be wasted).
  if [ "$DRY" != 1 ]; then
    LASTS="$(stat -c %Y "$D/merged" 2>/dev/null || echo 0)"
    if [ -n "$(git status --porcelain -- results/telemetry)" ] &&
       [ "$(( $(date +%s) - LASTS ))" -gt "$telemetry_batch_idle_s" ] &&
       [ "$(refreshing_count)" -eq 0 ]; then
      git add results/telemetry &&
        git commit -qm "chore(telemetry): hourly batch (no merge in the last hour)" >/dev/null 2>&1 &&
        git push -q github main >/dev/null 2>&1 && log "telemetry hourly batch committed"
    fi
  fi

  [ "$ONCE" = 1 ] && exit 0
  if [ "$MERGED_ONE" = 1 ]; then sleep "$busy_sleep_s"; else sleep "$idle_sleep_s"; fi
done
