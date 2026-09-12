#!/usr/bin/env bash
# lane.sh — one proof lane: dispatch, publish, CI, review.
#
#   local/bin/lane.sh <issue> <slug> [prover|orc]
#
# Creates or resolves the branch worktree, dispatches a codex worker with the
# issue body as the task, and then — if the worker committed — merges
# github/main, builds, opens the PR through pr_open.py, runs local/bin/ci.sh
# and local/bin/review.sh on the exact head.  Merging is the merge daemon's
# job; this script never calls pr_merge.py.
#
# Promoted from /tmp/lane-v17.sh (really v20) on 2026-09-12, work item W5 of
# the full-speed-mode v2 design.  Gate behaviour is unchanged from v20: the
# same merge of github/main, the same issue-#222 post-merge missing-path
# check, the same pr_open.py -> checked-push.sh publication, the same
# exact-head CI and review.  What changed:
#
#   1. Lane identity.  N comes from the BRANCH (`issue-<N>-<slug>`, the regex
#      pr_open.py uses) and the positional id, the branch and `gh issue view N`
#      must all agree.  Meta lanes numbered 1000+PR made `gh issue view 1342`
#      empty and `pr_open.py --issue 1342` exit 2; an off-convention branch now
#      stops the lane with a warning instead of being silently renumbered.
#   2. The pr_open FALLBACK IS GONE.  It hand-fed the pre-push hook a forged
#      ref tuple and then pushed with the hook-skipping environment override,
#      losing checked-push.sh's --force-with-lease and its post-preflight tree
#      and SHA re-verification.  No code path in this file sets that override
#      or calls the hook directly; a plain grep for either finds nothing.
#      A pr_open failure writes <N>.needs-attention and stops.
#   3. Worktree resolution is registry-first through worktree_resolve.sh; a
#      directory holding another branch parks the lane (worktree-mismatch)
#      instead of refreshing the wrong tree and pushing nothing (PR 213).
#   4. Admission polls for a free slot WITHOUT the global launch lock; the lock
#      is held only for a short jittered hold around the dispatch call.  The
#      wait is bounded and parks `no-slot` on expiry, instead of sleeping six
#      hours inside the lock and capping the pipeline at ~2.4 launches/minute
#      (the post-launch fixed 25-second hold is now a short jittered one).
#      One cap definition, reading the per-account caps through
#      local/bin/account_router.py.
#   5. The pre-push full build takes the machine-wide build lock ci.sh uses
#      (DESIGN.md invariant 7); the v20 explicit changed-module build stays as
#      belt-and-braces for modules outside the MIPStarRE.QPBT import closure.
#
# Markers: $CACHE_ROOT/watchdog/lanes/<N>.{done,needs-attention}, each naming
# the tool version that wrote it.  A needs-attention marker's first line is
# `<ts> lane.sh version=<v> reason=<slug>: <message>` — the janitor classifies
# the slug, a human reads the message.
#
# Environment: MIPSTARRE_CHECKOUT, MIPSTARRE_CACHE_ROOT, MIPSTARRE_LAKE_DATA,
#   LANE_BRANCH (refresh an existing PR branch), SKIP_DISPATCH=1 (the worktree
#   already holds the finished work), SKIP_REVIEW=1 (stacked PR),
#   MIPSTARRE_LANE_SLOT_WAIT_S (default 1800), MIPSTARRE_REVIEW_CMD.
set -u

P="${MIPSTARRE_CHECKOUT:-$HOME/MIPStarRE-qpbt}"
CACHE_ROOT="${MIPSTARRE_CACHE_ROOT:-$HOME/.cache/mipstarre-dev}"
OWNER_BIN="${MIPSTARRE_OWNER_BIN:-$CACHE_ROOT/owner-bin}"
export PATH="$OWNER_BIN:$HOME/.local/bin:$HOME/.elan/bin:$PATH"
# The model is the policy's decision, never a lane default: dispatch.sh asks
# model_policy.py, and the run-wide switch is `models.override` in the run
# brief (watchdog/model-override), which telemetry records on the session row.
# `auto` is the only value that lets both work. The literal `gpt-5.6-sol`
# default and the `watchdog/model.txt` side channel each pinned a model behind
# the policy's back, so a full speed run could not move its lanes to the hard
# model without editing a file nothing else reads.
export MIPSTARRE_CODEX_MODEL="${MIPSTARRE_CODEX_MODEL:-auto}"
export MIPSTARRE_SESSION="owner-operator"

STATE="$CACHE_ROOT/watchdog/lanes"; mkdir -p "$STATE"
SKIP_DISPATCH="${SKIP_DISPATCH:-0}"
SLOT_WAIT_S="${MIPSTARRE_LANE_SLOT_WAIT_S:-1800}"
BUILD_LOCK="${MIPSTARRE_FULL_BUILD_LOCK:-$CACHE_ROOT/.full-build-lock}"
BUILD_LOCK_WAIT_S="${MIPSTARRE_LANE_BUILD_LOCK_WAIT_S:-14400}"
BUILD_LOCK_STALE_S="${MIPSTARRE_FULL_BUILD_LOCK_STALE_S:-10800}"
DATA="${MIPSTARRE_LAKE_DATA:-/data/users/drx/mipstarre-cache}"
REVIEW_CMD="${MIPSTARRE_REVIEW_CMD:-local/bin/review.sh}"

#: pr_open.py:37 — the one branch convention a lane may exist for.
BRANCH_RE='^(codex/|claude/)?issue-([0-9]+)-([a-z0-9][a-z0-9-]*)$'

N_ARG="${1:-}"; SLUG="${2:-}"; ROLE="${3:-prover}"
MARKER_ID="${N_ARG:-unknown}"
BR="${LANE_BRANCH:-issue-$N_ARG-$SLUG}"

now() { date -u +%FT%TZ; }
log() { printf '== %s %s\n' "$(now)" "$*"; }
HELD_LOCK=""
cleanup() { [ -n "$HELD_LOCK" ] && rm -rf "$HELD_LOCK"; return 0; }
trap cleanup EXIT
fail() { # <reason-slug> <message...>
  local reason="$1"; shift
  printf '%s lane.sh version=%s reason=%s: %s\n' "$(now)" "$TOOL_VERSION" "$reason" "$*" \
    | tee "$STATE/$MARKER_ID.needs-attention"
  exit 1
}

tool_version() {
  local v
  v="$(git -C "$P" rev-parse --short HEAD 2>/dev/null || true)"
  [ -n "$v" ] || v="$(git hash-object "${BASH_SOURCE[0]}" 2>/dev/null | cut -c1-12 || true)"
  printf '%s\n' "${v:-unversioned}"
}
TOOL_VERSION="$(tool_version)"
log "tool=lane.sh version=$TOOL_VERSION"

[ -n "$N_ARG" ] && [ -n "$SLUG" ] || {
  printf 'usage: lane.sh <issue> <slug> [prover|orc]\n' >&2; exit 2; }

# ------------------------------------------------------------ lane identity
# A lane may only exist for a real issue.  The positional id, the branch
# prefix and `gh issue view` must agree; a deliberate off-convention branch
# stops the lane with a warning rather than being silently renumbered.
if [[ ! "$BR" =~ $BRANCH_RE ]]; then
  fail branch-off-convention "branch '$BR' is not issue-<N>-<slug>; refusing to guess a lane number"
fi
BR_N="${BASH_REMATCH[2]}"; BR_SLUG="${BASH_REMATCH[3]}"
case "$N_ARG" in
  ''|*[!0-9]*) fail lane-id-mismatch "lane id '$N_ARG' is not an issue number" ;;
esac
if [ "$((10#$BR_N))" -ne "$((10#$N_ARG))" ]; then
  fail lane-id-mismatch "lane id '$N_ARG' does not match branch '$BR' (issue $BR_N); meta lanes numbered 1000+PR have no issue"
fi
N="$((10#$BR_N))"
ISSUE_TITLE="$(gh issue view "$N" --json number,title --jq 'select(.number) | .title' 2>/dev/null || true)"
[ -n "$ISSUE_TITLE" ] || fail issue-missing "gh issue view $N returned nothing; lane $N has no issue"
MARKER_ID="$N"
[ "$BR_SLUG" = "$SLUG" ] || log "note: branch slug '$BR_SLUG' differs from the argument '$SLUG'; the branch wins"
log "identity ok N=$N branch=$BR issue=$N role=$ROLE"

rm -f "$STATE/$N.done" "$STATE/$N.needs-attention"
cd "$P" || fail checkout-missing "no checkout at $P"
git fetch -q github || fail fetch-failed "git fetch github failed"

# --------------------------------------------------------------- worktree
# Registry first (git's own record), then .worktrees/<branch> only when its
# HEAD is this branch; anything else is a mismatch and parks the lane.
W="$(bash "$P/local/bin/worktree_resolve.sh" --root "$P" --create "$BR")"
case "$?" in
  0) : ;;
  3) fail worktree-mismatch "a worktree directory for $BR holds a different branch" ;;
  *) fail worktree-add-failed "could not resolve or create a worktree for $BR" ;;
esac
[ -n "$W" ] && [ -d "$W" ] || fail worktree-add-failed "worktree resolution produced no directory for $BR"
log "worktree $W"

# build products live on the NVMe pool (2026-09-04)
if [ ! -L "$W/.lake" ] && { [ ! -e "$W/.lake" ] || [ -z "$(ls -A "$W/.lake" 2>/dev/null)" ]; }; then
  rm -rf "$W/.lake"; mkdir -p "$DATA/lake/$BR"; ln -s "$DATA/lake/$BR" "$W/.lake"; log ".lake -> $DATA/lake/$BR"
fi
log "warming $W"
local/bin/worktree-setup.sh "$W" >/dev/null 2>&1 || log "warm finished with warnings"
MIGRATE="$OWNER_BIN/migrate-packages.sh"
[ -r "$MIGRATE" ] || MIGRATE="$P/results/telemetry/owner-tools/migrate-packages.sh"
[ -L "$W/.lake/packages" ] || { [ -r "$MIGRATE" ] && bash "$MIGRATE" "$W" >/dev/null 2>&1; } || true

TASK="$STATE/$N.task.md"
{
  echo "You are dispatched for GitHub issue #$N in the worktree $W (branch $BR)."
  echo "Rules: work only in this worktree; prove the target declarations WITHOUT changing public signatures;"
  echo "never add sorry, axioms, or hypotheses to paper-labelled statements; check every changed file with"
  echo "\`lake env lean <file>\`; commit with conventional subjects (e.g. feat(QPBT/Games): ...); do NOT push;"
  echo "do NOT edit MIPStarRE/QPBT.lean (the operator serializes re-exports; name any needed re-export in your report);"
  echo "if the worktree already contains partial work for this issue, continue from it rather than restarting;"
  echo "when done, or if blocked, end with a short report: what is proved, what remains and why."
  echo; echo "----- ISSUE #$N -----"
  gh issue view "$N" --json title,body --jq '"# "+.title+"\n\n"+.body'
  if [ -f "$STATE/$N.repair.md" ]; then
    echo; echo "----- REPAIR REQUEST FROM THE OPERATOR (do this first) -----"; cat "$STATE/$N.repair.md"
  fi
} > "$TASK"

# ------------------------------------------------------------- admission
# ONE cap definition, and it is account_router.py's: `effective_caps` (which forces
# a `down` endpoint's cap to zero) and `live_pids` (which reaps dead markers).
# Re-implementing the cap read here is what let a lane launch a dispatch into an
# outage the router would have refused: a dead endpoint keeps freeing slots as its
# sessions die, so a local `cap - live` count reads an outage as headroom.
# Prints "free live cap"; exit 3 means no capacity record exists at all.
slots() {
  python3 - "$P" "$CACHE_ROOT" <<'PY'
import os, sys
from pathlib import Path
checkout, cache = Path(sys.argv[1]), Path(sys.argv[2])
sys.path.insert(0, str(checkout / "local" / "bin"))
router = None
try:
    import account_router as router
    accounts = list(router.ACCOUNTS)
except Exception:
    accounts = ["primary", "second"]
def alive(pid):
    try:
        os.kill(pid, 0)
    except ProcessLookupError:
        return False
    except PermissionError:
        return True
    except OSError:
        return False
    return True
if router is not None and any((cache / "watchdog" / f"max-codex-{a}").exists()
                              for a in accounts):
    try:
        caps = router.effective_caps(cache)          # a `down` endpoint counts as 0
        live = sum(len(router.live_pids(cache / "accounts" / a)) for a in accounts)
        cap = sum(max(0, value) for value in caps)
        print(f"{max(0, cap - live)} {live} {cap}")
        raise SystemExit(0)
    except SystemExit:
        raise
    except Exception:
        pass  # fall through to the file read below; never fail a lane on this
cap = live = 0
seen = False
for account in accounts:
    path = cache / "watchdog" / f"max-codex-{account}"
    if path.exists():
        seen = True
        try:
            cap += max(0, int(path.read_text().strip()))
        except ValueError:
            pass
    directory = cache / "accounts" / account
    if directory.is_dir():
        live += sum(1 for entry in directory.iterdir()
                    if entry.name.isdecimal() and alive(int(entry.name)))
if not seen:
    aggregate = cache / "watchdog" / "max-codex"
    if not aggregate.exists():
        print("0 0 0"); raise SystemExit(3)
    try:
        cap = max(0, int(aggregate.read_text().strip()))
    except ValueError:
        print("0 0 0"); raise SystemExit(3)
print(f"{max(0, cap - live)} {live} {cap}")
PY
}
free_slots() { local out; out="$(slots)" || return 3; set -- $out; printf '%s\n' "${1:-0}"; }
wait_for_slot() { # bounded; 0 = a slot is free, 1 = the wait expired
  local deadline free
  deadline=$(( $(date +%s) + SLOT_WAIT_S ))
  while :; do
    free="$(free_slots)" || fail no-capacity-record "no per-account cap file under $CACHE_ROOT/watchdog"
    [ "${free:-0}" -gt 0 ] && return 0
    [ "$(date +%s)" -ge "$deadline" ] && return 1
    sleep $(( 15 + RANDOM % 15 ))
  done
}

BEFORE="$(git -C "$W" merge-base github/main HEAD)"
if [ "$SKIP_DISPATCH" != 1 ]; then
  [ -e "$CACHE_ROOT/watchdog/codex-paused" ] && fail codex-paused "codex paused by the owner (watchdog/codex-paused); not dispatching"
  wait_for_slot || fail no-slot "no free worker slot within ${SLOT_WAIT_S}s (cap/live: $(slots))"
  RESUME=(); [ -s "$STATE/$N.thread" ] && RESUME=(--resume "$(cat "$STATE/$N.thread")")
  DRC=0
  for attempt in 1 2 3; do
    log "dispatch $ROLE for #$N (requested model $MIPSTARRE_CODEX_MODEL; model_policy.py resolves it, attempt $attempt)"
    # The global launch lock serializes the DISPATCH CALL only: waiting for a
    # slot inside it capped the whole pipeline at ~2.4 launches/minute and let
    # one starved lane block every other for up to six hours.
    exec 9>"$CACHE_ROOT/watchdog/launch.lock"; flock 9
    local/bin/dispatch.sh --role "$ROLE" --issue "$N" --worktree "$W" --sandbox workspace-write \
      ${RESUME[@]+"${RESUME[@]}"} --context-file "$TASK" -- "$(head -8 "$TASK")" \
      > "$STATE/$N.dispatch.log" 2>&1 &
    DPID=$!
    sleep $(( 2 + RANDOM % 6 ))   # short jittered hold, not a fixed 25 s
    flock -u 9
    wait "$DPID"; DRC=$?
    grep -o 'thread_id: [0-9a-f-]*' "$STATE/$N.dispatch.log" | tail -1 | cut -d' ' -f2 > "$STATE/$N.thread"
    if grep -q "429 Too Many Requests" "$STATE/$N.dispatch.log" && [ "$(grep -c item.completed "$STATE/$N.dispatch.log")" -lt 3 ]; then
      log "rate-limited before doing work; waiting 5 min"; sleep 300; continue
    fi
    break
  done
  log "dispatch exit $DRC"
  if [ -n "$(git -C "$W" status --porcelain | grep -v '^?? ')" ]; then
    fail uncommitted-worker-changes "worker left uncommitted changes (see $STATE/$N.dispatch.log)"
  fi
fi
[ "$(git -C "$W" rev-list --count "$BEFORE..HEAD")" -gt 0 ] || fail no-commits-ahead "no commits ahead of main for #$N"

# ------------------------------------------------ fresh base (gate 2b) + #222
git -C "$W" merge -q --no-edit github/main || fail merge-conflicted "merging github/main conflicted in $W"
# post-merge silent-loss guard (issue #222): a path present on github/main but
# absent after the merge must have been deleted by a branch commit, never by
# the merge itself.
LOST=""
for f in $(git -C "$W" diff --name-only --diff-filter=D github/main HEAD); do
  if [ -z "$(git -C "$W" log --no-merges --format=%h github/main..HEAD -- "$f" | head -1)" ]; then LOST="$LOST $f"; fi
done
[ -z "$LOST" ] || fail merge-loss-guard "merge of github/main left paths missing that main carries (issue #222):$LOST"
AFTER="$(git -C "$W" rev-parse HEAD)"

# ------------------------------------------------------------ pre-push build
# DESIGN.md invariant 7: at most one full `lake build` machine-wide.  The same
# advisory lease directory ci.sh takes, so a lane build and a CI build queue
# for each other instead of thrashing the NVMe cache.
lock_owner_alive() {
  local pid; pid="$(head -n 1 "$1/owner" 2>/dev/null || true)"
  case "$pid" in ''|*[!0-9]*) return 1 ;; esac
  kill -0 "$pid" 2>/dev/null
}
acquire_build_lock() {
  local waited=0 age stamp
  mkdir -p "$(dirname "$BUILD_LOCK")"
  while ! mkdir "$BUILD_LOCK" 2>/dev/null; do
    if lock_owner_alive "$BUILD_LOCK"; then
      :
    elif [ -f "$BUILD_LOCK/owner" ]; then
      log "breaking stale build lock (owner process is dead)"; rm -rf "$BUILD_LOCK"; continue
    else
      stamp="$(stat -c %Y "$BUILD_LOCK" 2>/dev/null || echo 0)"
      age=$(( $(date +%s) - stamp ))
      if [ "$age" -gt "$BUILD_LOCK_STALE_S" ]; then
        log "breaking stale build lock (no owner stamp, ${age}s old)"; rm -rf "$BUILD_LOCK"; continue
      fi
    fi
    [ "$waited" -ge "$BUILD_LOCK_WAIT_S" ] && return 1
    [ "$waited" = 0 ] && log "waiting for the machine-wide build lock $BUILD_LOCK"
    sleep 5; waited=$(( waited + 5 ))
  done
  printf '%s\n%s\nlane.sh lane=%s sha=%s\n' "$$" "$(now)" "$N" "$AFTER" > "$BUILD_LOCK/owner"
  HELD_LOCK="$BUILD_LOCK"
  return 0
}
release_build_lock() { [ -n "$HELD_LOCK" ] && rm -rf "$HELD_LOCK"; HELD_LOCK=""; }

acquire_build_lock || fail build-lock-timeout "could not take $BUILD_LOCK within ${BUILD_LOCK_WAIT_S}s"
log "lake build MIPStarRE.QPBT before the push gate (build lock held)"
( cd "$W" && timeout 2700 lake build MIPStarRE.QPBT > "$STATE/$N.build.log" 2>&1 ) || {
  release_build_lock; fail build-failed "lake build before push failed (see $STATE/$N.build.log)"; }
# v20 (2026-09-12): modules outside the MIPStarRE.QPBT import closure (e.g.
# Combining.Points.Absorption, MarginalContraction) get no olean from the
# umbrella build, so the changed modules are built explicitly; the per-file
# pre-push gate needs their oleans.  W7's reachability guard makes this
# belt-and-braces rather than load-bearing.
CHANGED_MODS="$(git -C "$W" diff --name-only --diff-filter=ACMR github/main HEAD -- 'MIPStarRE/*.lean' 2>/dev/null \
  | grep -v -E '/Test/' | sed -e 's#/#.#g' -e 's#\.lean$##' | tr '\n' ' ')"
if [ -n "$CHANGED_MODS" ]; then
  log "lake build of changed modules: $(printf '%s' "$CHANGED_MODS" | wc -w)"
  ( cd "$W" && timeout 2700 lake build $CHANGED_MODS >> "$STATE/$N.build.log" 2>&1 ) || {
    release_build_lock; fail build-failed "lake build of changed modules failed (see $STATE/$N.build.log)"; }
fi
release_build_lock

# ------------------------------------------------------------- publication
# pr_open.py -> checked-push.sh is the ONLY publication path.  There is no
# fallback: the deleted one forged the pre-push ref tuple and pushed with the
# hook-skipping override, losing --force-with-lease and the post-preflight
# tree and SHA re-verification.
log "opening PR"
PRB="$STATE/$N.pr.md"
{ echo "## Motivation"; echo; echo "Stage 4.3 proof packet for issue #$N (see the issue body for targets, sources and plan)."; echo
  echo "## Description"; echo; git -C "$W" log --format="- %s" "$BEFORE..$AFTER"; echo
  echo "## Testing"; echo; echo "Worker checked every changed file with \`lake env lean\`; exact-head CI and review follow."; } > "$PRB"
PR="$(local/bin/pr_open.py --branch "$BR" --issue "$N" --title "$ISSUE_TITLE" \
      --body-file "$PRB" --label formalization)" \
  || fail pr-open-failed "pr_open failed for #$N on $BR (see the lane log); not publishing by any other path"
[ -n "$PR" ] || fail pr-open-failed "pr_open returned no PR number for #$N"
echo "PR=$PR"
for _ in $(seq 1 30); do [ "$(gh pr view "$PR" --json headRefOid --jq .headRefOid)" = "$AFTER" ] && break; sleep 10; done

log "ci.sh $PR"; local/bin/ci.sh "$PR" >> "$STATE/$N.ci.log" 2>&1; echo "CI_EXIT=$?"

# --------------------------------------------------------------- review
if [ "${SKIP_REVIEW:-0}" = 1 ]; then
  log "review skipped (stacked PR; base still open)"
else
  if [ -e "$CACHE_ROOT/watchdog/codex-paused" ] && [ -z "${MIPSTARRE_REVIEW_CMD:-}" ]; then
    fail codex-paused "codex is paused; the review of PR $PR was not started"
  fi
  wait_for_slot || fail no-slot "no free worker slot for the review within ${SLOT_WAIT_S}s"
  log "$REVIEW_CMD $PR"
  exec 9>"$CACHE_ROOT/watchdog/launch.lock"; flock 9
  "$REVIEW_CMD" "$PR" >> "$STATE/$N.review.log" 2>&1 &
  RPID=$!
  sleep $(( 2 + RANDOM % 6 ))
  flock -u 9
  wait "$RPID"; echo "REVIEW_EXIT=$?"
fi

gh api "repos/${MIPSTARRE_GITHUB_REPO:-Dengnifer/MIPStarRE-A}/commits/$AFTER/status" \
  --jq '.statuses[] | select(.context|endswith("summary")) | .context+" "+.state+" "+(.description // "")'
printf 'PR=%s HEAD=%s TOOL=lane.sh VERSION=%s\n' "$PR" "$AFTER" "$TOOL_VERSION" > "$STATE/$N.done"
log "lane done"
