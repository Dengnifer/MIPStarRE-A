#!/usr/bin/env bash
# lane.sh <issue> <slug> [prover|orc] — one worker lane, run detached.
# Creates and warms the worktree, dispatches one codex worker with the issue body as the
# task, and then (if the worker committed) merges the base in, builds, opens the PR and
# runs CI and review.  Merging the PR is NOT part of a lane: that is the gate's and the
# merge daemon's decision.  Markers: <state>/lanes/<issue>.{done,needs-attention}, with
# the per-step logs beside them.
#
# SKIP_DISPATCH=1 skips the worker and goes straight to the refresh-and-PR tail — this
# is how the merge daemon refreshes a stale PR.
# LANE_BRANCH=<branch> works on an existing branch instead of issue-<n>-<slug>.
# SKIP_REVIEW=1 for a stacked PR whose base PR is still open (its review would read the
# base's files too).
#
# Rules paid for in incidents:
#   * Launches are serialised through <state>/launch.lock with a grace period: rate and
#     concurrency limits are per ACCOUNT, not per process.
#   * After merging the base in, a path that the base carries but the merge result does
#     not must have been deleted by a branch commit, never by the merge — otherwise the
#     lane stops (silent merge loss).
#   * Build before pushing: the per-file pre-push gate needs the build products of every
#     module the merge changed, and modules outside the root import closure get none
#     from the umbrella build, so changed modules are built explicitly.
#
# Provenance: kit-src/tmp-scripts/lane-v17.sh, hard-coded to one repository path, one
# cache directory, one library name, one model and one NVMe build pool.
set -u
KIT_SERVICE_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd -P)"
# shellcheck source=/dev/null
. "$KIT_SERVICE_DIR/service-lib.sh"

N="${1:?usage: lane.sh <issue> <slug> [role]}"; SLUG="${2:?usage: lane.sh <issue> <slug> [role]}"
ROLE="${3:-prover}"
BASE="${KIT_BASE_BRANCH:-main}"
P="$KIT_REPO_ROOT"; BR="${LANE_BRANCH:-issue-$N-$SLUG}"; W="$P/.worktrees/$BR"
SKIP_DISPATCH="${SKIP_DISPATCH:-0}"
STATE="$KIT_LANE_DIR"; mkdir -p "$STATE"
export MIPSTARRE_SESSION="${MIPSTARRE_SESSION:-service-lane}"
MODEL="${MIPSTARRE_CODEX_MODEL:-$(cat "$KIT_STATE_DIR/model.txt" 2>/dev/null || echo "$KIT_WORKER_MODEL")}"
[ -n "$MODEL" ] && export MIPSTARRE_CODEX_MODEL="$MODEL"

rm -f "$STATE/$N.done" "$STATE/$N.needs-attention"
fail() { echo "$(date -u +%FT%TZ) $*" | tee "$STATE/$N.needs-attention"; exit 1; }
log() { kit_log "$*"; }
cd "$P" || exit 1
git fetch -q github

if [ ! -d "$W" ]; then
  log "worktree $BR from github/$BASE"
  git worktree add -q -b "$BR" "$W" "github/$BASE" || fail "worktree add failed"
fi
# Optional: put the worktree's build products on a faster pool.  The pool is a local
# machine fact, so it lives in the state directory, not in the repository.
POOL="${KIT_LAKE_POOL:-$(cat "$KIT_STATE_DIR/lake-pool" 2>/dev/null || true)}"
if [ -n "$POOL" ] && [ ! -L "$W/.lake" ] && { [ ! -e "$W/.lake" ] || [ -z "$(ls -A "$W/.lake" 2>/dev/null)" ]; }; then
  rm -rf "$W/.lake"; mkdir -p "$POOL/lake/$BR"; ln -s "$POOL/lake/$BR" "$W/.lake"; log ".lake -> $POOL/lake/$BR"
fi
log "warming $W"
local/bin/worktree-setup.sh "$W" >/dev/null 2>&1 || log "warm finished with warnings"
MIGRATE="$P/results/telemetry/owner-tools/migrate-packages.sh"
[ -L "$W/.lake/packages" ] || { [ -x "$MIGRATE" ] && bash "$MIGRATE" "$W" >/dev/null 2>&1; } || true

TASK="$STATE/$N.task.md"
{
  echo "You are dispatched for GitHub issue #$N in the worktree $W (branch $BR)."
  echo "Rules: work only in this worktree; prove the target declarations WITHOUT changing public signatures;"
  echo "never add sorry, axioms, or hypotheses to paper-labelled statements; check every changed file with"
  echo "\`lake env lean <file>\`; commit with conventional subjects; do NOT push;"
  echo "do NOT edit $KIT_LEAN_ROOT.lean (the operator serialises re-exports; name any re-export you need in your report);"
  echo "if the worktree already contains partial work for this issue, continue from it rather than restarting;"
  echo "when done, or if blocked, end with a short report: what is proved, what remains and why."
  echo; echo "----- ISSUE #$N -----"
  gh issue view "$N" --json title,body --jq '"# "+.title+"\n\n"+.body'
  if [ -f "$STATE/$N.repair.md" ]; then
    echo; echo "----- REPAIR REQUEST FROM THE OPERATOR (do this first) -----"; cat "$STATE/$N.repair.md"
  fi
} > "$TASK"

BEFORE=$(git -C "$W" merge-base "github/$BASE" HEAD)
DRC=0
if [ "$SKIP_DISPATCH" != 1 ]; then
  [ -e "$KIT_STATE_DIR/codex-paused" ] && fail "workers are paused ($KIT_STATE_DIR/codex-paused); not dispatching"
  kit_wait_for_slot
  RESUME=(); [ -s "$STATE/$N.thread" ] && RESUME=(--resume "$(cat "$STATE/$N.thread")")
  EFFORT=(); [ -n "$KIT_WORKER_EFFORT" ] && EFFORT=(--effort "$KIT_WORKER_EFFORT")
  for attempt in 1 2 3; do
    log "dispatch $ROLE for #$N (model ${MIPSTARRE_CODEX_MODEL:-codex default}, attempt $attempt)"
    local/bin/dispatch.sh --role "$ROLE" --issue "$N" --worktree "$W" --sandbox workspace-write \
      "${RESUME[@]}" "${EFFORT[@]}" --context-file "$TASK" -- "$(head -8 "$TASK")" \
      > "$STATE/$N.dispatch.log" 2>&1 &
    DPID=$!; sleep 25; flock -u 9; wait "$DPID"; DRC=$?
    grep -o 'thread_id: [0-9a-f-]*' "$STATE/$N.dispatch.log" | tail -1 | cut -d' ' -f2 > "$STATE/$N.thread"
    if grep -q "429 Too Many Requests" "$STATE/$N.dispatch.log" \
       && [ "$(grep -c item.completed "$STATE/$N.dispatch.log")" -lt 3 ]; then
      log "rate-limited before doing any work; waiting 5 min"; sleep 300; continue
    fi
    break
  done
  log "dispatch exit $DRC"
  if [ -n "$(git -C "$W" status --porcelain | grep -v '^?? ')" ]; then
    fail "the worker left uncommitted changes (see $STATE/$N.dispatch.log)"
  fi
fi
[ "$(git -C "$W" rev-list --count "$BEFORE..HEAD")" -gt 0 ] || fail "no commits ahead of $BASE for #$N"

# Fresh base (merge gate 2b): the base may have moved since the worktree was created.
git -C "$W" merge -q --no-edit "github/$BASE" || fail "merging github/$BASE conflicted in $W"
LOST=""
for f in $(git -C "$W" diff --name-only --diff-filter=D "github/$BASE" HEAD); do
  if [ -z "$(git -C "$W" log --no-merges --format=%h "github/$BASE..HEAD" -- "$f" | head -1)" ]; then LOST="$LOST $f"; fi
done
[ -z "$LOST" ] || fail "merging github/$BASE left paths missing that $BASE carries:$LOST"
AFTER=$(git -C "$W" rev-parse HEAD)

log "lake build $KIT_LEAN_ROOT before the push gate"
( cd "$W" && timeout "${KIT_BUILD_TIMEOUT:-2700}" lake build "$KIT_LEAN_ROOT" > "$STATE/$N.build.log" 2>&1 ) \
  || fail "lake build before the push failed (see $STATE/$N.build.log)"
CHANGED_MODS=$(git -C "$W" diff --name-only --diff-filter=ACMR "github/$BASE" HEAD -- "$KIT_LEAN_ROOT/*.lean" 2>/dev/null \
  | grep -v -E '/Test/' | sed -e 's#/#.#g' -e 's#\.lean$##' | tr '\n' ' ')
if [ -n "$CHANGED_MODS" ]; then
  log "lake build of changed modules: $(echo "$CHANGED_MODS" | wc -w)"
  # shellcheck disable=SC2086
  ( cd "$W" && timeout "${KIT_BUILD_TIMEOUT:-2700}" lake build $CHANGED_MODS >> "$STATE/$N.build.log" 2>&1 ) \
    || fail "lake build of the changed modules failed (see $STATE/$N.build.log)"
fi

log "opening PR"
PRB="$STATE/$N.pr.md"
{ echo "## Motivation"; echo; echo "Proof packet for issue #$N (see the issue body for targets, sources and plan)."; echo
  echo "## Description"; echo; git -C "$W" log --format="- %s" "$BEFORE..$AFTER"; echo
  echo "## Testing"; echo; echo "Worker checked every changed file with \`lake env lean\`; exact-head CI and review follow."; } > "$PRB"
TITLE=$(gh issue view "$N" --json title --jq .title)
PR=$(local/bin/pr_open.py --branch "$BR" --issue "$N" --title "$TITLE" --body-file "$PRB" --label formalization) || {
  log "pr_open failed; pushing directly and retrying (pre-push output in $STATE/$N.push.log)"
  ( cd "$W" && printf "%s %s %s %s\n" "refs/heads/$BR" "$(git rev-parse HEAD)" "refs/heads/$BR" "$(git rev-parse "github/$BASE")" \
      | sh .githooks/pre-push github "$(git remote get-url github)" ) > "$STATE/$N.push.log" 2>&1 || true
  # The hook prints "<library> pre-push: ok"; match the invariant tail, not the name,
  # so a renamed library does not silently turn this check into a no-op.
  grep -q "pre-push: ok" "$STATE/$N.push.log" || fail "the pre-push gate failed (see $STATE/$N.push.log)"
  MIPSTARRE_SKIP_HOOKS=1 git -C "$W" push github "refs/heads/$BR:refs/heads/$BR" >> "$STATE/$N.push.log" 2>&1 \
    || fail "direct push failed (see $STATE/$N.push.log)"
  PR=$(local/bin/pr_open.py --branch "$BR" --issue "$N" --title "$TITLE" --body-file "$PRB" --label formalization) \
    || fail "pr_open failed after the direct push"
}
echo "PR=$PR"
for _ in $(seq 1 30); do [ "$(gh pr view "$PR" --json headRefOid --jq .headRefOid)" = "$AFTER" ] && break; sleep 10; done
log "ci.sh $PR"; local/bin/ci.sh "$PR" >> "$STATE/$N.ci.log" 2>&1; echo "CI_EXIT=$?"

if [ "${SKIP_REVIEW:-0}" = 1 ]; then
  log "review skipped (stacked PR; its base is still open)"
elif [ -e "$KIT_STATE_DIR/codex-paused" ]; then
  log "review skipped: workers are paused ($KIT_STATE_DIR/codex-paused)"
else
  kit_wait_for_slot
  log "review.sh $PR"; local/bin/review.sh "$PR" >> "$STATE/$N.review.log" 2>&1 &
  RPID=$!; sleep 25; flock -u 9; wait "$RPID"; echo "REVIEW_EXIT=$?"
fi
SLUG_REPO="$(kit_slug)" && gh api "repos/$SLUG_REPO/commits/$AFTER/status" \
  --jq '.statuses[] | select(.context|endswith("summary")) | .context+" "+.state+" "+(.description // "")'
echo "PR=$PR HEAD=$AFTER" > "$STATE/$N.done"
log "lane done"
