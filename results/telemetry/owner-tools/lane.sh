#!/usr/bin/env bash
# lane.sh — one stage-4.3 proof lane, run detached on ghz by the owner-operator.
#   lane.sh <issue> <slug> [prover|orc]
# Creates/warms the worktree, dispatches a codex worker with the issue body as
# the task, then (if the worker committed) opens the PR, runs CI and review.
# Merging is left to the operator (gate decisions). Writes markers under
# $STATE/lanes/<issue>.{done,needs-attention} and a log next to them.
set -u
export PATH="$HOME/.cache/mipstarre-dev/owner-bin:$HOME/.local/bin:$HOME/.elan/bin:$PATH"
export MIPSTARRE_CODEX_MODEL="${MIPSTARRE_CODEX_MODEL:-$(cat "$HOME/.cache/mipstarre-dev/watchdog/model.txt" 2>/dev/null || echo gpt-5.6-sol)}"
export MIPSTARRE_SESSION="owner-operator"
N="$1"; SLUG="$2"; ROLE="${3:-prover}"
P="$HOME/MIPStarRE-qpbt"; BR="${LANE_BRANCH:-issue-$N-$SLUG}"; W="$P/.worktrees/$BR"
SKIP_DISPATCH="${SKIP_DISPATCH:-0}"   # 1 = the worktree already holds the finished work; go straight to PR
STATE="$HOME/.cache/mipstarre-dev/watchdog/lanes"; mkdir -p "$STATE"
rm -f "$STATE/$N.done" "$STATE/$N.needs-attention"
fail() { echo "$(date -u +%FT%TZ) $*" | tee "$STATE/$N.needs-attention"; exit 1; }
log() { echo "== $(date -u +%FT%TZ) $*"; }
cd "$P" || exit 1
git fetch -q github

if [ ! -d "$W" ]; then
  log "worktree $BR from github/main"
  git worktree add -q -b "$BR" "$W" github/main || fail "worktree add failed"
fi
log "warming $W"
local/bin/worktree-setup.sh "$W" >/dev/null 2>&1 || log "warm finished with warnings"
[ -L "$W/.lake/packages" ] || bash /tmp/migrate-packages.sh "$W" >/dev/null 2>&1 || true

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

BEFORE=$(git -C "$W" merge-base github/main HEAD)
if [ "$SKIP_DISPATCH" != 1 ]; then
  # concurrency gate: the codex API rate-limits (HTTP 429) above ~5 sessions
  MAX_CODEX="${MAX_CODEX:-7}"
  live() { pgrep -fa 'codex exec' | grep -o '\-C [^ ]*' | sort -u | wc -l; }
  exec 9>"$HOME/.cache/mipstarre-dev/watchdog/launch.lock"; flock 9
  for _ in $(seq 1 720); do [ "$(live)" -lt "$MAX_CODEX" ] && break; sleep 30; done
  RESUME=(); [ -s "$STATE/$N.thread" ] && RESUME=(--resume "$(cat "$STATE/$N.thread")")
  for attempt in 1 2 3; do
    log "dispatch $ROLE for #$N (model $MIPSTARRE_CODEX_MODEL, attempt $attempt${RESUME:+, resuming ${RESUME[1]}})"
    local/bin/dispatch.sh --role "$ROLE" --issue "$N" --worktree "$W" --sandbox workspace-write \
      "${RESUME[@]}" --context-file "$TASK" -- "$(head -8 "$TASK")" > "$STATE/$N.dispatch.log" 2>&1 &
    DPID=$!; sleep 25; flock -u 9; wait "$DPID"
    DRC=$?
    grep -o 'thread_id: [0-9a-f-]*' "$STATE/$N.dispatch.log" | tail -1 | cut -d' ' -f2 > "$STATE/$N.thread"
    if grep -q "429 Too Many Requests" "$STATE/$N.dispatch.log" && [ "$(grep -c item.completed "$STATE/$N.dispatch.log")" -lt 3 ]; then
      log "rate-limited before doing work; waiting 5 min"; sleep 300; continue
    fi
    break
  done
  log "dispatch exit $DRC"
  if [ -n "$(git -C "$W" status --porcelain | grep -v '^?? ')" ]; then
    fail "worker left uncommitted changes (see $STATE/$N.dispatch.log)"
  fi
fi
[ "$(git -C "$W" rev-list --count "$BEFORE..HEAD")" -gt 0 ] || fail "no commits ahead of main for #$N"
# fresh-base (gate 2b): main may have moved since the worktree was created
PRE_MERGE=$(git -C "$W" rev-parse HEAD)
git -C "$W" merge -q --no-edit github/main || fail "merging github/main conflicted in $W"
AFTER=$(git -C "$W" rev-parse HEAD)
# the pre-push per-file gate needs the oleans of every module the merge changed
if [ "$PRE_MERGE" != "$AFTER" ] && git -C "$W" diff --name-only "$PRE_MERGE" "$AFTER" | grep -q '\.lean$'; then
  log "merge brought Lean changes; incremental lake build before push"
  ( cd "$W" && timeout 1800 lake build > "$STATE/$N.build.log" 2>&1 ) || fail "lake build after the merge failed (see $STATE/$N.build.log)"
fi

log "opening PR"
PRB="$STATE/$N.pr.md"
{ echo "## Motivation"; echo; echo "Stage 4.3 proof packet for issue #$N (see the issue body for targets, sources and plan)."; echo
  echo "## Description"; echo; git -C "$W" log --format="- %s" "$BEFORE..$AFTER"; echo
  echo "## Testing"; echo; echo "Worker checked every changed file with \`lake env lean\`; exact-head CI and review follow."; } > "$PRB"
TITLE=$(gh issue view "$N" --json title --jq .title)
PR=$(local/bin/pr_open.py --branch "$BR" --issue "$N" --title "$TITLE" --body-file "$PRB" --label formalization) || {
  log "pr_open failed; pushing directly and retrying (pre-push output in $STATE/$N.push.log)"
  git -C "$W" push github "refs/heads/$BR:refs/heads/$BR" > "$STATE/$N.push.log" 2>&1 || fail "direct push failed (see $STATE/$N.push.log)"
  PR=$(local/bin/pr_open.py --branch "$BR" --issue "$N" --title "$TITLE" --body-file "$PRB" --label formalization) || fail "pr_open failed after direct push"
}
echo "PR=$PR"
for _ in $(seq 1 30); do [ "$(gh pr view "$PR" --json headRefOid --jq .headRefOid)" = "$AFTER" ] && break; sleep 10; done
log "ci.sh $PR"; local/bin/ci.sh "$PR" >> "$STATE/$N.ci.log" 2>&1; echo "CI_EXIT=$?"
MAXR="${MAX_CODEX:-7}"
exec 9>"$HOME/.cache/mipstarre-dev/watchdog/launch.lock"; flock 9
for _ in $(seq 1 720); do [ "$(pgrep -fa 'codex exec' | grep -o '\-C [^ ]*' | sort -u | wc -l)" -lt "$MAXR" ] && break; sleep 30; done
log "review.sh $PR"; local/bin/review.sh "$PR" >> "$STATE/$N.review.log" 2>&1 &
RPID=$!; sleep 25; flock -u 9; wait "$RPID"; echo "REVIEW_EXIT=$?"
gh api "repos/Dengnifer/MIPStarRE-A/commits/$AFTER/status" --jq '.statuses[] | select(.context|endswith("summary")) | .context+" "+.state+" "+(.description // "")'
echo "PR=$PR HEAD=$AFTER" > "$STATE/$N.done"
log "lane done"
