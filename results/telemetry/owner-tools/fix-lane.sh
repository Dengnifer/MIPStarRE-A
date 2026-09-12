#!/usr/bin/env bash
#
# fix-lane.sh — the one lane-repair entry point, called by the merge daemon and
# by local/bin/janitor.sh.  Version 2 (2026-09-12): a thin, versioned wrapper
# around an orc dispatch whose task text comes from the committed briefs
# local/briefs/lane-repair-merge.md and local/briefs/lane-repair-build.md, not
# from a shell string literal.
#
# Usage: fix-lane.sh <PR> <LANE> <BRANCH> <merge|build> [--dry-run]
#
#   merge   the worktree is mid-merge of github/main with conflicts (or still
#           needs the merge)          -> resolve the conflicts and commit the merge
#   build   the merge is committed but `lake build` fails (renamed or removed
#           modules, broken proofs)   -> repair the branch and commit
#
# What it does, in order:
#
#   1. resolves the repository checkout and the worktree of <BRANCH>
#      registry-first (`git worktree list --porcelain`), never by guessing a path;
#   2. renders the committed brief for <mode> into
#      $CACHE_ROOT/watchdog/lanes/<LANE>.repair-task.md and refuses to dispatch
#      if any {{PLACEHOLDER}} is left unresolved;
#   3. dispatches ONE orc worker through local/bin/dispatch.sh (agents never
#      invoke codex directly — AGENTS.md / local/protocols/sessions.md);
#   4. relaunches the lane tail through the repository's local/bin/lane.sh with
#      SKIP_DISPATCH=1 — and only when the worktree is clean and not mid-merge.
#      There is no /tmp fallback: if local/bin/lane.sh is missing the lane stays
#      parked and this script exits nonzero;
#   5. when that tail finishes, clears the daemon's pr<PR>.failed marker so the
#      next scan can consider the PR again;
#   6. appends one attempt row and one outcome row to the repair ledger
#      $CACHE_ROOT/watchdog/janitor/repairs.jsonl.
#
# It never pushes, never merges, never touches a gate: the lane publishes through
# pr_open.py -> checked-push.sh, and a repair that drops paths main carries still
# fails the lane's post-merge missing-path check and merge_loss_guard.py.
#
# Exit codes:
#   0  repaired and the lane tail was relaunched (or --dry-run printed the plan)
#   2  usage / environment error (bad mode, missing checkout, missing brief)
#   3  the orc dispatch failed
#   4  the worktree is still mid-merge or dirty; the lane stays parked
#   5  the lane tail could not be relaunched (local/bin/lane.sh missing)
#
# Environment:
#   MIPSTARRE_REPO_ROOT    repository checkout (default: ~/MIPStarRE-qpbt, then
#                          the checkout this file sits in)
#   MIPSTARRE_CACHE_ROOT   override ~/.cache/mipstarre-dev
#   MIPSTARRE_GITHUB_REPO  owner/repo used in the rendered brief
#   MIPSTARRE_FIXLANE_LOCK_WAIT  dispatch --lock-wait seconds (default 900)

set -uo pipefail

PROG="fix-lane.sh"

usage() {
  sed -n '2,30p' "${BASH_SOURCE[0]}" | sed 's/^# \{0,1\}//'
}

die() { printf '%s: %s\n' "$PROG" "$2" >&2; exit "$1"; }

DRY_RUN=0
ARGS=()
for arg in "$@"; do
  case "$arg" in
    --dry-run) DRY_RUN=1 ;;
    -h|--help) usage; exit 0 ;;
    --*) die 2 "unknown option $arg" ;;
    *) ARGS[${#ARGS[@]}]="$arg" ;;
  esac
done
[ "${#ARGS[@]}" -eq 4 ] || die 2 "usage: $PROG <PR> <LANE> <BRANCH> <merge|build> [--dry-run]"

PR="${ARGS[0]}"; LANE="${ARGS[1]}"; BR="${ARGS[2]}"; MODE="${ARGS[3]}"
case "$PR" in ''|*[!0-9]*) die 2 "PR must be a number, got '$PR'";; esac
case "$LANE" in ''|*[!0-9]*) die 2 "LANE must be a number, got '$LANE'";; esac
case "$BR" in ''|*[![:alnum:]._/-]*) die 2 "BRANCH has characters that do not belong in a ref: '$BR'";; esac
case "$MODE" in merge|build) ;; *) die 2 "mode must be 'merge' or 'build', got '$MODE'";; esac

# --------------------------------------------------------------- locations

SCRIPT_DIR="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd)"
CACHE_ROOT="${MIPSTARRE_CACHE_ROOT:-$HOME/.cache/mipstarre-dev}"
W="$CACHE_ROOT/watchdog"; L="$W/lanes"; D="$W/daemon"; J="$W/janitor"

resolve_repo_root() {
  local candidate
  for candidate in "${MIPSTARRE_REPO_ROOT:-}" "$HOME/MIPStarRE-qpbt" \
                   "$(cd -- "$SCRIPT_DIR/../../.." 2>/dev/null && pwd)"; do
    [ -n "$candidate" ] || continue
    if [ -f "$candidate/AGENTS.md" ] && [ -d "$candidate/local/bin" ]; then
      printf '%s\n' "$candidate"; return 0
    fi
  done
  return 1
}
REPO_ROOT="$(resolve_repo_root)" \
  || die 2 "no repository checkout found (set MIPSTARRE_REPO_ROOT to the checkout with AGENTS.md)"

mkdir -p "$L" "$D" "$J" || die 2 "cannot create runtime state under $W"
LOG="$L/$LANE.fix.log"

version() {
  if [ -s "$CACHE_ROOT/owner-bin/tools-version" ]; then
    head -n 1 "$CACHE_ROOT/owner-bin/tools-version"
  else
    git -C "$REPO_ROOT" describe --always --dirty 2>/dev/null || echo unknown
  fi
}

log() { printf '== %s %s\n' "$(date -u +%FT%TZ)" "$*" | tee -a "$LOG"; }

# setsid detaches the relaunched lane from this repair's session; where it does
# not exist (non-Linux), nohup alone is used.
DETACH=""
command -v setsid >/dev/null 2>&1 && DETACH="setsid"

json_row() {
  python3 -c 'import json,sys; print(json.dumps(dict(zip(sys.argv[1::2], sys.argv[2::2])), ensure_ascii=False))' "$@"
}
ledger() { printf '%s\n' "$(json_row "$@")" >> "$J/repairs.jsonl"; }

# Reported first so a lane log always names the code that produced it (§7.6).
printf 'tool=%s version=%s\n' "$PROG" "$(version)" | tee -a "$LOG"
log "repair request: PR $PR lane $LANE branch $BR mode $MODE (repo $REPO_ROOT)"

# The attempt row is written here, before anything can fail, so that every
# invocation — this script's own failures included — counts against the
# janitor's per-lane repair cap.  A dry run consumes no budget.
if [ "$DRY_RUN" -eq 0 ]; then
  ledger key "lane:$LANE" event attempt action repair mode "$MODE" pr "$PR" lane "$LANE" \
         branch "$BR" ts "$(date -u +%FT%TZ)" tool "$PROG"
fi

# --------------------------------------------------------------- worktree

# Registry-first, exactly as autofix.sh:resolve_worktree does: a worktree whose
# path looks right may hold a different branch (PR 213, 2026-09-12).
resolve_worktree() {
  local helper="$REPO_ROOT/local/bin/worktree_resolve.sh" path=""
  if [ -x "$helper" ]; then
    path="$("$helper" "$BR" 2>/dev/null | head -n 1)"
    [ -n "$path" ] && { printf '%s\n' "$path"; return 0; }
  fi
  path="$(git -C "$REPO_ROOT" worktree list --porcelain 2>/dev/null \
    | awk -v ref="refs/heads/$BR" '
        /^worktree /   { wt = substr($0, 10) }
        /^branch /     { if (substr($0, 8) == ref) { print wt; exit } }')"
  [ -n "$path" ] || return 1
  printf '%s\n' "$path"
}

WT="$(resolve_worktree)" || {
  log "no worktree registered for branch $BR (worktree-mismatch); lane stays parked"
  ledger key "lane:$LANE" event outcome action repair mode "$MODE" pr "$PR" lane "$LANE" \
         branch "$BR" outcome worktree-missing ts "$(date -u +%FT%TZ)"
  exit 2
}
[ -e "$WT/.git" ] || die 2 "resolved worktree $WT is not a git worktree"
log "worktree $WT"

# --------------------------------------------------------------- brief

BRIEF="$REPO_ROOT/local/briefs/lane-repair-$MODE.md"
[ -f "$BRIEF" ] || die 2 "missing committed brief $BRIEF"
TASK="$L/$LANE.repair-task.md"
SLUG="$(printf '%s' "$BR" | sed -E 's/^issue-[0-9]+-//')"
REPO_SLUG="${MIPSTARRE_GITHUB_REPO:-$(git -C "$REPO_ROOT" remote get-url github 2>/dev/null \
  | sed -E 's#.*github\.com[:/]([^/]+/[^/]+?)(\.git)?$#\1#')}"
REPO_SLUG="${REPO_SLUG:-the repository}"

PR="$PR" LANE="$LANE" BR="$BR" WT="$WT" REPO_SLUG="$REPO_SLUG" \
BRIEF="$BRIEF" TASK="$TASK" python3 - <<'PY' || die 2 "rendering $BRIEF failed"
import os, re, sys
text = open(os.environ["BRIEF"], encoding="utf-8").read()
for key, value in (("PR", os.environ["PR"]), ("LANE", os.environ["LANE"]),
                   ("BRANCH", os.environ["BR"]), ("WORKTREE", os.environ["WT"]),
                   ("REPO", os.environ["REPO_SLUG"])):
    text = text.replace("{{%s}}" % key, value)
left = sorted(set(re.findall(r"\{\{[A-Z_]+\}\}", text)))
if left:
    sys.exit("fix-lane.sh: unresolved placeholders in the brief: " + " ".join(left))
open(os.environ["TASK"], "w", encoding="utf-8").write(text)
PY
log "task rendered from $BRIEF into $TASK"

if [ "$DRY_RUN" -eq 1 ]; then
  log "dry run: would dispatch an orc in $WT and relaunch lane $LANE with SKIP_DISPATCH=1"
  exit 0
fi

# --------------------------------------------------------------- orc dispatch

DISPATCH="$REPO_ROOT/local/bin/dispatch.sh"
[ -x "$DISPATCH" ] || die 2 "missing $DISPATCH (repairs go through the dispatcher, never through codex)"

unset MIPSTARRE_CODEX_MODEL
export MIPSTARRE_SESSION="${MIPSTARRE_SESSION:-lane-repair}"
export MIPSTARRE_ACCOUNT_WAIT="${MIPSTARRE_ACCOUNT_WAIT:-3600}"

log "orc dispatch for PR $PR ($BR), mode $MODE"
( cd "$REPO_ROOT" && "$DISPATCH" --role orc --issue "pr$PR" --pr "$PR" --worktree "$WT" \
    --sandbox workspace-write --persona local/personas/orchestrator.md \
    --lock-wait "${MIPSTARRE_FIXLANE_LOCK_WAIT:-900}" \
    --context-file "$TASK" -- "$(cat "$TASK")" ) >> "$LOG" 2>&1 < /dev/null
rc=$?
log "orc exited $rc"

if [ "$rc" -ne 0 ]; then
  ledger key "lane:$LANE" event outcome action repair mode "$MODE" pr "$PR" lane "$LANE" \
         branch "$BR" outcome dispatch-failed rc "$rc" ts "$(date -u +%FT%TZ)"
fi

# --------------------------------------------------------------- relaunch

GIT_DIR_ABS="$(git -C "$WT" rev-parse --absolute-git-dir 2>/dev/null || true)"
DIRTY="$(git -C "$WT" status --porcelain 2>/dev/null | grep -v '^??' || true)"
if [ -z "$GIT_DIR_ABS" ] || [ -e "$GIT_DIR_ABS/MERGE_HEAD" ] || [ -n "$DIRTY" ]; then
  log "worktree still conflicted or dirty; lane $LANE not relaunched (stays parked)"
  ledger key "lane:$LANE" event outcome action repair mode "$MODE" pr "$PR" lane "$LANE" \
         branch "$BR" outcome still-dirty ts "$(date -u +%FT%TZ)"
  exit 4
fi

LANE_SH="$REPO_ROOT/local/bin/lane.sh"
if [ ! -x "$LANE_SH" ]; then
  log "no $LANE_SH; refusing a /tmp lane runner — lane $LANE stays parked for the operator"
  ledger key "lane:$LANE" event outcome action repair mode "$MODE" pr "$PR" lane "$LANE" \
         branch "$BR" outcome no-lane-runner ts "$(date -u +%FT%TZ)"
  exit 5
fi

rm -f "$L/$LANE.done" "$L/$LANE.needs-attention"
( cd "$REPO_ROOT" && LANE_BRANCH="$BR" SKIP_DISPATCH=1 \
    $DETACH nohup "$LANE_SH" "$LANE" "$SLUG" prover > "$L/$LANE.lane.log" 2>&1 < /dev/null & \
  echo $! > "$L/$LANE.lane.pid" )
LP="$(cat "$L/$LANE.lane.pid" 2>/dev/null || echo 0)"
log "worktree repaired; lane tail $LANE relaunched (pid $LP) via $LANE_SH"
ledger key "lane:$LANE" event outcome action repair mode "$MODE" pr "$PR" lane "$LANE" \
       branch "$BR" outcome relaunched lane_pid "$LP" ts "$(date -u +%FT%TZ)"

# The daemon's failure marker is cleared only when the relaunched tail finishes,
# so a scan cannot pick the PR up while the lane is still running.
if [ "$LP" -gt 0 ] 2>/dev/null; then
  ( while kill -0 "$LP" 2>/dev/null; do sleep 30; done
    rm -f "$D/pr$PR.failed"
    printf '== %s lane %s finished: %s; pr%s.failed cleared\n' "$(date -u +%FT%TZ)" "$LANE" \
      "$(tail -n 1 "$L/$LANE.lane.log" 2>/dev/null | cut -c1-100)" "$PR" >> "$LOG" ) \
    > /dev/null 2>&1 < /dev/null &
fi
exit 0
