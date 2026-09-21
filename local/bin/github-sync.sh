#!/usr/bin/env bash
#
# github-sync.sh — push the named refs to this repository's GitHub home
# (git@github.com:<project.github_slug>.git, from local/project.json), then
# refresh the read-only record snapshot.
#
# Usage: local/bin/github-sync.sh [ref ...]      (default: main)
#
# Run after every merge to main.  Only the named refs are pushed: `git push
# --all` is deliberately gone.  GitHub now holds the records — issues, PRs, the
# per-SHA CI statuses and the review verdicts (local/protocols/issues-prs.md) —
# and a blanket push republishes every stale local branch, including the
# throwaway fix branches whose heads those records are bound to.  Push what you
# mean to publish.
#
# Exit codes:
#   0  requested refs and any final main telemetry published; snapshot reads are best-effort
#   1  a named ref or final telemetry publication failed, or snapshot commit failed
set -euo pipefail

PROG="github-sync.sh"
ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
_common="$(git -C "$ROOT" rev-parse --path-format=absolute --git-common-dir 2>/dev/null || true)"
case "$_common" in */.git) ROOT="$(dirname "$_common")" ;; esac
cd "$ROOT"
LOCAL_BIN="$ROOT/local/bin"

REFS=("$@")
[ "${#REFS[@]}" -gt 0 ] || REFS=(main)

# An existing `github` remote is authoritative; otherwise the remote is built
# from the configured slug, and a repository that has not been given one yet
# must not invent it.
if ! git remote get-url github >/dev/null 2>&1; then
  SLUG=$(python3 "$ROOT/scripts/project_config.py" --root "$ROOT" get project.github_slug 2>/dev/null || true)
  case "$SLUG" in
    ""|OWNER/*)
      echo "$PROG: this repository has no 'github' remote, and local/project.json" >&2
      echo "$PROG: still carries the placeholder name '${SLUG:-<empty>}'." >&2
      echo "$PROG: Set project.github_slug to the owner/repo of this project's" >&2
      echo "$PROG: GitHub home (creating that repository is a step the owner" >&2
      echo "$PROG: approves once), then run this again." >&2
      exit 1
      ;;
  esac
  git remote add github "git@github.com:$SLUG.git"
fi

RC=0
MAIN_PUSHED=0
for ref in "${REFS[@]}"; do
  git rev-parse --verify --quiet "refs/heads/$ref" >/dev/null || {
    echo "$PROG: no local branch '$ref'; skipping" >&2; RC=1; continue
  }
  pushed=0
  for i in 1 2 3 4 5; do
    if "$LOCAL_BIN/checked-push.sh" --repo-root "$ROOT" github \
        "refs/heads/$ref:refs/heads/$ref"; then
      echo "$PROG: pushed $ref ($(git rev-parse --short "$ref"))"
      pushed=1
      [ "$ref" != main ] || MAIN_PUSHED=1
      break
    fi
    echo "$PROG: push attempt $i for '$ref' failed; retrying" >&2
    sleep 15
  done
  [ "$pushed" -eq 1 ] || { echo "$PROG: all push attempts failed for '$ref'" >&2; RC=1; }
done

# Audit/recovery telemetry only — never lifecycle input (gh_common.py:390-392),
# so a snapshot failure must not fail a successful push.
if ! python3 "$LOCAL_BIN/gh_common.py" snapshot \
      --out-dir "$ROOT/results/telemetry/github-snapshot"; then
  echo "$PROG: warning: the GitHub record snapshot failed; the push above still stands" >&2
fi
# checked-push.sh requires the primary checkout to match the pushed commit
# exactly, so the snapshot just written (and any build ledger rows) must be
# committed before the next publish; otherwise every later push is refused.
SNAPSHOT_COMMITTED=0
if ! git -C "$ROOT" diff --quiet -- results/telemetry/github-snapshot results/telemetry/builds.jsonl 2>/dev/null; then
  if git -C "$ROOT" commit -q -m "chore(telemetry): GitHub record snapshot" \
    -- results/telemetry/github-snapshot results/telemetry/builds.jsonl; then
    SNAPSHOT_COMMITTED=1
  else
    echo "$PROG: could not commit the snapshot; the next push will need a clean tree" >&2
    RC=1
  fi
fi

# Keep the snapshot after publication, but do not leave an explicitly requested
# main ahead because of our own telemetry commit. Branch-only syncs keep their
# original scope. This final push never generates another snapshot.
if [ "$MAIN_PUSHED" -eq 1 ] && [ "$SNAPSHOT_COMMITTED" -eq 1 ]; then
  if "$LOCAL_BIN/checked-push.sh" --repo-root "$ROOT" github \
      refs/heads/main:refs/heads/main; then
    echo "$PROG: published snapshot on main ($(git rev-parse --short main))"
  else
    echo "$PROG: snapshot commit remains local; final main publication failed" >&2
    RC=1
  fi
fi

exit "$RC"
