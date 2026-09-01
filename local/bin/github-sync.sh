#!/usr/bin/env bash
#
# github-sync.sh — push the named refs to this repository's GitHub home,
# git@github.com:Dengnifer/MIPStarRE-A.git (standalone repo since the
# 2026-08-31 restructure; the old subtree-into-monorepo flow is retired, see
# EVOLUTION.md), then refresh the read-only record snapshot.
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
#   0  every ref pushed (the snapshot is best-effort and never fails the run)
#   1  a ref did not push after 5 attempts
set -euo pipefail

PROG="github-sync.sh"
ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
_common="$(git -C "$ROOT" rev-parse --path-format=absolute --git-common-dir 2>/dev/null || true)"
case "$_common" in */.git) ROOT="$(dirname "$_common")" ;; esac
cd "$ROOT"
LOCAL_BIN="$ROOT/local/bin"

REFS=("$@")
[ "${#REFS[@]}" -gt 0 ] || REFS=(main)

git remote get-url github >/dev/null 2>&1 ||
  git remote add github git@github.com:Dengnifer/MIPStarRE-A.git

RC=0
for ref in "${REFS[@]}"; do
  git rev-parse --verify --quiet "refs/heads/$ref" >/dev/null || {
    echo "$PROG: no local branch '$ref'; skipping" >&2; RC=1; continue
  }
  pushed=0
  for i in 1 2 3 4 5; do
    if git push github "refs/heads/$ref:refs/heads/$ref"; then
      echo "$PROG: pushed $ref ($(git rev-parse --short "$ref"))"
      pushed=1
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

exit "$RC"
