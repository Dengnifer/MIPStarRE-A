#!/usr/bin/env bash
# github-sync.sh — mirror this repository's main to GitHub as the
# MIPStarRE-A/ subtree of the private monorepo Dengnifer/MIPStarRE-qpbt.
#
# Usage: local/bin/github-sync.sh [--init]
#
#   --init   first run: create the local monorepo clone and perform the
#            initial `git subtree add`.
#
# Design (EVOLUTION.md 2026-08-31, "GitHub mirror restored as a surface"):
# the workflow stays fully local — issues, PRs, CI, reviews, and the
# registry never move to GitHub. The monorepo is a sharing/backup surface:
#   MIPStarRE-A/  = this repository (full history via git subtree)
#   MIPStarRE-B/  = the user's other track; NEVER touched by this script.
# Pushes authenticate with the repo-scoped deploy key
# ~/.ssh/id_ed25519_mipstarre_qpbt (write access to this one repo only).
set -euo pipefail

PROG="github-sync.sh"
ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
_common="$(git -C "$ROOT" rev-parse --path-format=absolute --git-common-dir 2>/dev/null || true)"
case "$_common" in
  */.git) ROOT="$(dirname "$_common")" ;;
esac
unset _common

MONO="${MIPSTARRE_GITHUB_MONO:-$HOME/.MIPStarRE-qpbt-github}"
REMOTE_URL="${MIPSTARRE_GITHUB_URL:-git@github.com:Dengnifer/MIPStarRE-qpbt.git}"
DEPLOY_KEY="${MIPSTARRE_GITHUB_KEY:-$HOME/.ssh/id_ed25519_mipstarre_qpbt}"
PREFIX="MIPStarRE-A"
BRANCH="${MIPSTARRE_GITHUB_BRANCH:-main}"

log() { printf '%s: %s\n' "$PROG" "$*" >&2; }
die() { printf '%s: error: %s\n' "$PROG" "$*" >&2; exit 1; }

[ -f "$DEPLOY_KEY" ] || die "deploy key $DEPLOY_KEY not found"
export GIT_SSH_COMMAND="ssh -i $DEPLOY_KEY -o IdentitiesOnly=yes"

if [ "${1:-}" = "--init" ]; then
  [ -d "$MONO/.git" ] && die "$MONO already exists; drop --init"
  git clone "$REMOTE_URL" "$MONO"
  cd "$MONO"
  if [ -z "$(git branch --list "$BRANCH")" ]; then
    git checkout -b "$BRANCH"
    printf '# MIPStarRE-qpbt\n\nA: `MIPStarRE-A/` (QPBT, Lean 4).  B: `MIPStarRE-B/` (attached separately).\n' > README.md
    git add README.md
    git commit -m "chore: monorepo root"
  fi
  git subtree add --prefix="$PREFIX" "$ROOT" main -m "chore: attach MIPStarRE-A (subtree of the ghz project repository)"
  git push -u origin "$BRANCH"
  log "initialized: $REMOTE_URL $BRANCH with $PREFIX/ at $(git -C "$ROOT" rev-parse --short main)"
  exit 0
fi

[ -d "$MONO/.git" ] || die "$MONO missing; run with --init first"
cd "$MONO"
git fetch origin "$BRANCH"
git checkout -q "$BRANCH"
git merge -q --ff-only "origin/$BRANCH" 2>/dev/null || true
git subtree pull --prefix="$PREFIX" "$ROOT" main \
  -m "chore: sync MIPStarRE-A to $(git -C "$ROOT" rev-parse --short main)"
git push origin "$BRANCH"
log "synced $PREFIX/ to $(git -C "$ROOT" rev-parse --short main) and pushed"
