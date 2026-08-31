#!/usr/bin/env bash
# github-sync.sh — push this repository to its GitHub home,
# git@github.com:Dengnifer/MIPStarRE-A.git (standalone repo since the
# 2026-08-31 restructure; the old subtree-into-monorepo flow is retired,
# see EVOLUTION.md). Run after every merge to main.
set -euo pipefail
ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
_common="$(git -C "$ROOT" rev-parse --path-format=absolute --git-common-dir 2>/dev/null || true)"
case "$_common" in */.git) ROOT="$(dirname "$_common")" ;; esac
cd "$ROOT"
git remote get-url github >/dev/null 2>&1 || git remote add github git@github.com:Dengnifer/MIPStarRE-A.git
for i in 1 2 3 4 5; do
  git push github --all && { echo "github-sync: pushed $(git rev-parse --short main)"; exit 0; }
  echo "github-sync: push attempt $i failed; retrying" >&2; sleep 15
done
echo "github-sync: all push attempts failed" >&2; exit 1
