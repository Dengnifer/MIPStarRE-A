#!/usr/bin/env bash
# main-session.sh — start (or resume) the project's MAIN codex session.
#
# Usage:
#   local/bin/main-session.sh            start a fresh main session
#   local/bin/main-session.sh --resume   resume the most recent codex session
#
# The main session is the orchestrating operator of this project (persona:
# local/personas/main.md; state: the owner's /goal briefing). It always works in the repo
# root — NOT the caller's cwd, NOT $HOME — and runs interactively so the
# user can steer it. Worker sessions are still started only via dispatch.sh.
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
_common="$(git -C "$ROOT" rev-parse --path-format=absolute --git-common-dir 2>/dev/null || true)"
case "$_common" in
  */.git) ROOT="$(dirname "$_common")" ;;
esac
unset _common

export PATH="$HOME/.elan/bin:$HOME/.local/bin:$PATH"

command -v codex >/dev/null 2>&1 || {
  printf 'main-session.sh: codex CLI not found on PATH\n' >&2; exit 1; }

if [ "${1:-}" = "--resume" ]; then
  exec codex -C "$ROOT" resume --last
fi

PROMPT="You are the MAIN SESSION of this project. Read, in order:
local/personas/main.md (your persona), local/README.md, AGENTS.md. The
owner will invoke /goal to provide the project-state briefing; treat it as
authoritative for state and next steps. Your working directory is the
repository root: $ROOT — all workflow tools are invoked as
local/bin/<tool> from there."

exec codex -C "$ROOT" "$PROMPT"
