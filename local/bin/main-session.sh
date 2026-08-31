#!/usr/bin/env bash
# main-session.sh — start (or resume) the project's MAIN codex session.
#
# Usage:
#   local/bin/main-session.sh            start a fresh main session
#   local/bin/main-session.sh --resume   resume the most recent codex session
#
# The main session is the orchestrating operator of this project (persona:
# local/personas/main.md; state: HANDOFF.md). It always works in the repo
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
[ -f "$ROOT/HANDOFF.md" ] || {
  printf 'main-session.sh: %s/HANDOFF.md missing — refusing to start an unbriefed main session\n' "$ROOT" >&2; exit 1; }

if [ "${1:-}" = "--resume" ]; then
  exec codex -C "$ROOT" resume --last
fi

PROMPT="You are the MAIN SESSION of this project. Before anything else,
read these three files in full, in this order:
1. HANDOFF.md            (state of the project and immediate next steps)
2. local/personas/main.md (your persona: role, operating loop, duties)
3. local/README.md        (the workflow layer's operator tour)
Then read AGENTS.md. Confirm to the user what stage the project is in and
what you will do next, then proceed per the checkpoint discipline. Your
working directory is the repository root: $ROOT — all workflow tools are
invoked as local/bin/<tool> from there."

exec codex -C "$ROOT" "$PROMPT"
