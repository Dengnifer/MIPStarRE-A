#!/usr/bin/env bash
# main-session.sh — start (or resume) the project's MAIN codex session.  THE launcher.
#
# Usage:
#   local/bin/main-session.sh            start a fresh main session
#   local/bin/main-session.sh --resume   resume the most recent codex session
#   local/bin/main-session.sh --print    print the command line and exit (no session)
#
# The main session is the orchestrating operator of this project (persona:
# local/personas/main.md; state: the owner's /goal briefing).  It always works in the repo
# root — NOT the caller's cwd, NOT $HOME — and runs interactively so the user can steer it.
# Worker sessions are still started only via dispatch.sh.
#
# THROUGH THE SHIM.  The model, the reasoning effort, the CODEX_HOME and the SPEED TIER all
# come from the run mode (`run_mode.py get main.model|main.effort|main.codex_home|speed`,
# briefed under `run.main`), and codex is invoked through the
# installed PATH shim ~/.cache/mipstarre-dev/owner-bin/codex, which is where the speed tier
# is applied.  The 2026-09-12 launcher (main-session-astra-v3.sh) `exec`'d an absolute
# ~/.local/bin/codex and therefore never received service_tier="priority": the owner
# switched the run to fast speed three times and the main session never ran at it.
# When no shim is installed the launcher falls back to `codex` on PATH and says so, so a
# developer checkout still works; on the operator host, run
# results/telemetry/owner-tools/install.sh first.
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
_common="$(git -C "$ROOT" rev-parse --path-format=absolute --git-common-dir 2>/dev/null || true)"
case "$_common" in
  */.git) ROOT="$(dirname "$_common")" ;;
esac
unset _common

readonly CACHE_ROOT="${MIPSTARRE_CACHE_ROOT:-$HOME/.cache/mipstarre-dev}"
readonly OWNER_BIN="${MIPSTARRE_OWNER_BIN:-$CACHE_ROOT/owner-bin}"
readonly RUN_MODE="${MIPSTARRE_RUN_MODE:-$ROOT/local/bin/run_mode.py}"

export PATH="$OWNER_BIN:$HOME/.elan/bin:$HOME/.local/bin:$PATH"

rm_get() { # rm_get KEY fallback — one value from the run mode, never a second copy of it
  local out=""
  out="$(python3 "$RUN_MODE" get "$1" 2>/dev/null)" || out=""
  out="$(printf '%s' "$out" | head -n 1 | tr -d '\r')"
  if [ -n "$out" ]; then printf '%s\n' "$out"; else printf '%s\n' "$2"; fi
}

CODEX="$OWNER_BIN/codex"
if [ ! -x "$CODEX" ]; then
  printf 'main-session.sh: no PATH shim at %s; falling back to codex on PATH.\n' "$CODEX" >&2
  printf 'main-session.sh: the run speed tier is applied by the shim — on the operator host\n' >&2
  printf 'main-session.sh: run results/telemetry/owner-tools/install.sh first.\n' >&2
  CODEX="$(command -v codex || true)"
  [ -n "$CODEX" ] || { printf 'main-session.sh: codex CLI not found on PATH\n' >&2; exit 1; }
fi

# `main.model`, `main.effort` and `main.codex_home` are run_mode keys (run.main in
# the brief, defaulted there to these same values).  The fallbacks below apply only
# when run_mode.py is absent or the run has not been briefed at all; when it IS
# briefed, the brief wins.  Say which happened rather than looking identical either
# way — the 2026-09-12 launcher's silent fallback is why the main session ran on the
# ambient CODEX_HOME while the brief named an account.
SOURCE="run-mode"
python3 "$RUN_MODE" get main.model >/dev/null 2>&1 || SOURCE="defaults (run mode unreadable)"
MODEL="$(rm_get main.model "${MAIN_MODEL:-gpt-6-astra}")"
EFFORT="$(rm_get main.effort "${MAIN_EFFORT:-xhigh}")"
SPEED="$(rm_get speed default)"
HOME_DIR="$(rm_get main.codex_home "${CODEX_HOME:-}")"
if [ -n "$HOME_DIR" ]; then
  # run-mode may hand back a ~-relative path
  case "$HOME_DIR" in "~/"*) HOME_DIR="$HOME/${HOME_DIR#\~/}" ;; esac
  export CODEX_HOME="$HOME_DIR"
fi

# The MAIN session is the trusted orchestrator: it commits, merges and pushes in the primary
# checkout, which codex's workspace-write sandbox forbids (.git stays read-only there;
# review of PR #41, F1).  Worker sessions get their own sandboxes from dispatch.sh.
# approval_policy=never: the automatic approval review timed out and dropped merges on
# 2026-09-03 (events.md).
readonly -a CODEX_ARGS=(
  -C "$ROOT"
  --sandbox danger-full-access
  -c 'approval_policy="never"'
  -c "model_reasoning_effort=\"$EFFORT\""
  -m "$MODEL"
)

PROMPT="You are the MAIN SESSION of this project. Read, in order:
local/personas/main.md (your persona), local/README.md, AGENTS.md. The
owner will invoke /goal to provide the project-state briefing; treat it as
authoritative for state and next steps. Your working directory is the
repository root: $ROOT — all workflow tools are invoked as
local/bin/<tool> from there."

printf 'main-session.sh: %s model=%s effort=%s speed=%s codex_home=%s (source: %s)\n' \
  "$CODEX" "$MODEL" "$EFFORT" "$SPEED" "${CODEX_HOME:-$HOME/.codex}" "$SOURCE" >&2

if [ "${1:-}" = "--print" ]; then
  printf '%s' "$CODEX"
  printf ' %q' "${CODEX_ARGS[@]}"
  printf ' <prompt>\n'
  exit 0
fi

cd "$ROOT"
if [ "${1:-}" = "--resume" ]; then
  exec "$CODEX" "${CODEX_ARGS[@]}" resume --last
fi
exec "$CODEX" "${CODEX_ARGS[@]}" "$PROMPT"
