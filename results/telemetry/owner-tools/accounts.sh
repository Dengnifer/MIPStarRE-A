#!/usr/bin/env bash
# accounts.sh — the owner's command for the live accounts file.
#
# Usage:
#   accounts.sh list [--json]
#   accounts.sh get <name> [field]
#   accounts.sh set <name> <field> <value>     ceiling|reserved|enabled|note|label|
#                                              endpoint|codex_home
#   accounts.sh enable <name>  [--note TEXT]
#   accounts.sh disable <name> [--note TEXT]
#   accounts.sh add <name> --endpoint E --codex-home D --ceiling N
#                          [--label L] [--reserved N] [--note TEXT] [--disabled]
#   accounts.sh remove <name>
#   accounts.sh probe [name]
#   accounts.sh log [-n N]
#
# What it edits: ~/.cache/mipstarre-dev/watchdog/accounts.json, the live source of
# truth for which keys exist, what their CEILINGS are, and whether the pipeline may
# use them.  The capacity controller and account_router.py re-read that file every
# tick and every reservation, so a change here reaches admission within 60 seconds
# with no session prompted, no brief re-applied and nothing restarted.
#
# `ceiling` is a ceiling and never a target: the controller's AIMD discovery runs
# below it and may never exceed `ceiling - external_reserved`.  Lowering it takes
# effect at the next tick; raising it lets the additive creep continue.
# `enabled false` is cap 0 immediately and no probes, and so is `remove`.
#
# Every write is atomic (temp file + rename) and appends one line to
# ~/.cache/mipstarre-dev/watchdog/capacity/accounts.log.  No key value is ever
# stored in the file: an entry names the codex home the key lives in, nothing more.
#
# `probe` runs one bounded read-only health probe per account through the capacity
# controller (the owner of endpoint health) and prints what it found; it is how a
# key disabled by measured health is checked by hand instead of waited on.
#
# This is a thin, versioned wrapper: every rule above is enforced by
# local/bin/accounts_file.py, so the CLI and the janitor's GitHub channel cannot
# disagree about what a valid entry is.
#
# Environment: MIPSTARRE_CHECKOUT (checkout holding local/bin; default the recorded
# owner-bin/repo-root, then ~/MIPStarRE-qpbt), MIPSTARRE_CACHE_ROOT.
#
# Exit codes: 0 ok · 2 usage, an invalid file or an invalid value (nothing written)
#             · 3 no such account · 4 no checkout found
set -u

PROG="accounts.sh"
CACHE_ROOT="${MIPSTARRE_CACHE_ROOT:-$HOME/.cache/mipstarre-dev}"
OWNER_BIN="${MIPSTARRE_OWNER_BIN:-$CACHE_ROOT/owner-bin}"

usage() { sed -n '2,44p' "${BASH_SOURCE[0]}" | sed 's/^# \{0,1\}//'; }

resolve_root() {
  local candidate
  for candidate in "${MIPSTARRE_CHECKOUT:-}" "${MIPSTARRE_REPO_ROOT:-}"; do
    [ -n "$candidate" ] && [ -f "$candidate/local/bin/accounts_file.py" ] && {
      printf '%s\n' "$candidate"; return 0; }
  done
  if [ -r "$OWNER_BIN/repo-root" ]; then
    candidate="$(cat "$OWNER_BIN/repo-root")"
    [ -f "$candidate/local/bin/accounts_file.py" ] && { printf '%s\n' "$candidate"; return 0; }
  fi
  # Running from the checkout itself (results/telemetry/owner-tools/accounts.sh).
  candidate="$(cd "$(dirname "${BASH_SOURCE[0]}")/../../.." 2>/dev/null && pwd)"
  [ -n "$candidate" ] && [ -f "$candidate/local/bin/accounts_file.py" ] && {
    printf '%s\n' "$candidate"; return 0; }
  candidate="$HOME/MIPStarRE-qpbt"
  [ -f "$candidate/local/bin/accounts_file.py" ] && { printf '%s\n' "$candidate"; return 0; }
  return 1
}

case "${1:-}" in
  -h|--help|"") usage; [ -n "${1:-}" ] && exit 0 || exit 2 ;;
esac

ROOT="$(resolve_root)" || {
  printf '%s: no checkout with local/bin/accounts_file.py found. Set MIPSTARRE_CHECKOUT.\n' \
    "$PROG" >&2
  exit 4
}

# The version banner every installed tool prints (owner-tools/README.md).  It goes
# to stderr so `accounts.sh get second ceiling` stays usable in a shell expression.
VERSION="$( { [ -s "$OWNER_BIN/tools-version" ] &&
    sed -n 's/.*short=\([^ ]*\).*/\1/p' "$OWNER_BIN/tools-version" | head -n 1; } ||
  git -C "$ROOT" rev-parse --short HEAD 2>/dev/null || true)"
printf 'tool=%s version=%s\n' "$PROG" "${VERSION:-unknown}" >&2

ACTOR="${MIPSTARRE_ACCOUNTS_ACTOR:-${USER:-owner}}"

command="$1"; shift
case "$command" in
  probe)
    exec python3 "$ROOT/local/bin/capacity_controller.py" probe "$@"
    ;;
  log)
    LINES=50
    case "${1:-}" in -n) LINES="${2:-50}" ;; esac
    LOG="$CACHE_ROOT/watchdog/capacity/accounts.log"
    [ -s "$LOG" ] || { printf '%s: no edits recorded yet (%s)\n' "$PROG" "$LOG"; exit 0; }
    exec tail -n "$LINES" "$LOG"
    ;;
  list|get|set|enable|disable|add|remove|seed|apply-directives)
    exec python3 "$ROOT/local/bin/accounts_file.py" --actor "$ACTOR" "$command" "$@"
    ;;
  *)
    printf '%s: unknown command %s\n\n' "$PROG" "$command" >&2
    usage >&2
    exit 2
    ;;
esac
