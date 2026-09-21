#!/usr/bin/env bash
# service-lib.sh — the two dozen lines every service script would otherwise repeat:
# find the repository, read local/project.json through local/bin/session/config.sh,
# fall back to plain environment defaults when the configuration is not there yet,
# and offer the handful of shared helpers (slug, log, event log, worker cap).
# Sourced, never executed.  Provenance: the repeated preamble of the origin's
# out-of-repo merge/lane/train scripts (kit-src/tmp-scripts), which hard-coded one
# repository path, one cache directory and one repository slug.

# Where this file lives (follow symlinks by hand; readlink -f is not everywhere).
kit__lib_self="${BASH_SOURCE[0]:-$0}"
while [ -L "$kit__lib_self" ]; do
  kit__lib_link="$(readlink "$kit__lib_self")"
  case "$kit__lib_link" in
    /*) kit__lib_self="$kit__lib_link" ;;
    *)  kit__lib_self="$(dirname "$kit__lib_self")/$kit__lib_link" ;;
  esac
done
KIT_SERVICE_DIR="$(cd "$(dirname "$kit__lib_self")" && pwd -P)"
export KIT_SERVICE_DIR
unset kit__lib_self kit__lib_link

# local/bin/service -> three levels up is the repository root.
KIT_REPO_ROOT="${KIT_REPO_ROOT:-$(cd "$KIT_SERVICE_DIR/../../.." && pwd -P)}"
export KIT_REPO_ROOT

# The configuration is authoritative when it is there; until then (and in unit tests that
# run without a project.json) the environment defaults below apply.  Set
# KIT_CONFIG_SOURCED=1 to say "the environment is already prepared, do not read
# local/project.json" — that is how a caller that sourced config.sh itself, and how a test
# driving these tools against a temporary tree, keeps its own KIT_* values.
if [ -z "${KIT_CONFIG_SOURCED:-}" ] && [ -f "$KIT_SERVICE_DIR/../session/config.sh" ]; then
  # shellcheck source=/dev/null
  . "$KIT_SERVICE_DIR/../session/config.sh" || true
  KIT_CONFIG_SOURCED=1
fi

: "${KIT_NAME:=PaperLib}"
: "${KIT_LEAN_ROOT:=$KIT_NAME}"
: "${KIT_TRACK:=main}"
: "${KIT_CACHE_ROOT:=$HOME/.cache/paperlib-dev}"
: "${KIT_STATE_DIR:=$KIT_CACHE_ROOT/watchdog}"
: "${KIT_GITHUB_SLUG:=}"
: "${KIT_TMUX:=paperlib}"
: "${KIT_PROGRESS_ISSUE:=}"
: "${KIT_OWNER_INBOX_ISSUE:=}"
: "${KIT_WORKER_MODEL:=}"
: "${KIT_WORKER_EFFORT:=}"
: "${KIT_LANES:=0}"
export KIT_NAME KIT_LEAN_ROOT KIT_TRACK KIT_CACHE_ROOT KIT_STATE_DIR KIT_TMUX

KIT_LANE_DIR="$KIT_STATE_DIR/lanes"
KIT_DAEMON_DIR="$KIT_STATE_DIR/daemon"
KIT_EVENT_LOG="$KIT_STATE_DIR/events-meta.log"
export KIT_LANE_DIR KIT_DAEMON_DIR KIT_EVENT_LOG

# The rotation shim (if installed) must win over a plain codex on PATH; elan and
# ~/.local/bin are the standard install locations of lake and gh.
case ":$PATH:" in
  *":$KIT_CACHE_ROOT/owner-bin:"*) ;;
  *) PATH="$KIT_CACHE_ROOT/owner-bin:$HOME/.local/bin:$HOME/.elan/bin:$PATH" ;;
esac
export PATH

kit_log() { echo "== $(date -u +%FT%TZ) $*"; }

# One dated line in the operator's event log; never fails the caller.
kit_plog() {
  mkdir -p "$KIT_STATE_DIR" 2>/dev/null || return 0
  echo "$(date -u +%FT%TZ) $*" >> "$KIT_EVENT_LOG" 2>/dev/null || true
}

# owner/repo for `gh api repos/<slug>/...`: configuration first, then the
# checkout's own `github` remote (gh_common.py resolves it the same way), then
# `origin`.  Empty output means "no slug" and every caller must treat that as an
# error rather than guessing.
kit_slug() {
  case "${KIT_GITHUB_SLUG:-}" in
    ""|OWNER/*) ;;
    *) echo "$KIT_GITHUB_SLUG"; return 0 ;;
  esac
  local url
  for remote in github origin; do
    url="$(git -C "$KIT_REPO_ROOT" remote get-url "$remote" 2>/dev/null)" || continue
    case "$url" in
      *github.com[:/]*) echo "$url" | sed -E -e 's#^.*github\.com[:/]##' -e 's#\.git$##'; return 0 ;;
    esac
  done
  return 1
}

# How many dispatched codex sessions may run at once: the state file the key
# watch maintains, else the configured lane count, else one.
kit_cap() {
  if [ -s "$KIT_STATE_DIR/max-codex" ]; then cat "$KIT_STATE_DIR/max-codex"; return; fi
  if [ -n "${MIPSTARRE_MAX_CODEX:-}" ]; then echo "$MIPSTARRE_MAX_CODEX"; return; fi
  if [ "${KIT_LANES:-0}" -gt 0 ] 2>/dev/null; then echo "$KIT_LANES"; return; fi
  echo 1
}

# Live dispatched sessions, counted by their distinct working directories.
kit_live_workers() { pgrep -fa 'codex exec' 2>/dev/null | grep -o -- '-C [^ ]*' | sort -u | wc -l; }

# Wait until a worker slot is free, holding the launch lock so a new process is
# counted before the next cap check (origin lesson: rate and concurrency limits
# are per account, not per process).
kit_wait_for_slot() {
  mkdir -p "$KIT_STATE_DIR"
  exec 9>"$KIT_STATE_DIR/launch.lock"; flock 9
  local i
  for i in $(seq 1 "${KIT_SLOT_WAIT_TICKS:-720}"); do
    [ "$(kit_live_workers)" -lt "$(kit_cap)" ] && break
    sleep "${KIT_SLOT_WAIT_SECONDS:-30}"
  done
}
