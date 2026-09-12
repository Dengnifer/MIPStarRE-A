#!/usr/bin/env bash
# offload-build.sh — "build this worktree on chsh when the run mode says so,
# and on this host whenever that does not work".  Sourced by local/bin/lane.sh
# and local/bin/ci.sh so the two carry ONE copy of the fallback rule.
#
#   . "$SCRIPT_DIR/offload-build.sh"
#   offload_local_build() { ( cd "$W" && timeout 2700 lake build "$@" ); }
#   offload_lake_build "$W" "lane-$N" MIPStarRE.QPBT
#
# `offload_lake_build <worktree> <label> [targets ...]` returns the exit code
# of whichever build actually ran and prints one line naming the host.
#
# The rule it exists to keep (local/protocols/full-speed-mode.md):
#
#   * chsh is used only in full speed mode.  The question is asked of
#     `run_mode.py get offload` through `build-on-chsh.sh --check`, never of a
#     file or an environment variable of our own.
#   * A LANE MUST NEVER FAIL BECAUSE CHSH IS UNREACHABLE.  Exit 64 (chsh
#     unusable) and 65 (artifacts not returned) fall back to the local build;
#     every other exit code is the build's own verdict and is passed through,
#     because a proof that does not compile does not compile anywhere and a
#     silent local retry would only spend the build lease twice.
#   * Which host built is in the lane log and, whenever the offload was
#     enabled, in $MIPSTARRE_CACHE_ROOT/watchdog/chsh/offload.log.
#
# The caller defines `offload_local_build <targets ...>`, which runs the local
# build exactly as it did before (cwd, timeout and git-env handling differ
# between the two callers); without one, a plain `lake build` in the worktree
# is used.
#
# Environment: MIPSTARRE_OFFLOAD_SCRIPT (the offload script to use),
#   MIPSTARRE_OFFLOAD=0 (never offload, for a run that must stay on this host),
#   MIPSTARRE_CACHE_ROOT, MIPSTARRE_OWNER_BIN, MIPSTARRE_CHECKOUT.

OFFLOAD_UNUSABLE=64
OFFLOAD_NO_ARTIFACTS=65

offload_state_dir() {
  printf '%s/watchdog/chsh\n' "${MIPSTARRE_CACHE_ROOT:-$HOME/.cache/mipstarre-dev}"
}

offload_note() { # <line> — the lane log always, offload.log when enabled
  printf 'offload: %s\n' "$*"
}

offload_record() { # <line> — one row in watchdog/chsh/offload.log
  local dir; dir="$(offload_state_dir)"
  mkdir -p "$dir" 2>/dev/null || return 0
  printf '%s %s\n' "$(date -u +%FT%TZ)" "$*" >> "$dir/offload.log" 2>/dev/null || true
}

offload_script() {
  local cache owner checkout candidate
  cache="${MIPSTARRE_CACHE_ROOT:-$HOME/.cache/mipstarre-dev}"
  owner="${MIPSTARRE_OWNER_BIN:-$cache/owner-bin}"
  checkout="${MIPSTARRE_CHECKOUT:-$HOME/MIPStarRE-qpbt}"
  for candidate in "${MIPSTARRE_OFFLOAD_SCRIPT:-}" \
                   "$owner/build-on-chsh.sh" \
                   "$checkout/results/telemetry/owner-tools/build-on-chsh.sh"; do
    [ -n "$candidate" ] && [ -r "$candidate" ] && { printf '%s\n' "$candidate"; return 0; }
  done
  return 1
}

offload_enabled_for_run() { # 0 = the run mode enables the offload
  local script
  [ "${MIPSTARRE_OFFLOAD:-1}" = 0 ] && return 1
  script="$(offload_script)" || return 1
  bash "$script" --check > /dev/null 2>&1
}

offload_lake_build() { # <worktree> <label> [targets ...]
  local wt="$1" label="$2"; shift 2
  local script rc started elapsed
  OFFLOAD_WORKTREE="$wt"

  if offload_enabled_for_run && script="$(offload_script)"; then
    started="$(date +%s)"
    # `|| rc=$?`, never a bare call: ci.sh runs its step bodies under `set -e`,
    # where a failing build would kill the step before the fallback could run.
    rc=0
    bash "$script" "$wt" "$@" || rc=$?
    elapsed=$(( $(date +%s) - started ))
    if [ "$rc" != "$OFFLOAD_UNUSABLE" ] && [ "$rc" != "$OFFLOAD_NO_ARTIFACTS" ]; then
      offload_note "$label built on chsh in ${elapsed}s (lake exit $rc) host=chsh"
      return "$rc"
    fi
    offload_note "$label: chsh is unusable (exit $rc after ${elapsed}s); building here instead"
    offload_record "lane=$label host=ghz reason=fallback-$rc targets=${*:-(default)}"
  fi

  started="$(date +%s)"
  rc=0
  if declare -F offload_local_build > /dev/null 2>&1; then
    offload_local_build "$@" || rc=$?
  else
    ( cd "$wt" && lake build "$@" ) || rc=$?
  fi
  offload_note "$label built on ghz in $(( $(date +%s) - started ))s (lake exit $rc) host=ghz"
  return "$rc"
}
