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
# Environment: MIPSTARRE_OFFLOAD_SCRIPT (the offload script to use; it can only
#   ever point at a DIFFERENT script, never turn the offload on — the run mode is
#   asked here as well, so a script whose `--check` exits 0 still offloads
#   nothing outside full speed mode), MIPSTARRE_OFFLOAD=0 (never offload, for a
#   run that must stay on this host), MIPSTARRE_OFFLOAD_TIMEOUT_S (wall clock for
#   one offload, default 3300; a timeout is a fallback, not a lane failure),
#   MIPSTARRE_RUN_MODE, MIPSTARRE_CACHE_ROOT, MIPSTARRE_OWNER_BIN,
#   MIPSTARRE_CHECKOUT.

OFFLOAD_UNUSABLE=64
OFFLOAD_NO_ARTIFACTS=65
#: `timeout`'s own code for "the command was killed at the deadline".
OFFLOAD_TIMED_OUT=124
#: Wall clock for ONE offload, a little above build-on-chsh.sh's own remote
#: `timeout 2700 lake build`.  The offload runs while the caller holds the
#: machine-wide full-build lease, so an offload that never returns stops every
#: build on this host; ssh's ServerAlive only notices a link that is dead, not
#: one that is merely slow.

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

offload_run_mode() { # the run_mode.py this host answers with, or nothing
  local cache checkout candidate
  cache="${MIPSTARRE_CACHE_ROOT:-$HOME/.cache/mipstarre-dev}"
  checkout="${MIPSTARRE_CHECKOUT:-$HOME/MIPStarRE-qpbt}"
  for candidate in "${MIPSTARRE_RUN_MODE:-}" \
                   "$checkout/local/bin/run_mode.py" \
                   "$HOME/MIPStarRE-qpbt/local/bin/run_mode.py"; do
    [ -n "$candidate" ] && [ -r "$candidate" ] && { printf '%s\n' "$candidate"; return 0; }
  done
  return 1
}

offload_run_mode_says_yes() { # 0 = this run may use a second host at all
  local py answer
  py="$(offload_run_mode)" || return 1
  answer="$(python3 "$py" get offload 2>/dev/null | head -n 1 | tr -d '[:space:]')"
  [ "$answer" = yes ]
}

offload_enabled_for_run() { # 0 = the run mode enables the offload
  local script
  [ "${MIPSTARRE_OFFLOAD:-1}" = 0 ] && return 1
  # The run mode is asked HERE, before MIPSTARRE_OFFLOAD_SCRIPT is honoured, so
  # that variable can only ever redirect the offload to a different script — it
  # cannot turn the farm on.  full-speed-mode.md section 5.1 claims exactly
  # that ("no environment variable that turns it on"), and until this check
  # existed any environment pointing the variable at a script whose `--check`
  # exits 0 made the claim false.
  offload_run_mode_says_yes || return 1
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
    timeout "${MIPSTARRE_OFFLOAD_TIMEOUT_S:-3300}" bash "$script" "$wt" "$@" || rc=$?
    elapsed=$(( $(date +%s) - started ))
    if [ "$rc" = "$OFFLOAD_TIMED_OUT" ]; then
      # A stalled offload is "chsh is unusable", never a verdict on the proof.
      offload_note "$label: the offload passed its wall clock; treating it as unusable"
      rc="$OFFLOAD_UNUSABLE"
    fi
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
