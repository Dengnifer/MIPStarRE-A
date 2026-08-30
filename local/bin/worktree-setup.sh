#!/usr/bin/env bash
# worktree-setup.sh — bootstrap a fresh worktree so an agent can build in it.
#
# Usage:
#   local/bin/worktree-setup.sh [<worktree>] [options]
#
#   <worktree>       Tree to bootstrap (default: the git toplevel of $PWD).
#   --check          Report-only: verify the bootstrap, change nothing, exit
#                    non-zero if anything is missing.
#   --build          Ask warm-worktree.sh to also run a full `lake build`.
#   --no-build       Ask warm-worktree.sh not to build on the cold path.
#   --force-cold     Ignore the hot main cache; cold-path this worktree.
#   --skip-warm      Do not call warm-worktree.sh at all.
#   --persist-path   Append the elan PATH line to $MIPSTARRE_SHELL_RC (default
#                    ~/.zshrc), idempotently.  Off by default: this script does
#                    not edit your shell configuration unless you ask.
#   -h | --help      Show this text.
#
# Local replacement for .codex/setup.sh (the Codex cloud environment hook), per
# local/DESIGN.md's GitHub->local mapping row "Codex cloud env setup
# (.codex/setup.sh) -> local/bin/worktree-setup.sh".
#
# Differences from .codex/setup.sh, all deliberate:
#   * elan is ASSERTED, never installed by piping a URL into a shell.  This runs
#     on a developer machine, not a disposable cloud runner.
#   * NO `lake update`.  .codex/setup.sh ran it on every boot; here it would move
#     lake-manifest.json out from under the hot-cache keyhash
#     (.github/workflows/pr-ci.yml:143-149) and mutate the vendored package trees.
#     Mathlib bumps are a separate, human-invoked operation — the parent workflow
#     made the same call at .github/workflows/update.yml:3-5.
#   * The ProofWidgets fresh-state workaround from
#     .github/workflows/docgen.yml:56-69 is kept, because a pristine worktree is
#     exactly the fresh state that bug bites.
#   * The build comes from the hot main cache via local/bin/warm-worktree.sh
#     instead of a cold `lake build`.
#
# Protocol: local/protocols/build-cache.md.

set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"

WORKTREE=""
CHECK_ONLY=0
PERSIST_PATH=0
SKIP_WARM=0
WARM_ARGS=()

log()  { printf '[worktree-setup] %s\n' "$*" >&2; }
warn() { printf '[worktree-setup] WARNING: %s\n' "$*" >&2; }
die()  { printf '[worktree-setup] ERROR: %s\n' "$*" >&2; exit 1; }

usage() {
  cat <<'EOF'
Usage: local/bin/worktree-setup.sh [<worktree>] [options]

  <worktree>       Tree to bootstrap (default: the git toplevel of $PWD).
  --check          Report-only: verify the bootstrap, change nothing.
  --build          Ask warm-worktree.sh to also run a full `lake build`.
  --no-build       Ask warm-worktree.sh not to build on the cold path.
  --force-cold     Ignore the hot main cache; cold-path this worktree.
  --skip-warm      Do not call warm-worktree.sh at all.
  --persist-path   Append the elan PATH line to $MIPSTARRE_SHELL_RC (~/.zshrc).
  -h | --help      Show this text.
EOF
}

# Ported from .githooks/pre-push: clear Git's per-invocation environment before
# invoking Lake or nested git operations, so an outer hook's GIT_DIR does not leak
# into the vendored package checkouts.
run_outside_git_env() (
  if command -v git >/dev/null 2>&1; then
    for name in $(git rev-parse --local-env-vars); do
      unset "$name" || true
    done
  fi
  "$@"
)

# ------------------------------------------------------------------------ steps

export_elan_path() {
  if [ -d "$HOME/.elan/bin" ]; then
    case ":$PATH:" in
      *":$HOME/.elan/bin:"*) ;;
      *) PATH="$HOME/.elan/bin:$PATH"; export PATH ;;
    esac
  fi
}

persist_elan_path() {
  local rc_file line
  rc_file="${MIPSTARRE_SHELL_RC:-$HOME/.zshrc}"
  line='export PATH="$HOME/.elan/bin:$PATH"'
  if [ -f "$rc_file" ] && grep -qxF "$line" "$rc_file"; then
    log "elan PATH line already present in $rc_file"
    return 0
  fi
  printf '%s\n' "$line" >> "$rc_file"
  log "appended the elan PATH line to $rc_file"
}

assert_elan() {
  export_elan_path
  if ! command -v elan >/dev/null 2>&1; then
    die "elan is not installed or not on PATH.
This script does not install toolchains by piping a URL into a shell.
Install elan yourself, then re-run:
  brew install elan-init      # or see https://github.com/leanprover/elan
and make sure \$HOME/.elan/bin is on PATH:
  export PATH=\"\$HOME/.elan/bin:\$PATH\""
  fi
  log "elan: $(elan --version 2>/dev/null || echo unknown)"
}

ensure_toolchain() { # <worktree>
  local tree="$1" pin
  [ -f "$tree/lean-toolchain" ] || die "$tree/lean-toolchain is missing; this is not a MIPStarRE worktree"
  pin="$(tr -d ' \t\r\n' < "$tree/lean-toolchain")"
  [ -n "$pin" ] || die "$tree/lean-toolchain is empty"
  if elan toolchain list 2>/dev/null | grep -qF "$pin"; then
    log "toolchain $pin already installed"
    return 0
  fi
  if [ "$CHECK_ONLY" -eq 1 ]; then
    warn "toolchain $pin is NOT installed (elan toolchain install $pin)"
    return 1
  fi
  log "installing toolchain $pin (one-time)"
  elan toolchain install "$pin" >&2 || die "elan toolchain install $pin failed"
}

assert_lake() {
  command -v lake >/dev/null 2>&1 || die "lake not found on PATH after the elan setup"
  command -v python3 >/dev/null 2>&1 || warn "python3 not found; the audit scripts and build telemetry will not run"
}

# DESIGN.md #8: the hooks and every diff-based audit silently self-disable when
# origin/main does not resolve.  Surface it loudly rather than let a worktree run
# with half its gates switched off.
check_origin_main() { # <worktree>
  local tree="$1"
  if run_outside_git_env git -C "$tree" rev-parse --verify origin/main >/dev/null 2>&1; then
    log "origin/main resolves"
    return 0
  fi
  warn "origin/main does not resolve in $tree."
  warn "The pre-push audits that diff against a base will SKIP themselves, and the"
  warn "PR machinery expects refs/remotes/origin/main to exist (DESIGN.md #8)."
  warn "Fix it with the local convention: a 'main' branch plus an origin/main alias"
  warn "maintained by local/bin/pr_merge.py."
  return 1
}

# The ProofWidgets fresh-state workaround (docgen.yml:56-69): `lake exe cache get`
# runs `lake update`, whose mathlib post-update hook prunes
# .lake/packages/proofwidgets/.lake/build/lib before fetching a cloud release.  On
# a tree that has never built, the directory does not exist and the uncaught
# exception aborts the whole cache fetch.  The local variant of the same
# fresh-state failure is a *dirty* vendored tree: build byproducts such as
# widget/js/lake.trace block the revision checkout — see the 2026-08-30 failed
# entry and its retry in results/telemetry/builds.jsonl.
proofwidgets_fresh_state_workaround() { # <worktree>
  local tree="$1" pkg name dirty=0
  if [ ! -d "$tree/.lake/packages" ]; then
    log "no .lake/packages yet (fresh worktree); warm-worktree.sh will fetch tier 2"
    return 0
  fi
  # Only tracked modifications are reset.  `git clean` is deliberately NOT run
  # inside a vendored package: it would delete downloaded build output and cost
  # hours to refetch.  If an untracked byproduct still blocks the checkout, the
  # cache fetch fails loudly and the caller falls back to compiling from source.
  for pkg in "$tree"/.lake/packages/*; do
    [ -d "$pkg/.git" ] || continue
    name="$(basename "$pkg")"
    if [ -n "$(run_outside_git_env git -C "$pkg" status --porcelain --untracked-files=no 2>/dev/null || true)" ]; then
      dirty=1
      if [ "$CHECK_ONLY" -eq 1 ]; then
        warn "vendored package tree $name is dirty; the Mathlib cache fetch will abort"
        continue
      fi
      log "resetting dirty vendored package tree: $name"
      run_outside_git_env git -C "$pkg" reset --hard >/dev/null 2>&1 \
        || warn "could not reset $name; the Mathlib cache fetch may abort"
    fi
  done
  if [ "$CHECK_ONLY" -eq 0 ]; then
    if [ -d "$tree/.lake/packages/proofwidgets" ]; then
      mkdir -p "$tree/.lake/packages/proofwidgets/.lake/build/lib"
    fi
    # A dirty tree that was reset is fixed, not a finding.
    return 0
  fi
  return "$dirty"
}

call_warm_worktree() { # <worktree> [args...]
  local tree="$1"; shift
  # Deliberately the copy next to THIS script, not the one inside the worktree:
  # a worktree may hold an unreviewed branch, and the bootstrap must not execute
  # code from the tree it is bootstrapping (the local analog of DESIGN.md #5).
  local warmer="$SCRIPT_DIR/warm-worktree.sh"
  if [ ! -f "$warmer" ]; then
    die "warm-worktree.sh not found at $warmer.
The build cache consumer is part of this bootstrap and has no fallback:
without it this worktree would silently start from a cold build.
Restore local/bin/warm-worktree.sh, or re-run with --skip-warm to accept that."
  fi
  if [ ! -x "$warmer" ]; then
    warn "$warmer is not executable; invoking it through bash"
    bash "$warmer" "$tree" "$@"
    return $?
  fi
  "$warmer" "$tree" "$@"
}

install_hooks() { # <worktree>
  local tree="$1"
  local installer="$tree/scripts/install_git_hooks.sh"
  if [ ! -f "$installer" ]; then
    warn "$installer is missing; the local pre-commit/pre-push gates are NOT installed"
    return 1
  fi
  if [ "$CHECK_ONLY" -eq 0 ]; then
    ( cd "$tree" && run_outside_git_env sh "$installer" --install ) \
      || { warn "install_git_hooks.sh --install failed"; return 1; }
  fi
  # Always verify: docs/ci-automation.md calls out --check for "each fresh
  # worktree used for a PR".
  if ( cd "$tree" && run_outside_git_env sh "$installer" --check ); then
    return 0
  fi
  warn "install_git_hooks.sh --check failed for $tree"
  return 1
}

# --------------------------------------------------------------------------- main

main() {
  while [ $# -gt 0 ]; do
    case "$1" in
      --check)        CHECK_ONLY=1; shift ;;
      --build)        WARM_ARGS+=(--build); shift ;;
      --no-build)     WARM_ARGS+=(--no-build); shift ;;
      --force-cold)   WARM_ARGS+=(--force-cold); shift ;;
      --skip-warm)    SKIP_WARM=1; shift ;;
      --persist-path) PERSIST_PATH=1; shift ;;
      -h|--help)      usage; exit 0 ;;
      -*)             usage >&2; die "unknown option: $1" ;;
      *)
        [ -z "$WORKTREE" ] || { usage >&2; die "more than one worktree given"; }
        WORKTREE="$1"; shift ;;
    esac
  done

  if [ -z "$WORKTREE" ]; then
    WORKTREE="$(run_outside_git_env git rev-parse --show-toplevel 2>/dev/null || true)"
    [ -n "$WORKTREE" ] || die "no worktree given and $PWD is not inside a git worktree"
  fi
  [ -d "$WORKTREE" ] || die "worktree $WORKTREE does not exist"
  WORKTREE="$(cd "$WORKTREE" && pwd)"
  [ -e "$WORKTREE/.git" ] || die "$WORKTREE is not a git worktree (no .git)"

  local status=0

  if [ "$CHECK_ONLY" -eq 1 ]; then
    log "checking $WORKTREE (report-only; nothing will be modified)"
  else
    log "bootstrapping $WORKTREE"
  fi

  # 1. elan and the pinned toolchain.
  assert_elan
  ensure_toolchain "$WORKTREE" || status=1

  # 2. PATH for this process, and optionally for future shells.
  if [ "$PERSIST_PATH" -eq 1 ] && [ "$CHECK_ONLY" -eq 0 ]; then
    persist_elan_path
  else
    log 'PATH for this process includes $HOME/.elan/bin; for future shells add:'
    log '  export PATH="$HOME/.elan/bin:$PATH"    (or re-run with --persist-path)'
  fi
  assert_lake

  # 3. NO `lake update`.  Stated, not silently omitted.
  log "skipping 'lake update' by design: it would move lake-manifest.json out from"
  log "under the hot-cache keyhash and mutate the vendored package trees."
  log "Mathlib bumps are a separate, human-invoked operation."

  # 4. origin/main sanity (DESIGN.md #8).
  check_origin_main "$WORKTREE" || status=1

  # 5. Fresh-state workaround, before anything runs `lake exe cache get`.
  proofwidgets_fresh_state_workaround "$WORKTREE" || status=1

  # 6. Prime the two-tier cache.
  if [ "$SKIP_WARM" -eq 1 ]; then
    log "--skip-warm: not priming .lake/build or .lake/packages"
  elif [ "$CHECK_ONLY" -eq 1 ]; then
    call_warm_worktree "$WORKTREE" --status || status=1
  else
    call_warm_worktree "$WORKTREE" "${WARM_ARGS[@]+"${WARM_ARGS[@]}"}" || status=1
  fi

  # 7. Local gates.  docs/ci-automation.md: run --check in each fresh worktree.
  install_hooks "$WORKTREE" || status=1

  if [ "$status" -eq 0 ]; then
    log "worktree ready: $WORKTREE"
  elif [ "$CHECK_ONLY" -eq 1 ]; then
    warn "check found problems in $WORKTREE (see the warnings above)"
  else
    warn "bootstrap finished with problems in $WORKTREE (see the warnings above)"
  fi
  return "$status"
}

main "$@"
