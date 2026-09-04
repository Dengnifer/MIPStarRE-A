#!/usr/bin/env bash
# Manage a worktree's optional external .lake directory.
#   lake-root.sh prepare <worktree> [--check]
#   lake-root.sh cleanup <repository> <branch>
set -euo pipefail
log() { printf '[lake-root] %s\n' "$*" >&2; }
die() { printf '[lake-root] ERROR: %s\n' "$*" >&2; exit 1; }
run_outside_git_env() (
  if command -v git >/dev/null 2>&1; then
    for name in $(git rev-parse --local-env-vars); do
      unset "$name" || true
    done
  fi
  "$@"
)
canonical_lake_root() { # <create: 0|1>
  local create="$1" root="${MIPSTARRE_LAKE_ROOT:-}"
  [ -n "$root" ] || return 1
  case "$root" in
    /*) ;;
    *) die "MIPSTARRE_LAKE_ROOT must be an absolute path: $root" ;;
  esac
  [ "$root" != "/" ] || die "MIPSTARRE_LAKE_ROOT must not be /"
  if [ "$create" -eq 1 ]; then
    mkdir -p "$root"
  else
    [ -d "$root" ] || die "MIPSTARRE_LAKE_ROOT does not exist: $root"
  fi
  (cd "$root" && pwd -P)
}
worktree_branch() { # <worktree>
  local branch
  branch="$(run_outside_git_env git -C "$1" symbolic-ref --quiet --short HEAD 2>/dev/null)" \
    || die "$1 is detached; MIPSTARRE_LAKE_ROOT requires a branch-owned worktree"
  run_outside_git_env git check-ref-format --branch "$branch" >/dev/null 2>&1 \
    || die "invalid worktree branch: $branch"
  printf '%s' "$branch"
}
prepare_lake() { # <worktree> <check-only: 0|1>
  local tree="$1" check_only="$2" root branch target link actual
  [ -n "${MIPSTARRE_LAKE_ROOT:-}" ] || return 0
  [ -d "$tree" ] || die "worktree does not exist: $tree"
  tree="$(cd "$tree" && pwd -P)"
  root="$(canonical_lake_root "$((1 - check_only))")"
  case "$root/" in "$tree/"*) die "the Lake root must be outside the worktree" ;; esac
  case "$tree/" in "$root/"*) die "the worktree must be outside the Lake root" ;; esac
  branch="$(worktree_branch "$tree")"
  target="$root/$branch"
  link="$tree/.lake"
  if [ -L "$link" ]; then
    actual="$(readlink "$link")"
    [ "$actual" = "$target" ] \
      || die "$link points to $actual, expected $target; refusing to orphan build data"
    [ ! -L "$target" ] || die "external Lake target must not be a symlink: $target"
    if [ "$check_only" -eq 1 ]; then
      [ -d "$target" ] || die "$link is dangling; expected directory $target"
    else
      mkdir -p "$target"
    fi
    log "$link already points to $target"
    return 0
  fi
  if [ "$check_only" -eq 1 ]; then
    die "$link is not a symlink to $target"
  fi
  if [ -e "$link" ]; then
    [ -d "$link" ] || die "$link exists and is not a directory"
    [ -z "$(find "$link" -mindepth 1 -maxdepth 1 -print -quit)" ] \
      || die "$link is populated; migrate it explicitly before enabling MIPSTARRE_LAKE_ROOT"
  fi
  [ ! -L "$target" ] || die "external Lake target must not be a symlink: $target"
  if [ -e "$target" ] && [ ! -d "$target" ]; then
    die "external Lake target exists and is not a directory: $target"
  fi
  mkdir -p "$target"
  [ ! -d "$link" ] || rmdir "$link"
  ln -s "$target" "$link"
  log "$link -> $target"
}
cleanup_lake() { # <repository> <branch>
  local repo="$1" branch="$2" root target line listing tree
  [ -d "$repo" ] || die "repository does not exist: $repo"
  repo="$(cd "$repo" && pwd -P)"
  root="$(canonical_lake_root 0)" \
    || die "MIPSTARRE_LAKE_ROOT must be set for lake-root cleanup"
  case "$root/" in "$repo/"*) die "the Lake root must be outside the repository" ;; esac
  case "$repo/" in "$root/"*) die "the repository must be outside the Lake root" ;; esac
  run_outside_git_env git check-ref-format --branch "$branch" >/dev/null 2>&1 \
    || die "invalid branch name: $branch"
  target="$root/$branch"
  listing="$(run_outside_git_env git -C "$repo" worktree list --porcelain)" \
    || die "cannot read the worktree registry under $repo"
  while IFS= read -r line; do
    case "$line" in
      "branch refs/heads/$branch")
        die "branch $branch still has a registered worktree; refusing cleanup"
        ;;
      "worktree "*)
        tree="${line#worktree }"
        if [ -L "$tree/.lake" ] && [ "$(readlink "$tree/.lake")" = "$target" ]; then
          die "$tree still points to $target; refusing cleanup"
        fi
        ;;
    esac
  done <<< "$listing"
  [ ! -L "$target" ] || die "refusing to remove symlink target $target"
  if [ ! -e "$target" ]; then
    log "no external Lake directory for $branch"
    return 0
  fi
  [ -d "$target" ] || die "external Lake target is not a directory: $target"
  rm -rf -- "$target"
  log "removed external Lake directory $target"
}
usage() {
  printf '%s\n' \
    'Usage: lake-root.sh prepare <worktree> [--check]' \
    '       lake-root.sh cleanup <repository> <branch>'
}
case "${1:-}" in
  prepare)
    [ "$#" -eq 2 ] || [ "$#" -eq 3 ] || { usage >&2; exit 2; }
    [ "$#" -eq 2 ] || [ "$3" = "--check" ] || { usage >&2; exit 2; }
    prepare_lake "$2" "$([ "$#" -eq 3 ] && printf 1 || printf 0)"
    ;;
  cleanup)
    [ "$#" -eq 3 ] || { usage >&2; exit 2; }
    cleanup_lake "$2" "$3"
    ;;
  -h|--help|help) usage ;;
  *) usage >&2; exit 2 ;;
esac
