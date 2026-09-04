#!/usr/bin/env bash
# Manage an optional external .lake: prepare <worktree> [--check] | cleanup <repo> <branch>.
set -euo pipefail
log() { printf '[lake-root] %s\n' "$*" >&2; }
die() { printf '[lake-root] ERROR: %s\n' "$*" >&2; exit 1; }
run_outside_git_env() (
  if command -v git >/dev/null 2>&1; then
    for name in $(git rev-parse --local-env-vars); do unset "$name" || true; done
  fi
  "$@"
)
reject_hot_main() { # <canonical-path>
  local base="${MIPSTARRE_CACHE_ROOT:-$HOME/.cache/mipstarre-dev}/hot-main" protected
  for protected in "$base" "$base/repo" "$base/snapshots" "$base/current"; do
    protected="$(realpath -m -- "$protected")" || die "cannot resolve hot-main"
    [ "$protected" != "/" ] || die "a protected hot-main path resolves to /"
    case "$1" in "$protected"|"$protected"/*) die "Lake target is inside hot-main: $1" ;; esac
  done
}
canonical_lake_root() { # <create: 0|1>
  local create="$1" root="${MIPSTARRE_LAKE_ROOT:-}"
  [ -n "$root" ] || return 1
  case "$root" in /*) ;; *) die "MIPSTARRE_LAKE_ROOT must be absolute: $root" ;; esac
  root="$(realpath -m -- "$root")" || die "cannot resolve MIPSTARRE_LAKE_ROOT"
  [ "$root" != "/" ] || die "MIPSTARRE_LAKE_ROOT must not resolve to /"; reject_hot_main "$root"
  [ "$create" -eq 1 ] || [ -d "$root" ] \
    || die "MIPSTARRE_LAKE_ROOT does not exist: $root"
  printf '%s' "$root"
}
validated_target() { # <canonical-root> <target>
  local root="$1" target="$2" resolved
  resolved="$(realpath -m -- "$target")" || die "cannot resolve Lake target: $target"
  case "$resolved" in "$root"/*) ;; *) die "Lake target escapes root: $resolved" ;; esac
  reject_hot_main "$resolved"
  printf '%s' "$resolved"
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
  local tree="$1" check="$2" root branch target resolved link actual
  [ -n "${MIPSTARRE_LAKE_ROOT:-}" ] || return 0
  [ -d "$tree" ] || die "worktree does not exist: $tree"
  tree="$(cd "$tree" && pwd -P)"
  root="$(canonical_lake_root "$((1 - check))")"
  case "$root/" in "$tree/"*) die "the Lake root must be outside the worktree" ;; esac
  case "$tree/" in "$root/"*) die "the worktree must be outside the Lake root" ;; esac
  branch="$(worktree_branch "$tree")"; target="$root/$branch"
  link="$tree/.lake"
  if [ -L "$link" ]; then
    actual="$(readlink "$link")"
    [ "$actual" = "$target" ] \
      || die "$link points to $actual, expected $target; refusing to orphan build data"
  elif [ "$check" -eq 1 ]; then die "$link is not a symlink to $target"
  elif [ -e "$link" ]; then
    [ -d "$link" ] || die "$link exists and is not a directory"
    [ -z "$(find "$link" -mindepth 1 -maxdepth 1 -print -quit)" ] \
      || die "$link is populated; migrate it before enabling MIPSTARRE_LAKE_ROOT"
  fi
  [ ! -L "$target" ] || die "external Lake target must not be a symlink: $target"
  if [ "$check" -eq 1 ]; then
    validated_target "$root" "$target" >/dev/null
    [ -d "$target" ] || die "$link is dangling; expected directory $target"
  else
    [ ! -e "$target" ] || [ -d "$target" ] \
      || die "external Lake target is not a directory: $target"
    resolved="$(validated_target "$root" "$target")"
    mkdir -p "$target"
    [ "$(validated_target "$root" "$target")" = "$resolved" ] \
      || die "Lake target changed while it was prepared: $target"
    if [ ! -L "$link" ]; then [ ! -d "$link" ] || rmdir "$link"; ln -s "$target" "$link"; fi
  fi
  log "$link -> $target"
}
cleanup_lake() { # <repository> <branch>
  local repo="$1" branch="$2" root target resolved line listing tree
  [ -d "$repo" ] || die "repository does not exist: $repo"
  repo="$(cd "$repo" && pwd -P)"
  root="$(canonical_lake_root 0)" || die "MIPSTARRE_LAKE_ROOT must be set for cleanup"
  case "$root/" in "$repo/"*) die "the Lake root must be outside the repository" ;; esac
  case "$repo/" in "$root/"*) die "the repository must be outside the Lake root" ;; esac
  run_outside_git_env git check-ref-format --branch "$branch" >/dev/null 2>&1 \
    || die "invalid branch name: $branch"
  target="$root/$branch"; validated_target "$root" "$target" >/dev/null
  listing="$(run_outside_git_env git -C "$repo" worktree list --porcelain)" \
    || die "cannot read the worktree registry under $repo"
  while IFS= read -r line; do
    case "$line" in
      "branch refs/heads/$branch") die "branch $branch still has a worktree" ;;
      "worktree "*)
        tree="${line#worktree }"
        [ ! -L "$tree/.lake" ] || [ "$(readlink "$tree/.lake")" != "$target" ] \
          || die "$tree still points to $target"
        ;;
    esac
  done <<< "$listing"
  [ ! -L "$target" ] || die "refusing to remove symlink target $target"
  if [ ! -e "$target" ]; then log "no external Lake directory for $branch"; return 0; fi
  [ -d "$target" ] || die "external Lake target is not a directory: $target"
  resolved="$(validated_target "$root" "$target")"
  rm -rf -- "$resolved"
  log "removed external Lake directory $target"
}
usage() { printf '%s\n' 'Usage: lake-root.sh prepare <worktree> [--check]' \
  '       lake-root.sh cleanup <repository> <branch>'; }
case "${1:-}" in
  prepare)
    [ "$#" -eq 2 ] || [ "$#" -eq 3 ] || { usage >&2; exit 2; }
    [ "$#" -eq 2 ] || [ "$3" = "--check" ] || { usage >&2; exit 2; }
    prepare_lake "$2" "$([ "$#" -eq 3 ] && printf 1 || printf 0)" ;;
  cleanup) [ "$#" -eq 3 ] || { usage >&2; exit 2; }; cleanup_lake "$2" "$3" ;;
  -h|--help|help) usage ;;
  *) usage >&2; exit 2 ;;
esac
