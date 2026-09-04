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
paths_overlap() {
  case "$1/" in "$2/"*) return 0 ;; esac
  case "$2/" in "$1/"*) return 0 ;; *) return 1 ;; esac
}
reject_hot_main() { # <canonical-path>
  local base="${MIPSTARRE_CACHE_ROOT:-$HOME/.cache/mipstarre-dev}/hot-main" protected
  for protected in "$base" "$base/repo" "$base/snapshots" "$base/current"; do
    protected="$(realpath -m -- "$protected")" || die "cannot resolve hot-main"
    [ "$protected" != "/" ] || die "a protected hot-main path resolves to /"
    paths_overlap "$1" "$protected" && die "Lake target overlaps hot-main: $1"
  done
}
canonical_lake_root() { # <create: 0|1>
  local create="$1" root="${MIPSTARRE_LAKE_ROOT:-}"
  [ -n "$root" ] || return 1
  case "$root" in /*) ;; *) die "MIPSTARRE_LAKE_ROOT must be absolute: $root" ;; esac
  root="$(realpath -m -- "$root")" || die "cannot resolve MIPSTARRE_LAKE_ROOT"
  [ "$root" != "/" ] || die "MIPSTARRE_LAKE_ROOT must not resolve to /"
  [ "$create" -eq 1 ] || [ -d "$root" ] || die "MIPSTARRE_LAKE_ROOT does not exist: $root"
  printf '%s' "$root"
}
validated_target() { # <canonical-root> <target>
  local root="$1" target="$2" resolved
  resolved="$(realpath -m -- "$target")" || die "cannot resolve Lake target: $target"
  case "$resolved" in "$root"/*) ;; *) die "Lake target escapes root: $resolved" ;; esac
  reject_hot_main "$resolved"
  printf '%s' "$resolved"
}
validate_repo_paths() { # <repository> <root> <target> <current-tree> <branch>
  local repo="$1" root="$2" target="$3" current="$4" branch="$5" listing line tree other
  listing="$(run_outside_git_env git -C "$repo" worktree list --porcelain)" \
    || die "cannot read worktrees under $repo"
  while IFS= read -r line; do
    case "$line" in
      "worktree "*)
        tree="$(realpath -m -- "${line#worktree }")"
        paths_overlap "$root" "$tree" && die "Lake root overlaps registered worktree: $tree" ;;
      "branch refs/heads/"*)
        other="${line#branch refs/heads/}"
        if [ "$other" = "$branch" ]; then
          [ -n "$current" ] && [ "$tree" = "$current" ] \
            || die "branch $branch still has a worktree"
        else
          other="$(realpath -m -- "$root/$other")" || die "cannot resolve target for $tree"
          [ "$other" != "$target" ] || die "target already used by $tree"
        fi ;;
    esac
  done <<< "$listing"
}
worktree_branch() { # <worktree>
  local branch
  branch="$(run_outside_git_env git -C "$1" symbolic-ref --quiet --short HEAD 2>/dev/null)" \
    || die "$1 is detached; a Lake root requires a branch"
  run_outside_git_env git check-ref-format --branch "$branch" >/dev/null 2>&1 \
    || die "invalid branch: $branch"
  printf '%s' "$branch"
}
prepare_lake() { # <worktree> <check-only: 0|1>
  local tree="$1" check="$2" root branch target resolved link actual
  [ -n "${MIPSTARRE_LAKE_ROOT:-}" ] || return 0
  [ -d "$tree" ] || die "worktree does not exist: $tree"
  tree="$(cd "$tree" && pwd -P)"
  root="$(canonical_lake_root "$((1 - check))")"
  branch="$(worktree_branch "$tree")"; target="$root/$branch"
  resolved="$(validated_target "$root" "$target")"
  validate_repo_paths "$tree" "$root" "$resolved" "$tree" "$branch"
  link="$tree/.lake"
  if [ -L "$link" ]; then
    actual="$(readlink "$link")"; [ "$actual" = "$target" ] \
      || die "$link points to $actual, expected $target; refusing to orphan build data"
  elif [ "$check" -eq 1 ]; then die "$link is not a symlink to $target"
  elif [ -e "$link" ]; then
    [ -d "$link" ] || die "$link exists and is not a directory"
    [ -z "$(find "$link" -mindepth 1 -maxdepth 1 -print -quit)" ] \
      || die "$link is populated; migrate it before enabling the Lake root"
  fi
  [ ! -L "$target" ] || die "external Lake target must not be a symlink: $target"
  if [ "$check" -eq 1 ]; then
    [ -d "$target" ] || die "$link is dangling; expected directory $target"
  else
    [ ! -e "$target" ] || [ -d "$target" ] || die "Lake target is not a directory: $target"
    mkdir -p "$target"
    [ "$(validated_target "$root" "$target")" = "$resolved" ] \
      || die "Lake target changed while preparing: $target"
    if [ ! -L "$link" ]; then [ ! -d "$link" ] || rmdir "$link"; ln -s "$target" "$link"; fi
  fi
  log "$link -> $target"
}
cleanup_lake() { # <repository> <branch>
  local repo="$1" branch="$2" root target resolved
  [ -d "$repo" ] || die "repository does not exist: $repo"
  repo="$(cd "$repo" && pwd -P)"
  root="$(canonical_lake_root 0)" || die "MIPSTARRE_LAKE_ROOT must be set for cleanup"
  run_outside_git_env git check-ref-format --branch "$branch" >/dev/null 2>&1 \
    || die "invalid branch: $branch"
  target="$root/$branch"; resolved="$(validated_target "$root" "$target")"
  [ ! -L "$target" ] || die "refusing to remove symlink target $target"
  if [ ! -e "$target" ]; then log "no external Lake directory for $branch"; return 0; fi
  [ -d "$target" ] || die "external Lake target is not a directory: $target"
  resolved="$(validated_target "$root" "$target")"
  validate_repo_paths "$repo" "$root" "$resolved" "" "$branch"
  rm -rf -- "$resolved"
  log "removed external Lake directory $target"
}
usage() { printf '%s\n' 'Usage: lake-root.sh prepare <tree> [--check] | cleanup <repo> <branch>'; }
case "${1:-}" in
  prepare)
    [ "$#" -eq 2 ] || [ "$#" -eq 3 ] || { usage >&2; exit 2; }
    [ "$#" -eq 2 ] || [ "$3" = "--check" ] || { usage >&2; exit 2; }
    prepare_lake "$2" "$([ "$#" -eq 3 ] && printf 1 || printf 0)" ;;
  cleanup) [ "$#" -eq 3 ] || { usage >&2; exit 2; }; cleanup_lake "$2" "$3" ;;
  -h|--help|help) usage ;;
  *) usage >&2; exit 2 ;;
esac
