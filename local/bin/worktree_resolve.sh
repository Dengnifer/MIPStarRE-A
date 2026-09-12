#!/usr/bin/env bash
# worktree_resolve.sh — resolve the worktree of a branch, registry first.
#
#   local/bin/worktree_resolve.sh [--root DIR] [--create] [--warm] [--quiet] <branch>
#   . local/bin/worktree_resolve.sh   # then call worktree_resolve <branch>
#
# Resolution order, identical to autofix.sh:resolve_worktree and ci.sh:
#   1. `git worktree list --porcelain`, matching `branch refs/heads/<branch>` —
#      git's own registry is the only authority on which directory holds a
#      branch;
#   2. the `.worktrees/<branch>` convention (and the `/`->`-` flattened
#      spelling autofix.sh uses), accepted ONLY when that directory's HEAD is
#      the branch asked for.
#
# A directory that exists but holds a different branch is a MISMATCH and is
# reported as one; it is never used and never silently moved.  On 2026-09-12
# PR 213's lane worktree held a different branch than the PR, so every refresh
# "succeeded" and pushed nothing at all (full-speed-mode v2 design §2 Item 5).
#
# Output: the absolute worktree path on stdout, nothing else.
# Exit: 0 resolved · 2 usage or git failure · 3 mismatch (a path exists for the
#       conventional name but holds another branch) · 4 no worktree (and
#       --create was not given).
set -u

worktree_resolve() { # <branch> [root] [create] [warm]
  local branch="${1:-}" root="${2:-}" create="${3:-0}" warm="${4:-0}"
  local found flat dest have start
  [ -n "$branch" ] || { printf 'worktree_resolve: branch required\n' >&2; return 2; }
  if [ -z "$root" ]; then
    root="$(git rev-parse --show-toplevel 2>/dev/null)" || {
      printf 'worktree_resolve: not a git repository\n' >&2; return 2; }
  fi
  git -C "$root" rev-parse --git-dir >/dev/null 2>&1 || {
    printf 'worktree_resolve: %s is not a git repository\n' "$root" >&2; return 2; }

  found="$(git -C "$root" worktree list --porcelain 2>/dev/null |
    awk -v b="branch refs/heads/$branch" '
      /^worktree /{ p = substr($0, 10) }
      $0 == b { print p; exit }')"
  if [ -n "$found" ] && [ -d "$found" ]; then
    printf '%s\n' "$found"
    return 0
  fi

  flat="$(printf '%s' "$branch" | tr '/' '-')"
  for dest in "$root/.worktrees/$branch" "$root/.worktrees/$flat"; do
    [ -e "$dest" ] || continue
    have="$(git -C "$dest" rev-parse --abbrev-ref HEAD 2>/dev/null || true)"
    if [ "$have" = "$branch" ]; then
      printf '%s\n' "$dest"
      return 0
    fi
    printf 'worktree_resolve: %s exists but holds %s, not %s\n' \
      "$dest" "${have:-no git worktree}" "$branch" >&2
    return 3
  done

  [ "$create" = 1 ] || return 4

  dest="$root/.worktrees/$branch"
  mkdir -p "$(dirname "$dest")"
  if git -C "$root" show-ref -q --verify "refs/heads/$branch"; then
    git -C "$root" worktree add --quiet "$dest" "$branch" || {
      printf 'worktree_resolve: git worktree add %s %s failed\n' "$dest" "$branch" >&2; return 2; }
  else
    start="github/main"
    git -C "$root" show-ref -q --verify "refs/remotes/github/$branch" && start="github/$branch"
    git -C "$root" worktree add --quiet -b "$branch" "$dest" "$start" || {
      printf 'worktree_resolve: git worktree add -b %s %s %s failed\n' "$branch" "$dest" "$start" >&2; return 2; }
  fi
  if [ "$warm" = 1 ] && [ -x "$root/local/bin/worktree-setup.sh" ]; then
    "$root/local/bin/worktree-setup.sh" "$dest" >&2 ||
      printf 'worktree_resolve: worktree-setup.sh reported warnings for %s\n' "$dest" >&2
  fi
  printf '%s\n' "$dest"
  return 0
}

# Sourced: export the function only.  Executed: parse the flags.
if [ "${BASH_SOURCE[0]}" = "${0}" ]; then
  ROOT=""; CREATE=0; QUIET=0; WARM=0; BRANCH=""
  while [ "$#" -gt 0 ]; do
    case "$1" in
      --root) ROOT="${2:-}"; shift ;;
      --create) CREATE=1 ;;
      --warm) WARM=1 ;;
      --quiet) QUIET=1 ;;
      -h|--help) sed -n '2,23p' "${BASH_SOURCE[0]}" | sed 's/^# \{0,1\}//'; exit 0 ;;
      --) shift; BRANCH="${1:-}" ;;
      -*) printf 'worktree_resolve.sh: unknown option %s\n' "$1" >&2; exit 2 ;;
      *) BRANCH="$1" ;;
    esac
    shift || true
  done
  [ -n "$BRANCH" ] || { printf 'usage: worktree_resolve.sh [--root DIR] [--create] [--warm] <branch>\n' >&2; exit 2; }
  if [ "$QUIET" = 1 ]; then
    worktree_resolve "$BRANCH" "$ROOT" "$CREATE" "$WARM" 2>/dev/null
  else
    worktree_resolve "$BRANCH" "$ROOT" "$CREATE" "$WARM"
  fi
  exit $?
fi
