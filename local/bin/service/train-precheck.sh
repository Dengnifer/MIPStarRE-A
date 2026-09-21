#!/usr/bin/env bash
# train-precheck.sh PR [PR...] — dry `--no-ff` merge of the members, in the order given,
# on top of the published base, in a THROWAWAY worktree.  No build, no push, nothing
# written to the primary checkout.  Prints one line per member: "merges clean" or the
# conflicting paths.
#
# NEVER `git config user.name` inside a throwaway worktree: repository-level config is
# shared by every worktree of the checkout, and one such override put about a hundred
# and eighty commits on the base branch under the wrong author.  The identity travels as
# `git -c` flags on the single command that needs it.
#
# Provenance: kit-src/tmp-scripts/meta-train-precheck.sh (repository path and slug
# hard-coded; its tail also grepped one project-specific Lean file, which is gone).
set -u
KIT_SERVICE_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd -P)"
# shellcheck source=/dev/null
. "$KIT_SERVICE_DIR/service-lib.sh"
cd "$KIT_REPO_ROOT" || exit 1

[ "$#" -ge 1 ] || { echo "usage: train-precheck.sh PR [PR...]" >&2; exit 2; }
SLUG="$(kit_slug)" || { echo "train-precheck: no GitHub slug (set project.github_slug)" >&2; exit 2; }
BASE="${KIT_BASE_BRANCH:-main}"
T="${TMPDIR:-/tmp}/kit-precheck-$$"

git fetch -q github
git worktree add -q --detach "$T" "github/$BASE" || exit 1
cleanup() { cd "$KIT_REPO_ROOT" && git worktree remove --force "$T" >/dev/null 2>&1; }
trap cleanup EXIT

cd "$T" || exit 1
RC=0
for N in "$@"; do
  H=$(gh api "repos/$SLUG/pulls/$N" --jq .head.sha) || { echo "PR $N: cannot read the head"; RC=1; continue; }
  git fetch -q github "$H" 2>/dev/null
  if git -c user.name=train-precheck -c user.email=train-precheck@localhost \
       merge -q --no-ff -m "precheck $N" "$H" >/dev/null 2>&1; then
    echo "PR $N ${H:0:10}: merges clean"
  else
    echo "PR $N ${H:0:10}: CONFLICT in: $(git diff --name-only --diff-filter=U | tr '\n' ' ')"
    git merge --abort 2>/dev/null
    RC=1
  fi
done
exit "$RC"
