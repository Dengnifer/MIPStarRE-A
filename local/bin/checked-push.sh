#!/usr/bin/env bash
#
# Run the repository's pre-push gate before opening the push transport. Git's
# native pre-push hook runs after receive-pack starts, so a long Lean check can
# leave that connection idle until the remote closes it. This helper preserves
# the gate while keeping the expensive work outside the transport lifetime.
set -euo pipefail

PROG="checked-push.sh"
ZERO_SHA="0000000000000000000000000000000000000000"
SCRIPT_ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"

usage() {
  cat <<'EOF'
Usage: local/bin/checked-push.sh [--repo-root PATH] [--train-manifest PATH] REMOTE LOCAL_REF:REMOTE_REF

Run .githooks/pre-push against one explicit branch ref, then push that ref.
Both refs must use their full refs/heads/... names.

With --train-manifest the push also leases every verified member ref at its
verified value, so the remote refuses the whole publication if one moved.
EOF
}

die() {
  printf '%s: error: %s\n' "$PROG" "$*" >&2
  exit 2
}

require_validation_checkout() {
  local checkout_sha checkout_state
  checkout_sha="$(git -C "$VALIDATION_ROOT" rev-parse --verify 'HEAD^{commit}')" ||
    die "cannot resolve HEAD in $VALIDATION_ROOT"
  [ "$checkout_sha" = "$LOCAL_SHA" ] ||
    die "$VALIDATION_ROOT is at $checkout_sha, not $LOCAL_REF at $LOCAL_SHA"
  checkout_state="$(
    git -C "$VALIDATION_ROOT" status --porcelain=v1 --untracked-files=all
  )" || die "cannot inspect working tree $VALIDATION_ROOT"
  [ -z "$checkout_state" ] ||
    die "working tree $VALIDATION_ROOT differs from $LOCAL_REF at $LOCAL_SHA"
}

REPO_ROOT="$SCRIPT_ROOT"
TRAIN_MANIFEST=""
while :; do
  case "${1:-}" in
    --repo-root) [ "$#" -ge 2 ] || die "--repo-root requires a path"; REPO_ROOT="$2"; shift 2 ;;
    --train-manifest) [ "$#" -ge 2 ] || die "--train-manifest requires a path"; TRAIN_MANIFEST="$2"; shift 2 ;;
    *) break ;;
  esac
done

case "${1:-}" in
  --help|-h)
    usage
    exit 0
    ;;
esac
[ "$#" -eq 2 ] || { usage >&2; exit 2; }

REMOTE="$1"
REFSPEC="$2"
case "$REMOTE" in
  ""|-*) die "REMOTE must name a configured Git remote" ;;
esac

LOCAL_REF="${REFSPEC%%:*}"
REMOTE_REF="${REFSPEC#*:}"
if [ "$LOCAL_REF" = "$REFSPEC" ]; then
  die "refspec must map an explicit local branch to an explicit remote branch"
fi
case "$LOCAL_REF:$REMOTE_REF" in
  refs/heads/*:refs/heads/*) ;;
  *) die "both sides of the refspec must start with refs/heads/" ;;
esac

REPO_ROOT="$(git -C "$REPO_ROOT" rev-parse --show-toplevel)" ||
  die "cannot resolve repository root from $REPO_ROOT"
git -C "$REPO_ROOT" check-ref-format "$LOCAL_REF" >/dev/null ||
  die "invalid local ref $LOCAL_REF"
git -C "$REPO_ROOT" check-ref-format "$REMOTE_REF" >/dev/null ||
  die "invalid remote ref $REMOTE_REF"

if [ "${MIPSTARRE_SKIP_HOOKS:-}" = "1" ]; then
  [ -z "$TRAIN_MANIFEST" ] || die "a train cannot bypass checked publication"
  unset MIPSTARRE_EXPECTED_PUSH_TUPLE
  # The bypass skips validation, not the explicit one-ref publication boundary.
  exec git -C "$REPO_ROOT" -c push.followTags=false push --no-follow-tags \
    "$REMOTE" "$REFSPEC"
fi

LOCAL_SHA="$(git -C "$REPO_ROOT" rev-parse --verify "$LOCAL_REF^{commit}")" ||
  die "cannot resolve local branch $LOCAL_REF"
WORKTREE_ROWS="$(git -C "$REPO_ROOT" worktree list --porcelain)" ||
  die "cannot list registered worktrees"
VALIDATION_ROOT=""
candidate=""
while IFS= read -r line; do
  case "$line" in
    "worktree "*) candidate="${line#worktree }" ;;
    "branch $LOCAL_REF") VALIDATION_ROOT="$candidate"; break ;;
  esac
done <<< "$WORKTREE_ROWS"
[ -n "$VALIDATION_ROOT" ] ||
  die "$LOCAL_REF is not checked out in a registered worktree"
VALIDATION_ROOT="$(git -C "$VALIDATION_ROOT" rev-parse --show-toplevel)" ||
  die "cannot resolve worktree for $LOCAL_REF"
require_validation_checkout

REMOTE_URL="$(git -C "$REPO_ROOT" remote get-url --push "$REMOTE")" ||
  die "cannot resolve push URL for remote $REMOTE"
REMOTE_ROWS="$(git -C "$REPO_ROOT" ls-remote --refs "$REMOTE_URL" "$REMOTE_REF")" ||
  die "cannot read $REMOTE_REF from remote $REMOTE"

REMOTE_SHA=""
while IFS=$'\t' read -r sha ref extra; do
  [ -n "$sha" ] || continue
  [ "$ref" = "$REMOTE_REF" ] || continue
  [ -z "$extra" ] || die "unexpected ls-remote output for $REMOTE_REF"
  [ -z "$REMOTE_SHA" ] || die "remote $REMOTE returned $REMOTE_REF more than once"
  REMOTE_SHA="$sha"
done <<< "$REMOTE_ROWS"
[ -n "$REMOTE_SHA" ] || REMOTE_SHA="$ZERO_SHA"
[[ "$LOCAL_SHA" =~ ^[0-9a-f]{40}$ ]] || die "unexpected local object id $LOCAL_SHA"
[[ "$REMOTE_SHA" =~ ^[0-9a-f]{40}$ ]] || die "unexpected remote object id $REMOTE_SHA"
if [ "$REMOTE_SHA" != "$ZERO_SHA" ] &&
    ! git -C "$REPO_ROOT" merge-base --is-ancestor "$REMOTE_SHA" "$LOCAL_SHA"; then
  die "$LOCAL_SHA would not fast-forward $REMOTE_REF from $REMOTE_SHA"
fi

HOOK="$VALIDATION_ROOT/.githooks/pre-push"
[ -x "$HOOK" ] || die "$HOOK is missing or not executable; run scripts/install_git_hooks.sh"

(
  unset MIPSTARRE_SKIP_HOOKS
  unset MIPSTARRE_EXPECTED_PUSH_TUPLE
  cd "$VALIDATION_ROOT"
  "$HOOK" "$REMOTE" "$REMOTE_URL"
) <<< "$LOCAL_REF $LOCAL_SHA $REMOTE_REF $REMOTE_SHA"

CURRENT_LOCAL_SHA="$(git -C "$REPO_ROOT" rev-parse --verify "$LOCAL_REF^{commit}")" ||
  die "cannot re-resolve local branch $LOCAL_REF after preflight"
[ "$CURRENT_LOCAL_SHA" = "$LOCAL_SHA" ] ||
  die "local branch $LOCAL_REF changed during preflight"
require_validation_checkout

MEMBER_LEASES=()
MEMBER_SPECS=()
if [ -n "$TRAIN_MANIFEST" ]; then
  # The verifier reports the member refs it just confirmed; each one is leased
  # below so the remote itself refuses the publication when a member branch
  # moves between verification and the transport.
  MEMBER_FILE="$(mktemp)" || die "cannot create a temporary file for the member refs"
  trap 'rm -f "$MEMBER_FILE"' EXIT
  python3 "$SCRIPT_ROOT/local/bin/pr_train.py" --verify-manifest "$TRAIN_MANIFEST" \
    --expected-main "$REMOTE_SHA" --expected-head "$LOCAL_SHA" \
    --expected-ref "$REMOTE_REF" --members-out "$MEMBER_FILE" ||
    die "train changed during preflight"
  while IFS=' ' read -r member_ref member_sha extra; do
    [ -n "$member_ref" ] || continue
    [ -z "$extra" ] || die "unexpected member row for $member_ref"
    case "$member_ref" in
      refs/heads/*) ;;
      *) die "member ref $member_ref must start with refs/heads/" ;;
    esac
    [ "$member_ref" != "$REMOTE_REF" ] ||
      die "member ref $member_ref collides with the published ref"
    git -C "$REPO_ROOT" check-ref-format "$member_ref" >/dev/null ||
      die "invalid member ref $member_ref"
    [[ "$member_sha" =~ ^[0-9a-f]{40}$ ]] ||
      die "unexpected member object id $member_sha for $member_ref"
    for seen in ${MEMBER_SPECS[@]+"${MEMBER_SPECS[@]}"}; do
      [ "${seen#*:}" != "$member_ref" ] || die "member ref $member_ref appears twice"
    done
    MEMBER_LEASES+=("--force-with-lease=$member_ref:$member_sha")
    MEMBER_SPECS+=("$member_sha:$member_ref")
  done < "$MEMBER_FILE"
  [ "${#MEMBER_SPECS[@]}" -ge 2 ] ||
    die "train manifest verified fewer than two member refs"
fi

printf '%s: gate passed before opening the push transport.\n' "$PROG" >&2
# Freeze the source object and atomically require the preflight remote tip.  The
# native hook is only a short defense-in-depth confirmation; the lease keeps the
# tuple binding intact when that hook is stale or not selected.  A train adds one
# no-op update per member ref under the same atomic transaction: each member is
# pushed back at its verified value, so the remote compares the advertised value
# at transport start and rejects the whole push -- main included -- when a member
# moved, while a member that did not move is simply already up to date and stays
# out of both the transaction and the native hook's tuple.  Disable implicit
# annotated-tag expansion so the transport contains only the validated refs.
LEASE_SHA="$REMOTE_SHA"
[ "$LEASE_SHA" != "$ZERO_SHA" ] || LEASE_SHA=""
MIPSTARRE_SKIP_HOOKS=1 \
  MIPSTARRE_EXPECTED_PUSH_TUPLE="$LOCAL_SHA $LOCAL_SHA $REMOTE_REF $REMOTE_SHA" \
  git -C "$REPO_ROOT" -c push.followTags=false push --no-follow-tags --atomic \
    --force-with-lease="$REMOTE_REF:$LEASE_SHA" \
    ${MEMBER_LEASES[@]+"${MEMBER_LEASES[@]}"} \
    "$REMOTE" "$LOCAL_SHA:$REMOTE_REF" ${MEMBER_SPECS[@]+"${MEMBER_SPECS[@]}"}
