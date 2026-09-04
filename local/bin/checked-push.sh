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
Usage: local/bin/checked-push.sh [--repo-root PATH] REMOTE LOCAL_REF:REMOTE_REF

Run .githooks/pre-push against one explicit branch ref, then push that ref.
Both refs must use their full refs/heads/... names.
EOF
}

die() {
  printf '%s: error: %s\n' "$PROG" "$*" >&2
  exit 2
}

REPO_ROOT="$SCRIPT_ROOT"
if [ "${1:-}" = "--repo-root" ]; then
  [ "$#" -ge 2 ] || die "--repo-root requires a path"
  REPO_ROOT="$2"
  shift 2
fi

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
  unset MIPSTARRE_EXPECTED_PUSH_TUPLE
  exec git -C "$REPO_ROOT" push "$REMOTE" "$REFSPEC"
fi

LOCAL_SHA="$(git -C "$REPO_ROOT" rev-parse --verify "$LOCAL_REF^{commit}")" ||
  die "cannot resolve local branch $LOCAL_REF"
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

HOOK="$REPO_ROOT/.githooks/pre-push"
[ -x "$HOOK" ] || die "$HOOK is missing or not executable; run scripts/install_git_hooks.sh"

(
  unset MIPSTARRE_SKIP_HOOKS
  unset MIPSTARRE_EXPECTED_PUSH_TUPLE
  cd "$REPO_ROOT"
  "$HOOK" "$REMOTE" "$REMOTE_URL"
) <<< "$LOCAL_REF $LOCAL_SHA $REMOTE_REF $REMOTE_SHA"

CURRENT_LOCAL_SHA="$(git -C "$REPO_ROOT" rev-parse --verify "$LOCAL_REF^{commit}")" ||
  die "cannot re-resolve local branch $LOCAL_REF after preflight"
[ "$CURRENT_LOCAL_SHA" = "$LOCAL_SHA" ] ||
  die "local branch $LOCAL_REF changed during preflight"

printf '%s: gate passed before opening the push transport.\n' "$PROG" >&2
# Freeze the source object and atomically require the preflight remote tip.  The
# native hook is only a short defense-in-depth confirmation; the lease keeps the
# tuple binding intact when that hook is stale or not selected.
LEASE_SHA="$REMOTE_SHA"
[ "$LEASE_SHA" != "$ZERO_SHA" ] || LEASE_SHA=""
MIPSTARRE_SKIP_HOOKS=1 \
  MIPSTARRE_EXPECTED_PUSH_TUPLE="$LOCAL_SHA $LOCAL_SHA $REMOTE_REF $REMOTE_SHA" \
  git -C "$REPO_ROOT" push --force-with-lease="$REMOTE_REF:$LEASE_SHA" \
    "$REMOTE" "$LOCAL_SHA:$REMOTE_REF"
