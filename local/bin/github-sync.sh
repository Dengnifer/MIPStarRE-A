#!/usr/bin/env bash
# Synchronize explicit GitHub refs and refresh the read-only audit snapshot.
set -euo pipefail

PROG=github-sync.sh
SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
ROOT="${MIPSTARRE_REPO_ROOT:-$(cd "$SCRIPT_DIR/../.." && pwd)}"
MODE=all
BASE=main

usage() {
  cat <<'EOF'
usage: local/bin/github-sync.sh [refs|snapshot|all] [--base BRANCH]

Fetches only the named base ref into refs/remotes/github/<base> and/or writes
the paginated open-issue/open-PR audit snapshot. It never pushes any ref.
EOF
}

while [ "$#" -gt 0 ]; do
  case "$1" in
    refs|snapshot|all) MODE="$1"; shift ;;
    --base) [ "$#" -ge 2 ] || { usage >&2; exit 2; }; BASE="$2"; shift 2 ;;
    -h|--help) usage; exit 0 ;;
    *) printf '%s: unknown argument: %s\n' "$PROG" "$1" >&2; exit 2 ;;
  esac
done

case "$BASE" in
  ""|*'['*|*']'*|*' '*|*~*|*^*|*:*|*\?*|*\**|*\\*)
    printf '%s: unsafe base ref: %s\n' "$PROG" "$BASE" >&2
    exit 2
    ;;
esac

python3 "$SCRIPT_DIR/github_api.py" --repo-root "$ROOT" probe >/dev/null

if [ "$MODE" = refs ] || [ "$MODE" = all ]; then
  git -C "$ROOT" remote get-url github >/dev/null
  git -C "$ROOT" fetch --no-tags github \
    "refs/heads/$BASE:refs/remotes/github/$BASE"
  printf '%s: fetched github/%s at %s\n' \
    "$PROG" "$BASE" "$(git -C "$ROOT" rev-parse --short "refs/remotes/github/$BASE")"
fi

if [ "$MODE" = snapshot ] || [ "$MODE" = all ]; then
  DEST="$ROOT/results/telemetry/github-snapshot"
  python3 "$SCRIPT_DIR/github_api.py" --repo-root "$ROOT" --no-probe \
    snapshot "$DEST" >/dev/null
  printf '%s: refreshed %s\n' "$PROG" "$DEST"
fi
