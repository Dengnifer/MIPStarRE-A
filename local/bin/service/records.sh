#!/usr/bin/env bash
# records.sh ["<subject tail>"] — publish the project's records.
# Folds the helper spools that live OUTSIDE the repository into their tracked registry,
# commits what is new under results/telemetry, and publishes the base branch with
# local/bin/github-sync.sh.
#
# It commits ONLY .md and .jsonl files under results/telemetry (plus the generated
# github-snapshot/*.json).  Anything else staged there is a mistake and aborts the run:
# records are records, not a back door for source changes.
#
# Rules paid for in incidents:
#   * Refuse while a train marker exists or a train process runs — a train needs the
#     primary checkout untouched for its whole run.
#   * Nothing a helper runs may write into the primary checkout; helpers append to spool
#     files under the cache root and this script folds them in.
#   * A tracked registry that a worker wrote into directly (declaration claims) has its
#     new rows moved to a spool and the tracked file restored, so the primary stays clean.
#
# Exit codes: 0 published, 3 a train is staged or running, 4 refused (dirty or
# non-record content), 5 publication failed.
# Provenance: kit-src/tmp-scripts/meta-records.sh, hard-coded to one repository path,
# one cache directory and one helper family's spool name.
set -u
KIT_SERVICE_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd -P)"
# shellcheck source=/dev/null
. "$KIT_SERVICE_DIR/service-lib.sh"
cd "$KIT_REPO_ROOT" || exit 1

D="$KIT_DAEMON_DIR"; BASE="${KIT_BASE_BRANCH:-main}"
SPOOL="$KIT_STATE_DIR/helper-sessions-spool.jsonl"
CLAIM_SPOOL="$KIT_STATE_DIR/declaration-claims-spool.jsonl"
REGISTRY="local/registry/declaration-claims.jsonl"

if [ -e "$D/train-approved.json" ] || [ -e "$D/train-approved.running.json" ]; then
  echo "train marker present: no record commit now"; exit 3
fi
# Anchored on this repository: a machine-wide match would also see another project's train.
pgrep -f "$KIT_REPO_ROOT/local/bin/(pr_train|daemon_train)[.]py" >/dev/null && { echo "a train of this repository is running"; exit 3; }
[ "$(git rev-parse --abbrev-ref HEAD)" = "$BASE" ] || { echo "the primary is not on $BASE"; exit 4; }

# A worker that claims declarations writes into a TRACKED file of the primary: move the
# new rows into a spool and restore the file, so the primary stays publishable.
if [ -f "$REGISTRY" ] && ! git diff --quiet -- "$REGISTRY"; then
  git diff -- "$REGISTRY" | grep "^+{" | cut -c2- >> "$CLAIM_SPOOL"
  git checkout -- "$REGISTRY" && echo "declaration-claim rows moved to the spool"
fi
if [ -s "$SPOOL" ]; then
  cat "$SPOOL" >> results/telemetry/owner-sessions.jsonl && : > "$SPOOL" && echo "helper spool folded"
fi

DIRTY_OTHER=$(git status --porcelain | awk '{print $NF}' | grep -v "^results/telemetry/" || true)
[ -z "$DIRTY_OTHER" ] || { echo "ABORT: dirty path outside results/telemetry:"; echo "$DIRTY_OTHER"; exit 4; }

git add -- results/telemetry
BAD=$(git diff --cached --name-only | grep -v -E "\.(md|jsonl)$" | grep -v "github-snapshot/.*\.json$" || true)
[ -z "$BAD" ] || { echo "ABORT: staged under results/telemetry but not a record (.md/.jsonl):"; echo "$BAD"; git reset -q; exit 4; }

if ! git diff --cached --quiet; then
  git commit -qm "chore(telemetry): ${1:-records}" && echo "committed $(git rev-parse --short HEAD)"
fi
git fetch -q github "$BASE"
if [ "$(git rev-parse "$BASE")" != "$(git rev-parse "github/$BASE")" ]; then
  bash local/bin/github-sync.sh "$BASE" 2>&1 | tail -n 2
  git fetch -q github "$BASE"
fi
[ "$(git rev-parse "$BASE")" = "$(git rev-parse "github/$BASE")" ] || { echo "ABORT: local $BASE != github/$BASE after publication"; exit 5; }
echo "local $(git rev-parse --short "$BASE") remote $(git rev-parse --short "github/$BASE") dirty=$(git status --porcelain | wc -l)"
