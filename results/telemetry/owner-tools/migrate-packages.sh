#!/usr/bin/env bash
# migrate-packages.sh [--dry-run] [<worktree> ...] — point every checkout at ONE shared,
# read-only package store: <cache_root>/packages/<key>, key = the first sixteen hex
# digits of sha256(lake-manifest.json + lean-toolchain).  The store is seeded by MOVING
# the primary checkout's .lake/packages (same filesystem: instant, inode-preserving, safe
# under running lake processes); each identical per-worktree copy is then swapped for a
# symlink and deleted.  Default set: every worktree plus the hot-cache checkout.
#
# Never point lake at a live worktree and never `lake update`: the store is shared and
# read-only on purpose, and a per-worktree copy of the packages costs gigabytes each.
#
# Provenance: the origin's owner-tools/migrate-packages.sh (checkout path hard-coded).
set -u
HERE="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd -P)"
CFG="$HERE/../../../local/bin/session/config.sh"
# shellcheck source=/dev/null
[ -f "$CFG" ] && . "$CFG" 2>/dev/null
P="${KIT_REPO_ROOT:-$(cd "$HERE/../../.." && pwd -P)}"
CACHE_ROOT="${MIPSTARRE_CACHE_ROOT:-${KIT_CACHE_ROOT:-$HOME/.cache/paperlib-dev}}"

DRY=0; [ "${1:-}" = "--dry-run" ] && { DRY=1; shift; }
key_of() { cat "$1/lake-manifest.json" "$1/lean-toolchain" | sha256sum | cut -c1-16; }
KEY=$(key_of "$P") || { echo "cannot read lake-manifest.json / lean-toolchain in $P"; exit 1; }
STORE="$CACHE_ROOT/packages/$KEY"
echo "store: $STORE"
mkdir -p "$CACHE_ROOT/packages"

if [ ! -d "$STORE" ]; then
  if [ -L "$P/.lake/packages" ]; then echo "the primary is already linked elsewhere: $(readlink "$P/.lake/packages")"; exit 1; fi
  [ -d "$P/.lake/packages" ] || { echo "the primary has no .lake/packages to seed from"; exit 1; }
  echo "seeding the store from the primary (mv + chmod -R a-w)"
  if [ "$DRY" -eq 0 ]; then
    mv "$P/.lake/packages" "$STORE" && chmod -R a-w "$STORE" && ln -s "$STORE" "$P/.lake/packages" || exit 1
  fi
fi
[ -L "$P/.lake/packages" ] || [ "$DRY" -eq 1 ] || {
  [ -e "$P/.lake/packages" ] && echo "the primary's packages is a real directory; not touching it" \
    || ln -s "$STORE" "$P/.lake/packages"; }

if [ $# -gt 0 ]; then set -- "$@"; else set -- "$P"/.worktrees/*/ "$CACHE_ROOT/hot-main/repo"; fi
freed=0
for w in "$@"; do
  w="${w%/}"; [ -d "$w" ] || continue
  pk="$w/.lake/packages"
  [ -e "$pk" ] || continue
  if [ -L "$pk" ]; then echo "linked  : $w"; continue; fi
  k=$(key_of "$w") || continue
  if [ "$k" != "$KEY" ]; then echo "SKIP    : $w (key $k differs from the store's $KEY)"; continue; fi
  sz=$(du -sm "$pk" | cut -f1)
  echo "migrate : $w (${sz} MB)"
  [ "$DRY" -eq 1 ] && continue
  mv "$pk" "$pk.migrating" && ln -s "$STORE" "$pk" && rm -rf "$pk.migrating" && freed=$((freed+sz)) || echo "FAILED  : $w"
done
echo "freed ~${freed} MB"; df -h / | tail -1
