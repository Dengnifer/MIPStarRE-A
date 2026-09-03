#!/usr/bin/env bash
# Migrate every checkout of ~/MIPStarRE-qpbt to the shared read-only package
# store: $CACHE_ROOT/packages/<key>, key = sha256(lake-manifest.json + lean-toolchain).
# Seeds the store by MOVING the primary checkout's .lake/packages (same
# filesystem: instant, inode-preserving, safe under running lake processes),
# then swaps each identical per-worktree copy for a symlink and deletes the copy.
# Usage: migrate-packages.sh [--dry-run] [<worktree> ...]   (default: all)
set -u
CACHE_ROOT="${MIPSTARRE_CACHE_ROOT:-$HOME/.cache/mipstarre-dev}"
P="$HOME/MIPStarRE-qpbt"
DRY=0; [ "${1:-}" = "--dry-run" ] && { DRY=1; shift; }
key_of() { cat "$1/lake-manifest.json" "$1/lean-toolchain" | sha256sum | cut -c1-16; }
KEY=$(key_of "$P"); STORE="$CACHE_ROOT/packages/$KEY"
echo "store: $STORE"
mkdir -p "$CACHE_ROOT/packages"

if [ ! -d "$STORE" ]; then
  if [ -L "$P/.lake/packages" ]; then echo "primary already linked elsewhere: $(readlink "$P/.lake/packages")"; exit 1; fi
  [ -d "$P/.lake/packages" ] || { echo "primary has no .lake/packages to seed from"; exit 1; }
  echo "seeding store from primary (mv + chmod -R a-w)"
  if [ "$DRY" -eq 0 ]; then
    mv "$P/.lake/packages" "$STORE" && chmod -R a-w "$STORE" && ln -s "$STORE" "$P/.lake/packages" || exit 1
  fi
fi
[ -L "$P/.lake/packages" ] || [ "$DRY" -eq 1 ] || { [ -e "$P/.lake/packages" ] && echo "primary packages is a real dir; not touching" || ln -s "$STORE" "$P/.lake/packages"; }

if [ $# -gt 0 ]; then set -- "$@"; else set -- "$P"/.worktrees/*/ "$CACHE_ROOT/hot-main/repo"; fi
freed=0
for w in "$@"; do
  w="${w%/}"; [ -d "$w" ] || continue
  pk="$w/.lake/packages"
  [ -e "$pk" ] || continue
  if [ -L "$pk" ]; then echo "linked  : $w"; continue; fi
  k=$(key_of "$w")
  if [ "$k" != "$KEY" ]; then echo "SKIP    : $w (key $k differs from store $KEY)"; continue; fi
  sz=$(du -sm "$pk" | cut -f1)
  echo "migrate : $w (${sz} MB)"
  [ "$DRY" -eq 1 ] && continue
  mv "$pk" "$pk.migrating" && ln -s "$STORE" "$pk" && rm -rf "$pk.migrating" && freed=$((freed+sz)) || echo "FAILED  : $w"
done
echo "freed ~${freed} MB"; df -h / | tail -1
