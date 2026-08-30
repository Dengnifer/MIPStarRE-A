#!/usr/bin/env bash
# fetch-latest-component.sh — copy the newest published version of a local site
# component into DEST_DIR.
#
# Usage: fetch-latest-component.sh NAME DEST_DIR
#   NAME       component name: site-blueprint | site-docs | site-badges
#   DEST_DIR   directory to populate (created only on a hit)
#
# Drop-in local replacement for scripts/fetch-latest-artifact.sh, the shim that
# .github/workflows/deploy-pages.yml:30-32 uses to pull the newest non-expired
# Actions artifact per component name across all producing workflows. The CLI
# contract is deliberately identical, including the miss contract:
#
#   * a miss (component never published, or a dangling `latest`) prints a
#     warning and exits 0 WITHOUT creating DEST_DIR — callers decide whether a
#     missing component is fatal. This is load-bearing: the refusals in
#     scripts/assemble-pages-site.sh:36,41 ("refusing to remove deployed API
#     docs" / "refusing to remove deployed badge endpoints") test for the
#     directory, so creating an empty DEST_DIR would silently break them.
#   * usage errors exit 2; a corrupt store exits 1 (that is not a miss).
#
# "Newest non-expired artifact" maps to "the target of the component's `latest`
# symlink"; artifact retention maps to the GC pass in local/bin/site.sh, which
# keeps the last N versions and never deletes the version `latest` points at.
# No gh CLI, no GH_TOKEN, no GITHUB_REPOSITORY.
#
# Environment:
#   MIPSTARRE_CACHE_ROOT  runtime state root (default ~/.cache/mipstarre-dev)
#
# Protocol: local/protocols/site.md
set -euo pipefail

prog="$(basename "$0")"

if [ "$#" -ne 2 ]; then
  echo "Usage: $prog NAME DEST_DIR" >&2
  exit 2
fi

NAME="$1"
DEST="$2"

# Component names index directories under the store root; keep them boring so a
# name can never escape it (the parent shim passed NAME straight into a URL
# query, which had the same requirement for a different reason).
case "$NAME" in
  ""|.|..)
    echo "$prog: invalid component name '$NAME'" >&2
    exit 2
    ;;
esac
if ! printf '%s' "$NAME" | grep -Eq '^[A-Za-z0-9][A-Za-z0-9._-]*$'; then
  echo "$prog: invalid component name '$NAME' (expected [A-Za-z0-9._-])" >&2
  exit 2
fi
if [ -z "$DEST" ]; then
  echo "$prog: DEST_DIR must not be empty" >&2
  exit 2
fi

CACHE_ROOT="${MIPSTARRE_CACHE_ROOT:-$HOME/.cache/mipstarre-dev}"
STORE="$CACHE_ROOT/site-components"
component_dir="$STORE/$NAME"
link="$component_dir/latest"

if [ ! -e "$link" ] && [ ! -L "$link" ]; then
  echo "warning: no component named '$NAME' has been published (looked for $link)" >&2
  exit 0
fi

if [ ! -L "$link" ]; then
  # A plain file or directory where the pointer belongs means the store was
  # edited by hand. Refusing loudly beats deploying an unknown version.
  echo "$prog: $link exists but is not a symlink — component store is corrupt" >&2
  echo "$prog: expected a symlink to a <timestamp> directory under $component_dir" >&2
  exit 1
fi

target="$(readlink "$link")"
case "$target" in
  /*) resolved="$target" ;;
  *)  resolved="$component_dir/$target" ;;
esac

if [ ! -d "$resolved" ]; then
  echo "warning: component '$NAME' has a dangling 'latest' symlink -> $target" >&2
  exit 0
fi

mkdir -p "$DEST"
# cp -R "$src/." copies the payload contents, dotfiles included, without
# nesting the version directory inside DEST (the unzip step it replaces
# behaved the same way).
cp -R "$resolved/." "$DEST/"

version="$(basename "$resolved")"
echo "==> ${NAME}: version ${version} -> ${DEST}"
if [ -f "$component_dir/$version.stamp" ]; then
  sed 's/^/    /' "$component_dir/$version.stamp"
fi
