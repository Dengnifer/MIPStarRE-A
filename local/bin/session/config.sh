#!/usr/bin/env bash
# Sourced by every session/service script: turns `local/project.json` into the
# environment.  Exports KIT_* (see scripts/project_config.py) plus the three
# MIPSTARRE_* variables the inherited tools already read.
#
#   . "$(dirname "$0")/config.sh"      # from local/bin/session/
#   . "$REPO/local/bin/session/config.sh"
#
# The configuration is authoritative: it overwrites MIPSTARRE_CACHE_ROOT and
# friends so that sourcing project B's config after project A's cannot leave A's
# cache behind.  Export afterwards if you really want something else.
# Reads only; creates no directory and no file.
#
# One escape hatch, and only one: a caller that sets KIT_CONFIG_SOURCED=1 says
# "the environment is already prepared, do not read local/project.json".  That is
# how a test (or an operator) drives these tools against a temporary tree without
# the real cache root coming back.  This file never sets or exports the flag
# itself -- an exported flag would travel into a child process of another project
# and re-create exactly the bleed the paragraph above prevents.
#
# Names outside spec 2.1 are left untouched, so the per-run knobs of the session
# tools (KIT_DRY_RUN, KIT_SAY, KIT_KEY_HOME_<KEY>, KIT_EXEC_*, ...) survive.

if [ -n "${KIT_CONFIG_SOURCED:-}" ]; then
  # Already prepared by the caller: keep every KIT_* and MIPSTARRE_* value as it is.
  return 0 2>/dev/null || exit 0
fi

# Repository root from this file's own location, following symlinks by hand
# (readlink -f is not everywhere, and $0 is the caller's script, not ours).
kit__config_self="${BASH_SOURCE[0]:-$0}"
while [ -L "$kit__config_self" ]; do
  kit__config_link="$(readlink "$kit__config_self")"
  case "$kit__config_link" in
    /*) kit__config_self="$kit__config_link" ;;
    *)  kit__config_self="$(dirname "$kit__config_self")/$kit__config_link" ;;
  esac
done
# local/bin/session/config.sh -> three levels up is the repository root.
kit__config_dir="$(cd "$(dirname "$kit__config_self")" && pwd -P)"
KIT_REPO_ROOT="$(cd "$kit__config_dir/../../.." && pwd -P)"
export KIT_REPO_ROOT

kit__config_py="$KIT_REPO_ROOT/scripts/project_config.py"
if [ ! -f "$kit__config_py" ]; then
  echo "config.sh: $kit__config_py is missing -- is $KIT_REPO_ROOT the repository root?" >&2
  unset kit__config_self kit__config_link kit__config_dir kit__config_py
  return 1 2>/dev/null || exit 1
fi

kit__config_shell="$(python3 "$kit__config_py" --root "$KIT_REPO_ROOT" shell)" || {
  echo "config.sh: could not read local/project.json (see the error above)" >&2
  unset kit__config_self kit__config_link kit__config_dir kit__config_py kit__config_shell
  return 1 2>/dev/null || exit 1
}
eval "$kit__config_shell"

# The inherited tools read these three names; keep them in step with the config.
export MIPSTARRE_CACHE_ROOT="${KIT_CACHE_ROOT:-}"
MIPSTARRE_FULL_BUILD_LOCK="$(python3 "$kit__config_py" --root "$KIT_REPO_ROOT" get paths.full_build_lock)"
export MIPSTARRE_FULL_BUILD_LOCK
# Before bootstrap the slug is the OWNER/REPO placeholder: leave the variable
# unset so gh_common.py falls back to the git remote instead of a fake repo.
case "${KIT_GITHUB_SLUG:-}" in
  ""|OWNER/*) unset MIPSTARRE_GITHUB_REPO ;;
  *) export MIPSTARRE_GITHUB_REPO="$KIT_GITHUB_SLUG" ;;
esac

unset kit__config_self kit__config_link kit__config_dir kit__config_py kit__config_shell
