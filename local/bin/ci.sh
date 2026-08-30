#!/usr/bin/env bash
#
# usage: local/bin/ci.sh <pr-id> [options]
#
#   Local replacement for .github/workflows/pr-ci.yml.  Runs the same eight
#   jobs (build, blueprint-render, paper-gaps, blueprint-sync, file-length,
#   proof-debt, proof-evasion, statement-origin) against the worktree of the
#   PR's branch, with the same per-area change gating, and records a per-step
#   result manifest that local/bin/review.sh and local/bin/autofix.sh consume.
#
#   <pr-id>            PR id: 7, 0007, 0007-slug, or a prs/ directory name.
#
#   --worktree PATH    Use PATH as the branch worktree instead of resolving it
#                      from `git worktree list` / .worktrees/<branch>.
#   --base REF         Override the base branch from the PR record (default:
#                      the record's `base`, else main).
#   --only STEP        Run only STEP (repeatable).  Gating still applies unless
#                      --force-all is given.  Makes the run PARTIAL.
#   --force-all        Ignore change gating; run every step.
#   --skip-build       Record the build step as skipped (operator override for
#                      a machine that must not compile right now).  Makes the
#                      run PARTIAL.
#   --dry-run          Resolve, gate and print the plan; run nothing, write
#                      nothing.
#   -h, --help         This message.
#
# Outputs
#   prs/<pr-dir>/ci/<head_sha>.json        per-step manifest (committed)
#   ~/.cache/mipstarre-dev/ci-logs/<id>/<sha>/<step>.log    step logs (runtime)
#   prs/<pr-dir>/pr.md                     frontmatter ci_status + head_sha
#   results/telemetry/builds.jsonl         one ci-build line when build ran
#
#   A PARTIAL run (--only / --skip-build) writes <head_sha>.partial.json
#   instead and never touches pr.md: a debugging run must not be able to hand
#   the review or merge gate a verdict it did not earn.
#
# Exit status
#   0  every gating step passed or was legitimately skipped
#   1  at least one gating step failed or could not run
#   2  the run could not start (bad id, missing worktree, unresolvable base)
#
# Environment
#   MIPSTARRE_CACHE_ROOT            default ~/.cache/mipstarre-dev
#   MIPSTARRE_FULL_BUILD_LOCK       default $CACHE_ROOT/.full-build-lock
#                                   (must equal cache-warmer.sh/warm-worktree.sh:
#                                   one path, one mutex)
#   MIPSTARRE_CI_BUILD_LOCK_WAIT_S  default 14400 (4h) wait for the build lock
#   MIPSTARRE_FULL_BUILD_LOCK_STALE_S default 10800 (3h) — applies ONLY to a
#                                   lock whose owner stamp is unreadable; a
#                                   lock with a live owner pid is never broken
#   MIPSTARRE_CI_REQUIRE_WARMER=1   fail the build step if warm-worktree.sh is
#                                   missing instead of doing a cold build
#   MIPSTARRE_CI_ALLOW_COLD_FETCH=1 let the build step materialise .lake/packages
#                                   itself instead of demanding worktree-setup.sh
#
# There is deliberately no LOCAL_CI_ENABLED kill switch: a disabled CI would
# hand the merge gate a green light it never earned.  See local/protocols/ci.md.

# shellcheck disable=SC2329  # step bodies and the trap handler run indirectly

set -euo pipefail

# ---------------------------------------------------------------------------
# Constants
# ---------------------------------------------------------------------------

SCRIPT_PATH="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)/$(basename "${BASH_SOURCE[0]}")"
SCRIPT_DIR="$(dirname "$SCRIPT_PATH")"

STEP_NAMES="build blueprint-render paper-gaps blueprint-sync file-length proof-debt proof-evasion statement-origin"

# Step exit codes with a meaning beyond "the command failed".
EXIT_TOOL_MISSING=91

CACHE_ROOT="${MIPSTARRE_CACHE_ROOT:-$HOME/.cache/mipstarre-dev}"
FULL_BUILD_LOCK="${MIPSTARRE_FULL_BUILD_LOCK:-$CACHE_ROOT/.full-build-lock}"
BUILD_LOCK_WAIT_S="${MIPSTARRE_CI_BUILD_LOCK_WAIT_S:-14400}"
BUILD_LOCK_STALE_S="${MIPSTARRE_FULL_BUILD_LOCK_STALE_S:-10800}"

# ---------------------------------------------------------------------------
# Utilities
# ---------------------------------------------------------------------------

info() { printf 'ci.sh: %s\n' "$*"; }
warn() { printf 'ci.sh: warning: %s\n' "$*" >&2; }

die() {
  printf 'ci.sh: error: %s\n' "$*" >&2
  exit 2
}

iso_now() { date +%Y-%m-%dT%H:%M:%S%z; }
epoch_now() { date +%s; }

# Git hooks and Lake disagree about GIT_DIR: a lake invocation that inherits
# the hook's git environment resolves nested package repositories against the
# wrong repo.  Same subshell trick as .githooks/pre-push:19-24.
run_outside_git_env() (
  for _name in $(git rev-parse --local-env-vars); do
    unset "$_name" || true
  done
  "$@"
)

# Locks are advisory mkdir-based lease directories, matching the hot-main
# writer lease convention in local/protocols/build-cache.md.
HELD_LOCKS=""

lock_age_s() {
  # $1 = lock dir.  Prints the age in seconds of its owner stamp, or a huge
  # number when the stamp is unreadable (treat as stale).
  local _stamp="$1/owner"
  if [ ! -f "$_stamp" ]; then
    printf '%s\n' 999999999
    return 0
  fi
  local _mtime
  _mtime="$(stat -f %m "$_stamp" 2>/dev/null || stat -c %Y "$_stamp" 2>/dev/null || echo 0)"
  printf '%s\n' "$(( $(epoch_now) - _mtime ))"
}

lock_owner_alive() {
  local _stamp="$1/owner"
  [ -f "$_stamp" ] || return 1
  local _pid
  _pid="$(head -n 1 "$_stamp" 2>/dev/null || true)"
  case "$_pid" in
    ''|*[!0-9]*) return 1 ;;
  esac
  kill -0 "$_pid" 2>/dev/null
}

# acquire_lock <dir> <wait_seconds> <stale_seconds> <tag>
# Returns 0 on success, 1 on timeout.  A lock whose owner process is ALIVE is
# NEVER broken, regardless of age: the parent workflow exempts main-branch
# (cache-seeding) runs from cancellation, and the local analog is that a
# running full build is always allowed to finish (the initial cold build took
# ~7 h; see results/telemetry/builds.jsonl).  The stale threshold applies only
# when the owner stamp is unreadable, so an interrupted mkdir cannot wedge the
# machine forever.
acquire_lock() {
  local _dir="$1" _wait="$2" _stale="$3" _tag="$4"
  local _waited=0
  mkdir -p "$(dirname "$_dir")"
  while ! mkdir "$_dir" 2>/dev/null; do
    if lock_owner_alive "$_dir"; then
      : # live owner: wait below, never break
    elif [ -f "$_dir/owner" ] || [ -f "$_dir/info" ]; then
      warn "breaking stale lock $_dir (owner process is dead)"
      rm -rf "$_dir"
      continue
    elif [ "$(lock_age_s "$_dir")" -gt "$_stale" ]; then
      warn "breaking stale lock $_dir (no owner stamp, older than ${_stale}s)"
      rm -rf "$_dir"
      continue
    fi
    if [ "$_waited" -ge "$_wait" ]; then
      return 1
    fi
    if [ "$_waited" -eq 0 ]; then
      info "waiting for lock $_dir (held by pid $(head -n 1 "$_dir/owner" 2>/dev/null || echo '?'))"
    fi
    sleep 5
    _waited=$(( _waited + 5 ))
  done
  printf '%s\n%s\n%s\n' "$$" "$(iso_now)" "$_tag" > "$_dir/owner"
  HELD_LOCKS="$HELD_LOCKS $_dir"
  return 0
}

release_lock() {
  local _dir="$1" _kept="" _held
  for _held in $HELD_LOCKS; do
    if [ "$_held" = "$_dir" ]; then
      rm -rf "$_held"
    else
      _kept="$_kept $_held"
    fi
  done
  HELD_LOCKS="$_kept"
}

RUN_TMP=""
cleanup() {
  local _lock
  for _lock in $HELD_LOCKS; do
    rm -rf "$_lock" 2>/dev/null || true
  done
  if [ -n "$RUN_TMP" ] && [ -d "$RUN_TMP" ]; then
    rm -rf "$RUN_TMP"
  fi
}
trap cleanup EXIT INT TERM

# ---------------------------------------------------------------------------
# Embedded Python helper (stdlib only): manifest assembly, atomic frontmatter
# rewriting, telemetry append.
# ---------------------------------------------------------------------------

write_helper() {
  cat > "$1" <<'PYHELPER'
#!/usr/bin/env python3
"""Manifest, frontmatter and telemetry helper for local/bin/ci.sh.

Three subcommands, all writing atomically (tempfile in the destination
directory + os.replace) so a crashed or killed CI run never leaves a
half-written manifest or a truncated PR record behind:

  manifest        assemble prs/<id>/ci/<head_sha>.json from a step TSV
  frontmatter     read or set one scalar key in a markdown YAML frontmatter
  telemetry       append one JSON line to results/telemetry/*.jsonl
"""

from __future__ import annotations

import argparse
import json
import os
import sys
import tempfile
from pathlib import Path
from typing import Sequence

FENCE = "---"


# ---------------------------------------------------------------------------
# Atomic write
# ---------------------------------------------------------------------------


def atomic_write(path: Path, text: str) -> None:
    """Write *text* to *path* via a same-directory tempfile and os.replace."""
    path.parent.mkdir(parents=True, exist_ok=True)
    handle, tmp_name = tempfile.mkstemp(
        dir=str(path.parent), prefix=path.name + ".", suffix=".tmp"
    )
    try:
        with os.fdopen(handle, "w", encoding="utf-8") as stream:
            stream.write(text)
            stream.flush()
            os.fsync(stream.fileno())
        os.replace(tmp_name, path)
    except BaseException:
        try:
            os.unlink(tmp_name)
        except OSError:
            pass
        raise


# ---------------------------------------------------------------------------
# Frontmatter
# ---------------------------------------------------------------------------


def split_frontmatter(text: str):
    """Return (opening, body_lines, rest) or None when there is no frontmatter."""
    lines = text.splitlines(keepends=True)
    if not lines or lines[0].strip() != FENCE:
        return None
    for index in range(1, len(lines)):
        if lines[index].strip() == FENCE:
            return lines[:1], lines[1:index], lines[index:]
    return None


def frontmatter_get(path: Path, key: str) -> str | None:
    split = split_frontmatter(path.read_text(encoding="utf-8"))
    if split is None:
        return None
    _, body, _ = split
    prefix = key + ":"
    for line in body:
        if line.startswith(prefix):
            value = line[len(prefix):].strip()
            if len(value) >= 2 and value[0] == value[-1] and value[0] in "'\"":
                value = value[1:-1]
            return value
    return None


def frontmatter_set(path: Path, pairs: Sequence[tuple[str, str]]) -> None:
    text = path.read_text(encoding="utf-8")
    split = split_frontmatter(text)
    if split is None:
        raise SystemExit(f"{path}: no YAML frontmatter to update")
    opening, body, rest = split
    for key, value in pairs:
        prefix = key + ":"
        replaced = False
        for index, line in enumerate(body):
            if line.startswith(prefix):
                body[index] = f"{key}: {value}\n"
                replaced = True
                break
        if not replaced:
            body.append(f"{key}: {value}\n")
    atomic_write(path, "".join(opening) + "".join(body) + "".join(rest))


# ---------------------------------------------------------------------------
# Manifest
# ---------------------------------------------------------------------------


def read_steps(path: Path) -> list[dict]:
    """Parse the tab-separated step records ci.sh appends as it runs."""
    steps: list[dict] = []
    if not path.exists():
        return steps
    for line in path.read_text(encoding="utf-8").splitlines():
        if not line.strip():
            continue
        fields = line.split("\t")
        while len(fields) < 6:
            fields.append("")
        step, outcome, seconds, log_path, blocking, note = fields[:6]
        steps.append(
            {
                "step": step,
                "outcome": outcome,
                "seconds": int(seconds or 0),
                "log_path": log_path,
                "blocking": blocking == "1",
                "note": note,
            }
        )
    return steps


def read_lines(path: Path | None) -> list[str]:
    if path is None or not path.exists():
        return []
    return [line for line in path.read_text(encoding="utf-8").splitlines() if line.strip()]


def build_manifest(args: argparse.Namespace) -> dict:
    areas = {}
    for item in args.area or []:
        name, _, value = item.partition("=")
        areas[name] = value == "1"
    steps = read_steps(Path(args.steps_tsv))
    return {
        "schema": 1,
        "generator": "local/bin/ci.sh",
        "replaces": ".github/workflows/pr-ci.yml",
        "pr": args.pr,
        "pr_dir": args.pr_dir,
        "branch": args.branch,
        "base": args.base,
        "base_ref": args.base_ref,
        "merge_base": args.merge_base,
        "head_sha": args.head_sha,
        "worktree": args.worktree,
        "started": args.started,
        "finished": args.finished,
        "seconds": args.seconds,
        "conclusion": args.conclusion,
        "partial": args.partial == 1,
        "areas": areas,
        "changed_files": read_lines(Path(args.changed_files_file) if args.changed_files_file else None),
        "warnings": read_lines(Path(args.warnings_file) if args.warnings_file else None),
        "steps": steps,
    }


# ---------------------------------------------------------------------------
# Subcommands
# ---------------------------------------------------------------------------


def cmd_manifest(args: argparse.Namespace) -> int:
    out = Path(args.out)
    atomic_write(out, json.dumps(build_manifest(args), indent=2, ensure_ascii=False) + "\n")
    print(out)
    return 0


def cmd_frontmatter(args: argparse.Namespace) -> int:
    path = Path(args.file)
    if not path.exists():
        print(f"{path}: no such file", file=sys.stderr)
        return 3
    if args.set:
        pairs = []
        for item in args.set:
            key, _, value = item.partition("=")
            if not key:
                print(f"bad --set argument: {item!r}", file=sys.stderr)
                return 3
            pairs.append((key, value))
        frontmatter_set(path, pairs)
        return 0
    if args.get:
        value = frontmatter_get(path, args.get)
        if value is None:
            return 1
        print(value)
        return 0
    print("frontmatter: pass --get or --set", file=sys.stderr)
    return 3


def cmd_telemetry(args: argparse.Namespace) -> int:
    record = {}
    for item in args.field or []:
        key, _, value = item.partition("=")
        record[key] = value
    for key in args.int_field or []:
        if key in record:
            try:
                record[key] = int(record[key])
            except ValueError:
                pass
    path = Path(args.out)
    path.parent.mkdir(parents=True, exist_ok=True)
    # One line, one write: concurrent appenders never interleave a short line.
    with path.open("a", encoding="utf-8") as stream:
        stream.write(json.dumps(record, ensure_ascii=False) + "\n")
    return 0


def build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(description=__doc__)
    subparsers = parser.add_subparsers(dest="command", required=True)

    manifest = subparsers.add_parser("manifest", help="assemble the per-SHA CI manifest")
    manifest.add_argument("--out", required=True)
    manifest.add_argument("--steps-tsv", required=True)
    manifest.add_argument("--pr", required=True)
    manifest.add_argument("--pr-dir", required=True)
    manifest.add_argument("--branch", required=True)
    manifest.add_argument("--base", required=True)
    manifest.add_argument("--base-ref", required=True)
    manifest.add_argument("--merge-base", required=True)
    manifest.add_argument("--head-sha", required=True)
    manifest.add_argument("--worktree", required=True)
    manifest.add_argument("--started", required=True)
    manifest.add_argument("--finished", required=True)
    manifest.add_argument("--seconds", type=int, required=True)
    manifest.add_argument("--conclusion", required=True)
    manifest.add_argument("--area", action="append", default=[], metavar="NAME=0|1")
    manifest.add_argument("--changed-files-file")
    manifest.add_argument("--warnings-file")
    manifest.add_argument("--partial", type=int, default=0, choices=(0, 1))
    manifest.set_defaults(func=cmd_manifest)

    frontmatter = subparsers.add_parser("frontmatter", help="read or set frontmatter keys")
    frontmatter.add_argument("--file", required=True)
    frontmatter.add_argument("--get")
    frontmatter.add_argument("--set", action="append", metavar="KEY=VALUE")
    frontmatter.set_defaults(func=cmd_frontmatter)

    telemetry = subparsers.add_parser("telemetry", help="append one JSONL record")
    telemetry.add_argument("--out", required=True)
    telemetry.add_argument("--field", action="append", default=[], metavar="KEY=VALUE")
    telemetry.add_argument("--int-field", action="append", default=[], metavar="KEY")
    telemetry.set_defaults(func=cmd_telemetry)

    return parser


def main(argv: Sequence[str] | None = None) -> int:
    args = build_parser().parse_args(argv)
    return args.func(args)


if __name__ == "__main__":
    sys.exit(main())
PYHELPER
}

# ---------------------------------------------------------------------------
# Argument parsing
# ---------------------------------------------------------------------------

usage() {
  sed -n '2,/^$/p' "$SCRIPT_PATH" | sed 's/^# \{0,1\}//'
}

PR_ARG=""
WORKTREE_OVERRIDE=""
BASE_OVERRIDE=""
ONLY_STEPS=""
FORCE_ALL=0
SKIP_BUILD=0
DRY_RUN=0

while [ $# -gt 0 ]; do
  case "$1" in
    -h|--help) usage; exit 0 ;;
    --worktree) [ $# -ge 2 ] || die "--worktree needs a path"; WORKTREE_OVERRIDE="$2"; shift 2 ;;
    --base) [ $# -ge 2 ] || die "--base needs a ref"; BASE_OVERRIDE="$2"; shift 2 ;;
    --only) [ $# -ge 2 ] || die "--only needs a step name"; ONLY_STEPS="$ONLY_STEPS $2"; shift 2 ;;
    --force-all) FORCE_ALL=1; shift ;;
    --skip-build) SKIP_BUILD=1; shift ;;
    --dry-run) DRY_RUN=1; shift ;;
    --) shift; break ;;
    -*) die "unknown option: $1 (try --help)" ;;
    *)
      [ -z "$PR_ARG" ] || die "unexpected extra argument: $1"
      PR_ARG="$1"; shift ;;
  esac
done

[ -n "$PR_ARG" ] || { usage >&2; die "a PR id is required"; }

for _only in $ONLY_STEPS; do
  case " $STEP_NAMES " in
    *" $_only "*) ;;
    *) die "--only: unknown step '$_only' (known: $STEP_NAMES)" ;;
  esac
done

# ---------------------------------------------------------------------------
# Resolution: repository, PR record, worktree, base
# ---------------------------------------------------------------------------

REPO_ROOT="$(cd "$SCRIPT_DIR/../.." && pwd)"
# The registry (issues/, prs/, results/telemetry/) is single-instance and
# lives in the PRIMARY checkout. When this script is invoked from a linked
# worktree copy, re-point the root at the primary (same resolution as
# cache-warmer.sh resolve_primary_repo; EVOLUTION.md 2026-08-30).
_common="$(git -C "$REPO_ROOT" rev-parse --path-format=absolute --git-common-dir 2>/dev/null || true)"
case "$_common" in
  */.git) REPO_ROOT="$(dirname "$_common")" ;;
esac
unset _common

[ -d "$REPO_ROOT/.git" ] || [ -f "$REPO_ROOT/.git" ] || die "$REPO_ROOT is not a git repository"

# Invariant 9 (bracket-free naming): the parent automation broke on ] in ids
# and branch names (docs/CONTRIBUTING.md:122-124).  Refuse them at the door.
case "$PR_ARG" in
  *'['*|*']'*|*' '*|*'*'*) die "PR id contains a forbidden character (brackets/space/glob): $PR_ARG" ;;
esac

PR_DIR=""
if [ -d "$REPO_ROOT/prs/$PR_ARG" ]; then
  PR_DIR="$REPO_ROOT/prs/$PR_ARG"
else
  case "$PR_ARG" in
    ''|*[!0-9]*) die "PR id must be numeric or an existing prs/ directory name: $PR_ARG" ;;
  esac
  # Strip leading zeros before padding: bash printf reads 0009 as octal.
  _num="$PR_ARG"
  while [ "${#_num}" -gt 1 ] && [ "${_num#0}" != "$_num" ]; do
    _num="${_num#0}"
  done
  PR_ID_PADDED="$(printf '%04d' "$_num")"
  if [ -d "$REPO_ROOT/prs/$PR_ID_PADDED" ]; then
    PR_DIR="$REPO_ROOT/prs/$PR_ID_PADDED"
  else
    for _candidate in "$REPO_ROOT/prs/$PR_ID_PADDED"-*; do
      [ -d "$_candidate" ] || continue
      [ -z "$PR_DIR" ] || die "PR id $PR_ID_PADDED matches more than one directory under prs/"
      PR_DIR="$_candidate"
    done
  fi
fi

[ -n "$PR_DIR" ] || die "no PR record found for '$PR_ARG' under $REPO_ROOT/prs/ (create it with the PR lifecycle scripts first)"

PR_MD="$PR_DIR/pr.md"
[ -f "$PR_MD" ] || die "$PR_MD is missing; a PR record without pr.md has no branch to test"

PR_DIR_NAME="$(basename "$PR_DIR")"
PR_ID="${PR_DIR_NAME%%-*}"

RUN_TMP="$(mktemp -d "${TMPDIR:-/tmp}/mipstarre-ci.XXXXXX")"
PY_HELPER="$RUN_TMP/ci_helper.py"
write_helper "$PY_HELPER"

command -v python3 >/dev/null 2>&1 || die "python3 is not on PATH; every audit job and the manifest writer need it"

helper() { python3 "$PY_HELPER" "$@"; }

fm_get() {
  # Prints the value of frontmatter key $1, or nothing when absent.
  helper frontmatter --file "$PR_MD" --get "$1" 2>/dev/null || true
}

BRANCH="$(fm_get branch)"
[ -n "$BRANCH" ] || die "$PR_MD has no 'branch' key in its frontmatter"
case "$BRANCH" in
  *'['*|*']'*|*' '*) die "branch name contains a forbidden character (invariant 9): $BRANCH" ;;
esac

BASE="$(fm_get base)"
[ -n "$BASE" ] || BASE="main"
[ -z "$BASE_OVERRIDE" ] || BASE="$BASE_OVERRIDE"

# Worktree: prefer git's own registry, fall back to the .worktrees/ convention.
WORKTREE=""
if [ -n "$WORKTREE_OVERRIDE" ]; then
  [ -d "$WORKTREE_OVERRIDE" ] || die "--worktree $WORKTREE_OVERRIDE does not exist"
  WORKTREE="$(cd "$WORKTREE_OVERRIDE" && pwd)"
else
  _current=""
  while IFS= read -r _line; do
    case "$_line" in
      "worktree "*) _current="${_line#worktree }" ;;
      "branch refs/heads/"*)
        if [ "${_line#branch refs/heads/}" = "$BRANCH" ]; then
          WORKTREE="$_current"
        fi
        ;;
    esac
  done < <(git -C "$REPO_ROOT" worktree list --porcelain 2>/dev/null || true)
  if [ -z "$WORKTREE" ]; then
    _fallback="$REPO_ROOT/.worktrees/$(printf '%s' "$BRANCH" | tr '/' '-')"
    if [ -d "$_fallback" ]; then
      WORKTREE="$_fallback"
    fi
  fi
fi

[ -n "$WORKTREE" ] || die "no worktree found for branch '$BRANCH'; create it (git worktree add .worktrees/$(printf '%s' "$BRANCH" | tr '/' '-') $BRANCH) or pass --worktree"
[ -d "$WORKTREE" ] || die "resolved worktree $WORKTREE does not exist"

_wt_branch="$(git -C "$WORKTREE" symbolic-ref --quiet --short HEAD 2>/dev/null || true)"
if [ -n "$_wt_branch" ] && [ "$_wt_branch" != "$BRANCH" ]; then
  warn "worktree $WORKTREE is on '$_wt_branch' but the PR record says '$BRANCH'"
fi

HEAD_SHA="$(git -C "$WORKTREE" rev-parse HEAD 2>/dev/null || true)"
[ -n "$HEAD_SHA" ] || die "$WORKTREE has no commits to test"

# Invariant 8: origin/main must resolve.  The diff-based audits and the change
# gating below silently self-disable without a base, which is exactly the
# "checks stopped running and nobody noticed" failure the parent repo hit.
BASE_REF=""
for _cand in "origin/$BASE" "$BASE"; do
  if git -C "$WORKTREE" rev-parse --verify --quiet "$_cand^{commit}" >/dev/null 2>&1; then
    BASE_REF="$_cand"
    break
  fi
done
[ -n "$BASE_REF" ] || die "neither origin/$BASE nor $BASE resolves in $WORKTREE; local convention is a main branch plus a refs/remotes/origin/main alias maintained by pr_merge.py (DESIGN.md invariant 8)"

MERGE_BASE="$(git -C "$WORKTREE" merge-base "$BASE_REF" "$HEAD_SHA" 2>/dev/null || true)"
[ -n "$MERGE_BASE" ] || die "no merge base between $BASE_REF and $HEAD_SHA"

# ---------------------------------------------------------------------------
# Change detection and per-area gating
#
# These globs MUST stay in lockstep with the dorny/paths-filter block in
# .github/workflows/pr-ci.yml:83-113 and with the trees the audit scripts
# scan.  The parent repo patched those filters twice after checks silently
# never ran; see local/protocols/ci.md, "Gating globs".
# ---------------------------------------------------------------------------

CHANGED_FILES="$RUN_TMP/changed-files.txt"
# --no-renames: report both the old and the new path so a rename out of a
# gated tree still trips that tree's filter.  Deletions count too.
git -C "$WORKTREE" diff --name-only --no-renames "$MERGE_BASE" "$HEAD_SHA" > "$CHANGED_FILES"

A_lean=0
A_mip_lean=0
A_ldt_lean=0
A_blueprint=0
A_blueprint_src=0
A_tex_chapter=0
A_paper_gaps=0
A_scripts=0
A_comparator=0
A_workflow=0

match_globs() {
  # $1 = path, $2.. = fnmatch patterns ('*' spans '/', as in minimatch '**')
  local _path="$1" _pattern
  shift
  for _pattern in "$@"; do
    # shellcheck disable=SC2254  # unquoted on purpose: $_pattern IS the glob
    case "$_path" in
      $_pattern) return 0 ;;
    esac
  done
  return 1
}

while IFS= read -r _file; do
  [ -n "$_file" ] || continue
  if match_globs "$_file" '*.lean' 'lakefile.*' 'lean-toolchain' 'lake-manifest.json'; then A_lean=1; fi
  if match_globs "$_file" 'MIPStarRE/*.lean'; then A_mip_lean=1; fi
  if match_globs "$_file" 'MIPStarRE/LDT/*.lean'; then A_ldt_lean=1; fi
  if match_globs "$_file" 'blueprint/*'; then A_blueprint=1; fi
  if match_globs "$_file" 'blueprint/src/*'; then A_blueprint_src=1; fi
  if match_globs "$_file" 'blueprint/src/chapter/*.tex'; then A_tex_chapter=1; fi
  if match_globs "$_file" 'docs/paper-gaps/*' 'texra-blueprint.toml' 'MIPStarRE/*.lean' 'blueprint/src/*' 'docs/*.md'; then A_paper_gaps=1; fi
  if match_globs "$_file" 'scripts/*'; then A_scripts=1; fi
  if match_globs "$_file" 'scripts/comparator/*'; then A_comparator=1; fi
  # 'workflow' is the local translation of "the CI definition itself changed":
  # the frozen reference workflow, this driver, or its protocol.
  if match_globs "$_file" '.github/workflows/pr-ci.yml' 'local/bin/ci.sh' 'local/protocols/ci.md'; then A_workflow=1; fi
done < "$CHANGED_FILES"

step_gate() {
  case "$1" in
    build)            [ "$A_lean" = 1 ] || [ "$A_comparator" = 1 ] || [ "$A_workflow" = 1 ] ;;
    blueprint-render) [ "$A_blueprint_src" = 1 ] || [ "$A_workflow" = 1 ] ;;
    paper-gaps)       [ "$A_paper_gaps" = 1 ] || [ "$A_workflow" = 1 ] ;;
    blueprint-sync)   [ "$A_lean" = 1 ] || [ "$A_blueprint" = 1 ] || [ "$A_scripts" = 1 ] || [ "$A_workflow" = 1 ] ;;
    file-length)      [ "$A_mip_lean" = 1 ] || [ "$A_scripts" = 1 ] || [ "$A_workflow" = 1 ] ;;
    proof-debt)       [ "$A_mip_lean" = 1 ] || [ "$A_tex_chapter" = 1 ] || [ "$A_scripts" = 1 ] || [ "$A_workflow" = 1 ] ;;
    proof-evasion)    [ "$A_mip_lean" = 1 ] || [ "$A_scripts" = 1 ] || [ "$A_workflow" = 1 ] ;;
    statement-origin) [ "$A_ldt_lean" = 1 ] || [ "$A_scripts" = 1 ] || [ "$A_workflow" = 1 ] ;;
    *) return 1 ;;
  esac
}

step_gate_paths() {
  case "$1" in
    build)            printf 'lean|comparator|workflow\n' ;;
    blueprint-render) printf 'blueprint_src|workflow\n' ;;
    paper-gaps)       printf 'paper_gaps|workflow\n' ;;
    blueprint-sync)   printf 'lean|blueprint|scripts|workflow\n' ;;
    file-length)      printf 'mip_lean|scripts|workflow\n' ;;
    proof-debt)       printf 'mip_lean|tex_chapter|scripts|workflow\n' ;;
    proof-evasion)    printf 'mip_lean|scripts|workflow\n' ;;
    statement-origin) printf 'ldt_lean|scripts|workflow\n' ;;
  esac
}

# ---------------------------------------------------------------------------
# Run bookkeeping
# ---------------------------------------------------------------------------

LOG_DIR="$CACHE_ROOT/ci-logs/$PR_ID/$HEAD_SHA"

# A run that was told to skip jobs cannot produce a merge-gate verdict.  It
# writes a clearly-named side manifest and never touches pr.md, so a debugging
# --only run can never leave the review gate a green ci_status it did not earn.
PARTIAL=0
if [ -n "$ONLY_STEPS" ] || [ "$SKIP_BUILD" = 1 ]; then
  PARTIAL=1
fi
if [ "$PARTIAL" = 1 ]; then
  MANIFEST="$PR_DIR/ci/$HEAD_SHA.partial.json"
else
  MANIFEST="$PR_DIR/ci/$HEAD_SHA.json"
fi
STEPS_TSV="$RUN_TMP/steps.tsv"
WARN_FILE="$RUN_TMP/warnings.txt"
: > "$STEPS_TSV"
: > "$WARN_FILE"

sanitize_field() {
  printf '%s' "$1" | tr '\t\n\r' '   ' | cut -c1-500
}

record_step() {
  # name outcome seconds log blocking note
  printf '%s\t%s\t%s\t%s\t%s\t%s\n' \
    "$1" "$2" "$3" "$4" "$5" "$(sanitize_field "${6:-}")" >> "$STEPS_TSV"
}

SHORT_SHA="$(git -C "$WORKTREE" rev-parse --short "$HEAD_SHA")"
info "PR $PR_ID  branch $BRANCH  head $SHORT_SHA  base $BASE_REF"
info "worktree $WORKTREE"
info "changed files: $(wc -l < "$CHANGED_FILES" | tr -d ' ')"
info "areas: lean=$A_lean mip_lean=$A_mip_lean ldt_lean=$A_ldt_lean blueprint=$A_blueprint blueprint_src=$A_blueprint_src tex_chapter=$A_tex_chapter paper_gaps=$A_paper_gaps scripts=$A_scripts comparator=$A_comparator workflow=$A_workflow"

if [ "$DRY_RUN" = 1 ]; then
  info "dry run: planned steps"
  for _step in $STEP_NAMES; do
    _plan="skip"
    if [ "$FORCE_ALL" = 1 ] || step_gate "$_step"; then _plan="run"; fi
    if [ -n "$ONLY_STEPS" ]; then
      case " $ONLY_STEPS " in
        *" $_step "*) ;;
        *) _plan="skip (--only)" ;;
      esac
    fi
    if [ "$_step" = build ] && [ "$SKIP_BUILD" = 1 ]; then _plan="skip (--skip-build)"; fi
    printf '  %-18s %s\n' "$_step" "$_plan"
  done
  info "manifest would be $MANIFEST"
  exit 0
fi

# Per-PR serialization.  A second run for the same PR is refused rather than
# cancelling the first: the parent workflow only cancels in-progress PR runs
# because the runner is disposable; locally a killed run leaves a half-built
# .lake/build and a half-held build lock behind (gotcha 5).
PR_LOCK="$CACHE_ROOT/locks/ci-$PR_ID.lock"
if ! acquire_lock "$PR_LOCK" 0 "$BUILD_LOCK_STALE_S" "ci.sh pr=$PR_ID sha=$HEAD_SHA"; then
  die "another ci.sh run for PR $PR_ID is in progress (lock $PR_LOCK, pid $(head -n 1 "$PR_LOCK/owner" 2>/dev/null || echo '?')); wait for it or break the lock by hand"
fi

mkdir -p "$LOG_DIR" "$PR_DIR/ci"

# Mark the record as running before anything can fail: a crashed run must never
# leave a stale `success` behind for the review gate to trust.
if [ "$PARTIAL" = 1 ]; then
  info "partial run (--only/--skip-build): pr.md ci_status will NOT be updated, and the manifest goes to $(basename "$MANIFEST")"
else
  helper frontmatter --file "$PR_MD" --set "ci_status=running" --set "head_sha=$HEAD_SHA"
fi

RUN_STARTED="$(iso_now)"
RUN_START_EPOCH="$(epoch_now)"

# ---------------------------------------------------------------------------
# Step bodies.  Each runs in a subshell with cwd = the branch worktree, stdout
# and stderr redirected to its log.  Exit 0 = pass, EXIT_TOOL_MISSING = the
# step could not run at all, anything else = a real failure.
# ---------------------------------------------------------------------------

note_warning() { printf '%s\n' "$*" >> "$WARN_FILE"; printf 'WARNING: %s\n' "$*"; }

require_tool() {
  # $1 = executable, $2 = how to install it
  if command -v "$1" >/dev/null 2>&1; then
    return 0
  fi
  printf 'ERROR: required tool %s is not on PATH.\n' "$1"
  printf 'Install it with: %s\n' "$2"
  exit "$EXIT_TOOL_MISSING"
}

step_build() {
  cd "$WORKTREE"

  # Warm .lake/build from the hot main snapshot before compiling.  The warmer
  # is the only writer of the shared snapshot; this worktree gets a private
  # copy-on-write clone (DESIGN.md invariant 1).
  if [ ! -d .lake/build ]; then
    if [ -x "$SCRIPT_DIR/warm-worktree.sh" ]; then
      echo "+ warm-worktree.sh $WORKTREE"
      if ! "$SCRIPT_DIR/warm-worktree.sh" "$WORKTREE"; then
        note_warning "warm-worktree.sh failed for $WORKTREE; falling back to a cold build"
      fi
    elif [ "${MIPSTARRE_CI_REQUIRE_WARMER:-}" = "1" ]; then
      printf 'ERROR: %s is missing and MIPSTARRE_CI_REQUIRE_WARMER=1.\n' "$SCRIPT_DIR/warm-worktree.sh"
      exit "$EXIT_TOOL_MISSING"
    else
      note_warning "local/bin/warm-worktree.sh not found; building $BRANCH from scratch (slow, but correct)"
    fi
  fi

  require_tool lake "install elan (https://github.com/leanprover/elan) and re-run"

  # Two-tier cache, do not conflate (gotcha 1): .lake/build holds this
  # project's oleans and is per-worktree; .lake/packages holds Mathlib and
  # friends.  When packages is a symlink it points at the shared hot-main
  # tree and must be treated as read-only: `lake exe cache get` writes there.
  if [ -L .lake/packages ]; then
    echo "+ .lake/packages is a shared symlink; skipping 'lake exe cache get' (read-only dependency tree)"
  elif [ -d .lake/packages ]; then
    echo "+ lake exe cache get"
    run_outside_git_env lake exe cache get
  elif [ "${MIPSTARRE_CI_ALLOW_COLD_FETCH:-}" = "1" ]; then
    note_warning "no .lake/packages in $WORKTREE; materialising dependencies inside CI (MIPSTARRE_CI_ALLOW_COLD_FETCH=1)"
    echo "+ lake exe cache get"
    run_outside_git_env lake exe cache get
  else
    printf 'ERROR: %s has no .lake/packages.\n' "$WORKTREE"
    printf 'Bootstrap the worktree first (local/bin/worktree-setup.sh), which also carries\n'
    printf 'the ProofWidgets prune workaround that only bites on package-free trees.\n'
    printf 'Override with MIPSTARRE_CI_ALLOW_COLD_FETCH=1 if you know the tree is clean.\n'
    exit "$EXIT_TOOL_MISSING"
  fi

  echo "+ lake build"
  run_outside_git_env lake build

  # pr-ci.yml:155-156
  echo "+ lake build MIPStarRE.LDT.Test.AxiomAudit"
  run_outside_git_env lake build MIPStarRE.LDT.Test.AxiomAudit

  # pr-ci.yml:158-159
  echo "+ scripts/comparator/check_challenge_drift.py"
  run_outside_git_env python3 scripts/comparator/check_challenge_drift.py --root .
}

step_blueprint_render() {
  cd "$WORKTREE"
  require_tool leanblueprint "pipx install leanblueprint && pipx inject --include-apps --force leanblueprint plastex"

  # pr-ci.yml:210-218.  The PDF pass is what catches undefined macros; it needs
  # a TeX installation the CI runner apt-installs and a laptop may not have.
  if command -v latexmk >/dev/null 2>&1 || command -v xelatex >/dev/null 2>&1; then
    echo "+ (cd blueprint && leanblueprint pdf)"
    ( cd blueprint && run_outside_git_env leanblueprint pdf )
    if [ ! -s blueprint/print/print.pdf ]; then
      echo "ERROR: leanblueprint pdf produced no output"
      exit 1
    fi
  else
    note_warning "no latexmk/xelatex on PATH; skipped 'leanblueprint pdf' (undefined-macro check did not run)"
  fi

  # pr-ci.yml:222-223: web.bbl is not committed and is regenerated from the
  # \cite keys in the blueprint sources.
  if command -v texra-blueprint >/dev/null 2>&1; then
    echo "+ texra-blueprint bbl"
    run_outside_git_env texra-blueprint bbl
  else
    note_warning "texra-blueprint not installed; skipped 'texra-blueprint bbl' (paper-gap cite keys may render unresolved)"
  fi

  # pr-ci.yml:225-243.  ^ERROR: is a hard failure; 'WARNING: File not found:'
  # is advisory.  Keep exit-code semantics, not annotation semantics.
  _web_log="$RUN_TMP/blueprint-web.txt"
  if command -v texra-blueprint >/dev/null 2>&1; then
    echo "+ (cd blueprint && texra-blueprint web)"
    ( cd blueprint && run_outside_git_env texra-blueprint web 2>&1 ) | tee "$_web_log"
  else
    echo "+ (cd blueprint && leanblueprint web)"
    ( cd blueprint && run_outside_git_env leanblueprint web 2>&1 ) | tee "$_web_log"
  fi

  if grep -q '^ERROR:' "$_web_log"; then
    echo "ERROR: blueprint has unresolved labels (see the ERROR lines above)"
    exit 1
  fi
  if grep -q 'WARNING: File not found:' "$_web_log"; then
    note_warning "blueprint has missing file references (see WARNING lines in the blueprint-render log)"
  fi
}

step_paper_gaps() {
  cd "$WORKTREE"
  require_tool texra-blueprint "pipx install 'git+https://github.com/LionSR/texra-blueprint@v0.3.8'"
  # pr-ci.yml:270-271
  echo "+ texra-blueprint --root . paper-gaps check"
  run_outside_git_env texra-blueprint --root . paper-gaps check
}

step_blueprint_sync() {
  cd "$WORKTREE"
  # pr-ci.yml:294-301
  echo "+ python3 -m unittest discover -s scripts/tests -p 'test_*.py'"
  run_outside_git_env python3 -m unittest discover -s scripts/tests -p 'test_*.py'

  echo "+ scripts/blueprint_lean_sync.py --update-lean-decls"
  run_outside_git_env python3 scripts/blueprint_lean_sync.py --root . --update-lean-decls

  echo "+ scripts/blueprint_lean_sync.py --ci"
  run_outside_git_env python3 scripts/blueprint_lean_sync.py --root . --ci

  # pr-ci.yml:303-317.  This job deliberately has NO Lean setup: on GitHub it
  # exhausted the runner disk repeatedly.  Locally the reason is the machine's
  # single full-build budget (invariant 7) — the axiom audit is reported, not
  # run, and a human runs it inside the build lock.
  echo "+ scripts/blueprint_axiom_audit_needed.py --base-ref $BASE_REF"
  _needed="$(run_outside_git_env python3 scripts/blueprint_axiom_audit_needed.py --base-ref "$BASE_REF" --head-ref "$HEAD_SHA")"
  if [ "$_needed" = "true" ]; then
    note_warning "blueprint axiom audit is required for this diff: run 'python3 scripts/blueprint_leanok_axioms.py --ci' in a Lean environment"
  else
    echo "No proof-level \\leanok axiom audit is required for this diff."
  fi
}

step_file_length() {
  cd "$WORKTREE"
  # pr-ci.yml:339-340
  echo "+ scripts/check_oversized_lean_files.py"
  run_outside_git_env python3 scripts/check_oversized_lean_files.py --root .
}

step_proof_debt() {
  cd "$WORKTREE"
  # pr-ci.yml:362-371
  echo "+ python3 -m unittest scripts/tests/test_audit_paper_facing_proof_debt.py"
  run_outside_git_env python3 -m unittest scripts/tests/test_audit_paper_facing_proof_debt.py

  echo "+ scripts/audit_paper_facing_proof_debt.py --ci"
  run_outside_git_env python3 scripts/audit_paper_facing_proof_debt.py --root . --ci
}

step_proof_evasion() {
  cd "$WORKTREE"
  # pr-ci.yml:407-412
  echo "+ proof-evasion regression tests"
  run_outside_git_env python3 -m unittest scripts/tests/test_check_duplicate_private_helpers.py
  run_outside_git_env python3 -m unittest scripts/tests/test_audit_conclusion_shaped_hypotheses.py
  run_outside_git_env python3 -m unittest scripts/tests/test_audit_lean_axiom_declarations.py
  run_outside_git_env python3 -m unittest scripts/tests/test_audit_unfaithful_markers.py

  # pr-ci.yml:414-430
  echo "+ scripts/audit_lean_axiom_declarations.py --ci"
  run_outside_git_env python3 scripts/audit_lean_axiom_declarations.py --root . --ci
  echo "+ scripts/audit_conclusion_shaped_hypotheses.py --ci"
  run_outside_git_env python3 scripts/audit_conclusion_shaped_hypotheses.py --root . --ci
  echo "+ scripts/audit_unfaithful_markers.py --ci"
  run_outside_git_env python3 scripts/audit_unfaithful_markers.py --root . --ci

  # pr-ci.yml:432-445: exit 1 from this one audit is advisory, anything else
  # is a real failure.  --github-annotations is dropped: ::warning lines are
  # inert outside Actions.
  echo "+ scripts/check_duplicate_private_helpers.py --ci (advisory)"
  set +e
  run_outside_git_env python3 scripts/check_duplicate_private_helpers.py --root . --ci
  _status=$?
  set -e
  if [ "$_status" -eq 1 ]; then
    note_warning "duplicate private-helper candidates were reported; this audit is advisory"
    _status=0
  fi
  if [ "$_status" -ne 0 ]; then
    exit "$_status"
  fi
}

step_statement_origin() {
  cd "$WORKTREE"
  # pr-ci.yml:466-471
  echo "+ scripts/check_statement_paper_origin.py"
  run_outside_git_env python3 scripts/check_statement_paper_origin.py --root .
}

run_step_body() {
  case "$1" in
    build) step_build ;;
    blueprint-render) step_blueprint_render ;;
    paper-gaps) step_paper_gaps ;;
    blueprint-sync) step_blueprint_sync ;;
    file-length) step_file_length ;;
    proof-debt) step_proof_debt ;;
    proof-evasion) step_proof_evasion ;;
    statement-origin) step_statement_origin ;;
    *) printf 'ERROR: no step body for %s\n' "$1"; return 2 ;;
  esac
}

# ---------------------------------------------------------------------------
# Dispatch
# ---------------------------------------------------------------------------

FAILED=0
ERRORED=0
BUILD_OUTCOME=""
BUILD_SECONDS=0

for STEP in $STEP_NAMES; do
  LOG="$LOG_DIR/$STEP.log"

  if [ -n "$ONLY_STEPS" ]; then
    case " $ONLY_STEPS " in
      *" $STEP "*) ;;
      *)
        record_step "$STEP" skipped 0 "$LOG" 1 "not selected by --only"
        continue
        ;;
    esac
  fi

  if [ "$FORCE_ALL" != 1 ] && ! step_gate "$STEP"; then
    record_step "$STEP" skipped 0 "$LOG" 1 "no changes under $(step_gate_paths "$STEP")"
    printf '  %-18s skipped\n' "$STEP"
    continue
  fi

  if [ "$STEP" = build ] && [ "$SKIP_BUILD" = 1 ]; then
    record_step "$STEP" skipped 0 "$LOG" 1 "operator passed --skip-build"
    printf '  %-18s skipped (--skip-build)\n' "$STEP"
    continue
  fi

  : > "$LOG"
  _step_start="$(epoch_now)"

  # Invariant 7: at most one full lake build machine-wide.  Only the build
  # step compiles; the audits are pure Python and take no lock.
  _locked=1
  if [ "$STEP" = build ]; then
    if acquire_lock "$FULL_BUILD_LOCK" "$BUILD_LOCK_WAIT_S" "$BUILD_LOCK_STALE_S" "ci.sh pr=$PR_ID sha=$HEAD_SHA"; then
      _locked=0
    else
      _locked=2
    fi
  else
    _locked=0
  fi

  if [ "$_locked" = 2 ]; then
    {
      printf 'ERROR: could not take the machine-wide full-build lock %s within %ss.\n' "$FULL_BUILD_LOCK" "$BUILD_LOCK_WAIT_S"
      printf 'Another full build (warmer or another worktree) is running; it is never killed.\n'
    } >> "$LOG"
    _rc="$EXIT_TOOL_MISSING"
  else
    set +e
    ( run_step_body "$STEP" ) >> "$LOG" 2>&1
    _rc=$?
    set -e
    if [ "$STEP" = build ]; then
      release_lock "$FULL_BUILD_LOCK"
    fi
  fi

  _elapsed=$(( $(epoch_now) - _step_start ))

  if [ "$_rc" -eq 0 ]; then
    _outcome=success
    _note=""
  elif [ "$_rc" -eq "$EXIT_TOOL_MISSING" ]; then
    _outcome=error
    _note="step could not run: $(grep -m1 '^ERROR:' "$LOG" 2>/dev/null || echo 'missing tool or prerequisite')"
    ERRORED=1
  else
    _outcome=failure
    _note="exit $_rc"
    FAILED=1
  fi

  record_step "$STEP" "$_outcome" "$_elapsed" "$LOG" 1 "$_note"
  printf '  %-18s %-8s %5ss  %s\n' "$STEP" "$_outcome" "$_elapsed" "$LOG"

  if [ "$STEP" = build ]; then
    BUILD_OUTCOME="$_outcome"
    BUILD_SECONDS="$_elapsed"
  fi
done

# ---------------------------------------------------------------------------
# Manifest, PR record, telemetry
# ---------------------------------------------------------------------------

RUN_FINISHED="$(iso_now)"
RUN_SECONDS=$(( $(epoch_now) - RUN_START_EPOCH ))

if [ "$FAILED" = 1 ]; then
  CONCLUSION=failure
elif [ "$ERRORED" = 1 ]; then
  CONCLUSION=error
else
  CONCLUSION=success
fi

helper manifest \
  --out "$MANIFEST" \
  --steps-tsv "$STEPS_TSV" \
  --pr "$PR_ID" \
  --pr-dir "$PR_DIR_NAME" \
  --branch "$BRANCH" \
  --base "$BASE" \
  --base-ref "$BASE_REF" \
  --merge-base "$MERGE_BASE" \
  --head-sha "$HEAD_SHA" \
  --worktree "$WORKTREE" \
  --started "$RUN_STARTED" \
  --finished "$RUN_FINISHED" \
  --seconds "$RUN_SECONDS" \
  --conclusion "$CONCLUSION" \
  --area "lean=$A_lean" \
  --area "mip_lean=$A_mip_lean" \
  --area "ldt_lean=$A_ldt_lean" \
  --area "blueprint=$A_blueprint" \
  --area "blueprint_src=$A_blueprint_src" \
  --area "tex_chapter=$A_tex_chapter" \
  --area "paper_gaps=$A_paper_gaps" \
  --area "scripts=$A_scripts" \
  --area "comparator=$A_comparator" \
  --area "workflow=$A_workflow" \
  --changed-files-file "$CHANGED_FILES" \
  --warnings-file "$WARN_FILE" \
  --partial "$PARTIAL" \
  > /dev/null

if [ "$PARTIAL" = 1 ]; then
  info "partial run: prs/$PR_DIR_NAME/pr.md left untouched (ci_status still reflects the last complete run)"
else
  helper frontmatter --file "$PR_MD" --set "ci_status=$CONCLUSION" --set "head_sha=$HEAD_SHA"
fi

# meta.md telemetry duty: every full build lands in builds.jsonl.
if [ -n "$BUILD_OUTCOME" ] && [ "$BUILD_OUTCOME" != skipped ]; then
  helper telemetry \
    --out "$REPO_ROOT/results/telemetry/builds.jsonl" \
    --field "ts=$RUN_FINISHED" \
    --field "kind=ci-build" \
    --field "trigger=ci.sh pr=$PR_ID" \
    --field "seconds=$BUILD_SECONDS" \
    --int-field seconds \
    --field "outcome=$BUILD_OUTCOME" \
    --field "sha=$HEAD_SHA" \
    --field "note=branch $BRANCH"
fi

info "conclusion: $CONCLUSION"
info "manifest: $MANIFEST"
info "logs: $LOG_DIR"
if [ -s "$WARN_FILE" ]; then
  info "warnings:"
  sed 's/^/  - /' "$WARN_FILE"
fi

[ "$CONCLUSION" = success ] || exit 1
exit 0
