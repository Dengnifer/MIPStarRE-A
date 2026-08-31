#!/usr/bin/env bash
#
# usage: local/bin/ci.sh <github-pr-number> [options]
#
#   Local replacement for .github/workflows/pr-ci.yml.  Runs the same eight
#   jobs (build, blueprint-render, paper-gaps, blueprint-sync, file-length,
#   proof-debt, proof-evasion, statement-origin) against the worktree of the
#   PR's branch, with the same per-area change gating. GitHub commit statuses
#   are the gate, and the full manifest is published as a marker-bound comment.
#
#   <github-pr-number> Positive GitHub pull-request number.
#
#   --worktree PATH    Use PATH as the branch worktree instead of resolving it
#                      from `git worktree list` / .worktrees/<branch>.
#   --base REF         Override the base branch from GitHub (default:
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
#   GitHub local-ci/<step> statuses        exact starting SHA, complete runs only
#   GitHub local-ci/summary                required digest-bound gate status
#   GitHub PR comment                      marker-bound full manifest
#   ~/.cache/mipstarre-dev/ci/<id>/<sha>/<run>/manifest.json
#   ~/.cache/mipstarre-dev/ci-logs/<id>/<sha>/<run>/<step>.log
#   results/telemetry/builds.jsonl         one ci-build line when build ran
#
#   A PARTIAL run (--only / --skip-build) stays entirely in runtime storage and
#   publishes no statuses or comments: debugging cannot satisfy a gate.
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

worktree_status() {
  git -C "$WORKTREE" status --porcelain=v1 --untracked-files=all 2>/dev/null
}

require_clean_worktree() {
  local _status
  _status="$(worktree_status)" || die "cannot inspect worktree cleanliness at $WORKTREE"
  if [ -n "$_status" ]; then
    printf '%s\n' "$_status" | sed 's/^/  /' >&2
    die "worktree $WORKTREE is dirty; CI requires committed tracked, staged, and untracked state"
  fi
}

worktree_is_clean() {
  local _status
  _status="$(worktree_status)" || return 1
  [ -z "$_status" ]
}

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
trap cleanup EXIT
trap 'exit 130' INT
trap 'exit 143' TERM

# ---------------------------------------------------------------------------
# Embedded Python helper (stdlib only): manifest assembly and telemetry append.
# ---------------------------------------------------------------------------

write_helper() {
  cat > "$1" <<'PYHELPER'
#!/usr/bin/env python3
"""Runtime-manifest and telemetry helper for local/bin/ci.sh.

Three subcommands, all writing atomically (tempfile in the destination
directory + os.replace) so a crashed or killed CI run never leaves a
half-written manifest or a truncated authoritative record behind:

  manifest        assemble an exact-head runtime manifest from a step TSV
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
        "base_sha": args.base_sha,
        "merge_base": args.merge_base,
        "head_sha": args.head_sha,
        "run_id": args.run_id,
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
    manifest.add_argument("--base-sha", required=True)
    manifest.add_argument("--merge-base", required=True)
    manifest.add_argument("--head-sha", required=True)
    manifest.add_argument("--run-id", required=True)
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
ONLY_STEPS=""
FORCE_ALL=0
SKIP_BUILD=0
DRY_RUN=0

while [ $# -gt 0 ]; do
  case "$1" in
    -h|--help) usage; exit 0 ;;
    --worktree) [ $# -ge 2 ] || die "--worktree needs a path"; WORKTREE_OVERRIDE="$2"; shift 2 ;;
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

[ -n "$PR_ARG" ] || { usage >&2; die "a GitHub PR number is required"; }

for _only in $ONLY_STEPS; do
  case " $STEP_NAMES " in
    *" $_only "*) ;;
    *) die "--only: unknown step '$_only' (known: $STEP_NAMES)" ;;
  esac
done

# ---------------------------------------------------------------------------
# Resolution: repository, authoritative GitHub PR, worktree, base
# ---------------------------------------------------------------------------

REPO_ROOT="$(cd "$SCRIPT_DIR/../.." && pwd)"
# Build telemetry remains single-instance in the primary checkout. When this
# script runs from a linked worktree, resolve that primary checkout here.
_common="$(git -C "$REPO_ROOT" rev-parse --path-format=absolute --git-common-dir 2>/dev/null || true)"
case "$_common" in
  */.git) REPO_ROOT="$(dirname "$_common")" ;;
esac
unset _common

[ -d "$REPO_ROOT/.git" ] || [ -f "$REPO_ROOT/.git" ] || die "$REPO_ROOT is not a git repository"

case "$PR_ARG" in
  ''|*[!0-9]*) die "PR number must be a positive GitHub number: $PR_ARG" ;;
esac
_num="$PR_ARG"
while [ "${#_num}" -gt 1 ] && [ "${_num#0}" != "$_num" ]; do
  _num="${_num#0}"
done
[ "$_num" != 0 ] || die "PR number must be positive"
PR_ID="$_num"

RUN_TMP="$(mktemp -d "${TMPDIR:-/tmp}/mipstarre-ci.XXXXXX")"
PY_HELPER="$RUN_TMP/ci_helper.py"
write_helper "$PY_HELPER"

command -v python3 >/dev/null 2>&1 || die "python3 is not on PATH; every audit job and the manifest writer need it"

helper() { python3 "$PY_HELPER" "$@"; }
PULL_JSON="$RUN_TMP/pull.json"
if ! python3 "$SCRIPT_DIR/github_api.py" --repo-root "$REPO_ROOT" pull "$PR_ID" > "$PULL_JSON"; then
  die "cannot read authoritative GitHub PR #$PR_ID"
fi

IFS="$(printf '\t')" read -r PR_STATE PR_DRAFT BRANCH BASE REMOTE_HEAD_SHA REMOTE_BASE_SHA < <(
  python3 - "$PULL_JSON" <<'PY'
import json
import re
import sys

pull = json.load(open(sys.argv[1], encoding="utf-8"))
state = str(pull.get("state") or "")
draft = "true" if pull.get("draft") else "false"
try:
    branch = str(pull["head"]["ref"])
    base = str(pull["base"]["ref"])
    head_sha = str(pull["head"]["sha"]).lower()
    base_sha = str(pull["base"]["sha"]).lower()
except (KeyError, TypeError):
    raise SystemExit("pull response lacks head/base data")
if (
    not branch
    or not base
    or not re.fullmatch(r"(?:[0-9a-f]{40}|[0-9a-f]{64})", head_sha)
    or not re.fullmatch(r"(?:[0-9a-f]{40}|[0-9a-f]{64})", base_sha)
):
    raise SystemExit("pull response contains an invalid exact head/base SHA or ref")
if any(ch in branch + base for ch in "[] \t\r\n"):
    raise SystemExit("pull response contains an unsafe branch or base ref")
print(state, draft, branch, base, head_sha, base_sha, sep="\t")
PY
)
[ "$PR_STATE" = open ] || die "GitHub PR #$PR_ID is not open (state=$PR_STATE)"

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
if [ "$_wt_branch" != "$BRANCH" ]; then
  die "worktree $WORKTREE is on '${_wt_branch:-detached}' but GitHub PR #$PR_ID uses '$BRANCH'"
fi

HEAD_SHA="$(git -C "$WORKTREE" rev-parse HEAD 2>/dev/null || true)"
[ -n "$HEAD_SHA" ] || die "$WORKTREE has no commits to test"
[ "$HEAD_SHA" = "$REMOTE_HEAD_SHA" ] || die "local branch tip $HEAD_SHA does not equal GitHub PR head $REMOTE_HEAD_SHA"

# The fetched GitHub base is the one coherent diff contract for hooks, CI, and
# statement audits. github-sync.sh and worktree-setup.sh maintain this ref.
BASE_REF="refs/remotes/github/$BASE"
git -C "$WORKTREE" rev-parse --verify --quiet "$BASE_REF^{commit}" >/dev/null 2>&1 || \
  die "$BASE_REF does not resolve; run local/bin/github-sync.sh refs --base '$BASE'"
LOCAL_BASE_SHA="$(git -C "$WORKTREE" rev-parse "$BASE_REF^{commit}")"
[ "$LOCAL_BASE_SHA" = "$REMOTE_BASE_SHA" ] || \
  die "local base ref $BASE_REF is $LOCAL_BASE_SHA, not GitHub PR base $REMOTE_BASE_SHA"
BASE_SHA="$REMOTE_BASE_SHA"

require_clean_worktree

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
  if match_globs "$_file" '.github/workflows/pr-ci.yml' '.githooks/*' \
      'local/bin/github_api.py' 'local/bin/issue_new.py' 'local/bin/issue_close.py' \
      'local/bin/pr_open.py' 'local/bin/ci.sh' 'local/bin/review.sh' \
      'local/bin/autofix.sh' 'local/bin/pr_merge.py' 'local/bin/agent.sh' \
      'local/bin/housekeeping.sh' 'local/bin/github-sync.sh' \
      'local/bin/export_issues.py' 'local/bin/worktree-setup.sh' \
      'local/bin/cache-warmer.sh' 'local/protocols/*' 'local/personas/*'; then
    A_workflow=1
  fi
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

RUN_ID="$(date -u +%Y%m%dT%H%M%SZ)-$$"
RUN_DIR="$CACHE_ROOT/ci/$PR_ID/$HEAD_SHA/$RUN_ID"
LOG_DIR="$CACHE_ROOT/ci-logs/$PR_ID/$HEAD_SHA/$RUN_ID"
MANIFEST="$RUN_DIR/manifest.json"

# A run that was told to skip jobs cannot produce a merge-gate verdict.  It
# writes only runtime data and publishes nothing, so a debugging --only run can
# never leave the review or merge gate a verdict it did not earn.
PARTIAL=0
if [ -n "$ONLY_STEPS" ] || [ "$SKIP_BUILD" = 1 ]; then
  PARTIAL=1
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
  info "runtime manifest would be $MANIFEST"
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

mkdir -p "$LOG_DIR" "$RUN_DIR"

# The helper repeats the exact comparison and clean-tree check inside every
# gate-relevant mutation, after its idempotency lookup and immediately before
# the POST. Error invalidation deliberately bypasses this guard so a dirty run
# can replace any already-published pending or success status.
PUBLICATION_GUARD="$RUN_TMP/publication-guard.json"
python3 - "$PUBLICATION_GUARD" "$PR_ID" "$BRANCH" "$BASE" "$HEAD_SHA" \
    "$BASE_SHA" "$WORKTREE" <<'PY'
import json
import sys

destination, number, branch, base, head_sha, base_sha, worktree = sys.argv[1:]
payload = {
    "schema": 1,
    "pr": int(number),
    "branch": branch,
    "base": base,
    "head_sha": head_sha,
    "base_sha": base_sha,
    "worktree": worktree,
    "pid": "",
    "owner": "",
    "locks": [],
}
with open(destination, "w", encoding="utf-8") as stream:
    json.dump(payload, stream, sort_keys=True)
    stream.write("\n")
PY

if [ "$PARTIAL" = 1 ]; then
  info "partial run (--only/--skip-build): no GitHub statuses or comments will be published"
fi

RUN_STARTED="$(iso_now)"
RUN_START_EPOCH="$(epoch_now)"

publish_status() {
  local _guard_mode="${4:-guarded}"
  if [ "$_guard_mode" = guarded ]; then
    python3 "$SCRIPT_DIR/github_api.py" --repo-root "$REPO_ROOT" --no-probe \
      post-status "$HEAD_SHA" "local-ci/$1" "$2" "$3" \
      --guard-file "$PUBLICATION_GUARD" >/dev/null
  else
    python3 "$SCRIPT_DIR/github_api.py" --repo-root "$REPO_ROOT" --no-probe \
      post-status "$HEAD_SHA" "local-ci/$1" "$2" "$3" >/dev/null
  fi
}

invalidate_ci_publication() {
  local _step
  for _step in $STEP_NAMES summary; do
    publish_status "$_step" error \
      "local CI run $RUN_ID failed evidence-integrity checks" unguarded || \
      warn "could not invalidate local-ci/$_step after publication abort"
  done
}

if [ "$PARTIAL" = 0 ]; then
  publish_status summary pending "local CI run=$RUN_ID is pending" ||
    die "could not publish pending status local-ci/summary on $HEAD_SHA"
fi

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

  if [ "$PARTIAL" = 0 ]; then
    publish_status "$STEP" pending \
      "local CI run $RUN_ID is pending" unguarded || \
      die "could not publish pending status local-ci/$STEP on $HEAD_SHA"
  fi

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
# Exact-head recheck, manifest, GitHub publication, telemetry
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

publication_snapshot_matches() {
  local _pull_json="$1" _remote_head="" _remote_base="" _local_head _local_base
  if python3 "$SCRIPT_DIR/github_api.py" --repo-root "$REPO_ROOT" --no-probe \
      pull "$PR_ID" >"$_pull_json"; then
    IFS="$(printf '\t')" read -r _remote_head _remote_base < <(
      python3 - "$_pull_json" <<'PY'
import json
import sys

pull = json.load(open(sys.argv[1], encoding="utf-8"))
print(
    str((pull.get("head") or {}).get("sha") or "").lower(),
    str((pull.get("base") or {}).get("sha") or "").lower(),
    sep="\t",
)
PY
    )
  fi
  _local_head="$(git -C "$WORKTREE" rev-parse HEAD 2>/dev/null || true)"
  _local_base="$(git -C "$WORKTREE" rev-parse "$BASE_REF^{commit}" 2>/dev/null || true)"
  [ "$_remote_head" = "$HEAD_SHA" ] \
    && [ "$_remote_base" = "$BASE_SHA" ] \
    && [ "$_local_head" = "$HEAD_SHA" ] \
    && [ "$_local_base" = "$BASE_SHA" ] \
    && worktree_is_clean
}

HEAD_STABLE=1
if [ "$PARTIAL" = 0 ]; then
  if ! publication_snapshot_matches "$RUN_TMP/final-pull.json"; then
    HEAD_STABLE=0
  fi
  if [ "$HEAD_STABLE" = 0 ]; then
    CONCLUSION=error
    note_warning \
      "head/base moved, the comparison became unreadable, or the worktree became dirty" \
      "during CI; no success statuses or manifest comment will be published"
  fi
fi

helper manifest \
  --out "$MANIFEST" \
  --steps-tsv "$STEPS_TSV" \
  --pr "$PR_ID" \
  --pr-dir "github-pr-$PR_ID" \
  --branch "$BRANCH" \
  --base "$BASE" \
  --base-ref "$BASE_REF" \
  --base-sha "$BASE_SHA" \
  --merge-base "$MERGE_BASE" \
  --head-sha "$HEAD_SHA" \
  --run-id "$RUN_ID" \
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

PUBLISH_FAILED=0
PUBLICATION_ABORTED=0
if [ "$PARTIAL" = 0 ] && [ "$HEAD_STABLE" = 0 ]; then
  invalidate_ci_publication
elif [ "$PARTIAL" = 0 ]; then
  while IFS="$(printf '\t')" read -r STEP OUTCOME _SECONDS _LOG _BLOCKING NOTE; do
    if ! worktree_is_clean; then
      warn "worktree became dirty during final status publication"
      HEAD_STABLE=0
      PUBLICATION_ABORTED=1
      break
    fi
    case "$OUTCOME" in
      skipped)
        STATUS_STATE=success
        STATUS_DESCRIPTION="local CI run=$RUN_ID skipped: ${NOTE:-not applicable}"
        ;;
      success)
        STATUS_STATE=success
        STATUS_DESCRIPTION="local CI run=$RUN_ID passed"
        ;;
      failure)
        STATUS_STATE=failure
        STATUS_DESCRIPTION="local CI run=$RUN_ID failed${NOTE:+: $NOTE}"
        ;;
      error|*)
        STATUS_STATE=error
        STATUS_DESCRIPTION="local CI run=$RUN_ID could not run${NOTE:+: $NOTE}"
        ;;
    esac
    if ! publish_status "$STEP" "$STATUS_STATE" "$STATUS_DESCRIPTION"; then
      warn "could not publish final status local-ci/$STEP=$STATUS_STATE"
      PUBLISH_FAILED=1
    fi
  done < "$STEPS_TSV"

  if [ "$PUBLICATION_ABORTED" = 0 ] \
      && ! publication_snapshot_matches "$RUN_TMP/pre-manifest-pull.json"; then
    warn "comparison or worktree changed immediately before manifest publication"
    HEAD_STABLE=0
    PUBLICATION_ABORTED=1
  fi

  if [ "$PUBLICATION_ABORTED" = 1 ]; then
    invalidate_ci_publication
  elif [ "$PUBLISH_FAILED" != 0 ]; then
    HEAD_STABLE=0
    PUBLICATION_ABORTED=1
    invalidate_ci_publication
  else
    CI_MARKER="<!-- mipstarre:ci-manifest pr=$PR_ID head=$HEAD_SHA run=$RUN_ID -->"
    COMMENT_FILE="$RUN_TMP/manifest-comment.md"
    {
      printf 'Local CI manifest for PR #%s at exact head `%s`.\n\n' "$PR_ID" "$HEAD_SHA"
      printf '```json\n'
      cat "$MANIFEST"
      printf '```\n\n%s\n' "$CI_MARKER"
    } > "$COMMENT_FILE"
    if ! python3 "$SCRIPT_DIR/github_api.py" --repo-root "$REPO_ROOT" --no-probe \
        comment-once "$PR_ID" "$COMMENT_FILE" "$CI_MARKER" \
        --guard-file "$PUBLICATION_GUARD" >/dev/null; then
      warn "could not publish the marker-bound CI manifest comment"
      PUBLISH_FAILED=1
      HEAD_STABLE=0
      PUBLICATION_ABORTED=1
      invalidate_ci_publication
    elif ! python3 "$SCRIPT_DIR/github_api.py" --repo-root "$REPO_ROOT" --no-probe \
        ci-finalize "$PR_ID" "$HEAD_SHA" "$BASE_SHA" "$RUN_ID" \
        --guard-file "$PUBLICATION_GUARD" >/dev/null; then
      warn "manifest read-back or local-ci/summary finalization failed"
      PUBLISH_FAILED=1
      HEAD_STABLE=0
      PUBLICATION_ABORTED=1
      invalidate_ci_publication
    fi
  fi
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

[ "$HEAD_STABLE" = 1 ] || exit 1
[ "$PUBLISH_FAILED" = 0 ] || exit 1
[ "$CONCLUSION" = success ] || exit 1
exit 0
