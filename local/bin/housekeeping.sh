#!/usr/bin/env bash
#
# Usage: local/bin/housekeeping.sh {standup|stale-audit|linter-sweep|readme-freshness|all}
#
# On-demand replacement for .github/workflows/housekeeping.yml, whose four jobs
# were bound to four cron entries (housekeeping.yml:14-18).  There is no
# scheduler here and that is deliberate: DESIGN.md:53 makes the dispatcher
# on-demand, so the operator decides when a job runs and sees its output.
#
#   standup           structured daily digest -> issues/standup/YYYY-MM-DD.md
#   stale-audit       report-only stale-citation audit of open issues
#   linter-sweep      report-only Lean linter-warning capture (FULL BUILD)
#   readme-freshness  report-only README freshness audit
#   all               standup + stale-audit + readme-freshness
#
# `all` deliberately EXCLUDES linter-sweep.  That job is a complete `lake build`
# — the upstream workflow gave it a 120-minute timeout (housekeeping.yml:321) —
# and it must never sit on a fast path someone runs casually.  Ask for it by
# name.
#
# Three of the four jobs are report-only, and that contract is load-bearing:
# docs/stale_issue_audit.md:143-144 states "Do **not** let the script close
# issues automatically", and DESIGN.md:88-90 generalizes it to the sweep and the
# freshness audit.  Nothing in this script closes, edits or labels an issue.
# `standup` is the sole writer, and it writes only its own digest file.
#
# Reports land in results/reports/.  Build logs and intermediate JSON go to
# ~/.cache/mipstarre-dev/ and are never committed (DESIGN.md:37-38).
#
# Environment:
#   MIPSTARRE_CACHE_ROOT   override ~/.cache/mipstarre-dev
#   MIPSTARRE_LLM_ENABLED  "false" disables every model call (none are wired yet)

set -euo pipefail

SCRIPT_DIR="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd)"
REPO_ROOT="$(cd -- "${SCRIPT_DIR}/../.." && pwd)"
CACHE_ROOT="${MIPSTARRE_CACHE_ROOT:-${HOME}/.cache/mipstarre-dev}"
REPORT_DIR="${REPO_ROOT}/results/reports"
LOG_DIR="${CACHE_ROOT}/logs"
LOCK_DIR="${CACHE_ROOT}/locks"

usage() {
  cat <<'USAGE'
Usage: local/bin/housekeeping.sh {standup|stale-audit|linter-sweep|readme-freshness|all}

  standup           structured daily digest -> issues/standup/YYYY-MM-DD.md
                    (72h lookback on Mondays, 24h otherwise; no model call)
  stale-audit       report-only stale-citation audit over open issues
  linter-sweep      report-only Lean linter-warning capture; FULL `lake build`,
                    taken under the machine-wide build lock. Never part of `all`.
  readme-freshness  report-only README freshness audit
  all               standup + stale-audit + readme-freshness

Reports are written to results/reports/. Build logs and intermediate JSON go to
${MIPSTARRE_CACHE_ROOT:-~/.cache/mipstarre-dev}/ and are never committed.

Only `standup` writes anything into the repository, and only its own digest.
The three audits are report-only by contract (docs/stale_issue_audit.md:143-144,
DESIGN.md:88-90): they never close, edit, or label an issue.
USAGE
}

die() {
  printf 'housekeeping.sh: %s\n' "$*" >&2
  exit 2
}

note() {
  printf '==> %s\n' "$*"
}

require_file() {
  local path="$1" why="$2"
  [ -f "${path}" ] || die "missing ${path}: ${why}"
}

# Run a command while holding an exclusive advisory lock.  macOS has no
# flock(1), so the lock is taken with fcntl through python3, which every job
# already requires.  A busy lock is a refusal, not a queue: two concurrent
# sweeps would interleave their reports.
run_locked() {
  local lock="$1"
  shift
  python3 - "${lock}" "$@" <<'PY'
import fcntl, os, subprocess, sys

lock = sys.argv[1]
cmd = sys.argv[2:]
os.makedirs(os.path.dirname(lock), exist_ok=True)
fd = os.open(lock, os.O_CREAT | os.O_RDWR, 0o644)
try:
    fcntl.flock(fd, fcntl.LOCK_EX | fcntl.LOCK_NB)
except OSError:
    sys.stderr.write(
        f"housekeeping.sh: {lock} is held by another process; refusing to start "
        "a second run.\n"
    )
    sys.exit(75)
os.ftruncate(fd, 0)
os.write(fd, f"{os.getpid()}\n".encode())
sys.exit(subprocess.call(cmd))
PY
}

timestamp() {
  date -u +%Y%m%dT%H%M%SZ
}

# ---------------------------------------------------------------------------
# standup
# ---------------------------------------------------------------------------
#
# Ports housekeeping.yml:31-215.  Upstream, six GitHub search/REST calls built
# an activity feed which a model then wrote up.  Here the feed is derived from
# `git log` plus the issues/ and prs/ registries, and the write-up is a
# structured digest with no model in the loop; the LLM hook is marked below.
#
# Two upstream rules are preserved exactly:
#   * the lookback window is 72 hours on Mondays and 24 hours otherwise, so the
#     Monday digest covers the weekend (housekeeping.yml:66-69);
#   * issues labelled `standup` are excluded from every feed
#     (housekeeping.yml:85-95, `-label:standup`).  Without that exclusion the
#     digest reports on its own previous output and the report grows every day.

job_standup() {
  note "standup: deriving the activity feed from git log and the local registries"
  mkdir -p "${REPO_ROOT}/issues/standup"
  python3 - "${REPO_ROOT}" <<'PY'
import subprocess
import sys
from datetime import datetime, timedelta, timezone
from pathlib import Path

repo_root = Path(sys.argv[1])
sys.path.insert(0, str(repo_root / "local" / "bin"))
try:
    import track
except ModuleNotFoundError as exc:
    sys.stderr.write(f"standup: cannot import local/bin/track.py ({exc})\n")
    raise SystemExit(2)

now = datetime.now(timezone.utc)
# Monday is weekday() == 0.
hours_back = 72 if now.weekday() == 0 else 24
since = now - timedelta(hours=hours_back)
since_iso = since.strftime("%Y-%m-%dT%H:%M:%SZ")
today = now.strftime("%Y-%m-%d")


def git(*args, default=""):
    try:
        result = subprocess.run(
            ["git", *args], cwd=str(repo_root),
            capture_output=True, text=True, check=False,
        )
    except FileNotFoundError:
        return default
    return result.stdout.strip() if result.returncode == 0 else default


def parse_stamp(value):
    if not isinstance(value, str) or not value:
        return None
    try:
        return datetime.strptime(value, "%Y-%m-%dT%H:%M:%SZ").replace(tzinfo=timezone.utc)
    except ValueError:
        return None


def in_window(value):
    stamp = parse_stamp(value)
    return stamp is not None and stamp >= since


def commit_time(sha):
    if not sha:
        return None
    iso = git("show", "-s", "--format=%cI", str(sha))
    if not iso:
        return None
    try:
        return datetime.fromisoformat(iso).astimezone(timezone.utc)
    except ValueError:
        return None


# --- commits on the base branch -------------------------------------------
base = "main" if git("rev-parse", "--verify", "--quiet", "refs/heads/main") else "HEAD"
raw_log = git("log", base, f"--since={since_iso}", "--pretty=format:%h%x1f%an%x1f%cI%x1f%s")
commits = []
for line in raw_log.splitlines():
    parts = line.split("\x1f")
    if len(parts) == 4:
        commits.append(dict(zip(("sha", "author", "date", "subject"), parts)))

# --- issues ----------------------------------------------------------------
# `standup` issues never enter the feed: automation must not report on itself.
issues = [i for i in track.iter_issues(repo_root) if "standup" not in i.labels]
opened = [i for i in issues if in_window(i.meta.get("created"))]
closed = [
    i for i in issues
    if i.state == "closed" and in_window(i.meta.get("updated"))
]
tracking = [i for i in issues if i.state == "open" and "tracking" in i.labels]

# --- pull requests ---------------------------------------------------------
merged, active, reviews = [], [], []
for pr in track.iter_prs(repo_root):
    # Review verdicts are collected for every PR, merged ones included: a
    # verdict written inside the window is activity even if the PR landed.
    review_dir = pr.path.parent / "reviews"
    if review_dir.is_dir():
        for verdict in sorted(review_dir.glob("*.*")):
            if verdict.name.startswith("."):
                continue
            stamp = datetime.fromtimestamp(verdict.stat().st_mtime, tz=timezone.utc)
            if stamp >= since:
                reviews.append((pr, verdict, stamp))

    state = pr.meta.get("state")
    if state == "merged":
        when = commit_time(pr.meta.get("merged_commit")) or parse_stamp(pr.meta.get("created"))
        if when is not None and when >= since:
            merged.append((pr, when))
    elif state == "open":
        head_when = commit_time(pr.meta.get("head_sha")) or parse_stamp(pr.meta.get("created"))
        if head_when is not None and head_when >= since:
            active.append((pr, head_when))


def bullets(rows):
    return "\n".join(rows) if rows else "- (none in this window)"


lines = []
lines.append(f"# Daily standup — {today}")
lines.append("")
window_note = f"Activity window: last {hours_back} hours (since {since_iso})."
if hours_back == 72:
    window_note += " Monday digest, covering the weekend."
lines.append(window_note)
lines.append("")

lines.append("## Merged pull requests")
lines.append("")
lines.append(bullets([
    f"- PR #{pr.id} (*{track.sanitize(pr.title, track.TITLE_LIMIT)}*) "
    f"— merged {when.strftime('%Y-%m-%dT%H:%M:%SZ')}, issue #{pr.issue or '?'}"
    for pr, when in sorted(merged, key=lambda row: row[1])
]))
lines.append("")

lines.append("## Active pull requests")
lines.append("")
lines.append(bullets([
    f"- PR #{pr.id} (*{track.sanitize(pr.title, track.TITLE_LIMIT)}*) "
    f"— branch `{pr.branch}`, ci_status {pr.meta.get('ci_status')!r}, "
    f"review_state {pr.meta.get('review_state')!r}, "
    f"fix_iterations {pr.meta.get('fix_iterations')}"
    for pr, _ in sorted(active, key=lambda row: row[0].id)
]))
lines.append("")

lines.append("## Issues opened")
lines.append("")
lines.append(bullets([
    f"- #{i.id} (*{track.sanitize(i.title, track.TITLE_LIMIT)}*) "
    f"— labels {', '.join(i.labels) or 'none'}"
    for i in opened
]))
lines.append("")

lines.append("## Issues closed")
lines.append("")
lines.append(bullets([
    f"- #{i.id} (*{track.sanitize(i.title, track.TITLE_LIMIT)}*) "
    f"— {i.state_reason or 'no reason recorded'}"
    for i in closed
]))
lines.append("")

lines.append("## Commits on " + base)
lines.append("")
lines.append(bullets([
    f"- `{c['sha']}` {track.sanitize(c['subject'], 120)} — {c['author']}, {c['date']}"
    for c in commits
]))
lines.append("")

lines.append("## Review activity")
lines.append("")
lines.append(bullets([
    f"- PR #{pr.id}: verdict `{verdict.name}` written {stamp.strftime('%Y-%m-%dT%H:%M:%SZ')}"
    for pr, verdict, stamp in sorted(reviews, key=lambda row: row[2])
]))
lines.append("")

lines.append("## Tracking parents")
lines.append("")
rows = []
for parent in tracking:
    resolved, total = track.child_counts(repo_root, parent)
    if total == 0:
        continue
    flag = " — ready to close" if resolved == total else ""
    rows.append(
        f"- #{parent.id} (*{track.sanitize(parent.title, track.TITLE_LIMIT)}*) "
        f"[{resolved}/{total} sub-issues closed]{flag}"
    )
lines.append(bullets(rows))
lines.append("")

# --------------------------------------------------------------------------
# LLM HOOK (not wired)
# --------------------------------------------------------------------------
# housekeeping.yml:183-215 fed this same feed to a model with
# .github/prompts/daily-standup-prompt.md and asked for a mathematical
# narrative.  To wire it: gate on MIPSTARRE_LLM_ENABLED != "false", pass the
# sections above already sanitized (they are), read the prompt from the
# committed main worktree, and append the narrative as a "## Narrative"
# section BELOW this digest rather than replacing it — the structured feed is
# the auditable part and must survive a model outage.
lines.append("## Narrative")
lines.append("")
lines.append(
    "_Not generated: the standup runs without a model today. The structured "
    "feed above is the whole digest._"
)
lines.append("")

path = repo_root / "issues" / "standup" / f"{today}.md"
created = track.utcnow()
if path.is_file():
    try:
        existing, _ = track.split_frontmatter(path.read_text(encoding="utf-8"))
        created = str(existing.get("created") or created)
    except track.LayerError:
        pass

meta = {
    "id": f"standup-{today}",
    "title": f"Daily standup — {today}",
    "state": "open",
    "state_reason": None,
    "parent": None,
    "children": [],
    "labels": ["standup"],
    "pinned": False,
    "created": created,
    "updated": track.utcnow(),
    "agent_session": None,
}
rendered = track.dump_frontmatter(meta, track.ISSUE_FIELDS) + "\n" + "\n".join(lines)
track.atomic_write(path, rendered)
print(f"wrote {path.relative_to(repo_root)} "
      f"({len(merged)} merged PR(s), {len(opened)} issue(s) opened, "
      f"{len(closed)} closed, {len(commits)} commit(s))")
PY
}

# ---------------------------------------------------------------------------
# stale-audit
# ---------------------------------------------------------------------------
#
# Ports housekeeping.yml:216-309.  The export step is the only GitHub-dependent
# part and is replaced by local/bin/export_issues.py; scripts/audit_stale_issues.py
# runs unchanged.  docs/stale_issue_audit.md:157-159 asks for a clean checkout of
# current main, so the working tree is checked and a dirty tree is reported —
# a flagged citation is only meaningful against committed code.

job_stale_audit() {
  local audit="${REPO_ROOT}/scripts/audit_stale_issues.py"
  local exporter="${SCRIPT_DIR}/export_issues.py"
  require_file "${audit}" "the stale-issue audit ports unchanged from the parent repo"
  require_file "${exporter}" "the local replacement for 'gh issue list --json'"

  mkdir -p "${REPORT_DIR}" "${CACHE_ROOT}"
  local issues_json="${CACHE_ROOT}/open-issues.json"

  if command -v git >/dev/null 2>&1 && [ -n "$(git -C "${REPO_ROOT}" status --porcelain 2>/dev/null || true)" ]; then
    printf 'note: the working tree is dirty; citations are audited against the files on disk, not against committed main (docs/stale_issue_audit.md:157-159).\n' >&2
  fi

  note "stale-audit: exporting open issues"
  python3 "${exporter}" --repo-root "${REPO_ROOT}" --state open --output "${issues_json}"

  note "stale-audit: running the report-only audit"
  python3 "${audit}" --issues "${issues_json}" --repo-root "${REPO_ROOT}" \
    --format json --output "${REPORT_DIR}/stale-issue-audit.json"
  python3 "${audit}" --issues "${issues_json}" --repo-root "${REPO_ROOT}" \
    --format text --output "${REPORT_DIR}/stale-issue-audit.txt"

  python3 - "${REPORT_DIR}/stale-issue-audit.json" <<'PY'
import json
import sys

# audit_stale_issues.py --format json emits a bare array of per-issue records.
with open(sys.argv[1], encoding="utf-8") as handle:
    data = json.load(handle)
issues = data if isinstance(data, list) else data.get("issues", [])
flagged = [i for i in issues if i.get("flagged")]
with_citations = [
    i for i in issues if i.get("file_citations") or i.get("decl_citations")
]
print(f"scanned {len(issues)} issue(s); {len(with_citations)} carry citations; "
      f"{len(flagged)} flagged")
for issue in flagged:
    print(f"  #{issue.get('number')} {issue.get('title', '')}")
    for path in issue.get("missing_files", []):
        print(f"      missing file citation: {path}")
    for line in issue.get("non_sorry_lines", []):
        print(f"      cited line no longer holds a sorry: {line}")
    for decl in issue.get("missing_decls", []):
        print(f"      unresolved declaration: {decl}")
print("Report-only: nothing was closed, edited or labelled. "
      "Human triage decides (docs/stale_issue_audit.md:143-144).")
PY
  note "stale-audit: reports in ${REPORT_DIR}/stale-issue-audit.{json,txt}"
}

# ---------------------------------------------------------------------------
# linter-sweep
# ---------------------------------------------------------------------------
#
# Ports housekeeping.yml:310-382: `lake exe cache get` then
# `lake build -q --log-level=info`, teed to a log, summarized by
# scripts/lean_linter_warning_report.py.  The upstream job explicitly did not
# open a PR (housekeeping.yml:340-341) and neither does this one; any autofix
# stays a separate, human-invoked command.
#
# The build takes the machine-wide advisory build lock required by
# DESIGN.md:81-82 — one full `lake build` at a time — so a sweep cannot race an
# agent's build or the cache warmer.

job_linter_sweep() {
  local reporter="${REPO_ROOT}/scripts/lean_linter_warning_report.py"
  require_file "${reporter}" "the linter-warning parser ports unchanged"
  command -v lake >/dev/null 2>&1 || die \
    "lake is not on PATH; the linter sweep is a full Lean build and cannot run without it"

  mkdir -p "${REPORT_DIR}" "${LOG_DIR}"
  local log_file="${LOG_DIR}/lean-build-$(timestamp).log"

  note "linter-sweep: full lake build under the machine-wide build lock (this is slow)"
  # THE machine-wide full-build mutex — same path and mkdir protocol as
  # cache-warmer.sh, warm-worktree.sh and ci.sh (DESIGN.md invariant 7).
  # A live owner is never broken; a dead owner's lock is.
  local build_lock="${MIPSTARRE_FULL_BUILD_LOCK:-${CACHE_ROOT}/.full-build-lock}"
  local waited=0 wait_max="${MIPSTARRE_CI_BUILD_LOCK_WAIT_S:-14400}"
  while ! mkdir "${build_lock}" 2>/dev/null; do
    local owner_pid
    owner_pid="$(head -n 1 "${build_lock}/owner" 2>/dev/null || true)"
    if [ -n "${owner_pid}" ] && kill -0 "${owner_pid}" 2>/dev/null; then
      [ "${waited}" -ge "${wait_max}" ] && die \
        "could not take ${build_lock} within ${wait_max}s (held by pid ${owner_pid})"
      [ "${waited}" -eq 0 ] && note "waiting for build lock ${build_lock} (pid ${owner_pid})"
      sleep 15; waited=$((waited + 15))
    else
      note "breaking stale build lock ${build_lock} (owner dead or unreadable)"
      rm -rf "${build_lock}"
    fi
  done
  printf '%s\n%s\n%s\n' "$$" "$(date -u +%Y-%m-%dT%H:%M:%SZ)" "housekeeping linter-sweep" \
    > "${build_lock}/owner"
  # shellcheck disable=SC2064  # expand build_lock now, not at trap time
  trap "rm -rf '${build_lock}'" RETURN
  run_locked "${LOCK_DIR}/lake-build.lock" \
    "${SCRIPT_DIR}/housekeeping.sh" --internal-lean-build "${log_file}"

  note "linter-sweep: summarizing warnings"
  python3 "${reporter}" \
    --log "${log_file}" \
    --json "${REPORT_DIR}/lean-linter-warnings.json" \
    --text "${REPORT_DIR}/lean-linter-warnings.txt"
  note "linter-sweep: build log ${log_file}"
  note "linter-sweep: reports in ${REPORT_DIR}/lean-linter-warnings.{json,txt}"
}

# Internal entry point: the build itself, invoked under the lock by run_locked.
internal_lean_build() {
  local log_file="$1"
  cd "${REPO_ROOT}"
  # The build's exit status is deliberately not fatal: a failing build still
  # produces the warning lines this sweep exists to collect.
  {
    lake exe cache get
    lake build -q --log-level=info
  } 2>&1 | tee "${log_file}" || true
}

# ---------------------------------------------------------------------------
# readme-freshness
# ---------------------------------------------------------------------------
#
# Ports housekeeping.yml:383-463.  The audit script is already fully local; only
# the artifact upload and step summary are dropped.  Report-only: it never edits
# the README and never opens a PR.

job_readme_freshness() {
  local audit="${REPO_ROOT}/scripts/audit_readme_freshness.py"
  require_file "${audit}" "the README freshness audit ports unchanged"
  mkdir -p "${REPORT_DIR}"

  note "readme-freshness: running the report-only audit"
  python3 "${audit}" --root "${REPO_ROOT}" \
    --readme "${REPO_ROOT}/README.md" \
    --format json --output "${REPORT_DIR}/readme-freshness.json"
  python3 "${audit}" --root "${REPO_ROOT}" \
    --readme "${REPO_ROOT}/README.md" \
    --format text --output "${REPORT_DIR}/readme-freshness.txt"

  python3 - "${REPORT_DIR}/readme-freshness.json" <<'PY'
import json
import sys

with open(sys.argv[1], encoding="utf-8") as handle:
    data = json.load(handle)
missing = data.get("missing_paths", [])
toolchain = (data.get("toolchain") or {}).get("mismatches", [])
submodules = (data.get("ldt_submodule_count") or {}).get("mismatches", [])
print(f"flagged: {bool(data.get('flagged'))}; missing paths: {len(missing)}; "
      f"toolchain mismatches: {len(toolchain)}; submodule-count mismatches: "
      f"{len(submodules)}")
for row in missing:
    print(f"  missing path: {row.get('path')} (line {row.get('line')})")
print("Report-only: the README was not modified.")
PY
  note "readme-freshness: reports in ${REPORT_DIR}/readme-freshness.{json,txt}"
}

# ---------------------------------------------------------------------------
# dispatch
# ---------------------------------------------------------------------------

# Run one job under its own per-job lock.  The upstream workflow used
# per-entity concurrency groups for the same purpose; the re-exec keeps the lock
# held for the whole job rather than for a single command, and the guard
# variable stops the re-exec from trying to take a lock it already holds.
dispatch_job() {
  local job="$1"
  if [ "${MIPSTARRE_HK_LOCKED:-}" = "${job}" ]; then
    case "${job}" in
      standup) job_standup ;;
      stale-audit) job_stale_audit ;;
      linter-sweep) job_linter_sweep ;;
      readme-freshness) job_readme_freshness ;;
    esac
    return 0
  fi
  local rc=0
  export MIPSTARRE_HK_LOCKED="${job}"
  run_locked "${LOCK_DIR}/housekeeping-${job}.lock" "${BASH_SOURCE[0]}" "${job}" || rc=$?
  unset MIPSTARRE_HK_LOCKED
  return "${rc}"
}

main() {
  if [ "$#" -lt 1 ]; then
    usage
    exit 2
  fi

  case "$1" in
    -h|--help|help)
      usage
      exit 0
      ;;
    --internal-lean-build)
      [ "$#" -eq 2 ] || die "--internal-lean-build needs a log path"
      internal_lean_build "$2"
      exit 0
      ;;
  esac

  local job="$1"
  case "${job}" in
    standup|stale-audit|linter-sweep|readme-freshness|all) ;;
    *) die "unknown job '${job}'. Expected one of: standup stale-audit linter-sweep readme-freshness all" ;;
  esac

  mkdir -p "${LOCK_DIR}" "${REPORT_DIR}"

  if [ "${job}" = "all" ]; then
    note "all: standup, stale-audit, readme-freshness (linter-sweep excluded — ask for it by name)"
    # One failing job must not hide the other two: a missing audit script or a
    # dirty tree is exactly the kind of thing the operator wants reported
    # alongside the reports that did get written.
    local failed=""
    local one
    for one in standup stale-audit readme-freshness; do
      dispatch_job "${one}" || failed="${failed} ${one}"
    done
    if [ -n "${failed}" ]; then
      printf 'housekeeping.sh: failed job(s):%s\n' "${failed}" >&2
      return 1
    fi
    return 0
  fi

  dispatch_job "${job}"
}

main "$@"
