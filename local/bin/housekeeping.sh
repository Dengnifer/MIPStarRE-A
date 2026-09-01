#!/usr/bin/env bash
# On-demand, report-only housekeeping over authoritative GitHub data.
set -euo pipefail

SCRIPT_DIR="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd)"
REPO_ROOT="$(cd -- "$SCRIPT_DIR/../.." && pwd)"
CACHE_ROOT="${MIPSTARRE_CACHE_ROOT:-$HOME/.cache/mipstarre-dev}"
REPORT_DIR="$REPO_ROOT/results/reports"
LOG_DIR="$CACHE_ROOT/logs"
LOCK_DIR="$CACHE_ROOT/locks"
BUILD_LOCK_PATH=""
BUILD_LOCK_IDENTITY=""
BUILD_LOCK_PID=""
BUILD_LOCK_TOKEN=""
BUILD_LOCK_DIGEST=""

usage() {
  cat <<'EOF'
usage: local/bin/housekeeping.sh {standup|stale-audit|linter-sweep|readme-freshness|all}

  standup           write a GitHub-derived digest under results/reports/standup/
  stale-audit       audit citations in authoritative open GitHub issues
  linter-sweep      capture Lean linter warnings under the full-build lock
  readme-freshness  run the report-only README audit
  all               standup + stale-audit + readme-freshness
EOF
}

die() { printf 'housekeeping.sh: %s\n' "$*" >&2; exit 2; }
note() { printf '==> %s\n' "$*"; }
timestamp() { date -u +%Y%m%dT%H%M%SZ; }

require_file() {
  [ -f "$1" ] || die "missing $1: $2"
}

run_locked() {
  local lock="$1"
  shift
  python3 - "$lock" "$@" <<'PY'
import fcntl
import os
import subprocess
import sys

lock = sys.argv[1]
os.makedirs(os.path.dirname(lock), exist_ok=True)
fd = os.open(lock, os.O_CREAT | os.O_RDWR, 0o644)
try:
    fcntl.flock(fd, fcntl.LOCK_EX | fcntl.LOCK_NB)
except OSError:
    sys.stderr.write(f"housekeeping.sh: lock is busy: {lock}\n")
    raise SystemExit(75)
os.ftruncate(fd, 0)
os.write(fd, f"{os.getpid()}\n".encode())
raise SystemExit(subprocess.call(sys.argv[2:]))
PY
}

job_standup() {
  note "standup: reading paginated GitHub issues and pull requests"
  mkdir -p "$REPORT_DIR/standup"
  python3 - "$REPO_ROOT" "$REPORT_DIR/standup" <<'PY'
import os
import subprocess
import sys
import tempfile
from datetime import datetime, timedelta, timezone
from pathlib import Path

root = Path(sys.argv[1])
destination = Path(sys.argv[2])
sys.path.insert(0, str(root / "local" / "bin"))
from github_api import GitHub  # noqa: E402

client = GitHub(repo_root=root)
client.probe_authentication()
issues = [
    row
    for row in client.paginate(f"/repos/{client.repo}/issues?state=all")
    if "pull_request" not in row
]
pulls = client.paginate(f"/repos/{client.repo}/pulls?state=all")

now = datetime.now(timezone.utc)
hours = 72 if now.weekday() == 0 else 24
since = now - timedelta(hours=hours)


def stamp(row, key="updated_at"):
    value = str(row.get(key) or "")
    try:
        return datetime.fromisoformat(value.replace("Z", "+00:00"))
    except ValueError:
        return datetime.min.replace(tzinfo=timezone.utc)


def clean(value, limit=160):
    text = "".join(
        ch for ch in str(value or "") if ch in "\t" or ord(ch) >= 32
    ).replace("\n", " ")
    return text[:limit]


def labels(row):
    return {
        str(item.get("name") if isinstance(item, dict) else item)
        for item in (row.get("labels") or [])
    }


def bullet(row, kind):
    number = row.get("number")
    url = row.get("html_url") or row.get("url") or ""
    title = clean(row.get("title"))
    return f"- [{kind} #{number}: {title}]({url})"


recent_issues = [row for row in issues if stamp(row) >= since and "standup" not in labels(row)]
recent_pulls = [row for row in pulls if stamp(row) >= since]
open_issues = [row for row in issues if row.get("state") == "open" and "standup" not in labels(row)]
open_pulls = [row for row in pulls if row.get("state") == "open"]

git_log = subprocess.run(
    [
        "git",
        "-C",
        str(root),
        "log",
        "refs/remotes/github/main",
        f"--since={since.isoformat()}",
        "--pretty=format:- `%h` %s",
    ],
    text=True,
    capture_output=True,
    check=False,
).stdout.strip()

lines = [
    f"# Daily standup - {now:%Y-%m-%d}",
    "",
    f"Activity window: last {hours} hours, from {since:%Y-%m-%dT%H:%M:%SZ}.",
    "",
    "## Recently updated pull requests",
    "",
]
lines.extend(bullet(row, "PR") for row in recent_pulls)
if not recent_pulls:
    lines.append("- (none in this window)")
lines.extend(["", "## Recently updated issues", ""])
lines.extend(bullet(row, "issue") for row in recent_issues)
if not recent_issues:
    lines.append("- (none in this window)")
lines.extend(["", "## Current open work", ""])
lines.append(f"- Open issues: {len(open_issues)}")
lines.append(f"- Open pull requests: {len(open_pulls)}")
lines.extend(["", "## Commits on GitHub main", "", git_log or "- (none in this window)", ""])
lines.append("Generated from live paginated GitHub reads; this report is not lifecycle authority.")
lines.append("")

path = destination / f"{now:%Y-%m-%d}.md"
fd, temporary = tempfile.mkstemp(dir=destination, prefix=path.name + ".", suffix=".tmp")
with os.fdopen(fd, "w", encoding="utf-8") as stream:
    stream.write("\n".join(lines))
    stream.flush()
    os.fsync(stream.fileno())
os.replace(temporary, path)
print(f"wrote {path.relative_to(root)}")
PY
}

job_stale_audit() {
  local audit="$REPO_ROOT/scripts/audit_stale_issues.py"
  local exporter="$SCRIPT_DIR/export_issues.py"
  require_file "$audit" "stale-issue audit is required"
  require_file "$exporter" "GitHub issue exporter is required"
  mkdir -p "$REPORT_DIR" "$CACHE_ROOT"
  local feed="$CACHE_ROOT/open-github-issues.json"
  python3 "$exporter" --repo-root "$REPO_ROOT" --state open --output "$feed"
  python3 "$audit" --issues "$feed" --repo-root "$REPO_ROOT" \
    --format json --output "$REPORT_DIR/stale-issue-audit.json"
  python3 "$audit" --issues "$feed" --repo-root "$REPO_ROOT" \
    --format text --output "$REPORT_DIR/stale-issue-audit.txt"
  note "stale-audit: report-only output is under $REPORT_DIR"
}

internal_lean_build() {
  local log_file="$1"
  cd "$REPO_ROOT"
  { lake exe cache get; lake build -q --log-level=info; } 2>&1 | tee "$log_file" || true
}

release_build_lock() {
  if [ -n "$BUILD_LOCK_PATH" ]; then
    python3 "$SCRIPT_DIR/runtime_lock.py" release-owned \
      "$BUILD_LOCK_PATH" "$BUILD_LOCK_IDENTITY" "$BUILD_LOCK_PID" \
      "$BUILD_LOCK_TOKEN" "$BUILD_LOCK_DIGEST" >/dev/null 2>&1 || true
    BUILD_LOCK_PATH=""
  fi
}

cleanup() {
  release_build_lock
}

trap cleanup EXIT
trap 'exit 130' INT
trap 'exit 143' TERM

job_linter_sweep() {
  local reporter="$REPO_ROOT/scripts/lean_linter_warning_report.py"
  require_file "$reporter" "linter warning reporter is required"
  command -v lake >/dev/null 2>&1 || die "lake is required for linter-sweep"
  mkdir -p "$REPORT_DIR" "$LOG_DIR"
  local log_file="$LOG_DIR/lean-build-$(timestamp).log"
  local build_lock="${MIPSTARRE_FULL_BUILD_LOCK:-$CACHE_ROOT/.full-build-lock}"
  local token result state identity holder observed_token digest detail rc=0
  token="$(python3 "$SCRIPT_DIR/runtime_lock.py" new-token)" || \
    die "could not allocate a full-build lock token"
  result="$(python3 "$SCRIPT_DIR/runtime_lock.py" acquire "$build_lock" \
    "$$" "$token" "housekeeping.sh linter-sweep")" || rc=$?
  IFS='|' read -r state identity holder observed_token digest detail <<EOF
$result
EOF
  [ "$rc" -eq 0 ] && [ "$state" = acquired ] || \
    die "full-build lock is unavailable: $build_lock (${state:-error}: ${detail:-unknown})"
  BUILD_LOCK_PATH="$build_lock"
  BUILD_LOCK_IDENTITY="$identity"
  BUILD_LOCK_PID="$holder"
  BUILD_LOCK_TOKEN="$observed_token"
  BUILD_LOCK_DIGEST="$digest"
  internal_lean_build "$log_file"
  python3 "$reporter" --log "$log_file" \
    --json "$REPORT_DIR/lean-linter-warnings.json" \
    --text "$REPORT_DIR/lean-linter-warnings.txt"
  release_build_lock
}

job_readme_freshness() {
  local audit="$REPO_ROOT/scripts/audit_readme_freshness.py"
  require_file "$audit" "README freshness audit is required"
  mkdir -p "$REPORT_DIR"
  python3 "$audit" --root "$REPO_ROOT" --readme "$REPO_ROOT/README.md" \
    --format json --output "$REPORT_DIR/readme-freshness.json"
  python3 "$audit" --root "$REPO_ROOT" --readme "$REPO_ROOT/README.md" \
    --format text --output "$REPORT_DIR/readme-freshness.txt"
}

dispatch_job() {
  local job="$1"
  if [ "${MIPSTARRE_HK_LOCKED:-}" = "$job" ]; then
    "job_${job//-/_}"
    return
  fi
  MIPSTARRE_HK_LOCKED="$job" run_locked "$LOCK_DIR/housekeeping-$job.lock" \
    "$SCRIPT_DIR/housekeeping.sh" "$job"
}

main() {
  [ "$#" -eq 1 ] || { usage; exit 2; }
  case "$1" in
    -h|--help|help) usage ;;
    standup|stale-audit|linter-sweep|readme-freshness) dispatch_job "$1" ;;
    all)
      local failed=""
      local job
      for job in standup stale-audit readme-freshness; do
        dispatch_job "$job" || failed="$failed $job"
      done
      [ -z "$failed" ] || die "failed job(s):$failed"
      ;;
    *) die "unknown job: $1" ;;
  esac
}

main "$@"
