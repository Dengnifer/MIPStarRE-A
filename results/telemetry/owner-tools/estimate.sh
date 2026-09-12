#!/usr/bin/env bash
# estimate.sh — the owner's completion estimate for track A (owner request 2026-09-04).
#
# Posts ONE two-line comment on the estimate issue and appends a row to
# results/telemetry/estimates.jsonl.  Method, unchanged so the series stays comparable:
# 197 stage-4.3 obligations at the start (171 on main at takeover + 26 in the chapter-16
# skeleton); implemented% = closed/197; days-to-go = open sites / sites closed on main in
# the trailing 24 h (a lower bound: the remaining sites are the harder ones).  Sites proved
# in open PRs are deduplicated across stacked PRs.
#
# What changed for the 30-minute cadence of fast mode (design §8 W4).  The 2026-09-12
# version took minutes and left the primary checkout dirty:
#   - open PRs came from `gh pr list` + up to 100 `gh pr view` calls.  They now come from
#     the committed read-only snapshot results/telemetry/github-snapshot/open-pulls.json
#     (gh_common.py snapshot writes it after every publish), and the in-PR count is
#     LABELLED as snapshot-derived with the snapshot's age.
#   - the per-branch fetch and diff ran in the primary checkout, clobbering its FETCH_HEAD
#     while checked-push.sh was using it.  They now run in a throwaway worktree under the
#     cache root, which has its own FETCH_HEAD and is removed afterwards.
#   - the 24-h-ago site count walked every Lean file on a 24-hour-old commit every run.  It
#     is now cached for the whole clock hour.
#   - the whole run is wrapped in `timeout`, and the body is rendered by
#     local/bin/estimate_post.py, the single writer of the estimate issue.
#
# Usage: estimate.sh [--dry-run] [--no-timeout]
# Exit codes: 0 posted · 2 usage · 3 no estimate issue in run-mode · 4 the snapshot is
#             missing · 124 the timeout fired (cron logs it; the next tick retries)
set -u

PROG="estimate.sh"
CACHE_ROOT="${MIPSTARRE_CACHE_ROOT:-$HOME/.cache/mipstarre-dev}"
W="$CACHE_ROOT/watchdog"
OWNER_BIN="${MIPSTARRE_OWNER_BIN:-$CACHE_ROOT/owner-bin}"
TIMEOUT_S="${MIPSTARRE_ESTIMATE_TIMEOUT:-600}"
DENOM=197

DRY=0; NO_TIMEOUT=0
for a in "$@"; do
  case "$a" in
    --dry-run) DRY=1 ;;
    --no-timeout) NO_TIMEOUT=1 ;;
    -h|--help) sed -n '2,30p' "$0" | sed 's/^# \{0,1\}//'; exit 0 ;;
    *) echo "$PROG: unknown argument '$a'" >&2; exit 2 ;;
  esac
done

export PATH="$OWNER_BIN:$HOME/.local/bin:$HOME/.elan/bin:$PATH"

ROOT="${MIPSTARRE_REPO_ROOT:-}"
if [ -z "$ROOT" ] && [ -r "$OWNER_BIN/repo-root" ]; then ROOT="$(cat "$OWNER_BIN/repo-root")"; fi
if [ -z "$ROOT" ]; then ROOT="$HOME/MIPStarRE-qpbt"; fi
RUN_MODE="${MIPSTARRE_RUN_MODE:-$ROOT/local/bin/run_mode.py}"
POST="${MIPSTARRE_ESTIMATE_POST:-$ROOT/local/bin/estimate_post.py}"

# One timeout around the whole run, re-entered once (before the banner, so a cron log gets
# exactly one "tool=" line).  A tick that hangs must not stack up with the next one: the
# cadence is 30 minutes in fast mode.
if [ "$NO_TIMEOUT" -eq 0 ] && command -v timeout >/dev/null 2>&1; then
  if [ "$DRY" -eq 1 ]; then exec timeout "$TIMEOUT_S" bash "$0" --no-timeout --dry-run
  else exec timeout "$TIMEOUT_S" bash "$0" --no-timeout; fi
fi

VERSION="$(sed -n 's/^short=//p' "$OWNER_BIN/tools-version" 2>/dev/null | head -n 1)"
echo "tool=$PROG version=${VERSION:-unreleased}"

cd "$ROOT" || { echo "$PROG: cannot enter $ROOT" >&2; exit 2; }

ISSUE="$(python3 "$RUN_MODE" get estimate_issue 2>/dev/null | head -n 1 | tr -d '\r')" || ISSUE=""
if [ -z "$ISSUE" ]; then
  # never silently no-op the owner's only progress channel (the 2026-09-12 script did
  # exactly that when watchdog/estimate-issue was missing)
  echo "$PROG: run_mode.py get estimate_issue produced nothing; the estimate is NOT posted." >&2
  echo "$PROG: fix the run brief (run.estimate_issue) and re-run." >&2
  exit 3
fi

git fetch -q github || echo "$PROG: git fetch failed; using the refs on disk" >&2
MAIN="$(git rev-parse --short github/main)"

count_at() { # open `sorry` sites in the QPBT tree at a ref
  git ls-tree -r --name-only "$1" -- MIPStarRE/QPBT | grep '\.lean$' | while read -r f; do
    git show "$1:$f" | grep -c 'sorry'
  done | awk '{ s += $1 } END { print s + 0 }'
}

NOW="$(count_at github/main)"

# --- the 24-h-ago count, cached for the clock hour ------------------------------------------
mkdir -p "$W"
HOUR="$(date -u +%Y%m%d%H)"
PREV_CACHE="$W/estimate-prev.$HOUR"
if [ -s "$PREV_CACHE" ]; then
  PREV="$(cat "$PREV_CACHE")"
  echo "$PROG: 24h-ago count $PREV from the hourly cache"
else
  PREV_REF="$(git rev-list -1 --before='24 hours ago' github/main)"
  if [ -n "$PREV_REF" ]; then PREV="$(count_at "$PREV_REF")"; else PREV="$NOW"; fi
  printf '%s\n' "$PREV" > "$PREV_CACHE"
  find "$W" -maxdepth 1 -name 'estimate-prev.*' ! -name "estimate-prev.$HOUR" -delete 2>/dev/null || true
fi

CLOSED=$((DENOM - NOW)); PCT=$((CLOSED * 100 / DENOM))
RATE=$((PREV - NOW))
if [ "$RATE" -gt 0 ]; then DAYS="$(python3 -c "print(round($NOW / $RATE, 1))")"; else DAYS="n/a"; fi

# --- sites proved in open PRs, from the committed snapshot, diffed in a throwaway worktree ---
SNAP_DIR="$ROOT/results/telemetry/github-snapshot"
SNAP="$SNAP_DIR/open-pulls.json"
if [ ! -r "$SNAP" ]; then
  echo "$PROG: no $SNAP; run local/bin/github-sync.sh (it writes the read-only snapshot)." >&2
  exit 4
fi
SNAP_AT="$(python3 -c '
import json, sys
try: print(json.load(open(sys.argv[1], encoding="utf-8")).get("generated", "unknown"))
except Exception: print("unknown")' "$SNAP_DIR/metadata.json" 2>/dev/null || echo unknown)"
BRANCHES="$(python3 -c '
import json, sys
pulls = json.load(open(sys.argv[1], encoding="utf-8"))
seen = []
for pr in pulls:
    ref = ((pr.get("head") or {}).get("ref") or "").strip()
    if ref and ref not in seen and all(c.isalnum() or c in "._/-" for c in ref):
        seen.append(ref)
print("\n".join(seen))' "$SNAP")"
NPR="$(printf '%s\n' "$BRANCHES" | grep -c . || true)"

WT="$CACHE_ROOT/estimate-worktree"
REMOVED="$CACHE_ROOT/estimate-removed.$$"
: > "$REMOVED"
cleanup() {
  rm -f "$REMOVED"
  git worktree remove --force "$WT" >/dev/null 2>&1 || true
  git worktree prune >/dev/null 2>&1 || true
}
trap cleanup EXIT
git worktree remove --force "$WT" >/dev/null 2>&1 || true
if git worktree add --detach "$WT" github/main >/dev/null 2>&1; then
  while IFS= read -r B; do
    [ -n "$B" ] || continue
    git -C "$WT" fetch -q github "$B" 2>/dev/null || continue
    git -C "$WT" diff -U0 'github/main...FETCH_HEAD' -- 'MIPStarRE/QPBT/*.lean' 2>/dev/null |
      awk '/^--- a\//{ f = $2 } /^-.*sorry/{ print f":"$0 }' >> "$REMOVED"
  done <<EOF
$BRANCHES
EOF
  INPR="$(sort -u "$REMOVED" | grep -c . || true)"
else
  echo "$PROG: could not create the throwaway worktree $WT; in-PR count unavailable" >&2
  INPR=0
fi

TS="$(date -u +'%Y-%m-%d %H:%MZ')"
SUB="$NOW of $DENOM sites open on main ($MAIN); $INPR proved in $NPR open PRs (GitHub snapshot $SNAP_AT); trailing-24h rate $RATE sites/day."

# --- post: estimate_post.py renders the body and is the single writer of the issue ----------
if [ "$DRY" -eq 1 ]; then
  printf '**%s — implemented ≈ %s%% · days to go ≈ %s**\n<sub>%s</sub>\n' "$TS" "$PCT" "$DAYS" "$SUB"
  echo "$PROG: [dry-run] nothing posted, estimates.jsonl not appended"
  exit 0
fi
if [ -r "$POST" ]; then
  python3 "$POST" --issue "$ISSUE" --timestamp "$TS" --percent "$PCT" --days "$DAYS" \
    --open-sites "$NOW" --denominator "$DENOM" --main "$MAIN" --in-pr "$INPR" \
    --open-prs "$NPR" --in-pr-source "github-snapshot" --snapshot-generated "$SNAP_AT" \
    --rate "$RATE" || echo "$PROG: estimate_post.py failed; the row below is still recorded" >&2
else
  echo "$PROG: no estimate_post.py at $POST; the estimate is NOT posted." >&2
  echo "$PROG: body would have been: **$TS — implemented ≈ ${PCT}% · days to go ≈ $DAYS** / <sub>$SUB</sub>" >&2
fi

python3 - "$ROOT/results/telemetry/estimates.jsonl" "$MAIN" "$DENOM" "$NOW" "$CLOSED" "$PCT" \
  "$PREV" "$RATE" "$DAYS" "$INPR" "$NPR" "$SNAP_AT" <<'PY'
import datetime, json, sys
(path, main, denom, now, closed, pct, prev, rate, days, inpr, npr, snap_at) = sys.argv[1:13]
row = {
    "ts": datetime.datetime.now(datetime.timezone.utc).strftime("%Y-%m-%dT%H:%M:%SZ"),
    "main": main, "denominator": int(denom), "open_sites": int(now),
    "closed_sites": int(closed), "percent": int(pct), "open_sites_24h_ago": int(prev),
    "rate_per_day": int(rate), "days_to_go": days,
    "sites_in_open_prs_dedup": int(inpr), "open_prs": int(npr),
    "in_pr_source": "github-snapshot", "snapshot_generated": snap_at,
}
with open(path, "a", encoding="utf-8") as fh:
    fh.write(json.dumps(row) + "\n")
PY
echo "$PROG: ${PCT}% / $DAYS days ($NOW open, rate $RATE/day, $INPR in $NPR PRs, snapshot $SNAP_AT)"
