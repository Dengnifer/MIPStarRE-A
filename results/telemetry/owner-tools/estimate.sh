#!/usr/bin/env bash
# estimate.sh — the periodic completion estimate (run it every few hours from cron).
# Posts ONE two-line comment on the progress issue and appends a JSON row to
# results/telemetry/estimates.jsonl.  Method (count-based): a fixed denominator of proof
# obligations, implemented% = closed/denominator, days-to-go = open sites divided by the
# sites closed on the integration branch in the trailing 24 h (a lower bound: the
# remaining sites are the harder ones).  Sites proved in open PRs are deduplicated across
# stacked PRs.
#
# The denominator is the baseline number of open sites.  It is read from
# <state>/estimate-denominator; on the first run the current count is written there, so a
# fresh project starts at 0% and needs no hand-editing.  The issue to post on is
# <state>/estimate-issue, else the configured progress issue.
#
# Provenance: the origin's owner-tools/estimate.sh (checkout path, library path, a
# denominator of 197 and the repository slug hard-coded).  The SORRY_SITE_RE assignment
# below is read verbatim by scripts/completion_gate.py — keep its shape (one line,
# single quotes) or the gate refuses to restate the rule in a second place.
set -u

# --- the real sorry-site rule ----------------------------------------------
# Count only lines that carry an actual `sorry` tactic/term.  An unanchored
# `grep -c sorry` also matches prose: a file that explains its hole in a
# docstring used to inflate the open-obligation number on the tracker issue.
#
# Source of truth for "does this line still hold a sorry": the comment-stripping
# rule of scripts/audit_stale_issues.py (`line_is_sorry` with `_SORRY_LINE_RE`),
# which drops `--` line comments before matching.  This script scans whole files
# instead of issue-cited lines, so it additionally anchors the token to the
# tactic/term positions it can occupy: a bare `sorry` line (optionally after a
# `·` bullet), `:= sorry`, `by sorry`, and `(sorry)`.  Keep the two in sync.
SORRY_SITE_RE='^[[:space:]]*(·[[:space:]]*)?sorry[[:space:]]*$|:=[[:space:]]*sorry[[:space:]]*\)?[[:space:]]*$|(^|[[:space:]])by[[:space:]]+sorry[[:space:]]*\)?[[:space:]]*$|\(sorry\)'

# Reads Lean source on stdin, prints the number of real sorry sites.
count_sorry_sites() { sed 's/--.*$//' | grep -c -E "$SORRY_SITE_RE"; }

# Offline entry point used by scripts/tests/test_estimate_sorry_count.py: print
# the site count of the given files and exit without touching git, gh, or the
# telemetry log.  The normal run below is unaffected.
if [ "${1:-}" = "--count-sorry-sites" ]; then
  shift
  total=0
  for f in "$@"; do total=$((total + $(count_sorry_sites < "$f"))); done
  echo "$total"
  exit 0
fi

HERE="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd -P)"
CFG="$HERE/../../../local/bin/session/config.sh"
# shellcheck source=/dev/null
[ -f "$CFG" ] && . "$CFG" 2>/dev/null
ROOT="${KIT_REPO_ROOT:-$(cd "$HERE/../../.." && pwd -P)}"
S="${KIT_STATE_DIR:-${KIT_CACHE_ROOT:-$HOME/.cache/paperlib-dev}/watchdog}"
LEAN_ROOT="${KIT_LEAN_ROOT:-PaperLib}"
BASE="${KIT_BASE_BRANCH:-main}"
export PATH="$HOME/.local/bin:$PATH"
cd "$ROOT" || exit 1
SLUG="${KIT_GITHUB_SLUG:-}"
case "$SLUG" in ""|OWNER/*) SLUG="$(git remote get-url github 2>/dev/null | sed -nE -e 's#^.*github\.com[:/]##p' | sed -E 's#\.git$##')";; esac

git fetch -q github
count_at() { git ls-tree -r --name-only "$1" -- "$LEAN_ROOT" | grep '\.lean$' \
  | while read -r f; do git show "$1:$f" | count_sorry_sites; done | awk '{s+=$1} END {print s+0}'; }

NOW=$(count_at "github/$BASE")
mkdir -p "$S"
DENOM=$(cat "$S/estimate-denominator" 2>/dev/null || true)
case "$DENOM" in ''|*[!0-9]*) DENOM=$NOW; echo "$DENOM" > "$S/estimate-denominator"; esac
[ "$DENOM" -gt 0 ] || DENOM=1
PREV_REF=$(git rev-list -1 --before="24 hours ago" "github/$BASE")
PREV=$([ -n "$PREV_REF" ] && count_at "$PREV_REF" || echo "$NOW")
CLOSED=$((DENOM - NOW)); [ "$CLOSED" -lt 0 ] && CLOSED=0
PCT=$((CLOSED * 100 / DENOM))
RATE=$((PREV - NOW))
if [ "$RATE" -gt 0 ]; then DAYS=$(python3 -c "print(round($NOW/$RATE,1))"); else DAYS="n/a"; fi

REMOVED="$S/estimate-removed.txt"; : > "$REMOVED"
if [ -n "$SLUG" ]; then
  for n in $(gh pr list --repo "$SLUG" --state open --limit 100 --json number --jq '.[].number'); do
    B=$(gh pr view "$n" --repo "$SLUG" --json headRefName --jq .headRefName)
    git fetch -q github "$B" 2>/dev/null || continue
    # Same anchored rule as count_sorry_sites: the cheap `sorry` match only
    # pre-filters, the removed line itself must be a real site.
    git diff -U0 "github/$BASE...FETCH_HEAD" -- "$LEAN_ROOT/*.lean" 2>/dev/null \
      | awk '/^--- a\//{f=$2; next} /^-.*sorry/{print f":"$0}' \
      | while IFS= read -r rec; do
          body=${rec#*:}
          [ "$(printf '%s\n' "${body#-}" | count_sorry_sites)" -gt 0 ] || continue
          printf '%s\n' "$rec"
        done >> "$REMOVED"
  done
fi
INPR=$(sort -u "$REMOVED" | wc -l)
TS=$(date -u +"%Y-%m-%d %H:%MZ"); MAIN=$(git rev-parse --short "github/$BASE")
ISSUE=$(cat "$S/estimate-issue" 2>/dev/null || echo "${KIT_PROGRESS_ISSUE:-}")

# --- total Lean code lines --------------------------------------------------
# Counted with the SAME rule as the merge-title Lean delta
# (pr_merge.lean_code_line_mask: blank and comment-only lines do not count),
# through results/telemetry/owner-tools/lean-loc.py, which imports that rule
# rather than copying it.  Cosmetic by contract, like the merge-title delta:
# if the helper fails, the clause is dropped and the record keeps JSON nulls.
LEAN_LOC_PY=results/telemetry/owner-tools/lean-loc.py
LEAN_CLAUSE=""; LEAN_FILES=null; LEAN_CODE=null
if LEAN_LOC=$(python3 "$LEAN_LOC_PY" --rev "github/$BASE" 2>/dev/null); then
  read -r LF LC _ <<< "$LEAN_LOC"
  case "$LF$LC" in
    ''|*[!0-9]*) ;;
    *) LEAN_FILES=$LF; LEAN_CODE=$LC
       CLAUSE=$(python3 "$LEAN_LOC_PY" --format-clause "$LF" "$LC" 2>/dev/null) || CLAUSE=""
       [ -n "$CLAUSE" ] && LEAN_CLAUSE="; $CLAUSE" ;;
  esac
fi

BODY="$S/estimate-body.md"
printf '%s\n' "**$TS — implemented ≈ ${PCT}% · days to go ≈ $DAYS**" \
  "<sub>$NOW of $DENOM sites open on $BASE ($MAIN); $INPR proved in open PRs; trailing-24h rate $RATE sites/day$LEAN_CLAUSE.</sub>" > "$BODY"
[ -n "$ISSUE" ] && [ -n "$SLUG" ] && gh api "repos/$SLUG/issues/$ISSUE/comments" -F body=@"$BODY" --jq .html_url
printf '{"ts":"%s","main":"%s","denominator":%s,"open_sites":%s,"closed_sites":%s,"percent":%s,"open_sites_24h_ago":%s,"rate_per_day":%s,"days_to_go":"%s","sites_in_open_prs_dedup":%s,"lean_code_lines":%s,"lean_files":%s}\n' \
  "$(date -u +%FT%TZ)" "$MAIN" "$DENOM" "$NOW" "$CLOSED" "$PCT" "$PREV" "$RATE" "$DAYS" "$INPR" "$LEAN_CODE" "$LEAN_FILES" \
  >> results/telemetry/estimates.jsonl
echo "estimate: ${PCT}% / $DAYS days ($NOW open of $DENOM, rate $RATE/day, $INPR in PRs)"
