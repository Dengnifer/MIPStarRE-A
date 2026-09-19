#!/usr/bin/env bash
# estimate.sh — 8-hourly completion estimate for track A (owner request 2026-09-04).
# Posts ONE two-line comment on the pinned "Completion estimate" issue and appends a JSON line
# to results/telemetry/estimates.jsonl. Method (count-based): 197 stage-4.3 obligations at the
# start (171 on main at takeover + 26 in the chapter-16 skeleton); implemented% = closed/197;
# days-to-go = open sites / sites closed on main in the trailing 24 h (lower bound: the
# remaining sites are the harder ones). Sites proved in open PRs are deduplicated across
# stacked PRs.
set -u
export PATH="$HOME/.local/bin:$PATH"

# --- real sorry-site rule (issue #168) -------------------------------------
# Count only lines that carry an actual `sorry` tactic/term.  An unanchored
# `grep -c sorry` also matches prose: MIPStarRE/QPBT/Games/StrategyClasses.lean
# and MIPStarRE/QPBT/Combining/Apply.lean each explain their hole in a
# docstring, so the open-obligation number posted on the tracker issue used to
# be larger than the number of real sites.
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

cd "$HOME/MIPStarRE-qpbt" || exit 1
git fetch -q github
count_at() { git ls-tree -r --name-only "$1" -- MIPStarRE/QPBT | grep '\.lean$' | while read -r f; do git show "$1:$f" | count_sorry_sites; done | awk '{s+=$1} END {print s+0}'; }
DENOM=197
NOW=$(count_at github/main)
PREV_REF=$(git rev-list -1 --before="24 hours ago" github/main)
PREV=$(count_at "$PREV_REF")
CLOSED=$((DENOM - NOW)); PCT=$((CLOSED * 100 / DENOM))
RATE=$((PREV - NOW))
if [ "$RATE" -gt 0 ]; then DAYS=$(python3 -c "print(round($NOW/$RATE,1))"); else DAYS="n/a"; fi
: > /tmp/estimate-removed.txt
for n in $(gh pr list --state open --limit 100 --json number --jq '.[].number'); do
  B=$(gh pr view "$n" --json headRefName --jq .headRefName); git fetch -q github "$B" 2>/dev/null || continue
  # Same anchored rule as count_sorry_sites: the cheap `sorry` match only
  # pre-filters, the removed line itself must be a real site.
  git diff -U0 "github/main...FETCH_HEAD" -- 'MIPStarRE/QPBT/*.lean' 2>/dev/null \
    | awk '/^--- a\//{f=$2; next} /^-.*sorry/{print f":"$0}' \
    | while IFS= read -r rec; do
        body=${rec#*:}
        [ "$(printf '%s\n' "${body#-}" | count_sorry_sites)" -gt 0 ] || continue
        printf '%s\n' "$rec"
      done >> /tmp/estimate-removed.txt
done
INPR=$(sort -u /tmp/estimate-removed.txt | wc -l)
TS=$(date -u +"%Y-%m-%d %H:%MZ"); MAIN=$(git rev-parse --short github/main)
ISSUE=$(cat "$HOME/.cache/mipstarre-dev/watchdog/estimate-issue" 2>/dev/null)

# --- total QPBT Lean code lines (owner request 2026-09-18) ------------------
# The owner asked that every update also say how big the QPBT development is.
# Counted with the SAME rule as the merge-title Lean delta
# (pr_merge.lean_code_line_mask: blank and comment-only lines do not count),
# through results/telemetry/owner-tools/lean-loc.py, which imports that rule
# rather than copying it.  Cosmetic by contract, like the merge-title delta:
# if the helper fails, the clause is dropped and the record keeps JSON nulls.
LEAN_LOC_PY=results/telemetry/owner-tools/lean-loc.py
LEAN_CLAUSE=""; LEAN_FILES=null; LEAN_CODE=null
if LEAN_LOC=$(python3 "$LEAN_LOC_PY" --rev github/main 2>/dev/null); then
  read -r LF LC _ <<< "$LEAN_LOC"
  case "$LF$LC" in
    ''|*[!0-9]*) ;;
    *) LEAN_FILES=$LF; LEAN_CODE=$LC
       CLAUSE=$(python3 "$LEAN_LOC_PY" --format-clause "$LF" "$LC" 2>/dev/null) || CLAUSE=""
       [ -n "$CLAUSE" ] && LEAN_CLAUSE="; $CLAUSE" ;;
  esac
fi
printf '%s\n' "**$TS — implemented ≈ ${PCT}% · days to go ≈ $DAYS**" "<sub>$NOW of $DENOM sites open on main ($MAIN); $INPR proved in open PRs; trailing-24h rate $RATE sites/day$LEAN_CLAUSE.</sub>" > /tmp/estimate-body.md
[ -n "$ISSUE" ] && gh api "repos/Dengnifer/MIPStarRE-A/issues/$ISSUE/comments" -F body=@/tmp/estimate-body.md --jq .html_url
printf '{"ts":"%s","main":"%s","denominator":%s,"open_sites":%s,"closed_sites":%s,"percent":%s,"open_sites_24h_ago":%s,"rate_per_day":%s,"days_to_go":"%s","sites_in_open_prs_dedup":%s,"lean_code_lines":%s,"lean_files":%s}\n' "$(date -u +%FT%TZ)" "$MAIN" "$DENOM" "$NOW" "$CLOSED" "$PCT" "$PREV" "$RATE" "$DAYS" "$INPR" "$LEAN_CODE" "$LEAN_FILES" >> results/telemetry/estimates.jsonl
echo "estimate posted: ${PCT}% / $DAYS days ($NOW open, rate $RATE/day, $INPR in PRs)"
