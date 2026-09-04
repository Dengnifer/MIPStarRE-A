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
cd "$HOME/MIPStarRE-qpbt" || exit 1
git fetch -q github
count_at() { git ls-tree -r --name-only "$1" -- MIPStarRE/QPBT | grep '\.lean$' | while read -r f; do git show "$1:$f" | grep -c 'sorry'; done | awk '{s+=$1} END {print s+0}'; }
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
  git diff -U0 "github/main...FETCH_HEAD" -- 'MIPStarRE/QPBT/*.lean' 2>/dev/null | awk '/^--- a\//{f=$2} /^-.*sorry/{print f":"$0}' >> /tmp/estimate-removed.txt
done
INPR=$(sort -u /tmp/estimate-removed.txt | wc -l)
TS=$(date -u +"%Y-%m-%d %H:%MZ"); MAIN=$(git rev-parse --short github/main)
ISSUE=$(cat "$HOME/.cache/mipstarre-dev/watchdog/estimate-issue" 2>/dev/null)
printf '%s\n' "**$TS — implemented ≈ ${PCT}% · days to go ≈ $DAYS**" "<sub>$NOW of $DENOM sites open on main ($MAIN); $INPR proved in open PRs; trailing-24h rate $RATE sites/day.</sub>" > /tmp/estimate-body.md
[ -n "$ISSUE" ] && gh api "repos/Dengnifer/MIPStarRE-A/issues/$ISSUE/comments" -F body=@/tmp/estimate-body.md --jq .html_url
printf '{"ts":"%s","main":"%s","denominator":%s,"open_sites":%s,"closed_sites":%s,"percent":%s,"open_sites_24h_ago":%s,"rate_per_day":%s,"days_to_go":"%s","sites_in_open_prs_dedup":%s}\n' "$(date -u +%FT%TZ)" "$MAIN" "$DENOM" "$NOW" "$CLOSED" "$PCT" "$PREV" "$RATE" "$DAYS" "$INPR" >> results/telemetry/estimates.jsonl
echo "estimate posted: ${PCT}% / $DAYS days ($NOW open, rate $RATE/day, $INPR in PRs)"
