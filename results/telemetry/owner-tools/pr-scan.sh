#!/usr/bin/env bash
# pr-scan.sh — the newest local review verdict for every open PR, in ONE GraphQL call
# (fast even with sixty PRs open).  Read-only; prints one line per PR plus a summary.
# Provenance: the origin's owner-tools/pr-scan.sh, which hard-coded the checkout path,
# the repository owner and name and wrote its scratch JSON to /tmp.
set -u
HERE="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd -P)"
CFG="$HERE/../../../local/bin/session/config.sh"
# shellcheck source=/dev/null
[ -f "$CFG" ] && . "$CFG" 2>/dev/null
ROOT="${KIT_REPO_ROOT:-$(cd "$HERE/../../.." && pwd -P)}"
export PATH="$HOME/.local/bin:$PATH"
cd "$ROOT" || exit 1

SLUG="${KIT_GITHUB_SLUG:-}"
case "$SLUG" in ""|OWNER/*) SLUG="$(git remote get-url github 2>/dev/null | sed -nE -e 's#^.*github\.com[:/]##p' | sed -E 's#\.git$##')";; esac
[ -n "$SLUG" ] || { echo "pr-scan: no GitHub repository (set project.github_slug in local/project.json)"; exit 2; }
OWNER="${SLUG%%/*}"; NAME="${SLUG##*/}"

OUT="${TMPDIR:-/tmp}/kit-prscan-$$.json"
trap 'rm -f "$OUT"' EXIT
timeout 90 gh api graphql -F owner="$OWNER" -F name="$NAME" -f query='
query($owner:String!, $name:String!) { repository(owner:$owner, name:$name) {
  pullRequests(states:OPEN, first:60, orderBy:{field:UPDATED_AT, direction:DESC}) {
    nodes { number headRefName updatedAt reviews(last:6) { nodes { submittedAt body } } } } } }' \
  > "$OUT" 2>"$OUT.err" || { echo "graphql failed: $(head -c 200 "$OUT.err")"; rm -f "$OUT.err"; exit 1; }
rm -f "$OUT.err"

python3 - "$OUT" <<'PY'
import json, re, sys
from collections import Counter
nodes = json.load(open(sys.argv[1]))["data"]["repository"]["pullRequests"]["nodes"]
rows = []
for pr in nodes:
    reviews = [r for r in pr["reviews"]["nodes"] if "mipstarre-review" in (r["body"] or "")]
    if reviews:
        body = reviews[-1]["body"]
        found = re.search(r"^VERDICT: *(\S+)", body, re.M)
        verdict = found.group(1) if found else "?"
        unresolved = len(re.findall(r"^- \[ \]", body, re.M))
        when = (reviews[-1]["submittedAt"] or "")[5:16]
    else:
        verdict, unresolved, when = "NO-LOCAL-REVIEW", 0, "-"
    rows.append((pr["number"], pr["headRefName"][:44], verdict, unresolved, when, pr["updatedAt"][5:16]))
for n, b, v, u, t, upd in sorted(rows):
    print(f"PR {n:<4} {b:<44} {v:<18} unresolved={u:<2} review@{t} upd@{upd}")
print("summary:", Counter(v for _, _, v, _, _, _ in rows))
PY
