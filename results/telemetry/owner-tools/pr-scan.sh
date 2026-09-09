export PATH="$HOME/.local/bin:$PATH"
# pr-scan.sh — latest local review verdict for every open PR in ONE GraphQL call (fast even with 60 PRs).
cd /home/drx/MIPStarRE-qpbt
timeout 90 gh api graphql -f query='query { repository(owner:"Dengnifer", name:"MIPStarRE-A") { pullRequests(states:OPEN, first:60, orderBy:{field:UPDATED_AT, direction:DESC}) { nodes { number headRefName updatedAt reviews(last:6) { nodes { submittedAt body } } } } } }' > /tmp/prscan.json 2>/tmp/prscan.err || { echo "graphql failed: $(head -c 200 /tmp/prscan.err)"; exit 1; }
python3 - <<'PY'
import json,re
d=json.load(open("/tmp/prscan.json"))["data"]["repository"]["pullRequests"]["nodes"]
rows=[]
for pr in d:
    revs=[r for r in pr["reviews"]["nodes"] if "mipstarre-review" in (r["body"] or "")]
    if revs:
        r=revs[-1]; b=r["body"]
        v=re.search(r"^VERDICT: *(\S+)", b, re.M); v=v.group(1) if v else "?"
        u=len(re.findall(r"^- \[ \]", b, re.M)); t=r["submittedAt"][5:16]
    else: v="NO-LOCAL-REVIEW"; u=0; t="-"
    rows.append((pr["number"], pr["headRefName"][:44], v, u, t, pr["updatedAt"][5:16]))
for n,b,v,u,t,upd in sorted(rows): print(f"PR {n:<4} {b:<44} {v:<18} unresolved={u:<2} review@{t} upd@{upd}")
from collections import Counter; print("summary:", Counter(v for _,_,v,_,_,_ in rows))
PY
