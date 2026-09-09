#!/usr/bin/env bash
# status-snapshot.sh — the operator's one-screen picture of track A on ghz (owner session, 2026-09-05).
# Usage: bash results/telemetry/owner-tools/status-snapshot.sh [--prs]   (--prs adds the per-PR verdict table; slower)
# Run it at the start of every operator cycle; act on every line that names something actionable:
#   workers far below the slots, a PR with unresolved findings and no loop, a failed marker, a needs-attention lane,
#   a stack child whose base merged, a ready packet without a lane.
export PATH="$HOME/.local/bin:$PATH"
S="$HOME/.cache/mipstarre-dev/watchdog"; L="$S/lanes"; ROOT="$HOME/MIPStarRE-qpbt"
cd "$ROOT" || exit 1
echo "== $(date -u +%FT%TZ) load $(cut -d' ' -f1 /proc/loadavg) | main $(git rev-parse --short github/main 2>/dev/null) | max-codex $(cat "$S/max-codex" 2>/dev/null)"
live=0; declare -A byhome
for p in $(pgrep -f "^node [^ ]*codex(\.js)?( |$).* exec( |$)" 2>/dev/null); do
  h=$(tr '\0' '\n' < "/proc/$p/environ" 2>/dev/null | sed -n 's/^CODEX_HOME=//p' | head -1); h="${h:-$HOME/.codex}"
  byhome[$h]=$(( ${byhome[$h]:-0} + 1 )); live=$((live+1))
done
echo "== workers: $live live codex exec sessions (the shim puts -m/-c before exec) ($(for h in "${!byhome[@]}"; do printf '%s=%s ' "$(basename "$h")" "${byhome[$h]}"; done))"
echo "== lanes: $(pgrep -af '^bash /tmp/lane-v1[3-7].sh' | awk '{print $4}' | sort -n | uniq | tr '\n' ' ')| autofix: $(pgrep -fa 'autofix.sh' | grep -o 'autofix.sh [0-9]*' | awk '{print $2}' | sort -u | tr '\n' ' ')"
echo "== needs-attention: $(ls "$L" | grep -E '^[0-9]+\.needs-attention$' | sed 's/\.needs-attention//' | tr '\n' ' ')| daemon failed markers: $(ls "$S/daemon" 2>/dev/null | grep -E '^pr[0-9]+\.failed$' | tr '\n' ' ')"
echo "== daemon (last 3, newest log):"; tail -n 3 "$(ls -t "$L"/daemon*.log 2>/dev/null | head -1)" 2>/dev/null | cut -c1-140
echo "== stacks (child:slug:base):"; sed 's/^/   /' "$L/stacks" 2>/dev/null
echo "== ready packets:"; timeout 60 python3 local/bin/ready_packets.py 2>/dev/null | sed -n '2,12p' | cut -c1-120 || echo "   (ready_packets timed out)"
if [ "${1:-}" = "--prs" ]; then
  echo "== open PRs (latest local review):"
  for p in $(timeout 30 gh pr list --state open --limit 100 --json number --jq '.[].number' | sort -n); do
    b=$(timeout 20 gh api "repos/Dengnifer/MIPStarRE-A/pulls/$p/reviews" --jq '[.[] | select(.body|test("mipstarre-review"))] | last | .body' 2>/dev/null)
    if [ -z "$b" ] || [ "$b" = "null" ]; then echo "   PR $p: no local review yet"; continue; fi
    v=$(printf '%s' "$b" | grep -m1 '^VERDICT' | cut -c10-72); u=$(printf '%s' "$b" | grep -c '^- \[ \]')
    loop=""; pgrep -f "autofix.sh $p " >/dev/null && loop=" [autofix running]"
    echo "   PR $p: $v unresolved=$u$loop"
  done
fi
echo "== #26 open blockers: $(timeout 20 gh issue view 26 --json comments --jq '[.comments[] | select(.body|test("owner-inbox id=B[0-9]+ status=open"))] | length' 2>/dev/null)"
