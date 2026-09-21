#!/usr/bin/env bash
# status-snapshot.sh [--prs] — one screen: what is running, what is stuck, what is ready.
# The operating session runs this at the start of every turn and acts on every line that
# names something actionable: workers far below the slots, a PR with unresolved findings
# and no fix loop, a daemon failed marker, a lane that needs attention, a stack child
# whose base merged, a ready packet with no lane, an open blocker in the owner inbox.
# `--prs` adds the per-PR verdict table (slower: one API call per PR).
#
# It runs on a FRESH project too: the state directory, the daemon directory, the lane
# directory, gh and the GitHub remote may all be missing, and each missing piece prints
# "(none)" or "(not set up yet)" instead of an error.  It always exits 0 — a status
# screen that fails is a status screen nobody runs.
#
# Provenance: the origin's results/telemetry/owner-tools/status-snapshot.sh, which
# hard-coded one repository path, one cache directory, one repository slug, one issue
# number and the /tmp path of its lane runner.
set -u
HERE="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd -P)"
CFG="$HERE/../../../local/bin/session/config.sh"
# shellcheck source=/dev/null
[ -f "$CFG" ] && . "$CFG" 2>/dev/null
ROOT="${KIT_REPO_ROOT:-$(cd "$HERE/../../.." && pwd -P)}"
S="${KIT_STATE_DIR:-${KIT_CACHE_ROOT:-$HOME/.cache/paperlib-dev}/watchdog}"
L="$S/lanes"; D="$S/daemon"
SERVICE="$ROOT/local/bin/service"
export PATH="$HOME/.local/bin:$PATH"
cd "$ROOT" 2>/dev/null || { echo "status-snapshot: $ROOT is not readable"; exit 0; }

none() { [ -n "$1" ] && printf '%s' "$1" || printf '(none)'; }
SLUG="${KIT_GITHUB_SLUG:-}"
case "$SLUG" in ""|OWNER/*) SLUG="$(git remote get-url github 2>/dev/null | sed -nE -e 's#^.*github\.com[:/]##p' | sed -E 's#\.git$##')";; esac

MAIN_SHA="$(git rev-parse --short github/main 2>/dev/null || git rev-parse --short HEAD 2>/dev/null || echo '(no commit)')"
LOAD="$(cut -d' ' -f1 /proc/loadavg 2>/dev/null || echo '?')"
CAP="$(cat "$S/max-codex" 2>/dev/null || echo '(unset)')"
echo "== $(date -u +%FT%TZ) load $LOAD | main $MAIN_SHA | slots $CAP | repo ${SLUG:-(no GitHub remote yet)}"

if [ ! -d "$S" ]; then
  echo "== state: $S does not exist yet — no session, no lanes, no merge daemon are running."
  echo "== next: local/bin/service/keyrot-install.sh, then start the session (local/bin/session/)."
  exit 0
fi

# workers, grouped by the CODEX_HOME they run on (the rotation shim picks it)
live=0; homes=""
for p in $(pgrep -f "^node [^ ]*codex(\.js)?( |$).* exec( |$)" 2>/dev/null); do
  h=$(tr '\0' '\n' < "/proc/$p/environ" 2>/dev/null | sed -n 's/^CODEX_HOME=//p' | head -1)
  homes="$homes $(basename "${h:-default}")"; live=$((live+1))
done
echo "== workers: $live live session(s)$( [ -n "$homes" ] && echo " ($(echo "$homes" | tr ' ' '\n' | sort | uniq -c | tr '\n' ' '))" )"

LANES=$(pgrep -af "^bash $SERVICE/lan[e].sh" 2>/dev/null | awk '{print $4}' | sort -n | uniq | tr '\n' ' ')
FIX=$(pgrep -fa 'autofix[.]sh' 2>/dev/null | grep -o 'autofix.sh [0-9]*' | awk '{print $2}' | sort -u | tr '\n' ' ')
echo "== lanes: $(none "$LANES")| fix loops: $(none "$FIX")"

ATT=$(ls "$L" 2>/dev/null | grep -E '^[0-9]+\.needs-attention$' | sed 's/\.needs-attention//' | tr '\n' ' ')
FAILED=$(ls "$D" 2>/dev/null | grep -E '^pr[0-9]+\.failed$' | tr '\n' ' ')
echo "== needs attention: $(none "$ATT")| daemon failed markers: $(none "$FAILED")"

DPID=$(cat "$D/daemon.pid" 2>/dev/null || true)
if [ -n "$DPID" ] && kill -0 "$DPID" 2>/dev/null; then DSTATE="running (pid $DPID)"
elif [ -e "$D/stop" ]; then DSTATE="stopped on purpose (stop file)"
elif [ -e "$D/train-approved.running.json" ]; then DSTATE="DOWN after a refused train — run local/bin/service/train-recover.sh"
else DSTATE="not running"; fi
echo "== merge daemon: $DSTATE"
NEWEST="$(ls -t "$L"/*daemon*.log 2>/dev/null | head -1)"
[ -n "$NEWEST" ] && tail -n 3 "$NEWEST" 2>/dev/null | cut -c1-140 | sed 's/^/   /'

if [ -s "$L/stacks" ]; then echo "== stacks (child:slug:base):"; sed 's/^/   /' "$L/stacks"; fi

echo "== ready packets:"
if [ -x local/bin/ready_packets.py ] || [ -f local/bin/ready_packets.py ]; then
  timeout 60 python3 local/bin/ready_packets.py 2>/dev/null | sed -n '2,12p' | cut -c1-120 | sed 's/^/   /' \
    || echo "   (ready_packets did not answer)"
else
  echo "   (local/bin/ready_packets.py not present)"
fi

if [ -n "$SLUG" ] && command -v gh >/dev/null 2>&1; then
  if [ "${1:-}" = "--prs" ]; then
    echo "== open PRs (newest local review):"
    for p in $(timeout 30 gh pr list --repo "$SLUG" --state open --limit 100 --json number --jq '.[].number' 2>/dev/null | sort -n); do
      b=$(timeout 20 gh api "repos/$SLUG/pulls/$p/reviews" --jq '[.[] | select(.body|test("mipstarre-review"))] | last | .body' 2>/dev/null)
      if [ -z "$b" ] || [ "$b" = "null" ]; then echo "   PR $p: no local review yet"; continue; fi
      v=$(printf '%s' "$b" | grep -m1 '^VERDICT' | cut -c10-72); u=$(printf '%s' "$b" | grep -c '^- \[ \]')
      loop=""; pgrep -f "autofix[.]sh $p " >/dev/null && loop=" [fix loop running]"
      echo "   PR $p: $v unresolved=$u$loop"
    done
  fi
  if [ -n "${KIT_OWNER_INBOX_ISSUE:-}" ]; then
    n=$(timeout 20 gh issue view "$KIT_OWNER_INBOX_ISSUE" --repo "$SLUG" --json comments \
        --jq '[.comments[] | select(.body|test("owner-inbox id=B[0-9]+ status=open"))] | length' 2>/dev/null)
    echo "== owner inbox (#$KIT_OWNER_INBOX_ISSUE) open blockers: ${n:-?}"
  else
    echo "== owner inbox: not configured yet (issues.owner_inbox in local/project.json)"
  fi
  [ -n "${KIT_PROGRESS_ISSUE:-}" ] && echo "== progress issue: #$KIT_PROGRESS_ISSUE" \
    || echo "== progress issue: not configured yet (issues.progress in local/project.json)"
else
  echo "== GitHub: no slug or no gh CLI — PR and issue lines skipped"
fi
exit 0
