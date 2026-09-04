#!/usr/bin/env bash
# handback.sh — Mode 2 → Mode 1: the owner session returns the operator role to
# a codex main session. Records the hand-back in telemetry, posts #27, clears
# the owner-operator watchdog flag, relaunches codex via main-session.sh in
# tmux `qpbt` and pastes the briefing. Run only on the owner's explicit command.
set -u
export PATH="$HOME/.local/bin:$HOME/.elan/bin:$PATH"
cd "$HOME/MIPStarRE-qpbt" || exit 1
S=qpbt; TS=$(date +%Y-%m-%dT%H:%M:%S%z); TSZ=$(date -u +%FT%TZ)
STATE="$HOME/.cache/mipstarre-dev/watchdog"
OPEN=$(gh pr list --state open --json number --jq '[.[].number]|@csv')
cat >> results/telemetry/events.md <<EOF

## ${TSZ%T*} — Operator hand-back: codex main session resumes from the owner session

- **Trigger:** owner decision (${TSZ}). The owner's Claude session ran the
  operator loop since 2026-09-03 23:11Z (Mode 2); the codex main session now
  resumes (Mode 1) from \`~/.codex/prompts/goal.md\` plus the #27 log.
- **State at hand-back:** main at $(git rev-parse --short github/main); open PRs: ${OPEN:-none};
  lanes in flight are listed in the #27 hand-back report.
EOF
printf '{"ts": "%s", "stage": "operator", "event": "handback", "note": "%s"}\n' "$TS" \
  "owner session returns the operator role to the codex main session; main at $(git rev-parse --short github/main); open PRs ${OPEN:-none}" >> results/telemetry/stages.jsonl
cat >> results/telemetry/owner-log.md <<EOF

## ${TSZ%T*} — Hand-back to the codex main session (${TSZ})

Mode 2 ended on the owner's command; codex main relaunched via
\`local/bin/main-session.sh\` (full access, approval never); watchdog back to
pane mode. Open PRs at hand-back: ${OPEN:-none}.
EOF
git add results/telemetry && git commit -q -m "chore(telemetry): operator hand-back to the codex main session" && local/bin/github-sync.sh | tail -1
rm -f "$STATE/owner-operator"
printf '%s\n' "<!-- mipstarre-progress-$(date -u +%Y-%m-%d)-handback -->" "### $(date -u +%Y-%m-%d) - Hand-back to the codex main session" "" "**Merged:** see the previous reports." "" "**Dispatched:** open PRs ${OPEN:-none}; lane state under ~/.cache/mipstarre-dev/watchdog/lanes/ on ghz (markers *.done / *.needs-attention, logs per lane)." "" "**Next:** the codex main session continues the queue from the standing briefing." "" "**Blocked:** none." > /tmp/p27-handback.md
gh api repos/Dengnifer/MIPStarRE-A/issues/27/comments -F body=@/tmp/p27-handback.md --jq .html_url
tmux capture-pane -p -t "$S" | grep -q "gpt-5.6-sol" && { echo "a codex session is already in $S"; exit 1; }
tmux send-keys -t "$S" 'cd ~/MIPStarRE-qpbt && local/bin/main-session.sh' Enter
for _ in $(seq 1 90); do tmux capture-pane -p -t "$S" | grep -q "Ask Codex" && break; sleep 2; done
sleep 3
tmux send-keys -t "$S" -l "OWNER MESSAGE: you resume the operator role from the owner session (Mode 1). Read ~/.codex/prompts/goal.md, local/personas/main.md, and the last three #27 reports (the newest is the hand-back). Lane state: ~/.cache/mipstarre-dev/watchdog/lanes/ (per-issue markers and logs; /tmp/lane-v4.sh, /tmp/merge.sh, /tmp/rerun_review.sh are the owner's helpers you may reuse). Rules unchanged: merge green PRs first every iteration; two review rounds then adjudicate for workflow PRs; never grow a PR to satisfy findings; blockers to #26, reports to #27. Continue."
tmux send-keys -t "$S" Enter
sleep 2; tmux send-keys -t "$S" "/goal resume" Enter; sleep 2; tmux send-keys -t "$S" Enter
echo "hand-back complete"
