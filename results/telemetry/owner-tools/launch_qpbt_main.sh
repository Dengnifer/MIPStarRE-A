#!/usr/bin/env bash
# Start a fresh codex main session in tmux session `qpbt` and brief it.
# Expects /tmp/qpbt-main-handoff.md on this host. Idempotent-ish: refuses if
# a codex TUI is still showing in the pane.
set -u
S=qpbt
if tmux capture-pane -p -t "$S" | grep -q "gpt-5.6-sol"; then
  echo "codex still running in $S; not starting another"; exit 1
fi
tmux send-keys -t "$S" 'cd ~/MIPStarRE-qpbt && codex' Enter
for _ in $(seq 1 90); do
  tmux capture-pane -p -t "$S" | grep -q "Ask Codex" && break
  sleep 2
done
tmux capture-pane -p -t "$S" | grep -q "Ask Codex" || { echo "TUI did not appear"; tmux capture-pane -p -t "$S" | tail -15; exit 1; }
sleep 2
tmux send-keys -t "$S" '/goal Formalize the quantum Pauli basis test in Lean 4 per the standing briefing at ~/.codex/prompts/goal.md; work the queue continuously; the only owner-gated control is MIPSTARRE_INFRA_OVERRIDE; when blocked on the owner, file a needs-owner issue and continue' Enter
sleep 2
tmux send-keys -t "$S" Enter
sleep 4
tmux load-buffer /tmp/qpbt-main-handoff.md && tmux paste-buffer -p -t "$S" && sleep 1 && tmux send-keys -t "$S" Enter
sleep 20
echo "--- pane ---"
tmux capture-pane -p -t "$S" -S -30 | grep -v "^\s*$" | tail -18
