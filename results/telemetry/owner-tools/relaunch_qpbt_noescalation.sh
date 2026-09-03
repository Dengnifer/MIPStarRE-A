#!/usr/bin/env bash
# Restart the qpbt operator session (resume, context preserved) with a sandbox
# that needs NO approval escalations for its normal work: workspace-write plus
# network access and the telemetry/cache root writable. Removes the automatic
# approval-review round trip (which timed out on 2026-09-03 and rejected commands).
set -u
S=qpbt
if tmux capture-pane -p -t "$S" | grep -q "gpt-5.6-sol"; then
  # interrupt a running turn first (Esc), then quit at the prompt
  tmux capture-pane -p -t "$S" | grep -q "esc to interrupt" && { tmux send-keys -t "$S" Escape; sleep 4; }
  tmux send-keys -t "$S" "/quit" Enter; sleep 2; tmux send-keys -t "$S" Enter
  for _ in $(seq 1 30); do tmux capture-pane -p -t "$S" | grep -q "gpt-5.6-sol" || break; sleep 2; done
  tmux capture-pane -p -t "$S" | grep -q "gpt-5.6-sol" && { echo "codex did not exit"; exit 1; }
fi
tmux send-keys -t "$S" 'cd ~/MIPStarRE-qpbt && codex resume --last -s workspace-write -c approval_policy="never" -c sandbox_workspace_write.network_access=true -c '"'"'sandbox_workspace_write.writable_roots=["/home/drx/.cache/mipstarre-dev","/home/drx/MIPStarRE-qpbt"]'"'"'' Enter
for _ in $(seq 1 90); do tmux capture-pane -p -t "$S" | grep -q "Ask Codex" && break; sleep 2; done
tmux capture-pane -p -t "$S" | grep -q "Ask Codex" || { echo "TUI did not appear"; tmux capture-pane -p -t "$S" | tail -12; exit 1; }
sleep 3
tmux send-keys -t "$S" -l "OWNER MESSAGE: you were restarted with approval_policy=never, sandbox workspace-write, network access on, and /home/drx/.cache/mipstarre-dev writable, so no command needs an approval review any more (the automatic approval review had been timing out and rejecting commands today; that is one reason merges failed). Make this permanent and prevent the other causes, each as a SMALL change: (1) in PR #41 (the launcher PR) make local/bin/main-session.sh start codex with exactly these flags, then merge #41; (2) one PR: review.sh refuses a THIRD review round on a PR whose diff touches only local/, .githooks/, scripts/tests/ or docs, printing the section-12 adjudication instruction instead (about 15 lines); (3) the same PR adds to local/personas/main.md the four rules from the owner's stall directive (merge green PRs first at every iteration; two rounds then adjudicate; never grow a PR to satisfy findings; findings asking for mechanisms are out of scope). Then continue exactly where you were: merge the green PRs, PR #51 when its review lands, then the Lean queue. Post a #27 report."
tmux send-keys -t "$S" Enter
sleep 2; tmux send-keys -t "$S" "/goal resume" Enter; sleep 2; tmux send-keys -t "$S" Enter
sleep 20; tmux capture-pane -p -t "$S" -S -20 | grep -v "^\s*$" | tail -10
