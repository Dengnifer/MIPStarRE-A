OPERATOR INSTRUCTION — GRACEFUL STAND-DOWN.

Your session ends now, on purpose, and another main session takes over. Reason: {{REASON}}. What comes next: {{NEXT_LAYOUT}}. Nothing is wrong with your work; this is a handover, not a correction. Aim to be finished within {{DEADLINE_MIN}} minutes, and start nothing new from here on.

Do these steps, in this order.

1. Start no new worker, delegate, review or merge train. Something already staged or running may finish. Jobs that need no model (a full build, a CI wrapper) may keep running — write down their process ids, their log files and what their result is for.

2. Let a running delegate finish its current task or reach a sound stopping point: work committed in its own worktree, pushed if it is publishable. Give it no follow-up task, then close it.

3. Bring your own current step to a safe point. No half-written files. No uncommitted edits in the primary checkout apart from the usual records. Every branch you were working on is either pushed or described in step 6.

4. Publish your pending records ({{RECORDS_CMD}}).

5. Release every claim held by you and by your delegates, with a note saying what state that work is in.

6. Append a handover section to {{HANDOFF_FILE}}, following the form in {{HANDOVER_TEMPLATE}}: every item in flight with its exact numbers, branch names, commit heads, worktrees, unpushed commits and running detached jobs; what is reviewed, gated, staged or waiting for a fresh review; the decisions you have open and what you would decide; and the two tasks you would hand to your successor first. Write it so that a reader who was never in this session can act on it.

7. {{PROGRESS_NOTE}}

8. As your LAST action, run exactly this, then end the turn and stay idle:

    touch {{DONE_MARKER}}

The operator closes this session once that marker appears.
