# Capacity restart complete: resume useful work

Meta has completed the owner-authorized relay-3 capacity restart. The same root
thread, 01a076bc-f4ad-7813-805b-c8b4dac71a14, remains named main in tmux qpbt.
Its verified runtime PID is 1101986, the canonical native lease reserves nine
descendant slots, and the owner key allocation is eleven. Authentication is
unchanged on relay-3. Main and all descendants remain Astra Ultra.

The checkpoint hold is explicitly released. Any earlier queued instruction to
checkpoint for this same cap11 transition is now obsolete. Do not checkpoint
again, rename checkpoint files, reset the goal, or wait for another release.
Use the saved checkpoints and preserve all cumulative budgets and worktrees.

Resume useful native work immediately. Restore the three checkpointed task
identities where available, then fill the remaining native capacity with
independent proof, required review, and bounded integration work. Main selects
the assignments. Aim for nine active native workers; maintain at least eight
whenever independent work exists, replenish completed workers promptly, and
record concrete reasons and durations for every lower-occupancy interval.

Write /tmp/qpbt-cap11-live-occupancy-20260907.json after the first refill with a
fresh native list_agents observation: timestamp, actual running count, each
active task and role, and any reason for operating below eight. This observation
must report active work rather than configured or reserved capacity. Continue
the existing goal and keep normal telemetry of subsequent occupancy changes.

The merge service's old literal five-slot guard was updated for this allocation.
The replacement is /tmp/merge-service-relay3-cap11-20260907.py, PID1089067.
Its original shared lock and journal remain in use. CI, independent review,
freshness, dirty-checkout, exact-head merge and external-admission gates were
preserved. The guard now expects eleven total and records nine descendants.
Four focused runtime-gate checks passed. Use its current receipt rather than
the stale service PID and cap5 warning in the earlier worker checkpoint.

Incorporate the launcher, service update, owner instructions, and runtime
receipt into the normal project telemetry and review workflow. The local Mac
mirror was not changed. Runtime receipt:
/tmp/qpbt-relay3-cap11-receipt-20260907.json
