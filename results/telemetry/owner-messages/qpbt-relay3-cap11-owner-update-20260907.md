# Owner allocation and occupancy instruction: relay-3 only

This is the latest owner instruction, issued on 2026-09-07:

"Do not use space key for now, but now the concurrency limit of the relay-3
key is 11. keep the concurrency >=8 for almost all of the times, <8 only if
for good reason."

It supersedes every older instruction limiting this episode to five total
slots or three native descendants. Do not use the Space key, start a second
credential pool, or revert credentials based on historical route labels.

## Runtime allocation

Continue the same native coordinator, 01a076bc-f4ad-7813-805b-c8b4dac71a14,
named main in tmux qpbt, with the existing scoped CODEX_HOME. Its authentication
continues to match ghz's relay-3 auth.json. Astra Ultra applies to main and every
native worker. External CLI worker admissions remain zero.

The relay-3 allocation is eleven. The existing canonical router counts the
VS Code app-server as one additional primary slot. Main therefore has nine
shared native descendant slots: nine workers plus main plus the counted server
equals eleven. Do not exceed this shared cap through nested delegation. The
router's historical space bucket label is metadata, not the active credential.

## Sustained useful work

Aim for nine active native workers. Keep at least eight active native workers
whenever useful independent work exists, so the owner's occupancy floor is also
met while main is coordinating or waiting. Count running agents doing assigned
work, not idle threads, reserved capacity, sleeping polling loops, or invented
filler assignments. Use current native status and attributable recent activity.

At each worker completion, immediately assign a useful successor from a prepared
queue. Preauthorize bounded successor chains with disjoint worktree ownership.
An assigned coordinator may use native followup_task to refill an idle sibling
from that approved queue while main is in a long turn. Preserve the global cap,
one writer per worktree, one primary index owner, independent review, and the
single full-build lock. Do not serialize unrelated proof work behind one CI job.

Before waiting on a dependency or long-running build, inspect the available
proof, review, and integration work and refill free slots. Keep a short ready
queue with ownership and dependency information so new work does not require a
fresh full-project census each time. Main retains task-selection authority.

An occupancy below eight is acceptable only for a concrete reason, such as a
checkpointed restart, API errors or backoff, exhaustion of independent ready
work, unresolved mathematical dependencies, or a necessary serialized write.
Record when the interval begins, the actual active count, its reason, the action
that will end it, and when the floor is restored. A configured cap, an unanswered
worker-completion message, or main's avoidable decision delay is not evidence of
useful occupancy. Never evade proof or review requirements to keep slots full.

## Resume and evidence

Read /tmp/qpbt-cap11-ready-20260907.json and each listed worker checkpoint.
Resume preserved native child identities when available. Otherwise continue
from their saved checkpoints in fresh native tasks, recording predecessor links.
Preserve all worktrees, uncommitted work, active subprocess ownership, proof-gap
attempts, elapsed budgets, and usage records. Do not reset any cumulative budget.

The capacity checkpoint hold ends only after the enlarged process and its
canonical native lease have been verified. Meta will explicitly release that
hold. After release, restore useful concurrency promptly and continue the
existing continuous project goal without further owner reminders.

Record this owner decision, runtime receipt, every occupancy exception, and
subsequent native work through the normal telemetry workflow. Unknown usage
remains null. Report the actual relay-3 credential separately from the router's
historical bucket until its schema is reconciled through the usual review.

Launcher: /tmp/qpbt-resume-relay3-cap11-20260907.sh
Receipt: /tmp/qpbt-relay3-cap11-receipt-20260907.json
