# Issue 418: completion handoff ordering

## Trigger

The September 8, 2026 regular 30-second lifecycle audit found that only 26 of
65 valid sampled minutes, or 40 percent, had at least eight useful native
workers. The record includes a gap of approximately 10.5 minutes and another
gap longer than six minutes. Later snapshots at nine workers are recoveries,
not evidence that the floor was sustained.

The current refill coordinator has a main-approved prepared-successor ledger at
`/tmp/qpbt-refill-preselected-successors-20260908.json`. That ledger is owned by
`/root/astra_refill_coordinator`; this issue reads it as evidence and does not
edit it. The observed delay is instead in the handoff order: the coordinator
can spend the vacancy interval reading predecessor receipts and rollout tails
before it activates an already prepared successor.

The same audit exposed a budget-clock error. A bounded geometry task started at
16:09:28 UTC, first reported progress at 16:24:57 UTC, and retained its original
20-minute deadline of 16:29:28 UTC. The 301.722 seconds of late read-only
scouting remain charged. First progress cannot reset a source deadline.

## Required order

While slots are occupied, main and the capable refill coordinator prepare more
than one useful, disjoint successor when the dependency frontier permits. Each
prepared record binds its issue, worktree or read-only scope, exact source
head or source snapshot, actually published inputs, eligible native identity
and role, current worktree or unique CI/review/publisher ownership, predecessor,
job class, exact model and effort, a complete hash-bound dispatch body, deadline
rule, completion condition, cumulative budget, authorized time limit, and any
inherited deadline. Its `ready_at` is the time those checks finish while the
predecessor still occupies its slot. A prose description of expected inputs or
one nominal successor line is not ready. Head, dependency, ownership, role, or
deadline changes invalidate readiness. Each expected completion has a separately
validated alternate; if none exists, the queue records the exact frontier blocker
and does not call that completion fully prepared.

After an attributable `task_complete` or equivalent terminal event, the
coordinator performs only the checks that cannot safely precede the vacancy:
shared-cap admission, target identity, unchanged prepared record, owned
operation or worktree, and unexpired budget. The activation payload carries an
absolute source deadline no later than the native call time plus the authorized
limit; a continuation retains an earlier inherited deadline. The coordinator
then makes the actual native `followup_task` or `spawn_agent` call before
detailed receipt adoption, rollout-tail reads, capture hashes, broad censuses,
or PR-history inspection. A blocked first choice records the exact prerequisite
and yields to another prepared, ready successor during the same completion
cycle. A failed or refused activation call follows the same alternate path.

After activation, the coordinator reconciles the fixed deadline against the
successor's actual current `task_started`, then verifies requested and observed
model and effort and first useful output. Only then does it adopt the
predecessor's detailed evidence. The coordinator's append-only transition batch
records predecessor completion, `ready_at`, the actual activation call,
successor thread and turn start, first useful output, absolute source deadline,
and any real blocker interval. The sole primary telemetry writer remains
unchanged.
Waiting for start evidence or adopting one predecessor cannot block activation
for a second real completion.

Quiet but live turns remain occupied until assignment, budget, and owned-operation
checks establish an actual completion or stall. Occupied runtime, fresh-output
lower bounds, API usage, and proof delivery remain distinct observations. An
initial recovery of an old vacancy is labelled backlog, and a closing eight- or
nine-worker snapshot does not establish sustained coverage or a prompt reaction.

## Scope and validation

This issue changes the native main/coordinator/session contract only. It does
not add a monitor, external dispatcher, nested worker pool, or queue framework;
change a lease, credential, model policy, root identity, or source theorem; edit
the coordinator-owned ledger; or alter the checked-in historical one-shot queue
executor. B8 remains at 13 attempts and 26,509 working seconds, and every other
predecessor budget remains cumulative.

The documentation diff must remain below the workflow ceiling, pass the git
hooks and canonical CI, and receive independent hard control-policy review at
its exact head before normal merge.

Runtime acceptance requires a natural post-merge completion in the
coordinator-owned latency batch with `ready_at` before completion, the actual
activation call before detailed adoption, and the successor's current
`task_started` and first useful output. This establishes the handoff ordering
for that transition only; sustained floor coverage requires the existing
interval audit rather than a closing count.
