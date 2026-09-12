# Main-selected useful-work admissions

Retired by #505: the supervisor entrypoints are disabled. Use `dispatch.sh` with
the worker caps in `sessions.md`; the material below describes historical operation.

Normative supplement to sessions/review protocols (#257 and #418). Only main selects
useful packets and binds prerequisites to closed issues, actual merged PRs and ancestry.
No discovery, filler, merges, adjudication, budget resumes, inbox actions or shell tasks.

## Native completion handoff

The active Space allocation is ten sessions total: the root plus at most nine native
descendants. The useful target is nine descendants, the floor is eight, and external
admission is zero. Count actual native turn activity once per process; ready payloads,
reservations, configured ceilings, and idle or completed turns do not count.

Intent precedes vacancy. While slots are occupied, main and the capable coordinator
validate useful, disjoint successors against their prerequisites, exact current head or
source snapshot, actually published inputs, eligible native identity and role, current
owner, unique operation, CI/review/publisher handle, or worktree, predecessor, job class,
exact model and effort, complete hash-bound dispatch body, deadline rule, cumulative
budget, completion condition, authorized time limit, and any inherited deadline. Record
`ready_at` when
validation finishes while the predecessor still occupies its slot. Descriptive input
strings and a nominal successor line are not operational readiness. Invalidate a record
when its head, dependency, role, ownership, or deadline changes. Each expected completion
has a separately validated alternate; if none exists, record the exact frontier blocker
and do not call that completion fully prepared.

Ordinary proof and CI-handoff records may replace their long literal activation body with
the #471 contract form. Such a record adds an immutable absolute `contract_path`, its
64-hex `contract_sha256`, and the exact `short_activation` message sealed before completion.
The short message contains only actor, operation id, contract path and hash, and a
conservative absolute deadline. The hashed full contract retains all ordinary readiness,
scope, input, ownership, model, effort, completion, cumulative-cost, and budget fields.
Existing full activation messages remain valid.

After a real terminal event, recheck only the capacity, target identity, unchanged intent,
owned operation or worktree, and deadline conditions that could not be settled earlier.
Put an absolute source deadline no later than the native call time plus the authorized
limit in a fresh activation payload; a continuation retains an earlier inherited deadline.
Call native `followup_task` or `spawn_agent` before detailed predecessor receipt adoption,
rollout-tail reads, hashes, broad censuses, or PR-history inspection. If the selected
successor is blocked or its activation call fails, record the exact reason and try the
prepared alternate in the same completion cycle. Do not reclaim a quiet live turn until
assignment, budget, and ownership checks establish actual completion or stall.

Immediately before a contract-form native call, verify the exact contract bytes and hash,
the presealed short message, and unchanged capacity, identity, head or source snapshot,
published inputs, owner, unique operation, actor/model/effort, and deadline prerequisites.
Send the stored short message without rebuilding the long arguments. A missing or wrong
hash, changed prerequisite, or expired deadline invalidates the candidate and records its
blocker before another prevalidated useful alternative is selected. An already-authorized
ordinary mechanical activation needs no new root round trip.

The root creates every new canonical native reviewer child so its direct parent matches
the review request's root; the coordinator does not spawn that child or represent itself
as the root. After the prior canonical consumer hold is released, the coordinator may
mechanically follow up an eligible existing direct-root child without another root round
trip only when a root-authorized prepared record preserves the request binding,
independence, current head, identity, model, effort, and ordinary review gates. Until both
the genuine response is validated and the waiting consumer accepts it, the completed
reviewer remains idle and unavailable for follow-up; a response file alone is insufficient.

The coordinator's append-only latency batch records predecessor `task_complete`,
`ready_at`, the actual activation call, successor thread and current `task_started` turn,
first useful output, the source deadline, and each real blocker interval. Reconcile the
fixed deadline with actual `task_started`; first tool use or progress never starts the
clock. Detailed adoption follows activation and start verification, but waiting for either
never serializes activation-first handling of another real completion. Initial recovery of
a pre-existing gap is backlog, not evidence of reaction time under this rule. A later
eight- or nine-worker snapshot does not establish sustained coverage. Occupied runtime,
fresh-output lower bounds, API usage, and proof delivery remain separate measurements.
Before mutation, the ordinary actor verifies the same hash, reads the full contract, and
rechecks its identity, model and effort, scope, inputs, ownership, and effective deadline.
That deadline is the earliest of the presealed absolute deadline, actual `task_started`
plus the authorized duration, and any inherited deadline.

Canonical review assignments are not ordinary contract-form records. They retain the
literal nonce, head, prompt digest and root-assignment format, direct-root parentage and
independence validation, and consumer identity holds required by `review.md`. Neither a
contract reference nor a short activation message substitutes for those bindings.

Runtime acceptance requires a natural post-merge completion whose coordinator-owned batch
shows `ready_at` before completion, the actual activation call before detailed adoption,
and the successor's current `task_started` and first useful output. This establishes the
ordering for one transition only. Sustained floor coverage still requires the existing
interval audit; neither a backlog recovery nor a closing count of nine is sufficient.

## Historical one-shot executor

The checked-in `useful_queue.py` remains the opt-in external one-shot helper reviewed in
#257; it is not the native completion controller and is unchanged by #418. Both `--run`
and `enabled: true` are required, defaults disable, and it admits at most one packet per
tick with a watch interval of at least five seconds. Its historical dispatcher policy,
two-slot review accounting, and normal green-CI review cap remain internal to that helper.
Existing fan-out and kill switches remain binding.

Native descendants use the shared root lease and `telemetry.py native-record`:
root/parent IDs, effective model and effort, key label, timestamps, status and
unknown usage provenance are retained; parent counters are not summed without
independent evidence. Native review uses the exact-head transport and cannot
bypass CI, independent review or merge gates.
For the one-shot executor, intent precedes creation. Router lock serializes tickets and
one-use descendant PID/start
claims; unclaimed slots count with real clients/reservations, including global CLI flags.
Worktree reservations exclude unrelated dispatch. Canonical locks/head checks persist.
Queued reviews cannot retry zero-token failures; uncertain launches/publication need adoption.
Cache useful-queue/ holds state/census JSON, append-only events and packet intent/log/receipt.
STOP/HOLD prevent new admissions/claims without killing workers. Refusals latch HOLD.
Turns/items/retries are separate observations, not server admission or mathematical usefulness.
Captures changed since first tick may include older events; unreadable/replaced/backlogged
evidence fails closed. Main stops the supervisor, inspects identities/captures/registry/GitHub,
repairs publication canonically without model retries, and reconciles under controller then
router locks only after disposition and no outstanding clients. Preserve attempts/events.
Only main clears HOLD. Deploy all four entry points after CI/independent review with old
supervisor stopped; no dirty/worktree/non-main execution. Packet/rollout details: the #257 brief.
