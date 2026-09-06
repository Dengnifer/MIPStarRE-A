# Active QPBT owner policy: space, five total

Recorded from the owner decision and the credential-free meta receipt
`space-cap5-switch-20260906.json`. This record supersedes the relay-1/cap8
operating target for the current QPBT run. Earlier relay-1 records, including
the native bootstrap and eight-worker observations, remain historical evidence
and are not relabelled.

## Current allocation

- Account label: `space`; all current QPBT sessions request `gpt-6-astra` at
  `ultra`.
- Hard limit: five total active native sessions, including the main session;
  at most four native descendants anywhere in the tree.
- Root accounting: count the main once; count each native descendant once
  across the shared tree. Do not count a ready list, reservation, configured
  ceiling, or an idle process as useful activity.
- External admission: zero. Existing proof, review, independent-review,
  exact-head CI, merge, credential and proof-integrity safeguards remain
  binding.
- The scoped directory's historical relay-1 name is not an account label.
  Telemetry uses `space`; private credentials, homes and backups are omitted.

## Verified transition

The owner switch was applied at `2026-09-06T14:06:36Z`; launch verification
completed at `2026-09-06T14:11:40Z`. At `2026-09-06T14:12:00Z`, an independent
scoped audit verified `active_total=5`, `active_native_descendants=4`, fresh
successful tool activity for the main and all four children, and no explicit
errors in the inspected turns. These are active-turn observations, not a claim
about simultaneous upstream requests or a sustained occupancy percentage.
Usage is unknown and is recorded as null until normal terminal session
telemetry exists.

The startup interval before the verified census is **unmeasured**, not a
reported vacancy: `below_floor_seconds=null` and
`below_floor_reason="no certified census during the switch; do not infer a
vacancy from absent evidence"`.

## Successor and vacancy policy

After every completion, failure, unblocking event or compaction, main must
reconcile actual native descendants and launch a disjoint, useful successor
promptly when a slot is available. Follow-up/resume work may reuse a terminal
task only after its prior result and worktree are inspected. A successor is
not counted until its native turn has started and produced useful tool
activity. Record each observation's UTC time, active total, active native
descendants, vacancy start/end, elapsed vacancy seconds, and concrete reason
(completion, failure, transport/service delay, dependency, or safe gate).
When no useful successor exists, record the binding dependency rather than
starting filler. Never claim a sustained floor from two successful refills, a
ready list, reservations, or a configured cap.

Main retains task selection, decomposition and integration ownership. No
external worker, credential route, manual merge, review bypass, proof
assumption, or budget reset follows from this policy.
