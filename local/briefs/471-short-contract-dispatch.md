# Issue 471: presealed ordinary activation contract

## Scope

This optional representation applies only to already-authorized ordinary proof
and CI-handoff successors. Existing complete literal activation messages remain
valid. Canonical native reviews are excluded: they retain the literal nonce,
head, prompt digest, root assignment, author exclusions, direct-parent checks,
and consumer holds required by `review.md`.

No executable parser is added. The capable coordinator may adopt this format
only after issue #471 passes canonical CI, independent hard review, normal
merge, and an explicit runtime compatibility observation.

## Full contract

The contract is an immutable UTF-8 JSON file. `contract_sha256` is the lowercase
SHA-256 of its exact bytes. A complete ordinary contract has this shape:

```json
{
  "schema": "qpbt-ordinary-successor-contract-v1",
  "operation": {
    "id": "unique-operation-id",
    "kind": "proof",
    "issue": 123,
    "pull_request": null,
    "predecessor": "thread-or-operation-id",
    "completion_condition": "precise bounded completion condition"
  },
  "actor": {
    "thread_id": "canonical-uuid",
    "role": "prover",
    "model": "gpt-5.6-sol",
    "effort": "ultra"
  },
  "scope": {
    "worktree": "/absolute/owned/worktree",
    "read_only_paths": [],
    "head": "40-hex-current-head",
    "source_snapshot": null,
    "published_inputs": [
      {"name": "dependency", "sha256": "64-hex-input-hash"}
    ]
  },
  "ownership": {
    "owner": "/root/actor-name",
    "unique_operation": "worktree-or-ci-handle",
    "disjoint_from": ["other-live-operation"]
  },
  "capacity": {
    "total": 10,
    "native_cap": 9,
    "target": 9,
    "floor": 8,
    "external_admission": 0
  },
  "budget": {
    "preserved_costs": {"attempts": 0, "working_seconds": 0},
    "authorized_seconds": 900,
    "clock": "actual_native_task_started",
    "presealed_absolute_deadline": "2026-09-08T20:45:00Z",
    "inherited_deadline": null,
    "effective_deadline_rule": "minimum of all applicable deadlines"
  }
}
```

For `kind: "ci_handoff"`, the operation also identifies the exact PR, head,
worktree, unique CI ownership, expected manifest/status contexts, and the
adopt-existing-run rule. The contract contains no credentials, private home
data, or live telemetry write instruction.

## Ready record

The coordinator validates the contract while the predecessor remains active.
The ready record adds:

```json
{
  "contract_path": "/absolute/immutable/ordinary-contract.json",
  "contract_sha256": "64-hex-sha256-of-exact-contract-bytes",
  "short_activation": "ORDINARY_ACTIVATE actor op-id /contract.json sha256 deadline",
  "short_activation_sealed_at": "2026-09-08T20:30:00Z",
  "ready_at": "2026-09-08T20:30:01Z"
}
```

The exact `short_activation` literal is sealed before predecessor completion.
It contains only actor, operation id, absolute contract path and hash, and a
conservative absolute deadline. It is not rebuilt after completion.

Immediately before the native call, the activator verifies the exact contract
bytes and hash, stored short message, actor/model/effort, capacity, ownership,
unique operation, current head or snapshot, published inputs, and deadlines.
Failure invalidates the candidate, records the blocker, and selects another
prevalidated useful alternative. An already-authorized ordinary mechanical
activation needs no new root round trip.

On actual `task_started`, the actor verifies the same hash and reads the full
contract before mutation. It rechecks identity, model and effort, scope,
inputs, ownership, and deadlines. The effective deadline is the earliest of
the presealed absolute deadline, actual `task_started` plus
`authorized_seconds`, and any inherited deadline. First tool use or progress
cannot reset the clock.

## Evidence boundary

The readiness record and latency batch retain the contract path and hash,
sealing time, `ready_at`, predecessor completion, native call, actual successor
turn, first useful output, requested and observed model and effort, effective
deadline, and blocker intervals. Occupied runtime, fresh-output lower bounds,
API usage, and proof delivery remain distinct observations.

The recorded 63.076-, 73.171-, 116.521-, and 134.213-second misses and 66.95%
coverage over 119.63 valid minutes remain historical failures. This format
alone does not demonstrate prompt activation or sustained recovery.
