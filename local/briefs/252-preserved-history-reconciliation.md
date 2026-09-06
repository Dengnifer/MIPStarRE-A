# Issue 252: preserved-history reconciliation

Session `orc-252-20260906-03`, September 6, 2026. This is a separate operations
PR, not a fifth PR238 review. Primary main and all supervisors remain untouched.

## Inputs and preservation

Private primary checkpoint: `2bb1a67b788befba4634c2a646e15fd65b4c9c24`.
Actual source merge: `32a32edee16d3932525e4b1da9f84009e1fbb13b`, parents
`a61ee557b33a2d8a4721e92b08b6d06dcb69ed57` and
`132caf66ef70ef781256c198011bab11ae7545b5`. Primary gh_common confirmed the
actual merge: GitHub `merged_at` is September 6 at 04:44:46 UTC; the assignment
records daemon confirmation at 04:44:53 UTC.

Merge `defb81b888ebeea5a968e8be4ab5580d006b5166` retains the entire private
history. Merge `5d31c3065e6ab54d99097a7dea44510d61538a89` has parents
`defb81b888ebeea5a968e8be4ab5580d006b5166` and the actual source merge.
The published snapshot descends from both. Source/protocol bytes match the
actual source merge; all five private operational briefs remain byte-identical.

`results/telemetry/reconciliation/issue-252-preservation.json` records the
finite capture boundary, every captured file's mode/size/SHA-256, and the
event-resolution provenance. Every historical telemetry blob reachable from
the frozen parents was read and its Git hash recomputed: 2,305 blobs and
930,441,658 raw bytes. Both merge-loss audits and normal commit hooks passed.
The event log preserves private bytes and every incoming insertion verbatim:
three source blocks, 11,001 bytes, 163 lines, without row deduplication.
Both complete originals remain available in their preserved ancestors.

Runtime backup directory:
`~/.cache/mipstarre-dev/issue-252-reconciliation-20260906T044639Z/`.
It includes the raw index, binary patches, captured files, audit records, and
a verified bundle covering 2bb1a67. The earlier owner bundle stops at 9102b74;
the additional backup does not assume those checkpoints are identical.

## Gates

Use primary pr_open.py/checked-push and ordinary CI. Detached CI retains
`MIPSTARRE_CI_BUILD_LOCK_WAIT_S=14400`. The old origin/main alias is not moved
or overridden; it may conservatively include already merged workflow changes.
Primary main must dispatch a separate reviewer after green exact-head CI:
this author cannot review itself or launch a subagent, and ci.sh does not
dispatch review. Only the main daemon may eventually call the normal merge gate.

## Main's final dirty-telemetry procedure

Do not commit more telemetry on primary before this PR merges: another private
commit would not be an ancestor of the reviewed head and would recreate divergence.
Main must coordinate its writers, take a fresh verified raw backup including
tracked/untracked files, index, modes, and binary patches, and require primary
HEAD still equals 2bb1a67 with only telemetry dirt. The capture recorded here
is not a writer lock; subsequent worker/session/CI output remains primary-owned.

Only main may then perform a path-restricted `git stash push -u` for
`results/telemetry`, pin its exact stash commit SHA and parents, and verify a
clean primary without moving main. Keep the stash and backup; do not blindly
pop/drop, reset, rebase, publish main, or use automatic conflict unions.
After actual daemon merge, the ordinary tail can fast-forward 2bb1a67. A late
dirty-tail refusal means deferred housekeeping, not permission to repeat a merge.

Restore only proven late suffixes: compare each stashed raw file with this PR's
captured raw snapshot, require a byte-prefix relationship and coordinated
destination writers, and append the suffix exactly once. Earlier captured rows
are already present; never append the entire saved file or deduplicate rows.
For new-file collisions, non-prefix changes, modes, deletions, symlinks, or
partial writes, stop and reconcile explicitly from the pinned backups. Retain
the stash SHA until every path is accounted for and restored bytes are verified.

No cap, relay policy, review rule, B7/B8 disposition, proof budget, or worker
allocation changes. The earlier 900-second timeout remains a failed attempt
with unavailable usage, not a successful zero-token session.
