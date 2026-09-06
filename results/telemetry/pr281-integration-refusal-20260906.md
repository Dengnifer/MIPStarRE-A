# PR281 integration refusal and restoration

Session `orc-252-20260906-09`; requested effort xhigh. The single authorized
attempt did not merge PR281. The unchanged gate refused concurrent primary
telemetry dirt before any merge API call. Restoration succeeded. No retry ran.

## Evidence

- Preparation: `/tmp/pr281-integration-20260906T105525Z-v1/README.md` and
  `SHA256SUMS`; 90 lines of code adaptation to the existing PR276 implementation.
- Runtime: `/home/drx/.cache/mipstarre-dev/pr281-integration-20260906T105525Z-v1/`.
- Coordinator PID 554790, preservation PID 555460, daemon PID 556960; all exited.
- Operation elapsed: 51.828 seconds; terminal bound: 1200 seconds.
- `attempt-1/preflight.json` and `attempt-1/daemon-preflight.json`: base
  `41b2a034ec1cea71b6f8cb6469e158965c628c20`, head
  `a418f28629cdd8fcba054f7eed04d5d1a8e04621`, review 5125092399,
  ten green exact-head statuses, closed prerequisite #49, no open children.
- `attempt-1/daemon.log`: gate 2 refusal after PR207 reviewer capture publication.
- `finisher-result.json`: preservation/gate exit 1; restoration exit 0.
- `restoration.jsonl`: 242 per-path entries, including events.md mode 0664 to
  saved 0600 at line 4, and sessions.jsonl raw-multiplicity verification at line 17.
- `restoration-summary.json`: 242 paths restored; 72,019,238 bytes appended or
  created. All 73,141,518 captured bytes remain archived; raw rows were not deduplicated.
- `final-verification.json`: live GitHub and local readback at 11:02:52 UTC;
  PR281 open/unmerged, issue278 open, all main references still at the base.
  There is no merge SHA. All saved modes, held-inode raw rows, prior commits,
  and original staging were verified. The two concurrent PR207 files remain.

## Preserved State

New stash `2b87495689367ace4146e0eeec9060da2389a646`; previous stash
`46c5682018c2a0c3b684960ccd033f69f9b7a157`. Neither was applied or dropped.
The new stash bundle and held/retained inodes are in runtime `attempt-1/`.
Its snapshot is `snapshot-20260906T105937949554Z/`, with the original raw index,
staged and unstaged binary patches, status inventory, file bytes/modes, and
prior-commit list. The original staging was empty and remains empty.
The earlier PR276 failure and subsequent resolution were not edited.

Saved sessions.jsonl contains 904 rows; restoration contains those rows plus
the PR207 review completion, 905 rows total. Its completion is preserved at
`results/telemetry/sessions.jsonl:780`. All saved multiplicities and inode
appends were verified through the final boundary. Later publishers remain
responsible for their normal telemetry appends and captures.

Final session tokens and wall time will be written by the existing dispatcher
after this session returns, using the canonical capture
`/home/drx/.cache/mipstarre-dev/sessions/orc-252-20260906-09.jsonl` and the normal
published capture and sessions.jsonl registry row. No usage total is estimated.

## Next Safe Gate

Main should first establish a quiet telemetry-publication boundary, then
prepare a fresh pinned operation with a new snapshot and all normal live checks.
This operation has spent its one attempt and must not be replayed. Cache
warming is deferred. PR280/282/207 and #27 publication remain outside this task.
