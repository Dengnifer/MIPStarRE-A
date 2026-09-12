# PR491 review-handoff telemetry preservation

- Recorded at: `2026-09-09T05:18:16Z`.
- Reviewed worktree: `/home/drx/MIPStarRE-qpbt/.worktrees/issue-490-pasting-restoration`.
- Branch and unchanged source head: `issue-490-pasting-restoration` at
  `4c836c5441b584883707b3991bc31c6655d52b67`.
- Sole pre-parking change: unstaged `results/telemetry/events.md`, 40 inserted
  lines and no deletions. No source, Lean, blueprint, index, or proof-budget
  file was changed.
- Committed events blob: `82946e9014f87e02d61eaa4f270ec5a2bfe5c55c`.
- Exact parked events blob: `a01061c81d363c2c1a96ae11dc6ba9ea450f1566`
  (499450 bytes; filesystem mode `0664`, Git mode `100644`).
- Retained named stash: `ac4436a704a396676d4fd35fd47cc495b8f6ea50`,
  message
  `pr491-review-handoff-events-4c836c5441b584883707b3991bc31c6655d52b67-20260909T051816Z`.
  Its first parent is the exact source head, and its events blob is the parked
  blob above. Do not drop this stash before restoration and normal telemetry
  publication.
- Retained runtime patch:
  `/home/drx/.cache/mipstarre-dev/telemetry-parks/pr491-4c836c5441b584883707b3991bc31c6655d52b67-events-20260909T051816Z.patch`
  (3598 bytes), SHA-256
  `f78770c8e5fa6a744990f18efb5ce1eb209e283d22c11d61bb61ab9db1f568c4`,
  stable patch ID `880b5983febfa0e2b5a5fcde9973f1b63223ba98`.
- Verification: the full-index binary diff from the stash first parent to the
  stash has the same SHA-256 as the retained patch; the reviewed worktree is
  clean and remains at the source head.

## Restoration plan

After the detached review publisher no longer reads the worktree, first verify
that the branch is still at the source head and the worktree is clean. Then run:

```bash
git -C /home/drx/MIPStarRE-qpbt/.worktrees/issue-490-pasting-restoration \
  stash apply --index ac4436a704a396676d4fd35fd47cc495b8f6ea50
git -C /home/drx/MIPStarRE-qpbt/.worktrees/issue-490-pasting-restoration \
  hash-object results/telemetry/events.md
```

The second command must print
`a01061c81d363c2c1a96ae11dc6ba9ea450f1566`. Retain the stash until the
restored record is included in the normal primary telemetry reconciliation and
publication.

If the head moved or `events.md` gained later appends, do not use `stash pop`
and do not overwrite the newer file. Preserve the current bytes, materialize
the committed and parked blobs from the source head and retained stash, verify
that their difference is exactly the hash-recorded 40-line patch, and restore
only that delta ahead of or alongside the later append-only suffix. Verify raw
row multiplicities and the final prefix before dropping any preservation
artifact.

This receipt is intentionally uncommitted in the primary checkout. No main
commit or push is part of this handoff.
