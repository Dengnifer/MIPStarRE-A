# Local operations operator guide

GitHub is the authority for active issues and pull requests; this repository
provides the machine-local execution, review, cache, and telemetry layer.
Architecture and invariants are in [`DESIGN.md`](DESIGN.md). Protocol changes
follow [`protocols/meta.md`](protocols/meta.md).

## Lifecycle

```text
GitHub issue -> branch/worktree -> agent sessions -> exact-head CI -> review
             -> optional auto-fix -> guarded GitHub merge -> local main refresh
```

1. Create an issue with `local/bin/issue_new.py --title "..." --body-file ...`.
2. Create `issue-<number>-<slug>`, add a worktree, and run
   `local/bin/worktree-setup.sh` there.
3. Open or adopt a PR with `local/bin/pr_open.py --branch ... --base main`.
4. Dispatch every agent through `local/bin/dispatch.sh`; never invoke the model
   runner directly.
5. Run `local/bin/ci.sh <pr-number>`. Complete runs publish all canonical
   `local-ci/*` statuses, a marker-bound exact-head manifest comment, and then
   the digest-bound `local-ci/summary` gate.
6. Run `local/bin/review.sh <pr-number>`. A clean commit-bound `COMMENT` review
   plus `local-review/summary=success` is sufficient; GitHub approval is not a
   gate. Ordinary reruns adopt complete evidence; use `--new-round` to request
   another guarded attestation for the unchanged exact head and base.
7. Optionally run `local/bin/autofix.sh <pr-number> --mode auto` when the PR has
   the opt-in label.
8. Merge with `local/bin/pr_merge.py <pr-number>`, which invokes only guarded
   `gh pr merge --merge --match-head-commit` after all evidence and strict
   protection on the actual base are current. Read-back accepts only a real
   merge commit with frozen base/head parents in that order.

`local/bin/github-sync.sh` creates an atomic audit snapshot under
`results/telemetry/github-snapshot/`. Lifecycle commands never read snapshots
as authority. `local/bin/housekeeping.sh standup` writes reports under
`results/reports/standup/`.

## Ground rules

- Read `AGENTS.md` before changing mathematics or Lean.
- Never run `lake update`, write to the hot cache, or run an unlocked full
  build.
- One session never reviews its own work.
- Invoke lifecycle tools through the primary checkout's `local/bin/` path and
  pass the prepared feature worktree where the command accepts `--worktree`.
  This keeps append-only telemetry single-instance while the shared GitHub
  client discovers `gh` and the `github` remote or fails closed.
- `MIPSTARRE_GITHUB_ACTOR` is the sole evidence publisher and defaults to the
  repository owner (`Dengnifer` here). The authenticated `gh` user must match;
  changing marker text or posting from another account grants no authority.
- No existing workflow lock is reclaimed by acquisition, including a complete
  same-host record whose PID is dead: its descendants may still be running.
  Complete locks record `pid`, a random UUID `token`, directory `identity`, and
  structured `owner` metadata; transitions use the persistent sibling
  `.<lock-name>.transition` mutex. After proving the owner and every descendant
  have stopped, recover a complete dead-owner claim explicitly with
  `runtime_lock.py break-stale`. Ownerless, malformed, partial, and foreign-host
  records fail closed. After the same process audit, an incomplete record may
  be removed manually at the exact path printed by the error.
- The retired registry under `results/telemetry/registry-archive/` is immutable
  research data, never workflow input.
- Record protocol friction in `results/telemetry/events.md`, then amend
  `protocols/EVOLUTION.md` under the meta protocol when behavior must change.
