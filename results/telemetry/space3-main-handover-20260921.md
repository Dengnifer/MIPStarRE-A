# Space-3 main handover, 2026-09-21

The owner ordered a graceful handover at 12:47 UTC: the new main will use the
cpa key, with two space-3 lane subagents through the shim. The retiring main
started no new task, review, CI run or train after that instruction. The meta
will provision the replacement layout after the standdown sentinel. Proxy and
ChatGPT-subscription use remain forbidden; this session changed no credentials
or watchdog settings.

## Published Work

- PR 663: `8bd40f9f77d27815f65d85e81a6570146657173a`, branch
  `issue-662-comparator-acceptance-20260920`. Publication repairs F1/F2 of
  review 5266355928 on the previous head. Both unnecessary global instances
  were removed; the 41,017-byte original LDT fixture is restored with SHA-256
  `cbe5642bb88db75f86bd79936896e684aa407a02108d8259ead71a0738783e73`.
  Its independent baseline regression, both drift checks and 94 focused tests
  pass. The hook suite ran 843 tests with 9 skips. An independent disposable
  challenge build passed 8,686 jobs. All four targets and direct raw effects
  remain; documentation does not claim current comparator acceptance. Fresh
  exact-head CI and independent review are still required.
- PR 659: `71715c4c06b13de3f1d0d4fcb0f698ba472a2f90`, branch
  `issue-642-artifact-packaging-20260919`. The placeholder-domain boundary
  repair is published. Canonical CI completed in 327 seconds, partial=false;
  all nine statuses were independently read back as success. The authorized
  10-minute independent verification remains pending. Preserve all five full
  prior reviews and count this next observation honestly as the sixth.
- PR 650: `7fb24231f23ea894f0665ddedc10cd05c4f9b8ab`, branch
  `issue-637-deviations-page-20260919`. Review 5262974908 remains adverse with
  two unresolved findings. The older approval is superseded. Refresh the
  deviations snapshot and PR body against the source repair already on main.
- PR 660: `418e0271d898b5cee443c48490056ef0bff55eab`, branch
  `issue-652-comparator-multi-challenge-20260919`. Reviewed and gated but stale;
  this commit remains an ancestor of PR 663. Verify its integration after the
  service merges 663 instead of duplicating the source work.

MAIN verified all four author worktrees clean, with local heads equal to their
GitHub heads and no unpublished commits. Their paths are the corresponding
branch names under `/home/drx/MIPStarRE-qpbt/.worktrees/`. The primary checkout
was clean at `a8352dc1e58993718bd1d7a29c2a4ac2e314223b` before these final records.

## Completed Jobs

All three detached jobs below have exit receipts 0 and their PIDs are gone.
No source build or CI job from this main needs monitoring after handover.

- PID 1036629: `/tmp/main-build663-ldt-restore-20260921.sh`, log with the same
  stem and `.log`. Locked full build, 12:13:48-12:27:43 UTC, 835 seconds and
  9,326 jobs. Frozen source tree `512a2d13b4e2329c10e02e029d5d1a0ee8f295bd`;
  `MIPStarRE` subtree `587d10e0d77526bbc80c85f3f56d26ab9939dc70` also occurs in
  the published repair. Follow-up checks passed all 13 QPBT axiom assertions
  and all 1,837 blueprint axiom declarations across 368 modules.
- PID 1086816: `/tmp/main-regenerate663-review-fix-20260921.sh`, same-stem log;
  12:31:10-12:31:34 UTC. Fresh candidate directory
  `/tmp/issue662-reviewfix-postbuild-20260921.GwMDUg` supplied the restored LDT
  fixture and 31-file QPBT tree adopted by the author.
- PID 1114242: `/tmp/main-ci659-71715c4c-20260921.sh`, same-stem log;
  12:41:23-12:46:50 UTC. Manifest:
  `~/.cache/mipstarre-dev/ci-manifests/pr659-71715c4c06b13de3f1d0d4fcb0f698ba472a2f90.json`.
  Build and blueprint rendering were legitimately skipped by the canonical
  change filter, rather than repeated unnecessarily.

The final native author, Popper `01a0c3fb-2377-7db3-9aa9-c3c6a1a71c21`, completed
its original task at 12:58:00.154 UTC after 1069.227 seconds and was closed.
Actual runtime model, effort and terminal usage are recorded in `sessions.jsonl`.
No follow-up task was sent. Its full receipt is
`/tmp/main-pr663-review-fix-publication-space3-20260921-result.md`.

The merge daemon was still alive as PID 367515, with log
`~/.cache/mipstarre-dev/watchdog/lanes/daemon-cpa-571-20260916.log`.
Neither train-approved marker exists; no train is staged or running. The
daemon and watches are left for the meta. The two remaining claims, main-ci659
and main-fix663, will be released after this record publication as ordered;
their actual release receipts belong in the final handoff section.

## Remaining Acceptance Work

The raw Pauli-effect transfer has already merged in PR 668 at
`ee868cab15356655fddd68edba3e7c1e46e285f8`; do not repeat the obsolete blocker.
Zero QPBT proof holes and the merged PR 647 completion protocol do not yet
establish artifact readiness. Issues 666 and 667 retain documentation and gap
register/blueprint obligations, and final artifact validation remains due.

The separate `/home/drx/QPBT-comparator` checkout has unpublished working-file
changes on `draft-challenge`, committed/public head
`9e879feb96174ee0089a487d8bcebf659ef99a48`. Both dependency pins still name
`a942ecb56fd25933da51286070ddc615609edc76`. Four-target configuration is present,
but official GitHub workflow/run/open-PR lists are empty. Private completeness
auxiliary equality, real landrun, nanoda and a verified merged-main pin remain
pending. Preserve that work; use independent disposable dependency checkouts,
never a live author worktree as a Lake-managed Git dependency.

Recommended first two worker tasks: the bounded independent verification of
659, and a fresh independent review of 663 after the new main runs canonical
CI on its published head. Adapt the prepared task briefs to the owner's new
lane layout. Review or CI results on previous commits cannot approve a changed
head. Only the merge service merges PRs; fresh approved PRs merge separately.

The complete operational handoff, claim releases, final published main revision
and retained local comparator state will be appended under
`HANDOVER FROM THE SPACE-3 MAIN` in `/tmp/qpbt-main-handoff-v5.md`. One issue 27
comment and the standdown sentinel follow. Issue 168 and the parked
infrastructure PRs 552, 554, 556 and 561 remain untouched.
