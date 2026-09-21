# MAIN resume on space-3, 2026-09-21

Observed at 10:12 UTC. The owner's space-3-only instruction governs this run:
main plus one native delegate, no dispatched workers, no proxy or subscription
login, no fallback key. The meta and Opus helpers are retired. Issue 168 is not
updated. The active goal is an artifact ready for an ITP submission.

## Reconciled state

Published main is `3ff0b33b06d66c41b29c6fc8da4a65b1d181a527`. GitHub and committed
telemetry contain progress beyond the resume briefing:

- PR 668 merged as `ee868cab15356655fddd68edba3e7c1e46e285f8` at 04:26:55 UTC;
  issue 665 is closed. It proves transfer to the direct Pauli effects for both
  headline theorems. Independent review 5262938015, subsequent exact-diff
  carry 5263040957, complete CI and the blueprint axiom audit preceded merge.
  The original audit report remains dated evidence; do not repeat its repair.
- PR 650 remains at `7fb24231f23ea894f0665ddedc10cd05c4f9b8ab`. The newer native
  review 5262974908 requests two changes, superseding the briefing's older
  approval 5262668187. Keep its adverse summary until those findings are fixed.
- PR 659's repair is published at `ee5bdb702734bad82e25d486e9d56ede2db689fa`,
  with complete green CI and no review at that head. The next step is a fresh
  independent review using `/tmp/main-review-pr659-ee5bdb70-20260921.md`,
  amended only for the current space-3 routing and current state.
- PR 660 remains at `418e0271d898b5cee443c48490056ef0bff55eab`, approved by
  review 5262898910 with no unresolved findings and green CI/review summaries.
  `/tmp/meta-gate.py 660` confirmed the existing gate. It is stale relative to
  main; the merge service is live, with no refresh workers. Its changes are
  being integrated into PR 663, so no concurrent refresh is assigned.
- PR 663 is published at `a942ecb56fd25933da51286070ddc615609edc76`, with green
  CI but no independent review. The author worktree has local commit
  `d9a380b8`, incorporating the merged direct-effect repair, and an unfinished
  merge of PR 660. Preserve all staged files, four conflict sites, and the
  untracked `ProofProbe.lean`. No old-head approval is appropriate while this
  necessary integration remains unpublished.

The merge service is PID 367515, running `/tmp/merge-daemon-v9k-cpa.sh` with
the zero-worker mode enforced. At 10:10:24 UTC its only candidate was PR 660.
No train was staged: there is only one approved candidate, and PR 663's local
tip does not match its published head. Parked PRs 552, 554, 556 and 561 remain
untouched.

## Delegate ownership

The first fresh reviewer, `01a0c371-8e25-7e13-bff7-e10905d45ddb`, was stopped
at preflight after the newer records were discovered. It read instructions
and PR metadata only; it created no worktree, changed no file, ran no tests,
and posted no review. It was closed before the next admission. This incurred
77.168 seconds and is retained in session telemetry, not reported as a review.

The sole live delegate is Sol/ultra author
`01a0c373-664c-7123-bde2-1786665a2da3`, started at 10:11:55.140 UTC, under
`main-fix 663`. It continues predecessor
`01a0c25b-c0be-7e52-b34b-b93341ae2f81` in the preserved issue-662 worktree and
the external comparator draft checkout. Main authorizes a further 45 minutes
of working time, with a 20-minute checkpoint at 10:31:55.140 UTC and a stop
deadline at 10:56:55.140 UTC. The predecessor's original 60-minute assignment
and all K6/K7 work remain charged; this is not a fresh episode or budget reset.

The first deliverable is the completed configuration merge with split-module
generation and the corrected direct-effect statements. Then pursue all four
registered comparator targets, retaining concrete diagnostics if the tranche
ends before acceptance. Main runs canonical CI; a different fresh thread must
review the published result. Official comparator evidence still requires the
unchanged tools, real landrun and nanoda, and a merged-main library pin.

## Completion check

`python3 scripts/completion_gate.py check --track qpbt` on `3ff0b33b06d6`
exited 1:

| Criterion | Result |
| --- | --- |
| C1 proof integrity | PASS: 332 Lean files, no proof-hole site |
| C2 headline axioms | DELEGATED: all four audit commands present; build evidence required |
| C3 paper-gap status | FAIL: no terminal-status column |
| C4 blueprint marking | FAIL: 11 of 528 linked nodes unmarked and unexempted |
| C5 comparator | FAIL: no verified QPBT completion record |
| C6 narrow documentation scan | PASS; does not discharge the broader issue 666 audit |
| C7 artifact files | FAIL: DEVIATIONS.md, ARTIFACT.md, make_artifact.sh not merged |

Issues 666 and 667 already track the documentation and register work. Do not
create duplicate issues or alter the criteria to claim completion. After the
comparator integration checkpoint, schedule the prepared PR 659 review and
the PR 650 repairs as permitted by the single delegate limit.
