# HANDOVER AT THE 04:00 PAUSE

Owner-requested graceful landing, 2026-09-22 19:30Z (03:30 China).
The project is not complete. No new worker, review, CI or train is authorized
until the owner resumes it. The allocation on resumption, unless superseded,
is space-d only: one main and at most one gpt-5.6-sol ultra worker, using default
dispatch/review routing. No hard-job or Astra override for helpers, no native
delegate, no other key, no proxy or subscription login. Continue to document
intermediate deviations; do not restart the deferred proof tasks.

The already-running issue713 task and PR716 CI have both finished normally.
All queued wrappers have exited without admitting another worker or review,
the merge services have stopped, and every open claim has been released.
No process was killed. Their final receipts are recorded below.

## Completion Evidence

Read-only `python3 scripts/completion_gate.py check --track qpbt` at exact main
`f3282cce948576e83fabbcba4aa4ef89b9d6fdf7` returned exit 1:

```text
completion gate: track qpbt  commit f3282cce9485
C1 proof integrity        PASS      340 Lean files, no site
C2 headline axioms        DELEGATED all 4 headline theorems asserted
C3 paper gaps terminal    FAIL      9 of 21 rows not terminal
C4 blueprint marked       FAIL      3 of 547 linked nodes unmarked and unexempted
C5 lean comparator        DELEGATED verified library ecb97d1f66ee
C6 docs truthful          PASS      1 registered document checked
C7 artifact readiness     DELEGATED all 6 registered artifact files present
FAIL: C3, C4 - the track is not finished
```

This inventory command launches no Lean build or CI. Its C6 check is narrow;
the final truthfulness pass remains required. The built headline axiom audit,
marked blueprint axiom audit, comparator drift check, and final authored and
anonymous artifact checks remain required on the eventual final commit.
The new telemetry commits after this check do not constitute a final gate run.

## Every Register Row

Names below are files under `docs/paper-gaps/`. "Closed" means terminal in the
current register; it does not claim a divergent printed intermediate is proved.
The register has 21 rows: 12 terminal and nine nonterminal. The proposed
combining-map row in PR723's repair is additional and is not yet on main.

| Note | Main status | Work at pause |
|---|---|---|
| qpbt_anticommuting-probability.tex | no-difference | Closed. |
| qpbt_characteristic-two-pauli-scope.tex | no-difference | Closed; general-prime construction is merged. |
| qpbt_combined-lines-error-term.tex | open | Issue713 integrated locally at 8536f34a1a8d252f4daa5291a904c7808fa495c8; clean, unpublished, no PR/CI/review yet. |
| qpbt_cross-basis-phase.tex | corrected | Closed; PR672 adoption evidence retained. |
| qpbt_decoding-identity.tex | corrected | Closed; PR672 adoption evidence retained. |
| qpbt_delta-bound-exponent-comparison.tex | no-difference | Closed. |
| qpbt_extraction-transfer.tex | no-difference | Closed. |
| qpbt_raw-pauli-effects.tex | no-difference | Closed; the headline uses raw prescribed effects. |
| qpbt_ld-dimension-divisibility.tex | open | PR716 at 7c6f5cdf, full CI green, SECOND review not started; marked axiom audit still required. |
| qpbt_ld-simultaneous-sandwich.tex | no-difference | Closed; do not conflate this with the dimension/import deviation. |
| qpbt_ld-sandwich-indexing.tex | corrected | Closed. |
| qpbt_linearity-distance-normalization.tex | pending | PR725 at 7f59d0e3, full CI green, FIRST review not started. |
| qpbt_linearity-theorem-quotation.tex | open | Issue720 brief prepared, author not started. |
| qpbt_ms-rigidity-symmetric-strategies.tex | pending | PR726 at 456b0d16, full CI green, FIRST review not started. |
| qpbt_pauli-binary-factor-index.tex | corrected | Closed. |
| qpbt_pasting-product-error.tex | pending | PR717 at da1201c5, full CI green, SECOND review not started. |
| qpbt_polynomial-error-square-root.tex | pending | PR715 at b5a68dcc, full CI green, SECOND review not started. |
| qpbt_symmetrization-attainment.tex | documented-deviation | Closed by merged PR707, 0771440bb2dd9f7cc7f702300839a44051277dd0. |
| qpbt_win-implications-corrections.tex | pending | PR724 at d2e98314, full CI green, FIRST review not started. |
| qpbt_combined-points-field-valued.tex | no-difference | Closed; distinct source padding issue remains in issue720. |
| qpbt_subline-claims-line-marginal.tex | open | Issue721 brief prepared, author not started; PR696's direct complex bounds are merged. |

The nine proposed documentary closures do not change statements or prove the
printed forms. Each requires the TeX note, blueprint remark, terminal register
row, and DEVIATIONS disclosure, plus complete CI and independent review.

## Blueprint Nodes

The gate inspected all 547 linked nodes. Apart from the three listed failures,
544 satisfy its static mark/exemption condition; the full marked axiom audit
is separate. The former completion obligations and coordinated repairs are:

| Node | State at pause |
|---|---|
| def:canonical-complement | Closed: deterministic algorithm/cost PR708 merged 7b9dd8f2e77eb20d59e8fac878d89fe0c9854fa9. |
| lem:canonical-complement | Closed: correspondence PR691 merged 968b0cc3b29c53f1b2ee6ec7feb137f6ae3272a9. |
| def:generalized-pauli | Closed: general-prime formalization marked on main. |
| lem:pauli-observable-expansion | Closed: general-prime statement and proof marked. |
| def:cl-func | Closed: faithful recursive definition marked. |
| def:cl-dist | Closed: shared-seed distribution marked. |
| def:typed-cl-functions | Closed: typed recursive definition marked. |
| def:typed-cl-distributions | Closed: typed shared-seed distribution marked. |
| lem:qld-xz-lines | Unmarked/unexempted on main; issue721 brief includes the reasoned completed-evaluation/source-law exemption. Author not started. |
| def:combine-map | Unmarked/unexempted on main; PR723 proposes a reasoned carrier-mismatch exemption. Its documentary repair is prepared but not started. |
| lem:qld-4-13 | Unmarked/unexempted on main; issue713's local documentation adds the reasoned unproved/unrefuted-rate exemption. No source mark is authorized. |
| lem:ld-soundness | Additional review-discovered mismatch: PR716 removes the unsupported source mark and adds an exemption; a separate lem:ld-soundness-formalized node states the completed-POVM result with its marks. SECOND review remains. |

Keep the established combined-line support node's marks and its explicit
direct-carrier, completed-evaluation and error qualifications. Existing sync
warnings (four chapter16 orphan marks and two statement/proof asymmetries)
must be considered in the final truthfulness pass; static sync success is not
a blanket semantic certification. The current exemption document also retains
stale prose saying PR708 is unmerged. The final pass must reconcile it.

## Every Open PR

The following complete list was read from GitHub, not inferred from worktrees.
Full head SHAs distinguish current CI from earlier adverse-review heads.

| PR | Head | CI and review state |
|---|---|---|
| 715 | b5a68dcc9e4ac40978ee269af202acfba2f12c6b | CI green; SECOND independent review required. Prior sole finding was common PR707 support, now integrated. |
| 716 | 7c6f5cdf3b28657c8cee164095034418d5c20fa0 | CI green; SECOND independent review and full marked axiom audit required after the source/completed-POVM repair. |
| 717 | da1201c55461eefb3c166a638e231754686372a9 | CI green; SECOND independent review required after wording repair and PR707 integration. |
| 723 | 94a4bafeb598688427a95e460e01cbe956c279d8 | CI green; FIRST review 5282487123 requests changes: three entries, two distinct documentary defects. |
| 724 | d2e98314c187ae8fb9a8f0a0c8eb29ba6655b126 | CI green; FIRST review not started. |
| 725 | 7f59d0e3b9008054226cebf7f43d04e9dacdf4af | CI green; FIRST review not started. |
| 726 | 456b0d160ec81c459aa166e058a6a8e05ca74b9f | CI green; FIRST review not started. |
| 552 | 722b62ef5e697d27bb4ddb9684618d2a187ff6cf | Owner-parked infrastructure; CI green, changes requested, 11 findings. |
| 554 | da37ea065b81034b9be3f25d4a4967bfab40b266 | Owner-parked infrastructure; CI green, changes requested, two findings. |
| 556 | 48641733e827af326e54a873e5ab8f1e41b69822 | Owner-parked infrastructure; CI green, changes requested, seven findings. |
| 561 | 082b3b3f8094ce3a27e8964555f91710c4bb09b9 | Owner-parked infrastructure; CI green, changes requested, nine findings. |

PR723 repair packet `/tmp/main-fix723-documentary-record-20260922.md` corrects
the false 19-of-21 note inventory and supplies a dedicated TeX combining-map
note plus terminal register row. Both reviewers accepted the mathematical
singleton comparison and its limited conclusion. Do not modify issue721's
separate subline note/row, import PR706, or add proof work. One 3600s repair,
full CI, then SECOND independent review; the queued repair never started.

## Local Work Preserved

All published documentation worktrees have their branch names from the PRs;
their seven paths begin with issues710,711,712,714,718,719,722 under
`/home/drx/MIPStarRE-qpbt/.worktrees/`. Each published head was checked clean.
Issue713 is the only unpublished documentary task and is finalized below.

- `.worktrees/issue-697-linearity-padding-20260922`: local HEAD
  `af2bde5948516f4ea00633742aa3044f9932b5c0`, retained MERGE_HEAD
  `498299c63793d83179b7d1f929475200dd08c144`. Three unmerged paths:
  `MIPStarRE/QPBT.lean`, `blueprint/src/chapter/ch15_qpbt_combining.tex`, and
  `local/registry/declaration-claims.jsonl`. PR702 is closed unmerged at
  published `b167f8e1368060201f5bb8fbf7dca961230d10da`. Preserve all work.
- `.worktrees/issue-698-geometric-line-functions-20260922`: local HEAD
  `ff0242149723d3a8bc01adb9712083cba00cf111`, MERGE_HEAD
  `87837aff5d2ce366976850e8a93a587e1ae2de20`; the exemption-file conflict and
  all incoming staged changes remain. No proof continuation is authorized.
- `.worktrees/issue-704-tensor-code-import-20260922`: clean local HEAD
  `9f9e62eab8233e6f552bdfac013248bc2ddd9f4f`. Original 3264s and interrupted
  sole continuation 3387s remain recorded; missing token usage is not zero.
- `.worktrees/issue-701-ms-prescribed-extraction-20260922`: clean published
  `5edfe0e21cb75a2c696718d8378fe298b47a462c`. PR706 is closed unmerged
  after its allowed continuation; do not claim this proof is on main.
- `/home/drx/QPBT-comparator`: the owner's original draft checkout still has
  modified and untracked challenge files. Do not reset, clean or stash it.
  Use the separate clean `/tmp/qpbt-comparator-rename-705-20260922` checkout
  or a new isolated checkout for final comparator work.

All earlier attempts, failed validations, review rounds and session costs are
retained. A new integration or review does not renew a proof budget.

## Comparator and Artifact

GitHub rechecked the official runs as completed/success:
35638601720 at challenge `360402fdf4a39399f94331452d6e5d0a35c144be`, and its
main rerun 35741427654. Comparator main is still that challenge, pinned to
library `ecb97d1f66eec1e6fad964f144f78b91ce1fab36`. PR677's verification record
is merged as `c7f473e117c6b0ca6220835bb18333e17400ed50`.

The renamed-library URL commit `0f02b0b980041b7ef0f490f9adc18d2a61283121`
on comparator branch `issue-662-closure-20260921-diagnostic` also passed official
run35742141249. It has not been promoted to comparator main; main's manifest
still has the redirected old URL. Library rename/packaging PR709 is merged as
`6bf80a37ffcd9eeea1891d8c333fd2e3b645dee0`.

No run certifies the eventual final library commit yet. Finish library changes
and records, freeze exact main C, obtain the final exact-C gate and delegated
evidence, pin the comparator to C, get all four official targets accepted, and
fast-forward comparator main to verified challenge F. Record C/F/run and the
artifact manifest in the final evidence without moving library main afterward.
Read `/tmp/main-final-truthfulness-and-evidence-20260922.md` for the prepared
ordering and the distinction between the historical in-repository record and
the immutable final evidence.

The artifact guide PR681 is merged (`1482a2020db6045ea32c2c1467d33a6d9e3845d9`).
The earlier packaging preflight passed 49 PDF/leak checks, but it is not final.
`/tmp/main-final-artifact-links-20260922.md` retains three known reference
defects: a link to an audit excluded from the artifact and two nonexistent LDT
source filenames. Recheck all links after exemptions land; do not ship essential
mathematical exposition only in an excluded audit.

## First Steps After Owner Resumption

1. Read this final handover and current snapshot; re-enable only the owner's
   authorized one-Sol space-d layout. Old blocked queue processes must be gone
   before restarting anything. Re-claim every touched PR and preserve dirty
   worktrees. Never reuse an Astra-forcing historical wrapper.
2. Review green PR715 and PR717 (SECOND), then PR716 (SECOND),
   and PR725/724/726 (FIRST), one worker at a time. Use 2700s review phases and
   default Sol ultra routing. Revalidate exact heads and actual CI first.
   Before gating PR716, run the full marked blueprint axiom audit requested
   by its CI warning; its green summary does not discharge that extra check.
3. Publish issue713's preserved final local commit, run full CI, then FIRST
   review. Complete PR723's prepared single documentary repair, CI and SECOND
   review. Do not erase previous findings or report queued reviews as done.
4. Admit the unstarted 3600s documentation briefs
   `/tmp/main-document-subline-20260922.md` (issue721, including qld-xz-lines)
   and `/tmp/main-document-linearity-quotation-20260922.md` (issue720), one at
   a time. No new proofs for any register row.
5. Let canonical gates and the model-free service merge reviewed work after
   explicit resumption. A fresh approved ancestor PR merges alone, never in a
   train. Integrate shared register/exemption prose without dropping another
   row. Restore the merge machinery only as authorized; do not merge by hand.
6. Finish artifact references and the complete truthfulness pass, then the
   exact-commit completion gate, delegated audits, final artifact and comparator
   verification described above. Post the final completion evidence only when
   all requirements actually pass; no issue168 updates.

## Graceful Landing

At 19:30Z the worker/review queue had one running Sol integration (issue713),
one queued PR723 repair, and the queued row reviews. The latter had not made
model calls. The pause marker, zero worker admission caps, goal-keeper stop,
merge-loop stop, and daemon stop were installed without sending process signals.
The PR716 CI-review watcher exited at its pause guard; its review never started.

Timing exception: the pre-existing PR716 publication wrapper entered `ci.sh`
and claimed CI at 19:30:59Z during the pause transition. The owner said nothing
was to be killed, so this already-entered run was allowed to finish; no further
CI was launched manually. The wrapper lacked an admission guard between its
checked push and CI. Its final outcome and all claims are resolved below.

Final outcomes:

- Issue713 session `orc-713-20260923-02` ended normally at 19:40:35Z, exit0,
  1052s. Final local head `8536f34a1a8d252f4daa5291a904c7808fa495c8` has parents
  `6cda45af97dfb87745105afb5b6a8067b8300aa7` and
  `0771440bb2dd9f7cc7f702300839a44051277dd0`. MERGE_HEAD is cleared and the
  worktree is clean. The original authored row/exemption and all incoming
  changes were preserved. Web, sync, all 1920 declarations and normal hooks
  passed: 876 tests in343.695s, nine existing skips. The local static gate
  still fails for eight other rows and two other nodes; this is not the main
  gate result. Exact receipt:
  `/tmp/main-sol-c4-integration-preserved713-20260922-result.md`.
- PR716's publication/CI wrapper exited0; GitHub confirmed all `local-ci/*`
  contexts successful at `7c6f5cdf3b28657c8cee164095034418d5c20fa0`. Its CI
  manifest is `~/.cache/mipstarre-dev/ci-manifests/pr716-7c6f5cdf3b28657c8cee164095034418d5c20fa0.json`.
  The CI explicitly warns that the full marked axiom audit must still run.
  No second review started. The wrapper released main-ci716 normally.
- The pending PR723 repair exited1 at its pause guard; no model task started.
  PR715's waiting review exited1 at the same guard and the remaining row
  queue exited3. The PR716 CI-to-review watcher exited1 on the pause marker.
  These are intentional non-admissions, not completed or failed reviews.
- Main released main-fix713 with the clean unpublished head, outstanding
  publication/CI/audit/FIRST-review work, and owner-pause reason. The complete
  append-only claim ledger was then checked: zero open claims for either
  party. All recorded worker, CI, queue, merge-loop and daemon PIDs were gone.
- Worker caps are0/0/0. `watchdog/paused`, `goal-keeper.stop`,
  `meta-auto-merge.stop` and `daemon/stop` remain set. Space-d is not retired;
  this is an owner pause. The session remains open. Resume only on the owner's
  word, then restore the authorized one-Sol allocation and re-claim work.

The telemetry record and completed session capture are published through
`bash /tmp/meta-records.sh`; the final remote-main verification is included
with this same handover in `/tmp/qpbt-main-handoff-v5.md` and the single closing
comment on issue27. The final operation is `/goal pause`, not `/quit` and not
a declaration of project completion.
