<!-- mipstarre-review pr=483 head=f0ca102b27b601ff7c9c95e922d5c685a90cd155 -->
# Review - PR 483 @ f0ca102b27b601ff7c9c95e922d5c685a90cd155

Independent bounded correspondence recheck after the PR was retargeted to `main`.
This preserves the prior independent full review, review 5254705122 at
`0a391ac54f64529d7e95866166205285f11f0c55`, and its recorded costs.

## Findings

- [x] F1 (prior prose finding) `blueprint/src/chapter/ch15_qpbt_combining.tex` -
  the question/answer-role correction accepted by review 5254705122 remains on
  current `main`; the refreshed three-file patch does not regress it.

No unchecked findings.

## Review

**Correspondence scope.** Automatic carry-forward under `local/protocols/review.md`
section 13 does not apply literally: the approved head had a 16-file main-relative
patch (`+509/-55`), while current `main` has absorbed thirteen of those files and
the exact-head patch is now three files (`+89/-0`). The normalized whole-patch
hash therefore changed. I performed the permitted bounded fresh recheck of all
three remaining files; this is not a fifth full-review round or a counter reset.

**Whole current patch.** `MIPStarRE/QPBT/Combining/Lines.lean` adds the aggregate
import; `NondegenerateFiberCollision.lean` is byte-identical to the approved head;
and the 31-line subordinate blueprint node matches the Lean theorem's nonzero-line
hypothesis, distinct degree-bounded coefficient polynomials, unnormalized fiber
mass inequality, factor `c/q`, and formalization-only status. The proof is not a
duplicate Schwartz--Zippel argument: it specializes the existing unchanged
`linePointDist_nondegenerate_weighted_collision_le` API to the fixed-line
indicator and removes the direction indicator using `hdir`. The imported weighted
module, `LineDefs.lean`, and the cited paper mirror are byte-identical to the prior
approved review context. Current `main` contains neither this theorem nor its
blueprint node, so the patch remains substantive.

**Source fidelity.** Paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:950-955`, in the
proof of `lem:qld-xz-lines`, sets the pasting collision parameter to `md/q` by
Schwartz--Zippel. The generic Lean bound
`bound / Fintype.card (ScalarQ L)` is exactly that fixed-fiber ingredient after
specializing `bound = md`; no bridge, residual, fallback, extra conclusion-shaped
hypothesis, or weakened conclusion was introduced. This is a useful public
corollary supporting the pasting argument, not a claim that the distinct headline
combined-line construction is complete; absence of a current call site is not a
defect.

**Evidence and limits.** The published head and local worktree both read
`f0ca102b27b601ff7c9c95e922d5c685a90cd155`, and the worktree is clean. All nine
exact-head `local-ci/*` contexts are successful; `local-ci/summary` reports 408s.
The PR publication record also reports the supplemental blueprint axiom audit as
1,762 PASS, 0 FAIL, with no proof-level tag depending on `sorryAx`. I confirmed
the three-file `+89/-0` diff, `git diff --check`, unique declaration/blueprint
links, and no prohibited construct in the new module. I did not rerun CI, a full
build, or the already-passed module/root/declaration checks, and made no source or
status changes.

VERDICT: APPROVED (code=APPROVED, prose=APPROVED)
