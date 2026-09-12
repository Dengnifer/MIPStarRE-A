# PR 400: author repair after the fourth full review

This is an author disposition, not an independent review or an adjudication.
It addresses review [5151764063](https://github.com/Dengnifer/MIPStarRE-A/pull/400#pullrequestreview-5151764063)
at `0ddc67e8923f8d2c27cbb2fbce6ea9d495861257`, with four code findings and
twelve prose findings. The source is
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex`,
`def:ith-restricted-line` and its following observation (1038-1061),
`lem:qld-sublines` (1063-1116), and `claim:17-1` through `claim:17-3` (1140-1239).

## Preserved accounting

The four published full review rounds remain charged:

| Round | Review | Head |
| --- | --- | --- |
| 1 | 5147250926 | `37a2e268bc1ef7434e13c9b8b3daf3c02d18b94e` |
| 2 | 5147805296 | `abe2d5c42e25b0edbfef6b516039a295ffa81d97` |
| 3 | 5150130136 | `b94bd06f0c2b69579f97c065c44fe63f71f8c0d6` |
| 4 | 5151764063 | `0ddc67e8923f8d2c27cbb2fbce6ea9d495861257` |

No fifth review is requested. All earlier C1/C3 proof, compiler-drain,
publication, review, and attempt costs remain charged. B8 stays at 13 attempts
and 26509 working seconds. This author repair adds no mathematical proof
attempt and does not reopen the exhausted source obligations.
All prior commits and the earlier source-scope audit are preserved.

## Findings disposition

The identifiers below are lane-local; the combined GitHub ledger numbers the
prose findings F5-F16, after code F1-F4. "Repaired" describes the author's
change, not a reviewer approval. All paths abbreviated below are relative to
`MIPStarRE/QPBT/Combining/`, except the blueprint and paper-gap paths.

| Finding | Author disposition and evidence |
| --- | --- |
| Code F1 | Retained for main: consolidation of placement, product-average, completed-effect, and regrouping proofs in `Claims.lean:44` and `Claims.lean:178`. The shared alternatives are `Points/PlacementSupport.lean`, `Lines/RestrictedAverage.lean`, and `SubLineZDeficit.lean`. This re-raises the earlier duplication concern. It is a maintenance recommendation, not a source-certification repair; no proof rewrite is attempted. |
| Code F2 | Partly repaired: the unused public pass-through alias is removed and its sole call site uses `uniformDistribution_map_lineRepMap_add_smul` directly. The private bind proof at `UniformLinePoint.lean:36` and projection proof at `UniformLinePoint.lean:183` remain for main's maintenance disposition. |
| Code F3 | Repaired in `docs/paper-gaps/qpbt_ld-dimension-divisibility.tex`, section `sec:auxiliary-subline-scalars`: the marginal components are refined seed-bearing restrictions, with source push-forwards still open. |
| Code F4 | Repaired in the same section: joint point measurements are projective; paired-line measurements are complete, with no assertion of their projectivity. |
| Prose F1 | Repaired in blueprint `def:ith-restricted-line-refined`, `lem:restricted-line-refined-mixture-bounds`, and `lem:restricted-lines-completed-consistency`: auxiliary coordinates and sums use 0 through m-1, with chi-zero equal to the paper's chi minus one. Source indices stay one-based. |
| Prose F2 | Repaired by narrowing the certified definition to normalized restrictions and their total mass. Event mass 1/m is no longer asserted in that node; `clDistribution_seedEvent_mass` remains in `Lines/RestrictedMixture.lean`. Source push-forward assertions were removed from the certified node and identified as open outside it. No new result was invented. |
| Prose F3 | Repaired by removing `Placement.exists_isOpposite` and `uniformDistribution_map_uncurry` from the unrelated certified nodes `lem:qld-4-10-same-placement` and `lem:qld-sublines-uniform-point`. Both Lean declarations remain available. |
| Prose F4 | Repaired: the auxiliary scalar estimates' dependencies now occur in their proof blocks, and the Z estimate cites `lem:restricted-line-refined-mixture-bounds`. |
| Prose F5 | Repaired: `Defs.lean`, `Lines.lean`, `Lines/RestrictedAverage.lean`, `Lines/RestrictedMixture.lean`, and `Lines/SubLineMixture.lean` identify the seed-bearing or completed-answer auxiliary scope and corresponding blueprint labels. |
| Prose F6 | Repaired: numeric blueprint ranges are removed from the added subline support modules and `Points/PlacementSupport.lean`; durable labels and immutable paper locators remain. |
| Prose F7 | Repaired in `Claims.lean`: source claims remain open, the placement is described by its tensor bipartition, and the elaboration-process comment is removed. |
| Prose F8 | Repaired: the paragraph after `def:ith-restricted-line-refined` describes the distinction between the two laws rather than implementation progress. |
| Prose F9 | Retained for main: the inherited `SubLineRaw` naming family is unchanged (`Lines/SubLineConstruct.lean:53` and its consumers). A wholesale public rename is outside this author repair. Recommend treating it as advisory maintenance, with any tracking or final disposition assigned by main. |
| Prose F10 | Repaired: `uniformDistribution_map_lineRepMap_add_smul_current` is deleted; repository search found only its definition and the one call now redirected to the shared theorem. No downstream public statement changes. |
| Prose F11 | Repaired: `uniformDistribution_map_ldSeed` describes uniformity and the auxiliary construction, without the implementation-history sentence. The earlier duplication record is not erased from git history. |
| Prose F12 | Repaired: `Lines/SubLineMixture.lean` describes a distributional identity and explicitly states the directly indexed auxiliary scope. |

## Statement integrity

Paper assumptions: the source's seed-indexed line distributions, one-based
coordinate labels, and the measurements constructed by its preceding lemmas.
Lean assumptions: unchanged parameter types, zero-based `Fin m` restrictions,
seed-bearing descriptions, completed evaluations, projective joint point
measurements, complete paired-line measurements, and the directly indexed
`SubLineWitness`. No bridge, reality assumption, or projectivity hypothesis
has been added.

Paper conclusions: source restricted mixture and consistency estimates and
the complex scalar estimates of Claims 17-1 and 17-3. Lean conclusions:
unchanged auxiliary mixture, completed-consistency, and real-part estimates.
Verdict: faithful zero-based notation for the auxiliary statements; different
carriers and the weaker real-part Claim 17-1 remain explicitly distinguished
from the source. Source-labelled entries stay uncertified. The only deleted
Lean statement is a redundant alias, not a mathematical result.

## Validation and handoff

Single-file elaboration of `UniformLinePoint.lean` and `Claims.lean` passed;
the latter reports only its existing Claim 17-2 proof hole. The edited-module
scan finds that hole and the two existing joint-line construction holes in
`Lines.lean`, with no new axiom or proof bypass. The source-header checker
reports no changed public source-labelled headers. Hook installation,
whitespace, blueprint LaTeX conventions, paper-gap style, and paper-gap
reference checks pass. Blueprint web rendering and synchronization pass;
all 1421 generated declaration-list entries resolve. Existing repository-wide
statement-only and paper-gap-marker warnings remain warnings.

Checked branch publication and canonical exact-head CI follow this commit;
their results belong in the session handoff and GitHub evidence, not in a
rewritten historical review. Main owns final disposition of Code F1, the
remaining Code F2 parts, and Prose F9. The exact-head review/adjudication gate
must still be satisfied: the primary `pr_merge.py` requires a marker-bound
review on the final head even for adjudication. This author neither launches
a fifth review nor manufactures that evidence. The current-main ancestry
gate must also be checked by main before integration.

### Checked publication outcome

At 2026-09-09T16:53:06+08:00, checked publication of repair commit
`d688e60edb187f73d0cec004cb497eda921de060` had failed before push transport.
Every changed Lean file, the integrity audits, and blueprint rendering and
synchronization passed. The subsequent reverse-coverage warning check failed
on `git diff --merge-base origin/main HEAD`: Git reported multiple merge bases.
At diagnosis, `origin/main` was `1c297a4b8fb8a74b64784ba4c8fe7e10d0ffc6ee`;
the two bases were `a111c34ab3ca8b0db115b73156ddcd5bf886e9f8` and
`d9be57dedd4ea3a3321943539f0785fde00f172d`.

The remote PR head remained `0ddc67e8923f8d2c27cbb2fbce6ea9d495861257`.
No hook bypass, shared-ref change, integration merge, or workflow patch was
attempted. Main must resolve the publication precondition through its
authorized integration workflow before exact-head CI can run. The full-build
lock was not taken by this author repair, since no full build was started.
