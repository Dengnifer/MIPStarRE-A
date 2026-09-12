# Issue 515: Combined Line Measurement Consistency

## Statement Integrity

The source is `lem:qld-xz-lines`, especially
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:900-961`.
The blueprint entries are `lem:qld-xz-lines` and
`lem:combined-line-measurement-consistency`.

The paper starts with a normalized projective strategy passing with error
`epsilon` and the previously constructed joint projective point measurements.
Their self-consistency and both ordered-product comparisons hold with
polynomially small point error. It concludes evaluated consistency of the
explicit X-Z-X line POVM on two independent line-point samples, in every
opposite placement, with polynomial error in `epsilon` and `md/q`.

The internal Lean theorem first fixes `deltaQ` and `IsPolyErr deltaQ`, then
chooses `deltaP`. It quantifies over admissible parameters, a projective
setting, a `CombinedPointsWitness S (deltaQ epsilon)`, and every directed
opposite placement. Its conclusion concerns `S.combinedLineMeasurement`
itself under the original product distribution. The target header is
byte-for-byte unchanged from `ae124f8f09ee002444ac5b9711822c0f1daae142`.

Verdict: exact preservation of the existing internal theorem. The source
existence theorem still obtains its point witness internally. No new
hypothesis, altered quantifier, weakened conclusion, changed measurement,
or error convention is introduced. The existing additive interpretation of
two-variable polynomial error is retained.

## Mathematical Proof

The two completed point-to-line marginal defects are at most
`Delta = 8 * deltaQ(epsilon) + C * (epsilon + sqrt(epsilon))`.
Conditioning on a nonzero X-line direction retains mass `r >= 1/2` and
increases these bounds to `Delta/r`. Uniform affine resampling and the
coefficient-polynomial root bound give the conditional collision estimate
`md/q`. These facts are proved, not assumed.

The existing heterogeneous pasting theorem needs only the two marginal
comparisons. Reindexing each directed opposite placement preserves the state
norm and all consistency expressions; the unused registers stay on the
line side. Ordering answers Z then X makes its output exactly the X-Z-X
sandwich. Reversing the answer order preserves the defect.

The measurement does not change on conditioning. The discarded mass is at
most `1/(2q)`, and every pointwise defect is at most one. Restoration gives
`r * pastingError(md/q, Delta/r) + 1/(2q)`. The independent unit bound and
the existing `exists_conditioned_polynomial_bound` produce `deltaP`.

## Recovered Proofs

The complete earlier construction was saved in
`f6a340c8dc3c12566d9312215c578939efeb8b4a`, in
`exists_combinedLinesWitness_ofPointsWitness`. Its X-Z-X construction,
register transport, answer permutation, and final scalar argument are
reused in the three new consistency modules and the target proof.
The current heterogeneous theorem replaces the older three-comparison API.

The prerequisite modules below were recovered selectively from saved commits.
No entire branch, workflow file, or unrelated theorem was adopted.

| Module below Combining | Source Commit |
| --- | --- |
| `Lines/AffineEvaluation.lean` | `a78776b60809389a79b13495d7dff1732c329cfa` |
| `Lines/AxisLineResampling.lean` | `2fc7a102dfdbcba2e10d2909e068835c2676e9b5` |
| `Lines/CombinedPointLineMarginalDefect.lean` | `1a758a6ed24485393986dfa45cf3e864f6859dff` |
| `Lines/CombinedPointLineMarginalDistance.lean` | `c5d1bb3ee4d0fe0faaede13506860cb88a86eeba` |
| `Lines/ConditionalCollision.lean` | `35e546a6f1f44984cae2eb59bf0b69866d131155` |
| `Lines/ConditionedPastingDefect.lean` | `d202314f1a3d899c5fc5ae591ba9694c3544c3e0` |
| `Lines/ConditionedPointLineMarginalDefect.lean` | `5ec10637448447af76c8bc965bd15d5f1acfbc6a` |
| `Lines/DiagonalZeroDirectionMass.lean` | `549ce1e4a117b52facddb4730e7f82953e915d1d` |
| `Lines/FiberCollision.lean` | `35e546a6f1f44984cae2eb59bf0b69866d131155` |
| `Lines/MixedResampling.lean` | `85a5d78b7c9ed98fd70e025cda93cb10531a176e` |
| `Lines/MixedZeroDirectionMass.lean` | `01513e10a03fb909c6f517caf9763e409bc8fbfb` |
| `Lines/NondegeneratePastingDistribution.lean` | `629c9f1679af95b30248a6a992cdd9513f7defb0` |
| `Lines/NondegeneratePastingMass.lean` | `d3af665fa869416f99fafdb6906c1809ba77e8e1` |
| `Lines/OptionPointMarginalTransport.lean` | `0ad2261cd63916becb5af914c630cd23a5a8d002` |
| `Lines/OptionPostprocessDistance.lean` | `c8076b9bad449b6ad58dfc6a57dcb5619fdf0a3f` |
| `Lines/PastingRestoration.lean` | `c605ac8670a149d1fddb0f01f7cbdd4b5ad84801` |
| `Lines/PointMarginalTransport.lean` | `dca04c7b92d617e7de0c0eee513c9b1d943eacc3` |
| `Lines/PointSelfConsistency.lean` | `0db47321ddc0f010f23f816a4aed0415d3f48533` |
| `Lines/ProductWeightedCollision.lean` | `d56ba35c9be8c22fedb75b1873f8d1431c276512` |
| `Lines/RestrictedConsistency.lean` | `91b6dad3d200d59f205fbbb546d878e529a8729a` |
| `Lines/SamePlacementDistance.lean` | `a635df177dd363aa139f1e941f7a235930b8d836` |
| `Lines/UniformAffineCollision.lean` | `f15d0fc5721622360564b8083577dba1f02bfc04` |
| `Lines/WeightedCollision.lean` | `7e28563a6a942eb09898546225fa6f85938f2ca7` |
| `Lines/ZeroDirectionMass.lean` | `5922ecc4d5692d1f0a66d853c90bf7a24952159b` |
| `Points/WitnessMarginals.lean` | `1bdbbb4bf3d93656d2b081ce61322aca68ba731e` |

Two further required helpers are recovered from existing-file changes:
`avgOver_lineRepMap_resample_parameter` in `Lines/SubLineUniform.lean`
from `2fc7a102dfdbcba2e10d2909e068835c2676e9b5`, and the restricted-mass
identities in `Games/RestrictedAverage.lean` from
`91b6dad3d200d59f205fbbb546d878e529a8729a`.
The point-marginal projection identities are recovered from `f6a340c8`.
The existing support-based `avgOver_mix` replaces a duplicated helper;
the existing coefficient root bound avoids the unused polynomial adapter.
Missing historical blueprint labels are replaced by the actual source citation.

## Validation

Focused Lean checks passed for the new pasting application, restoration,
and `Lines.lean`, using the checkout's Lean 4.32.0 toolchain.
The target, both combined-line witness existence theorems, both quantitative
consistency estimates, and heterogeneous pasting have axiom closure exactly
`[propext, Classical.choice, Quot.sound]`. There is no `sorryAx` dependency.
The changed proof files contain no proof holes, new axioms, or kernel bypasses.
The target header comparison and whitespace check pass.

The locked full build passed (9,248 jobs), and `leanblueprint web` and
blueprint declaration synchronization passed. The web render retains existing
bibliography warnings. Publication checks are recorded separately in the
session handoff; no independent review is claimed by this author session.

The first published-head CI passed the mathematical and rendering checks,
but one model-policy fixture failed because it inherited the prover's
hardness reason while selecting a bounded job. The exact test passes with
`MIPSTARRE_JOB_CLASS` and `MIPSTARRE_HARDNESS_REASON` unset in addition to
the invoking, review, and prose model settings. The incident is recorded in
`results/telemetry/events.md` at 2026-09-12T05:37Z. No workflow or fixture
code is changed to obtain that result.

## Prior Work and Accounting

This packet continues the existing #118 episode. The preserved historical
checkpoint is 13 attempts and 26,509 working seconds, recorded in
`audits/2026-09-09_subline-scalar-realignment.md`. In particular,
`mathfix-118-20260906-08` saved `f6a340c8` and validation commit
`61750e7c41c1ea246333afc1f2aa173e915dba07` before its 2,700-second timeout.
Those costs are included in the historical total, not counted again.
The timeout's zero usage fields do not establish zero model work.

Later relevant external records are also retained: the #445 proof and
publication sessions took 2,735 and 2,040 seconds; the #490 proof and
publication sessions took 4,161 and 1,821 seconds; and the #414 publication
repair took 3,880 seconds and failed. These five records total 14,637 seconds,
separately from the earlier 26,509-second mathematical-gap checkpoint. This is
an identified subtotal, not a complete cost total for all prerequisite lanes;
owner records and missing usage remain in their original telemetry.

Session `prover-515-20260912-01` is additional work under the owner's renewed
60-active-minute authorization. Its dispatcher supplies final time and token
accounting. No previous attempt or cost is reset, and no subagent is launched.
The first dependency checks exposed omitted saved helper declarations and
obsolete API names; these were repaired by recovering existing proofs and
using the current APIs.

The extended-line distribution and scalar obligations are separate and remain
outside this packet. Independent review and the ordinary exact-head CI gate
remain required before merge.
