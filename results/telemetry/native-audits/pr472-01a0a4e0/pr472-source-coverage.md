# PR472 / Issue468: Published-Main Source-Semantic Coverage

## Verdict And Scope

**Fully covered mathematically for issue468's conditioned point-line marginal
task, with unique documentation enumerated below.** Published main already proves
both estimates, on exactly the PR's domain, with exactly its sampler, directed
placements, completion, answer order, and error bound. There is no missing
issue468 proof obligation to discharge before using these estimates on main.

This is not a canonical review, approval, or assertion that the entire ancestral
PR472 diff has been integrated without loss. In particular, PR-specific blueprint
labels and inherited standalone self-consistency helpers are not thereby accounted
for. No lifecycle action is authorized by this report.

- Audit worktree: `/home/drx/MIPStarRE-qpbt/.worktrees/issue-468-main-coverage`.
- Published main and audit HEAD: `bf864c016b3426a690c02f93bea9d40986604195`.
- Read-only PR472 head: `cfdebb0ec47e9cc61242862c09b53db85096c12b`.
- GitHub reports PR472 OPEN, branch `issue-468-conditioned-point-line-marginals`,
  base `issue-463-conditioned-pasting-defect` at
  `d202314f1a3d899c5fc5ae591ba9694c3544c3e0`.
- GitHub's main ref was independently read through primary `gh_common.py` and
  still named `bf864c016b3426a690c02f93bea9d40986604195`.
- The issue468 implementation commit `5ec10637448447af76c8bc965bd15d5f1acfbc6a`
  adds the conditioned marginal theorem and its re-export. This identifies the
  task boundary; ancestry is not used as evidence of mathematical coverage.
- PR487's supplied report was read only for context. Neither its unpublished
  integration `7c3b54bcdf4627a3efa5164dc2a5066e883cfe16` nor any of its compiled
  proof artifacts was used as published-main evidence.

## Source And Domain

Primary source passages read:

1. `references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex`,
   `def:line-point-dist`, lines 274-287: the equal mixture of axis and diagonal
   CL line-point laws, not a uniform distribution on every line description.
2. `references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex`,
   `eq:qld-q-self-cons`, lines 693-697, in `lem:qld-4-10`: the constructed joint
   projective point family is self-consistent on uniform independent point pairs;
   the lemma also supplies both ordered-product comparisons and their symmetric
   equivalents.
3. The same file, `lem:qld-xz-lines`, lines 882-894 and proof lines 900-963,
   especially `eq:pasting-q1`: the two marginal inputs are compared on independent
   draws from the source line-point law. Pasting and joint point self-consistency
   subsequently produce an unconditioned paired-line consistency statement.

The common Lean domain, unchanged between PR and main, is as follows.

- `P : AdmissibleParams`: natural `q,m,d`, `1 <= d`,
  `q = 2^k` for an odd natural `k`, and `m` divides `q`. Thus `m >= 1` and `q > 0`.
  The finite scalar field is the fixed `PauliScalar P` model. No bound such as
  `m = 1`, `d < q`, or `m*d < q` is added. The existing positive-degree convention
  is explicit here; the cited paper prints natural-number parameters without
  separately resolving its convention for degree zero. This audit does not claim
  a new extension to `d = 0`.
- `epsilon, deltaQ : Real` are arbitrary, including zero. There is no additional
  small-error, strict-positivity, or polynomial-error premise on these scalars.
- `S : ProjectiveSetting P epsilon` contains a bipartite strategy with separate
  finite-dimensional player spaces, a unit state, complete measurements,
  projectivity of both players' measurements, and value at least `1 - epsilon`.
  Equal player dimensions, strategy symmetry, and traciality are not assumed.
- `points : CombinedPointsWitness S deltaQ` supplies complete projective
  measurements `Q_side(x,z)` on the expanded local spaces, with answers `(a,b)`
  in the scalar-field square. On uniform independent `(x,z)`, it bounds by
  `deltaQ` each of: joint self-distance across opposite placements; distance to
  the opposite product `M_X(x,a) M_Z(z,b)`; and distance to the opposite product
  `M_Z(z,b) M_X(x,a)`. These are three distinct fields, all quantified over every
  directed opposite pair. The witness is an explicit auxiliary input, not a
  witness constructed by the theorem under audit.
- `p1.IsOpposite p2` is exactly the four directed pairs
  `(AA', BA'')`, `(BA'', AA')`, `(BB', AB'')`, `(AB'', BB')`.
  Each effect uses the measurement on that placement's own player side.
  The state is the strategy state tensored with the two EPR states and shuffled
  into the six-register order. No placement or reversal is omitted.

Let `D = linePointDist P.toLdParams`,
`s = ((ell_X,x),(ell_Z,z)) ~ D x D`, and

`E(s) := ell_X.direction != 0`,
`r := Pr[E] = nondegenerateLinePastingMass P.toLdParams`.

The conditioned law first restricts `D x D` to `E` and divides its weights by
`r`, then sends `s` to

`q = (((ell_X,ell_Z),(ell_Z,z)),(ell_X,x))`.

Thus `q.1.1` is the common line pair, `q.1.2` is the Z line-point sample,
and `q.2` is the X line-point sample. The inverse used in the generic estimate
is `(q.2,q.1.2)`. Only the X direction is restricted; zero Z directions remain.
The denominator is this exact retained mass, not its square, not the mass of
two nonzero directions, and not a replacement by `1 - 1/(2q)`. The common
proved bounds are `1/2 <= r <= 1`, so positivity is derived, not assumed.

Write `Q^+_XZ = Q.postprocess (a,b -> (some a,some b))` and
`Q^+_ZX = Q.postprocess (a,b -> (some b,some a))`.
The point completion adds zero effects whenever either answer is `none`.
`L_W(ell,u)` denotes `lineEvalMeasExp`, the expanded line measurement
postprocessed by `evalOpt ell u`, with answers in `Option F_q`. Its `none`
effect collects polynomials without a well-defined evaluation; it is not
silently deleted. Put `B_C = 8*deltaQ + C*(epsilon + sqrt(epsilon))`;
`deltaLine epsilon` is definitionally `sqrt(epsilon)` on both commits.

For placed complete measurements, the consistency defect is the average of
`sum_{a != b} Re <psiHat, A_a B_b psiHat>`. Squared distance instead averages
`sum_a ||(A_a-B_a) psiHat||^2`. These two conclusions are not conflated.

## Mathematical Coverage Table

All names below are in `MIPStarRE.QPBT`. Paths are relative to
`MIPStarRE/QPBT/Combining/Lines/`; line references identify the audited snapshots.
The same-named compiled signatures were compared, not merely their names.

| PR declaration and location | Published-main counterpart | Complete contract beyond the common domain | Result |
| --- | --- | --- | --- |
| `exists_combinedPoints_conditioned_line_marginal_defect_le`, `ConditionedPointLineMarginalDefect.lean:25` | Same name, `Conditioning.lean:65` | `exists C >= 1`, before all `P,epsilon,deltaQ,S,points,p1,p2`; on the conditioned law above, `fst Q^+_ZX` on `p1` versus `L_Z(ell_Z,z)` on `p2` has defect `<= B_C/r`, AND `snd Q^+_ZX` versus `L_X(ell_X,x)` has defect `<= B_C/r`. Same constant in both conclusions. | Exact; both Z-then-X comparisons covered. |
| `consistencyDefect_nondegenerateLinePastingDist_le`, `ConditionedPastingDefect.lean:24` | Same name, `Conditioning.lean:36` | Arbitrary universe-polymorphic finite decidable `Outcome`; two families of COMPLETE measurements on the respective expanded spaces, indexed by the entire source sample `s`; every directed opposite pair. No `points`, projectivity of these two families, or defect-bound premise. Defect on the relabelled conditioned law `<=` the original `D x D` defect divided by `r`. | Exact; nonnegativity is proved from positivity on disjoint registers. |
| `exists_combinedPoints_line_marginal_defect_le`, `CombinedPointLineMarginalDefect.lean:25` | Same name, `PointComparison.lean:343` | Same universal-constant order and common domain; unconditioned `D x D`; `fst Q^+_XZ` versus X line, AND `snd Q^+_XZ` versus Z line, with point on `p1`, line on `p2`; defect `<= B_C` for each. Denominator 1. | Exact antecedent; no point error dropped. |
| `exists_combinedPoints_line_marginal_distance_le`, `CombinedPointLineMarginalDistance.lean:25` | Same name, `PointComparison.lean:245` | Same domain/order as preceding row; first take the X or Z coordinate and then postprocess by `some`; corresponding squared distances, not defects, are `<= B_C`. | Exact. |
| `exists_expLine_point_same_placement_distance_le`, `SamePlacementDistance.lean:30` | Same name, `PointComparison.lean:204` | `exists C >= 1`, then all `P,epsilon,S,p1,p2`, opposite premise, then every `W`; no supplied point witness. On one draw from `D`, evaluated line and completed point are BOTH placed on `p2`; squared distance `<= C*(epsilon+sqrt(epsilon))`. | Exact; every placement has an opposite. |

The remaining nine shared declarations complete the checked set of fourteen:

| PR declaration(s) | Main location | Domain, sampling, and conclusion |
| --- | --- | --- |
| `avgOver_linePointDist_point`, `avgOver_prod_linePointDist_points` in `PointSelfConsistency.lean:60,76` | `PointComparison.lean:35,49` | Every `L : LdParams` (`q,m,d,k` natural, `m,d,k >= 1`, admissible q, `m` divides q), every real function on a point or point pair. Point averages under `D` or `D x D` equal uniform point or point-pair averages exactly. No strategy, placement, completion, or error. |
| `CombinedPointsWitness.postprocess_fst_effect`, `.postprocess_snd_effect` in the imported `Combining/Points.lean:52,67` | `PointComparison.lean:66,82` | Common witness domain, every side and every `x,z` and field answer: the X or Z postprocessed effect equals the finite sum over the omitted field coordinate. Pointwise identities, no sampler or opposite-placement premise. |
| `CombinedPointsWitness.marginal_X_linePoint_distance_le`, `.marginal_Z_linePoint_distance_le` in `PointMarginalTransport.lean:29,51` | `PointComparison.lean:96,118` | Common witness domain and every directed opposite pair. On `D x D`, X or Z marginal of Q on `p1` versus the corresponding expanded POINT on `p2` has squared distance `<= 4*deltaQ`. Field answers, denominator 1. |
| `ProjectiveSetting.opFamilyDistSq_postprocess_some` in `OptionPostprocessDistance.lean:30` | `PointComparison.lean:140` | Every `P,epsilon,S`; arbitrary `Sample : Type*`, finite decidable `Answer`, any finite-support `Distribution Sample`, any placements (NOT necessarily opposite), two complete measurement families. Adding a zero `none` answer preserves squared distance exactly. No witness or error premise. |
| `CombinedPointsWitness.marginal_X_option_linePoint_distance_le`, `.marginal_Z_option_linePoint_distance_le` in `OptionPointMarginalTransport.lean:25,43` | `PointComparison.lean:164,183` | The two preceding point-marginal comparisons on `D x D`, on every directed opposite pair, after zero completion on both sides. Squared distance `<= 4*deltaQ`, denominator 1. |

The nine supporting signatures also agree exactly. Main's ordinary proof changes
include using existing placement-zero lemmas and extracting completion identities;
none changes these contracts. The conditioned target's proof performs the same
answer swap, obtains the positive mass internally, applies the two unconditioned
bounds, and transports the restricted expectation. No additional bridge,
producer, witness field, normalization assumption, or parameter restriction
appears on main.

## Source-Versus-Lean Audit

| Aspect | Paper | Checked Lean | Verdict |
| --- | --- | --- | --- |
| Ambient assumptions | Admissible parameters, a strategy winning at least `1-epsilon`; projectivity after Naimark; separate player spaces. | The common domain above, including explicit finite index types and unit state. Same on both commits. | Existing finite-dimensional/boundary encoding; no new restriction relative to PR. Degree-zero convention is not newly adjudicated. |
| Point family | Constructed in `lem:qld-4-10`, with uniform self-consistency and both ordered-product comparisons. | A supplied `CombinedPointsWitness S deltaQ`; `deltaQ` remains arbitrary and retained quantitatively. | Correct conditional auxiliary, NOT an unrestricted source existence theorem. |
| Marginal conclusion | `eq:pasting-q1` compares X and Z point marginals to evaluated lines on independent source line-point samples, with polynomially small error. | Unconditioned completed marginal bounds `B_C`; conditioned completed bounds `B_C/r`, in Z-then-X order after explicit relabelling. | Exact PR-to-main auxiliary equivalence; completion and conditioning are explicit formalization support, not a changed source law. |
| Final line conclusion | `lem:qld-xz-lines` produces a paired-line POVM, axis-degree support, and unconditioned consistency in all symmetric placements. | None of the issue468 targets asserts this existence/construction conclusion. | Not certified by the target estimates alone; no weakened substitute is called the source theorem. |
| Self-consistency | `eq:qld-q-self-cons` is the separate second pasting input. | A field of the supplied witness; issue468 transfers the marginal inputs, not the completed joint self-consistency theorem of PR487. | Distinct obligations remain distinct. |

Both snapshots retain `\notready` and no `\leanok` on the source-labelled
`lem:qld-xz-lines` node. Main has additional construction code, but this bounded
audit does not use that code to certify the source theorem or settle its wider
paper-gap documentation.

## Unique Documentation And Public Surface

PR472 has twelve separate auxiliary blueprint labels in chapter 15 that are
absent as labels on published main. Their substance must not be confused with
twelve absent mathematical proofs:

| PR-only label | Published-main documentation or disposition |
| --- | --- |
| `lem:joint-point-marginal-effects` | Grouped under `lem:qld-line-point-marginal-identities`. |
| `lem:joint-point-marginal-distance` | The uniform-point marginal results already exist in `Points/WitnessMarginals.lean`; main's grouped marginal discussion includes their `4*deltaQ` consequence, but not this separate exposition/link pair. |
| `lem:linepoint-point-marginal-average` | Grouped under `lem:qld-line-point-marginal-identities`. |
| `lem:point-self-consistency-linepoint` | Distinct inherited standalone self-consistency exposition and links; outside issue468's marginal task, not certified as integrated here. |
| `lem:point-marginal-linepoint-transport` | Grouped under `lem:qld-point-line-marginal-bounds`. |
| `lem:option-completion-distance` | Grouped under `lem:qld-line-point-marginal-identities`. |
| `lem:option-point-marginal-linepoint` | Grouped under `lem:qld-point-line-marginal-bounds`. |
| `lem:expline-point-same-placement` | Grouped under `lem:qld-point-line-marginal-bounds`. |
| `lem:combined-point-line-marginal-distance` | Grouped under `lem:qld-point-line-marginal-bounds`. |
| `lem:combined-point-line-marginal-defect` | Grouped under `lem:qld-point-line-marginal-bounds`. |
| `lem:conditioned-pasting-defect` | Partly grouped under `lem:qld-line-conditioning-restoration`; PR separately links the mass, its `[1/2,1]` bounds, sampler definition and normalization. Preserve this extra detail if consolidating, subject to the correction below. |
| `lem:conditioned-point-line-marginal-defect` | Grouped under `lem:qld-line-conditioning-restoration`, with the same numerator, retained-mass denominator, and Z-then-X conclusion. |

There is no unique missing proof of issue468's target or the fourteen checked
supporting results. Nevertheless, `PointSelfConsistency.lean` also contains
`CombinedPointsWitness.self_consistency_defect_le` and
`CombinedPointsWitness.self_consistency_linePoint_defect_le`, absent as public
declaration names from published main. They predate the issue468 implementation
(introduced by `0c84ef25`) and are not used by its marginal proof, which uses only
the two sampler identities from that module. Their standalone API and blueprint
entry are inherited content to preserve or adjudicate separately, not evidence of
a missing conditioned marginal. This report neither calls them integrated by
name nor borrows their preservation on unpublished PR487 as main coverage.

**Additional statement mismatch in the new PR-only blueprint:**
`lem:conditioned-pasting-defect` says "any two families of operators". Its linked
Lean theorem assumes complete measurement families. Nonnegativity does not
follow merely from disjoint placements for arbitrary operators: scalar effects
can have a negative product. A defect integrand zero on the retained event and
negative on the discarded event would contradict the displayed conditioning
inequality. The blueprint must state complete measurements, or give appropriate
positivity hypotheses in a separately justified generalization. No Lean proof is
missing for the actual measurement statement. Main's grouped statement already
says "arbitrary complete measurements". The PR-only option-completion node also
uses broader "families of operators" wording than its measurement-valued link;
its zero-outcome identity is mathematically general, but the advertised domain is
not the literal linked signature.

## Latest Review: Unresolved Record Versus Current Code

The latest and only returned review is
[review 5185191419](https://github.com/Dengnifer/MIPStarRE-A/pull/472#pullrequestreview-5185191419),
submitted 2026-09-12T04:31:19Z against
`5ec10637448447af76c8bc965bd15d5f1acfbc6a`, with recorded verdict
CHANGES_REQUESTED. All six findings remain unchecked in that historical record;
there is no returned review of current `cfdebb0e`. The following are audit
observations, not changes to review status:

| Finding | Current PR472 content | Published-main relevance |
| --- | --- | --- |
| F1: duplicated `avgOver_mix_noFinite` | Addressed in code: duplicate removed; `RestrictedAverage` imported and existing `avgOver_mix` used. | Main already uses the shared lemma. |
| F2: certified linear-error claim lacks a linked linear-error signature | Still present in chapter 14: item 2 is advertised with error `epsilon`, while linked `expLine_point_cons` and `ExpandedLineConclusions` expose the common square-root error. | Same issue persists on main. The checked same-placement proof uses the actual square-root interface, so issue468's numerator is unaffected. |
| F3: `lineTauMeas` linked without defining its polynomial-pair outcomes | Still present in PR chapter 14: it is attached to the convolution definition without a separate product-outcome definition. | Main has separate `def:line-tau-product-measurement` and `lem:expanded-line-measurement-postprocess` entries resolving this distinction. Do not replace them with the PR version. |
| F4: missing marginal/sampling/conditioned blueprint entries | Substantially addressed by the twelve entries above, with declaration and status tags. | Main already has grouped entries; retain distinct exposition deliberately, and correct the arbitrary-operator overstatement before certifying the new generic node. |
| F5: missing reversed-orientation proof dependency | Still absent from the chapter-14 `lem:qld-comm-line-cons` proof's `\uses`, despite the Lean proofs invoking `win_low_degree_interchanged_proof`. A dependency in a different node does not repair this one. | Same omission on main; not loss of a directed estimate in Lean. |
| F6: visibility/reorganization prose in `Expanded.lean:34` | Still says the other lemma is private/invisible and discusses consolidating copies. | Same prose on main. |

## Verification And Evidence

All paths below are under this worktree's `.lake/` unless explicitly stated.
The reproducible orchestration is `lake env python3 .lake/pr472-check.py`.
It uses the actual pinned Lean **4.32.0** (the inherited AGENTS prose still says
4.31.0); both commits' toolchain and dependency manifests agree. No update was run.

- Fresh source compilation of PR `ConditionedPastingDefect.lean` and
  `ConditionedPointLineMarginalDefect.lean`, and main `PointComparison.lean` and
  `Conditioning.lean`. Compiler products are private, in `pr472-compiled-pr/` and
  `pr472-compiled-main/`; pre-existing dependencies are linked read-only.
- Separate probes import the appropriate freshly compiled modules. Fourteen
  common target/support signatures, the two expanded-line comparison signatures,
  eighteen transitive axiom closures, and eight printed domain/definition records
  agree byte for byte with `pp.all true`.
- Both final probe exits are zero. The identical output has 1,090,154 bytes and
  SHA-256 `6923033c77798ac0ede3766d9b5ed7f4853e1f1094dd79ed4cf5406a39de2ba2`.
- Every inspected theorem closure contains only `propext`, `Classical.choice`,
  and `Quot.sound`. No `sorryAx`, added axiom, or kernel bypass appears in these
  closures. Targeted source scans found no holes/bypasses in the checked modules.
- Exact-commit source inventory compares 25 domain, sampler, measurement,
  dependency, and paper/toolchain files: 24 are byte-identical. The only differing
  file is `Points/WitnessMarginals.lean`, whose changes are source-citation
  docstrings only. In particular the witness, placements, underlying law,
  conditioning event, normalization, and evaluated-answer definitions are unchanged.

Evidence index:

| Artifact | Content |
| --- | --- |
| `pr472-issue468.json`, `pr472-metadata.json`, `pr472-reviews.json`, `pr472-published-main.json` | Read-only GitHub responses through primary `/home/drx/MIPStarRE-qpbt/local/bin/gh_common.py`. |
| `pr472-check.py`, `pr472-commands.json`, `pr472-environments.json` | Exact focused commands, exit codes, durations, commits and artifact search paths. |
| `pr472-check-pr-ConditionedPastingDefect.log`, `pr472-check-pr-ConditionedPointLineMarginalDefect.log` | Fresh PR source checks. |
| `pr472-check-main-PointComparison.log`, `pr472-check-main-Conditioning.log` | Fresh main source checks. |
| `pr472-signatures-main.lean`, `pr472-signatures-pr.lean`, corresponding `.log` files | Fully explicit compiled signatures, definitions and axiom closure outputs. |
| `pr472-signature-comparison.json`, `pr472-signatures.diff`, `pr472-axioms-main.json`, `pr472-axioms-pr.json` | Exact comparison and extracted closure evidence. Final diff is empty. |
| `pr472-source-inventory.py`, `pr472-source-inventory.json`, `pr472-blueprint-labels.json`, `pr472-blueprint.diff` | Exact source hashes and distinct blueprint labels. The full chapter diff is retained as data; unrelated sections were not audited. |
| `pr472-probe-initial-main.log`, `pr472-probe-initial-pr.log` | Initial probe diagnostics for an unsupported pretty-print option, removed before final verification. |

The first private artifact overlay exposed a Lean namespace-search issue, fixed
by linking the unchanged branch dependencies read-only. This was a scratch-probe
configuration failure, not a missing mathematical artifact. No missing dependency
required a rebuild. No full build, CI, reviewer, blueprint rendering, publication,
merge, tracked edit, commit, external model call, descendant, or primary telemetry
write was performed. The actual source tree and all pre-existing issue/PR/review
and cost records are unchanged.

## Recommendation And Remaining Work

MAIN can treat **issue468's two conditioned marginal bounds as already
mathematically available on published main**, without a new proof or a stronger
hypothesis. Before treating the entire PR472 branch as losslessly integrated,
separately account for its twelve auxiliary labels, the two inherited
self-consistency public helpers, and the still-recorded review findings.
Correct the PR-only generic conditioning blueprint's measurement hypothesis;
preserve main's separate product/convolution definitions. Do not turn auxiliary
`\leanok` markers into certification of the source-labelled line theorem.

No exact-head review or normal gate is supplied by this audit. The source theorem,
the rest of the ancestral stack, and PR487's completed self-consistency integration
remain outside this coverage verdict. There is no unresolved issue468 marginal
statement whose proof needs to be invented or supplied as a bridge.

Timing: actual task start was **2026-09-15T11:43:18Z**. Final completion time and
elapsed duration are recorded in the final timing line below, before the absolute
2026-09-15T12:02:00Z deadline.

Final completion: **2026-09-15T12:01:29Z**; actual elapsed **18 minutes 11 seconds**
(1091 seconds). Both tracked worktrees are clean; all focused compiler
processes have terminated. Final status logs are `pr472-final-status-main.log`
and `pr472-final-status-pr.log`.
