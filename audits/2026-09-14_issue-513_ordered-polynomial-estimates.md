---
title: "Both ordered estimates for rounded extended-polynomial measurements"
date: 2026-09-14
purpose: >
  Record the quantitative proofs of the two ordered estimates used in the
  global polynomial-pair construction, their actual soundness and rounding
  inputs, and the remaining concentration and completion obligations.
issue: "#513"
status: partial
---

# Scope

This continuation proves the calculation at `eq:qld-g-42` and `eq:qld-g-43`
for rounded extended-polynomial projective measurements. The main new theorem
is `ExtendedLineGame.exists_rounded_polynomial_ordered_estimates` in
`MIPStarRE/QPBT/Combining/ExtendedLineGame/RoundedPolynomialEstimates.lean`.
It constructs the measurements using direct soundness and projective rounding,
then proves both product orders on the actual six-register state, in both
heterogeneous placements `AA' | BA''` and `BB' | AB''`.

`MIPStarRE/QPBT/Combining/OrderedPolynomialEstimates.lean` contains the
projective-refinement calculation and its application to every directed
opposite placement of a `CombinedPointsWitness`. The aggregate QPBT import,
declaration inventory, and four auxiliary blueprint entries are synchronized.
The public `exists_globalPairWitness` declaration is unchanged and remains
unproved. Its source blueprint entry remains `notready`.

# Source of Truth

The first reading was
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1267-1404`,
particularly the two ordered displays and their explanation at lines
1283-1300. The proof uses the existing forms of Fact agreement and
Fact add-a-proj2. The active blueprint source entry is `lem:qld-4-7`.

Both preceding issue513 audits were read:
`2026-09-12_issue-513_composition-compatibility.md` and
`2026-09-14_issue-513_polynomial-consistency.md`. The latter's weaker
point-derived compressed-consistency estimate is preserved but is not used
by the new constructor. The merged theorem
`exists_direct_ld_soundness_of_k_eq_one_any_strategy` already preserves all
three soundness conclusions through compression, including polynomial
consistency with the original soundness error.

The initial clean head was `a04ff2bb2fd082f32dfa394f583aceef85f75cc0`.
The authorized normal merge of main snapshot
`d8bb9efb9760348c9bb9c85019549bcbda593df9` produced
`5d0540ba24b570df9f9bfad731932bb5383b0cb0`; the merge-loss guard passed
without conflicts. Only the authorized third-attempt worktree was written.

The following preserved sources were inspected read-only:

- PR535 at `1744bd9533055b9b43af9a8d46906cbafb69afdd`: the recovered
  polynomial-pair embedding, restriction, completion, and retained-overlap
  results in `PairCompletion.lean`, together with its provenance audit.
- PR549 at `aeaca3aee589ff666c5ab6feb2681e2cb06e8b1d`: the actual
  `exists_extendedLinesWitness_established` statement and construction,
  including its directly indexed completed-answer restriction and established
  error. This patch was not copied or integrated; PR552 integration belongs
  to the other native session.
- Saved issue119 trees and their ordered-product APIs, and the issue295
  polynomial-image branch at `2c8f1476`, which contains
  `nonlinear_mass_le_ordered_error` and the preceding scalar-linearity bounds.

# Findings

## Projective Refinement

Let `R` be a complete projective measurement, and let `e_x(g)` be any finite
outcome readout. Suppose the evaluated measurement has consistency defect at
most `eta` with a complete measurement `B_x`. Suppose also that the squared
distances from `B_x` to `A_x`, and from `A_x` to an arbitrary operator family
`T_x`, are at most `deltaSelf` and `deltaOrder`, respectively. Then

$$
 \mathbb E_x\sum_g\|R_g(I-T_{x,e_x(g)})\psi\|^2
 \leq 4\eta+4\delta_{\rm Self}+4\delta_{\rm Order}.
$$

Projectivity gives `R_g R^{e_x}_{e_x(g)} = R_g`. Agreement bounds the
evaluated squared distance by twice the consistency defect. The existing
function-indexed left-multiplication inequality retains the entire sum over
`g` without an outcome-cardinality factor. Two squared-distance triangle
inequalities give the constants displayed above. The operator family `T`
need not be positive or projective; in particular it may be either ordered
product of the point effects.

For the actual expanded setting, take `B` to be `Q` on the opposite block
and `A` to be `Q` on the same block as `R`. The proved `extendedQ_spec`
supplies both intermediate errors with bound `deltaQ`, separately for the
`XZ` and `ZX` products. Consequently each ordered error is at most
`4 eta + 8 deltaQ`. The theorem quantifies over every directed opposite
placement and makes no equal-player-space assumption.

## Actual Soundness And Rounding

The concrete constructor takes the existing point witness and its extended
line witness, with their actual errors `deltaQ` and `deltaL`. Set

$$
 e=3\bigl(\sqrt{\delta_Q+\delta_L}+md/q\bigr),\qquad
 \delta=\delta_{\rm ld}(a,b,e,q,2m+2,d,1),
$$
$$
 \eta=\delta+\sqrt{220\delta^{1/4}}+2\sqrt{2\delta}.
$$

The existing passing-value theorem supplies `e`; admissibility makes it
positive. Direct soundness for arbitrary strategies supplies polynomial
POVMs on the original expanded spaces with all three defects at most
`delta`. Thus the simultaneous rounding theorem uses polynomial-consistency
error `delta`, without replacing it by the larger point-derived error.

The two rounded measurements are chosen together before either product
order. Their outcomes are the actual singleton polynomial tuples of the
direct `k=1` theorem. The readout evaluates the unique polynomial at the
joint point and applies the canonical field equivalence. Postprocessing the
actual direct-game point answer by the same scalar readout recovers exactly
the extended `Q` measurement. There is no support or basis restriction.

The joint coordinate equivalence transports the uniform law to uniform
`(x,z,alpha,beta)`. The existing `pairState` correlation identities transfer
the consistency to `psiHat` for both heterogeneous placements; the reversed
orientation uses commutation of opposite placements and exchanges the two
outcome sums. No symmetry of the original strategy is assumed.

For each of `XZ` and `ZX`, the final theorem proves

$$
 \mathbb E_{x,z,\alpha,\beta}\sum_g
 \left\|(R_g)_{p_1}\left[I-
   \left(\sum_{\alpha r+\beta s=g(x,z,\alpha,\beta)}
     M_X(x,r)M_Z(z,s)\right)_{p_2}\right]\hat\psi\right\|^2
 \leq4\eta+8\delta_Q,
$$

with the displayed product reversed for `ZX`, and for both
`(p_1,p_2)=(AA',BA'')` and `(BB',AB'')`. The sum includes every polynomial
outcome. In particular, `eta` is not renamed as the paper's unrounded
low-degree error, and the dependence on `deltaL` has not been discarded.

# Required Action

The two ordered estimates are now proved from actual direct soundness and
rounding. The remaining global-pair construction requires the following
mathematics and composition:

1. Compose with the separately established extended-line constructor and its
   actual error. Its directly indexed, completed-answer domain remains
   explicit. Identification with the source-labelled seed-bearing game is a
   separate tracked source discrepancy, not an assertion of this auxiliary.
2. Transport the singleton polynomial representation and the new ordered
   error to the saved scalar-nonlinearity estimate. Check its explicit
   coefficient and total-degree terms against the individual-degree bound;
   do not substitute an unverified asymptotic bound.
3. Prove concentration for both remaining variable-separation classes:
   a coefficient of `alpha` depending nontrivially on `z`, and a coefficient
   of `beta` depending nontrivially on `x`. These require opposite product
   orders. The saved scalar-nonlinearity theorem does not prove them.
4. Combine all three excluded classes to prove `eq:qld-g-non-separable`.
   Derive the retained point overlaps through `eq:qld-sgg-mhat-sandwich`
   for both Pauli bases and both placements, then use PR535's completion.
5. Absorb the actual error, including the eighth-root rounding term and
   every point and line contribution, into the final universal `deltaQld`
   constants. The prior absorption of a different error expression is not
   silently substituted for this obligation.

No new axiom, proof hole, producer input, or global-pair witness assumption
was introduced. The existing open proof in `exists_globalPairWitness` is
neither discharged nor modified by this continuation.

# Validation

The two new Lean modules and both aggregate import files typecheck without
warnings. The required private object for the merged
`AnyStrategySoundness.lean` was compiled in this worktree. Axiom inspection
of both new public operator lemmas, the concrete
rounded constructor, the existing arbitrary-strategy soundness theorem, and
`extendedQ_spec` lists exactly `propext`, `Classical.choice`, and `Quot.sound`.
The unchanged `exists_globalPairWitness` still lists `sorryAx`.

The private axiom-check file is `.lake/Issue513OrderedAxioms.lean`.
The production files contain no proof holes, unsafe bypasses, placeholder
tactics, or debug commands. Whitespace and 100-column scans pass.
`leanblueprint web` succeeds with the existing missing-bibliography warnings.
Declaration inventory regeneration follows the web build, so generated legacy
references do not enter the committed inventory. The ordinary git hooks are
installed and checked. Blueprint synchronization and changed-declaration
coverage pass; the declaration checker resolves all 1454 inventory entries,
including the five new public names. No full build, CI, review, publication, push, PR
mutation, or descendant session was run.

# Statement Integrity

- Paper assumptions of `lem:qld-4-7`: admissible parameters, positive test
  error, and a projective strategy passing the Pauli test.
- Public Lean assumptions: unchanged `AdmissibleParams`, positive error,
  and `ProjectiveSetting`. No premise was added.
- Paper conclusion: universal constants and projective polynomial-pair
  measurements with all four point-consistency requirements.
- Public Lean conclusion: unchanged `GlobalPairWitness` and `deltaQld`,
  with the original quantifier order.
- Verdict: the existing faithful boundary encoding is preserved; its proof
  remains incomplete. The new constructor is an explicitly restricted
  auxiliary on the directly indexed extended-line domain. Its blueprint
  statement displays that input and its complete quantitative conclusion.

# Review Use

Check the three independent errors in
`projective_refinement_ordered_dist_le` first. Then inspect the two uses of
`extendedQ_spec` and the exact norm sum in `extendedPolynomialOrderedError`.
The concrete constructor should be checked for its use of the third
compressed soundness conclusion, its joint uniform question transport, and
the Bob-side outcome-sum exchange. The source theorem remains `notready`;
the new completion tags refer only to the auxiliary statements and proofs.

# History And Costs

This native continuation began at 2026-09-14T09:35:13Z with a 25-minute
elapsed limit, including focused validation, audit, and a normal commit.
Main records its terminal end time and native telemetry after completion.
No runtime, account, router, review lane, or protected control was changed.

The preserved issue119/513 subtotal is 9760 session-seconds. The preceding
Huygens continuation adds its separately recorded 1311.339-second span,
2026-09-14T07:53:23.325Z through 08:15:14.664Z. Neither history is reset.
These are recorded session spans, not a new attribution of active proof time.
The earlier known additive token history remains 31,555,490 input,
30,806,016 cached input, and 87,658 output tokens, including 28,404 reasoning
tokens. Unknown usage and cumulative native snapshots remain unknown and
nonadditive. No overlapping histories are summed. The broader issue278/B8
history of twelve attempts and 24242 seconds remains preserved separately.
