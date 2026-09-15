---
title: "Actual rounded scalar-nonlinear outcome mass"
date: 2026-09-14
purpose: >
  Record the composition of the rounded ordered estimates with the recovered
  scalar-nonlinearity theorem, including coefficient transport, degree bounds,
  actual errors, proof provenance, and the remaining global-pair obligations.
issue: "#513"
status: partial
---

# Scope

The concrete scalar-mass composition target is complete. The status remains
partial because the source global polynomial-pair construction is not complete.
The new theorem
`ExtendedLineGame.exists_rounded_polynomial_scalar_mass` constructs both
rounded measurements with their actual ordered estimates and proves the
scalar-nonlinear outcome mass bound on both player placements.

The implementation consists of three modules:

- `Combining/PolynomialImageBounds.lean`: only the required dependency chain
  recovered from PR296, with supporting lemmas private.
- `Combining/ExtendedLineGame/ScalarPolynomial.lean`: injective singleton,
  field, and coordinate transport; exact evaluation; genuine degree bounds.
- `Combining/ExtendedLineGame/ScalarNonlinearMass.lean`: the full outcome-mass
  estimate and its application to the actual rounded constructor.

All paths above are relative to `MIPStarRE/QPBT/`. The QPBT aggregate import
and seven auxiliary blueprint entries are synchronized. The public
`exists_globalPairWitness` statement and its source entry's `notready` marker
are unchanged. No new proof hole, axiom, or conditional producer was added.

# Source of Truth

The first mathematical reading was
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1267-1348`,
especially `eq:qld-g-42`, `eq:qld-g-prime`, and `eq:qld-g-prime-bound`.
The coefficient expansion and nonlinear-coefficient argument are at
lines 1310-1326. The active source entry is blueprint `lem:qld-4-7`.
The preceding ordered-estimates audit,
`audits/2026-09-14_issue-513_ordered-polynomial-estimates.md`, was read
before implementation.

The corrected PR296 proof was read using `git show` at immutable head
`2c8f147643d151d8616864cf49817dc6422a9a86`, before any concentration work.
Its original path and namespace are retained. Every recovered proof has
module-level provenance; no recovered proof earns new-proof attribution.
Unused averaging and reverse-order auxiliary theorems were not imported.
The concentration proof bodies and statements are preserved; only the
visibility of internal supporting lemmas and documentation are changed.
No part of the saved branch's blueprint, history, or unrelated modules was
recovered. Current-main and local polynomial APIs were searched before
introducing the coordinate definitions.

The initial worktree was clean at
`34433164c715f3395d609013edb289cc4de41a45`. All writes were confined to
`.worktrees/issue-513-independent-attempt3-20260912`. PR552, other worktrees,
protected controls, and account state were not touched.

# Findings

## Polynomial Representation

Let `g` be the actual singleton tuple returned by direct soundness at
dimension `2m+2` and `k=1`. Map its coefficients by the established canonical
field equivalence, rename its variables by the coordinate equivalence, and
apply Mathlib's `MvPolynomial.sumRingEquiv`. This gives

$$
 p_g\in F[x_1,\ldots,x_m,z_1,\ldots,z_m][\alpha,\beta],\qquad F=\mathbb F_q.
$$

The resulting map on singleton outcomes is proved injective. The nested
evaluation, including specialization of coefficient polynomials at the base
point, is proved equal to `extendedPolynomialRead`. The joint sample-space
equivalence is proved compatible with `directPointExtendedQuestionEquiv`.
It identifies the full uniform distribution with the nested uniform base and
scalar averages, without replacing the joint law by separate marginals.

A coefficient of a coefficient polynomial is exactly the coefficient of the
corresponding combined monomial. Nonvanishing therefore gives membership in
the original polynomial's support. The original `polyFunc` certificate bounds
each exponent by `d`, yielding

$$
 \deg(\operatorname{coeff}_e p_g)\leq 2md,
 \qquad \deg p_g\leq2d.
$$

The inequalities hold for every coefficient, including coefficients outside
the support. Since admissibility already gives `d >= 1`, the degree term in
the recovered estimate satisfies

$$
 D(p_g)=\sup_{e\in\operatorname{supp}p_g}
       \deg(\operatorname{coeff}_e p_g)+\max\{1,\deg p_g\}+1
       \leq(2m+2)d+1.
$$

No transport equality, coefficient estimate, or degree conclusion is assumed.

## Actual Mass And Error

For any opposite placements `p1,p2`, put
`psi_g = placed(R_g) psiHat`, and use the point projectors on `p2` in the
recovered theorem. Opposite placements commute, so its residual is exactly
the residual defining the actual `XZ` ordered error. The measurement on
`p1` remains on its original expanded local space. Both heterogeneous
placements are covered, without any equality or symmetry assumption on
the players' spaces.

The restricted nonlinear sum is bounded by the full outcome sum, whose
squared masses sum to one by completeness, projectivity, and normalization
of `psiHat`. Consequently there is no polynomial-label cardinality factor.
The canonical field has cardinality `q`, proved using its existing field model.
The general concrete bound is

$$
 N_{p_1}(R)\leq2E^{XZ}_{p_1,p_2}(R)+\frac{2((2m+2)d+1)}q.
$$

Apply the already-proved rounded constructor, which uses PR361's stronger
arbitrary-strategy compression, to the actual point and direct-domain line
witnesses with errors `deltaQ,deltaL`. With exactly the previous definitions

$$
 e=3\left(\sqrt{\delta_Q+\delta_L}+\frac{md}{q}\right),\quad
 \delta=\delta_{\rm ld}(a,b,e,q,2m+2,d,1),\quad
 \eta=\delta+\sqrt{220\delta^{1/4}}+2\sqrt{2\delta},
$$

the two measurements are chosen together and satisfy

$$
 N_{AA'}(R_A),\ N_{BB'}(R_B)
 \leq2(4\eta+8\delta_Q)+\frac{2((2m+2)d+1)}q.
$$

Both `XZ` and `ZX` ordered estimates with error `4 eta + 8 deltaQ` are
retained in the constructor's conclusion. No ordered estimate, mass bound,
or supplied global-pair measurement is an input. The line witness's existing
directly indexed, completed-answer domain remains an explicit restriction.

# Required Action

Scalar-linearity excludes only the first of the three unwanted polynomial
classes. The precise next mathematical obligations are concentration of the
coefficient of `alpha` that depends nontrivially on `z`, and of the coefficient
of `beta` that depends nontrivially on `x`. These use opposite product orders
and lead to `eq:qld-g-non-separable`. The current theorem retains both orders
but does not assert either concentration result.

The retained overlaps through `eq:qld-sgg-mhat-sandwich`, for both Pauli bases
and both player placements, must then be proved before applying the recovered
PR535 pair completion. Finally, the actual error expression, including the
eighth-root rounding loss and all point and line errors, must be absorbed into
the universal `deltaQld` constants. The directly indexed line construction
also retains the source-domain discrepancy documented in
`docs/paper-gaps/qpbt_ld-dimension-divisibility.tex` and
`docs/paper-gaps/qpbt_combined-lines-error-term.tex`.

The existing `exists_globalPairWitness` proof hole remains the source-facing
obligation for issue #513. This continuation does not introduce or relocate it.

# Validation

All three new modules typecheck with `lake env lean`; their required private
objects were emitted only inside this worktree. Both `MIPStarRE/QPBT.lean`
and `MIPStarRE.lean` pass focused checks. The production modules contain no
proof holes, unsafe bypasses, placeholder tactics, or debug commands.
Whitespace and 100-column checks pass.

The private `.lake/Issue513ScalarAxioms.lean` checks both recovered public
theorems, all four polynomial transport/degree theorems, the concrete mass
bound, and the actual rounded constructor. Every closure is exactly
`propext`, `Classical.choice`, and `Quot.sound`. The unchanged global-pair
theorem still reports `sorryAx`.

`leanblueprint web` succeeds with the existing missing-bibliography warnings.
The declaration inventory is regenerated after the web build; it is a
gitignored generated file in this checkout. Blueprint synchronization and
changed-declaration coverage pass, including every new public declaration.
`lake exe checkdecls blueprint/lean_decls` resolves all 1469 inventory entries.
The source-statement header guard reports no changed source-labelled public
headers. The ordinary hooks were checked at the beginning and are used for
the normal commit. No full build, CI, review, publication, push, PR mutation,
or descendant session was run.

# Statement Integrity

For the source theorem `lem:qld-4-7`, the paper assumes admissible parameters,
a positive error, and a projective strategy passing the Pauli test. Its
conclusion is a projective polynomial-pair measurement satisfying all four
point-consistency requirements with universal constants. The corresponding
public Lean assumptions, conclusion, error parameters, quantifier order,
and player and field scope are unchanged. Verdict: the existing faithful
boundary encoding is preserved; the source proof remains incomplete.

For the new auxiliary, the paper calculation excludes polynomials outside
`alpha*g1(x,z)+beta*g2(x,z)` after establishing ordered consistency. Lean
derives that mass estimate for the actual rounded outcomes, with the full
outcome sum and explicit errors displayed above. The constructor explicitly
assumes the existing point and direct-domain line witnesses. Verdict: exact
quantitative composition under the stated auxiliary inputs, with no additional
transport or degree assumption. It is not advertised as the full source lemma.

# Review Use

Check the nonzero combined-coefficient identity in `ScalarPolynomial.lean`
and the full joint evaluation transport first. Then inspect the commuting
placed residual and the two enlargements from the restricted nonlinear sum
to the full measurement sum in `ScalarNonlinearMass.lean`. Finally verify
that the constructor uses the already-established rounded measurements and
retains their original errors and both product orders. The recovered
concentration argument is prior work, not a second new proof of concentration.

# History And Costs

This owner-authorized native continuation first recorded the clock at
2026-09-14T10:09:36Z, with a 25-minute elapsed limit including checks, audit,
and normal commits, and three minutes reserved for finalization. MAIN records
the terminal native completion time and telemetry; there is no budget or
history reset and no descendant session.

Preserved prior spans are the 9760-second issue119/513 subtotal, the
1311.339-second Huygens continuation from 2026-09-14T07:53:23.325Z through
08:15:14.664Z, and the 1262.781-second Erdos ordered-estimates continuation
from 09:35:02.045Z through 09:56:04.826Z. These are recorded session spans,
not new attributions of active proof time. No overlapping histories are added.

The earlier known additive token history remains 31,555,490 input,
30,806,016 cached input, and 87,658 output tokens, including 28,404 reasoning
tokens. Unknown usage and cumulative native snapshots remain unknown and
nonadditive. The separate issue278/B8 history of twelve attempts and 24242
seconds is preserved, without merging it into this continuation's accounting.
