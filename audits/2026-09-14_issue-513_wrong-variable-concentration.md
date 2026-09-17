---
title: "Wrong-variable concentration and the faithful polynomial-pair image"
date: 2026-09-14
purpose: >
  Record both wrong-variable estimates for the actual rounded measurements,
  the common exceptional fibers, and concentration on the bounded combining
  image, while distinguishing the remaining source global-pair obligations.
issue: "#513"
status: partial
start_head: 863582759ef93b50eadfd415eb01150b45286676
---

# Scope

The requested concentration target is complete: both wrong-variable classes
and their union with scalar-nonlinear outcomes are bounded for the actual
rounded measurements. The source global-pair construction remains incomplete,
which is the reason for the partial status of this audit.

The two new modules are `Combining/PolynomialFiberBounds.lean` and
`Combining/ExtendedLineGame/WrongVariableMass.lean`, relative to
`MIPStarRE/QPBT/`. The latter provides
`exists_rounded_polynomial_wrong_variable_mass` and
`exists_rounded_polynomial_separated_mass`. Both retain the actual ordered
estimates on the same measurements. `ScalarPolynomial.lean` supplies the
partial-polynomial degree certificates, exact readout transport, and the
identification with the existing bounded `combinePoly` image.

The public `exists_globalPairWitness` statement and proof are unchanged.
Its source blueprint entry remains `notready`. No retained overlap or
completed-measurement consistency is inferred from concentration.

# Source of Truth

The first mathematical reading was
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1328-1404`,
including `eq:qld-g-separable`, `eq:qld-g-48`, `eq:qld-g-2`, both
wrong-variable displays, and `eq:qld-g-non-separable`. The coefficient and
fiber calculation was read before writing tactics. The active source node
is blueprint `lem:qld-4-7`; the faithful encoding is `def:combine-map`.

The preceding ordered-estimates and scalar-nonlinear-mass audits were read.
PR535's `PairCompletion.lean` was inspected read-only at
`1744bd9533055b9b43af9a8d46906cbafb69afdd`. The current `combinePoly`,
`Poly`, and `PolyPair` APIs already suffice for image identification, so
no completion implementation or saved-tree mutation was needed.

The inherited PR296 chain in `PolynomialImageBounds.lean` retains its
immutable provenance `2c8f147643d151d8616864cf49817dc6422a9a86`.
Its Schwartz--Zippel average and diagonal-error helper are exposed for
reuse, and its norm-to-residual calculation is factored into a shared lemma
used by both concentration proofs. The affine collision calculation is
reused from `PointsDataProcessing.lean`. These recovered or existing proofs
are not new-proof credit.

# Findings

## Uniform Exceptional Fibers

Write a coefficient polynomial as
$p(x,z)=\sum_e c_e(z)x^e$. If it depends formally on $x$, some nonzero
exponent has $c_e\ne0$. This one coefficient is chosen before any
measurement outcome. Its zero set is common to every outcome label $b$.
If the coefficient degrees are at most $C$ and the degree in $x$ is at
most $D$, the exceptional-set probability is at most $C/q$. Outside it,
the specialized polynomial differs from every constant, so every fiber
$p(x,z)=b$ has probability at most $D/q$.

For nonnegative weights $w(z,b)$ with $\sum_b w(z,b)=M$ for every $z$,
the checked weighted inequality is

$$
 \mathbb E_z\sum_b\Pr_x[p(x,z)=b]w(z,b)\leq(C+D)M/q.
$$

The weights are allowed to depend on the fixed block. Their independence
of the varying block is explicit, not an assumed averaged independence.
Neither a sum of outcome-wise exceptional sets nor a factor counting
outcomes appears.

## Ordered Norms And Actual States

For the beta coefficient depending on x, use the ordered product XZ.
Its Gram operator is the Z-X-Z sandwich outside the zero-beta exception.
Scalar-answer collisions cost at most $q^{-1}\|\psi_g\|^2$; the zero
scalar costs at most the same amount. Drop the middle X contraction.
The remaining Z weight depends only on z, so the common-fiber estimate
applies. For alpha depending on z, reverse both blocks and scalars and
use ZX, whose sandwich is X-Z-X.

The partial degrees are derived from the original individual-degree
certificate, with $C=D=md$. Thus the ordered image norm is at most
$(2md+2)\|\psi_g\|^2/q$. The actual vectors are always
$\psi_g=(R_g)_{p_1}\hat\psi$. Opposite placements commute, identifying
their residual with the actual ordered-error residual. Completeness,
projectivity, and normalization give $\sum_g\|\psi_g\|^2=1$ over the
entire outcome type.

Consequently, for both orders and every opposite pair,

$$
 W^{o}_{p_1}(R)\leq2E^o_{p_1,p_2}(R)+2(2md+2)/q.
$$

The Boolean false selects beta depending on x and XZ; true selects alpha
depending on z and ZX. In particular, both heterogeneous placements
$AA'\mid BA''$ and $BB'\mid AB''$ are covered without equal player spaces
or a symmetry assumption.

## Faithful Separated Image

A constant partial polynomial comes from a polynomial on the fixed block.
Its coefficients still have individual degree at most d. The injective
scalar expansion therefore proves that every scalar-linear outcome with
both correct dependencies is the field transport of
$\combine_{g_X,g_Z}=\alpha g_X(x)+\beta g_Z(z)$ for an existing
`PolyPair P`. This is equality of formal polynomials, not only their
finite-field evaluations, and needs no new field-size restriction.

Define G as the actual mass outside this bounded combining image. Its
complement is covered by the three excluded classes. The checked bound is

$$
 G_{p_1}(R)\leq4E^{XZ}_{p_1,p_2}(R)+2E^{ZX}_{p_1,p_2}(R)
                 +(12md+4d+10)/q.
$$

The scalar-nonlinear contribution remains the previously checked
$2E^{XZ}+2((2m+2)d+1)/q$; it is not reproved or credited here.

## Actual Rounded Errors

With the same direct-domain line witness and point witness as before, set

$$
 \delta=\delta_{\rm ld}\bigl(a,b,
   3(\sqrt{\delta_Q+\delta_L}+md/q),q,2m+2,d,1\bigr),
 \qquad \eta=\delta+\sqrt{220\delta^{1/4}}+2\sqrt{2\delta},
 \qquad E=4\eta+8\delta_Q.
$$

The actual two rounded measurements satisfy both wrong-variable bounds
$2E+2(2md+2)/q$, and their separated-image masses are at most
$6E+(12md+4d+10)/q$. Both ordered estimates remain in the constructors'
conclusions. No concentration, residual producer, or supplied global-pair
witness is an assumption.

# Required Action

The next source obligation is the retained-overlap argument through
`eq:qld-sgg-mhat-sandwich`, for both Pauli bases and both player placements.
Concentration alone does not give these overlaps. Then use the saved PR535
restriction and completion API and derive evaluated point consistency.
Absorb the actual errors, including the eighth-root rounding term and the
line error, into the final universal `deltaQld` constants.

The directly indexed completed-answer line-witness restriction remains
documented in `docs/paper-gaps/qpbt_ld-dimension-divisibility.tex` and
`docs/paper-gaps/qpbt_combined-lines-error-term.tex`. Identifying that domain
with the source game remains separate. The existing proof hole in
`exists_globalPairWitness` is neither discharged nor relocated.

# Validation

Focused Lean checks cover all changed mathematical modules and the two
aggregate imports; only necessary worktree-local objects are emitted.
The private `.lake/Issue513WrongVariableAxioms.lean` inspects all new
major theorem closures and the unchanged source theorem. New closures
contain only `propext`, `Classical.choice`, and `Quot.sound`; the source
theorem retains its pre-existing `sorryAx`.

Production files contain no new proof holes, unsafe bypasses, placeholder
tactics, or debugging commands. Whitespace and 100-column checks pass.
`leanblueprint web` succeeds with existing bibliography warnings. The
declaration inventory is regenerated after that build; blueprint sync,
new-declaration coverage, and source-header checks pass. The existing
declaration-checker executable resolves all 1489 inventory entries.
The normal installed git hooks are used. No full build, native CI, review,
push, publication, PR mutation, descendant, or runtime change is performed.

# Statement Integrity

Paper assumptions for the concentration calculation are the already
constructed projective polynomial measurement, the two ordered estimates,
and bounded individual degree. Lean derives those inputs from the existing
rounded constructor under its displayed point and direct-domain line
witnesses. Degrees and common exceptional sets are internal conclusions.
The paper conclusion is small mass outside the separated image; Lean gives
the explicit bound above on that exact bounded combining image. Verdict:
faithful quantitative encoding under the explicitly restricted auxiliary
inputs, with both player placements and every outcome retained.

For source `lem:qld-4-7`, paper and public Lean assumptions remain the
admissible parameters, positive error, and projective Pauli strategy.
The paper and public Lean conclusions remain the global polynomial-pair
witness and all four point-consistency requirements. Quantifiers and errors
are unchanged. Verdict: the existing faithful boundary encoding is preserved,
and its source proof remains incomplete. New auxiliary blueprint nodes are
marked complete only for their displayed statements.

# Review Use

Check the common exceptional coefficient before the weighted sum. Then
check the removal of the middle contraction and the reversal of both
blocks and scalar coefficients. Inspect the normalized full outcome sum
and the injective formal-polynomial identification with `combinePoly`.
The final union estimate deliberately proves no retained-overlap statement.

# History And Costs

The first local clock was 2026-09-14T10:30:33.840615Z. This native
continuation has an owner-authorized 25-minute elapsed limit, including
validation, audit, and normal commit, with three minutes reserved for
finalization. MAIN records the authoritative terminal receipt and usage.
The local pre-commit validation checkpoint was 2026-09-14T10:50:28.354483Z,
1194.513868 seconds after the first local clock. This checkpoint is not the
terminal session duration and must not be added to the terminal receipt.
Only `.worktrees/issue-513-independent-attempt3-20260912` is written.
PR552, its controls and index, PR544's external CI, and other worktrees
are untouched. The preceding prover remains recorded and closed.

Preserve these prior spans separately: the 9760-second issue119/513
subtotal; Huygens 1311.339 seconds; Erdos ordered estimates 1262.781
seconds; Singer scalar mass 827.06 seconds. These are recorded session
spans, not newly attributed active proof time. No overlapping histories
are added, and none is reset.

The previously known additive token history remains 31,555,490 input,
30,806,016 cached input, and 87,658 output tokens, including 28,404
reasoning tokens. Current native token usage is unavailable here.
Unknown usage and cumulative native snapshots remain unknown and
nonadditive. The separate issue278/B8 history of twelve attempts and
24242 seconds is preserved without merging it into this accounting.
