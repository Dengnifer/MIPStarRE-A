# Real polynomial evaluation collisions

## Scope and source

Issue #259 is based on merged commit
`32a32edee16d3932525e4b1da9f84009e1fbb13b`. No declarations from unmerged
branches are used.

The primary source is `lem:schwartz-zippel` in
`references/qpbt-paper/04_preliminaries.tex:856-864`: two distinct polynomials
of total degree at most a natural number `D` agree on at most a `D/q` fraction
of the points of the finite field's Cartesian power. For individual degree at
most `d` in `m` variables, the total degree of their difference is at most
`m*d`. Blueprint `lem:schwartz-zippel-individual` records this specialization.

The intended extraction use is the calculation preceding blueprint
`eq:qld-nonencoding-mass`. The paper's calculation in
`lem:qld-construct-the-paulis`,
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1483-1492`,
substitutes the encoding of the decoded outcome for that outcome.
`docs/paper-gaps/qpbt_decoding-identity.tex` explains why this substitution
requires an encoding hypothesis. The blueprint instead bounds the mass outside
the encoding image. The present result proves only its scalar collision
ingredient, not the mass estimate or the existence of a global measurement.

## Existing results and specialization

`MIPStarRE.LDT.Preliminaries.schwartzZippel_individualDegree` already proves
the required estimate for the actual `polyFunc` subtype, using
`MvPolynomial.schwartz_zippel_totalDegree`. Its probability is a nonnegative
rational cardinality ratio, not the real `avgOver` expected by QPBT support
comparison.

`MIPStarRE.LDT.Preliminaries.polynomialAgreement_avg_le_mdq` already gives a
real estimate for LDT's `Polynomial params` and coded `Point params` carrier.
It does not directly accept QPBT's `Poly P`, the `polyFunc` subtype, or its
scalar-function evaluation domain. The new module does not repeat its
coordinate transport or reprove Schwartz–Zippel.

`MIPStarRE.QPBT.polyFunc_eval_collision_le` rewrites the real uniform average
as a normalized sum, identifies the sum of equality indicators with the
cardinality of the equality set, and casts the existing rational inequality
to the reals. `MIPStarRE.QPBT.poly_eval_collision_le` specializes this result
to `Poly P` and `evalPoly`, using the fixed field model's cardinality `P.q`.
Both are exported by `MIPStarRE/QPBT.lean`; only the unrestricted generic
result is added to the existing individual-degree blueprint node.

## Statement integrity

- Paper assumptions: two distinct polynomial representatives over a finite
  field, in `m` variables, each of individual degree at most `d`.
- Lean assumptions: `[Field K] [Fintype K] [DecidableEq K]`, natural numbers
  `m` and `d`, and distinct elements of `polyFunc m K d`.
- Paper conclusion: uniform evaluation agreement probability at most `md/q`.
- Lean conclusion: the real uniform average of the equality indicator is at
  most `(m * d : ℝ) / Fintype.card K`.
- Verdict: faithful boundary hypotheses. Finiteness represents the finite
  field, and decidable equality enables the finite indicator. The QPBT
  specialization uses only the existing `AdmissibleParams`, with no additional
  restrictions. Neither theorem adds a proof obligation to its assumptions.

The generic theorem permits `m = 0` and `d = 0`. In either case two distinct
constant representatives have zero agreement probability. It does not assume
`d < |K|`: for degrees large enough that distinct representatives define the
same function, Schwartz–Zippel remains valid, possibly with a bound at least
one. Field nonemptiness implies nonemptiness of the sampling space even when
`m = 0`; no separate positivity assumption or error parameter is needed.

## Future consumer

For `SandwichProduct.avg_diagonal_postprocess_stateQForm_le` or
`SandwichProduct.point_codeword_defect_le_avg_evaluated_add`, instantiate
`Γ := Poly P`, `Y := Fin P.m → PauliScalar P`, `R := PauliScalar P`,
`eval := evalPoly`, and `ε := (P.m * P.d : ℝ) / P.q`. The collision argument is
exactly `fun first second hne => poly_eval_collision_le first second hne`.
Nonnegativity of this error follows from nonnegativity of natural casts and
division; strict positivity is unnecessary.

Applying that comparison to the nonencoding-mass problem still requires the
encoding-supported reference measurement, its evaluated consistency estimate,
and the quantitative mass argument. None is supplied here as an assumption or
claimed as proved. `EncodingSupport.lean`, the global witness construction,
and the #118 restricted-law obligations are unchanged. A1–A6 introduce no new
issue: the only non-type hypothesis is polynomial inequality, the probability
is the actual uniform average, and the proof terminates in the existing
project and Mathlib collision theorems.

## Validation

Both the new module and `MIPStarRE/QPBT.lean` pass `lake env lean` without
diagnostics. The changed Lean files contain no `sorry` or `axiom` matches.
Printing the axiom dependencies of each new theorem gives exactly `propext`,
`Classical.choice`, and `Quot.sound`.

Scratch checks outside the repository verify the cases of zero variables,
zero degree, and degree equal to the cardinality of `ZMod 2`. They also
elaborate the two complete sandwich support theorem applications described
above. `leanblueprint web` succeeds, with bibliography-entry warnings in the
existing blueprint. The machine-wide full-build lock was held by another CI
run during these file-level checks; no unlocked full build was attempted.
