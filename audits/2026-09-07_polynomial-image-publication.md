# Ordered Polynomial-Image Bounds

## Mathematical Content

Let X and Z be complete projective measurements with outcomes in a finite
field F, acting on the same finite-dimensional complex space. For scalars
alpha, beta, and a, the ordered indicator is the sum of X_b Z_c over pairs
with alpha*b + beta*c = a. It is an ordered operator, not an asserted POVM
effect, and no commutation between X and Z is assumed.

For nonzero beta, orthogonality of the X effects and field cancellation
identify its Gram operator with the corresponding sum of Z_c X_b Z_c.
At beta zero, completeness of Z leaves a coarse-grained X projection. Both
Gram and diagonal operators are contractions, so their quadratic forms on
an arbitrary vector differ by at most its squared norm. Uniform averaging
costs one over the field cardinality, weighted by the actual vector mass.
Summing this estimate over measurement outcomes introduces no outcome-count
factor.

For a polynomial in alpha and beta over the ring of base-point polynomials,
failure of scalar linearity supplies a nonzero coefficient outside the two
linear monomials. This coefficient is chosen independently of both outcome
labels. Schwartz--Zippel bounds its exceptional base-point set. On the
complement, a second application bounds agreement with every linear answer
polynomial. The sandwich weights are nonnegative and sum to the squared
state norm, which permits the two averages without an assumed collision law.

The final `nonlinear_mass_le_ordered_error` retains the actual ordered
correlation error on its right-hand side. It does not derive that error from
game success, prove block separation, or construct a global polynomial-pair
measurement. This is the precise boundary of the recovered content.

## Source And Statement Audit

The source is `references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1289-1320`,
specifically `eq:qld-g-42`, `eq:qld-g-43`, `eq:qld-g-prime`, and the
coefficient argument before `eq:qld-g-prime-bound`. The latter source bound
also uses the preceding approximate-correlation estimates; those estimates
are not claimed here.

- Paper objects: projective X/Z measurements, polynomial coefficients, and
  vectors obtained by applying fixed polynomial-outcome projectors.
- Lean objects: arbitrary finite projective measurements and fixed vectors,
  with explicit finite-field and coordinate instances. Normalization and
  cross-register hypotheses are not added.
- Paper conclusion: concentration outside the scalar-linear image after the
  ordered-correlation error has been bounded using earlier source steps.
- Lean conclusion: the corresponding auxiliary mass inequality with that
  actual error displayed explicitly, and the coefficient degrees retained.
- Verdict: a proved auxiliary ordered-correlation estimate, not the
  unrestricted source conclusion or global-pair construction.

Blueprint `lem:aux-ordered-nonlinear-mass` states exactly that auxiliary
inequality, including its error term and lack of vector normalization.
The existing source-labelled `lem:qld-4-7` remains unchanged and not ready.

## Public-API Recovery

The preserved module imported the issue118-only
`Combining.Points.Consistency`. Two norm identities arrived through that
unpublished dependency. The squared norm of an operator image is its Gram
quadratic form; the quadratic form of the identity is the squared vector
norm. Current public declarations provide exactly these identities:
`MagicSquareRigidity.norm_applyOperatorToState_sq` and
`DistanceCalculus.stateQForm_one`. The first writes the quadratic form as a
real inner product, so one reflexivity step and one explicit definitional
conversion replace the former notation wrapper.

The recovery imports public `GroundSlice` and
`MIPStarRE.LDT.Preliminaries.Polynomials` instead of the issue118-only
module. Public `SandwichProduct.postprocess_isProjective`,
`stateQForm_nonneg`, and `stateQForm_finset_sum` supply the other existing
steps. No new mathematical helper, inequality, premise, or source step was
introduced or omitted.

All 22 declaration headers match the preserved module: 21 public
declarations and the existing private agreement-probability helper. The
only proof-body changes are the two public norm-identity names and the
definitional conversions described above. The aggregate imports the new
module so ordinary project CI includes it.

## Validation And Preservation

The module type-check and its scoped Lake build pass using only standard
public dependency artifacts. All 21 public axiom queries report exactly
`propext`, `Classical.choice`, and `Quot.sound`, with no `sorryAx` or
additional axiom. The active Lean path contains ordinary dependency and
new-worktree build directories, with no issue118 private validation prefix.

Original source SHA256:
`871109bd97b6d50354dbf89f2d828cf4c4a9c2877a88b2aa4a654f764df42762`.
The prior attempt13 axiom receipt has SHA256
`1c4c69600ff7268aa218d07f4c7624dfb5b43475aec8dc7d3f3226767591872a`.
Both remain preserved in their original locations. The old evidence is not
a substitute for the fresh public-source checks recorded for issue #295.

This publication does not reopen B8. Its recorded budget remains 13 attempts
and 26509 working seconds; no original anchor, attempt, or working-time
counter is reset, extended, or discharged. The issue118 worktree, source,
private artifacts, gap notes, and audits are not modified. Closed issue #49
is the publication prerequisite; #118 is the origin of the recovered
content, not a claim that its remaining construction is complete.
