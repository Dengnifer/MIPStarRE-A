# Recovery of the Low-Degree Line Restriction

This note records the restricted mathematical scope of issue #297, a child of
#116. It recovers the polynomial prerequisite for the honest strategy in #156;
it does not prove the remaining expanded-line consistency conclusions or the
honest-strategy theorem on current main.

## Source and Construction

The encoding in equation `eq:ld-encoding`,
`references/qpbt-paper/04_preliminaries.tex:869-896`, is a linear combination
of products of one affine factor in each coordinate. After the substitution
`x = u_0 + t v`, each factor has degree at most one in `t`. The degree of a
product is bounded by the sum of the degrees, and that of a sum by the maximum.
Thus the restricted encoding has degree at most `m`; on an axis-parallel line
only one coordinate varies, so its degree is at most one. The existing
parameter assumption `1 <= d` gives the answer bounds `m*d` and `d`.

These are the line answers used in `lem:pauli-completeness`, paper
`08_classical_and_quantum_low_degree_tests.tex:1244-1273`, and the ancillary
restriction used in `lem:qld-comm-line-cons`, paper
`14_analysis_of_the_pauli_basis_test.tex:552-556`.

The formal proof uses Mathlib's degree inequalities for polynomial sums and
products. It does not infer a formal polynomial degree bound from equality of
polynomial functions over a finite field. Coefficient truncation is justified
by that formal degree bound. Affine substitution commutes with evaluation, so
the coefficient list evaluates correctly at every point of the line. The
`EvaluatesTo` predicate quantifies over every parameter representing that
point; in particular, no nonzero-direction hypothesis is added.

## Recovery Manifest

- Initial current-main base: `0efa4ecb7abc50343705e2fd245df71c6e12c59d`.
- Preserved issue116 worktree head:
  `f1dc470395734138ab5e8c4ff1fc485d1edce79a`.
- Source module:
  `MIPStarRE/QPBT/Observables/LineMeasurement/Restriction.lean` in that tree.
  Its source blob is `f2c47922720e30f68ea103ec7b6aebc44a4d4743`.
- Preserved original honest-strategy head:
  `c7d3ea2c8d09e440fe77eb225b97da3f71d37276`.
- Preserved current honest-strategy recovery head:
  `1c223a5f5b2f5c0af9483cc99b6d3771a3385bdc`.

All three saved worktrees were clean before recovery and are left untouched.
The complete saved expanded-line proof in PR213 is not replaced or reduced.

The public definitions `polynomialOnLine`, `restrictToLine`, and
`DegPoly.FitsDegree` move verbatim from current `LineMeasurement.lean` to its
public `Restriction` module. Their names, arguments, values, and public
availability through `LineMeasurement` are unchanged. The existing public
degree theorem has the same statement and now uses the saved proof.

The recovered proof declarations are the coordinate degree bounds,
`polynomialOnLine_lowDegreeEncoding_natDegree_le_sum`, the general and axis
encoding degree bounds, the axis coefficient bound, `eval_polynomialOnLine`,
`evalCoefficient_restrictToLine`, `evaluatesTo_restrictToLine`,
`evalOpt_restrictToLine`, and `evalOpt_restrictToLine_lowDegreeEncoding`.
Their mathematical statements and proofs are retained, with one API adaptation:
`evalOpt_restrictToLine` directly uses the already-public
`WinImplications.evalOpt_eq_some_of_evaluatesTo`. This avoids restoring the old
`LineMeasurement.Evaluation` module merely for an equivalent implication.
Docstrings now distinguish the generic substitution identities from the
source-facing restriction calculation and cite stable blueprint labels.

## Statement Integrity

- Paper assumptions: the multilinear encoding, the chosen affine line, and
  the existing positive degree parameter. The axis bound additionally assumes
  an axis-parallel line; an evaluation assertion assumes a point on that line.
- Lean assumptions: the existing `LdParams`, `LineDesc`, and encoding label;
  the axis theorem assumes `line.kind = .axis`, and partial evaluation assumes
  `u` belongs to `line.pointSet`. No strategy, residual, bridge, or extra
  degree hypothesis is added to the encoding theorem.
- Paper conclusions: legal degree bounds for the line answers and evaluation
  equal to the low-degree encoding at the sampled point.
- Lean conclusions: degree at most `m*d`, degree at most one on an axis line,
  vanishing coefficients above `d` there, and the exact coefficient and
  partial-evaluation identities, including the indicator-vector formula.
- Verdict: faithful boundary hypotheses, with the explicit multilinear bound
  one on axis lines. For a general polynomial, the coefficient-list identity
  explicitly assumes the degree bound needed to avoid truncation; it is a
  separate Lean-only auxiliary, not a new premise of a paper theorem.

The seven remaining direct proof holes in `LineMeasurement.lean` are unchanged.
The only new proof-level blueprint result is
`lem:low-degree-encoding-line-restriction`; no status for the full expanded-line
or honest-strategy theorem is advanced by this prerequisite.

## Validation

The recovered source module passes `lake env lean`. The scoped Lake build of
`MIPStarRE.QPBT.Observables.LineMeasurement.Restriction` recompiles that module
successfully, and the original `LineMeasurement.lean` consumer then passes its
direct source check. A separate fresh import checks the axiom closures of all
twelve public declarations above, including the three relocated definitions:
only `propext`, `Classical.choice`, and `Quot.sound` occur. The same check proves
the two definitional coefficient-list identities and the evaluation identity
for an arbitrary zero-direction line.

The mathematical prerequisites are the already-merged encoding identity from
#62, canonical line geometry from #106, and the existing public partial
evaluation lemma from #112. Neither the unfinished point-consistency packet
#115 nor the parent packet #116 is a premise of these restriction proofs.
