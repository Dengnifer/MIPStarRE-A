import Mathlib.Algebra.MvPolynomial.CommRing
import MIPStarRE.LDT.Preliminaries.Polynomials

/-!
# The low-degree encoding

This module encodes the Boolean subcube by multilinear indicator polynomials
and packages the resulting low-degree code as honest polynomial representatives.

## References

The source-facing nodes are `def:polynomials-degree`,
`def:low-degree-encoding`, and `def:indicator-vector` in
`blueprint/src/chapter/ch11_qpbt_algebra.tex:321-417`; the paper origin is
`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:917-925`.
The polynomial class `def:polyfunc` is reused from
`MIPStarRE.LDT.Preliminaries.polyFunc` (the LDT formalization).
-/

open scoped BigOperators
open MvPolynomial

namespace MIPStarRE.QPBT

/- The Boolean cube indexes the `2^m` qudits in the low-degree encoding. -/
/-- The Boolean cube indexing the `2^m` qudits of the test.  This is the index
type in `def:low-degree-encoding`, blueprint
`blueprint/src/chapter/ch11_qpbt_algebra.tex:381-401`, paper origin
`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:917-925`.
-/
abbrev Cube (m : ℕ) := Fin m → Bool

/--
The representative polynomial which is `1` at `y` on the Boolean cube and
zero at the other cube points.  This is the indicator polynomial in
`def:low-degree-encoding` (blueprint lines 381-401; paper
`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:917-925`).
-/
noncomputable def indicatorPoly {K : Type*} [CommRing K] {m : ℕ} (y : Cube m) :
    MvPolynomial (Fin m) K :=
  ∏ i : Fin m, if y i then X i else (1 - X i)

/--
The multilinear low-degree encoding of a coefficient string.  Polynomial
representatives are used, as fixed by issue #0004, rather than quotienting by
functional equality.  Blueprint: `def:low-degree-encoding`,
`blueprint/src/chapter/ch11_qpbt_algebra.tex:381-401`; paper origin:
`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:917-925`.
-/
noncomputable def lowDegreeEncoding {K : Type*} [CommRing K] {m : ℕ}
    (a : Cube m → K) : MvPolynomial (Fin m) K :=
  ∑ y : Cube m, a y • indicatorPoly y

/- Evaluation shorthand for the representative polynomial in
`def:low-degree-encoding`; it is Lean-only notation. -/
/-- Evaluation shorthand for the low-degree encoding.  Blueprint
`blueprint/src/chapter/ch11_qpbt_algebra.tex:381-401`, paper origin
`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:917-925`.
-/
noncomputable def lowDegreeEnc {K : Type*} [CommRing K] {m : ℕ}
    (a : Cube m → K) (x : Fin m → K) : K :=
  eval x (lowDegreeEncoding a)

/--
The indicator vector `ind_m(x)` of `def:indicator-vector`.
Blueprint: `blueprint/src/chapter/ch11_qpbt_algebra.tex:403-417`; paper origin:
`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:917-925`.
-/
noncomputable def indicatorVec {K : Type*} [CommRing K] {m : ℕ}
    (x : Fin m → K) : Cube m → K :=
  fun y => eval x (indicatorPoly y)

/--
The defining dot-product identity for the encoding, corresponding to
Equation `eq:low-degree-encoding-definition` and `lem:indicator-vector` in the
blueprint `blueprint/src/chapter/ch11_qpbt_algebra.tex:403-417`, paper origin
`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:917-925`.
It is a proof obligation in stage 4.1.
-/
theorem lowDegreeEnc_eq_dotProduct {K : Type*} [CommRing K] {m : ℕ}
    (a : Cube m → K) (x : Fin m → K) :
    lowDegreeEnc a x = dotProduct a (indicatorVec x) := by
  sorry

/-- Re-export of the LDT polynomial representative class (`def:polyfunc`).
Blueprint `blueprint/src/chapter/ch11_qpbt_algebra.tex:321-329`; paper origin
`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:917-925`.
-/
noncomputable abbrev polyFunc (m d : ℕ) (K : Type*) [CommSemiring K] :
    Submodule K (MvPolynomial (Fin m) K) :=
  MIPStarRE.LDT.Preliminaries.polyFunc m K d

end MIPStarRE.QPBT
