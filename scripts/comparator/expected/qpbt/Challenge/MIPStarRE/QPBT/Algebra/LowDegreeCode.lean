import Mathlib

/-! Challenge mirror of `MIPStarRE/QPBT/Algebra/LowDegreeCode.lean`.

One challenge module per contributing library module, importing the
mirrors of the library modules this one imports.  The partition is
what makes Lean generate the same auxiliary declarations, under the
same names, as the library does. -/

open scoped BigOperators MatrixOrder Matrix ComplexOrder
namespace MIPStarRE.QPBT

-- elaboration context of MIPStarRE/QPBT/Algebra/LowDegreeCode.lean
section
open MvPolynomial

-- source: MIPStarRE/QPBT/Algebra/LowDegreeCode.lean:30-35  (MIPStarRE.QPBT.Cube)
/-- The Boolean cube indexing the `2^m` qudits of the test.  This is the index
type in blueprint
`def:low-degree-encoding`, paper origin
`references/qpbt-paper/04_preliminaries.tex:832-897`.
-/
abbrev Cube (m : ℕ) := Fin m → Bool

-- source: MIPStarRE/QPBT/Algebra/LowDegreeCode.lean:37-45  (MIPStarRE.QPBT.indicatorPoly)
/--
The representative polynomial which is `1` at `y` on the Boolean cube and
zero at the other cube points.  This is the indicator polynomial in blueprint
`def:low-degree-encoding`; paper
`references/qpbt-paper/04_preliminaries.tex:832-897`.
-/
noncomputable def indicatorPoly {K : Type*} [CommRing K] {m : ℕ} (y : Cube m) :
    MvPolynomial (Fin m) K :=
  ∏ i : Fin m, if y i then X i else (1 - X i)

-- source: MIPStarRE/QPBT/Algebra/LowDegreeCode.lean:47-55  (MIPStarRE.QPBT.lowDegreeEncoding)
/--
The multilinear low-degree encoding of a coefficient string.  Polynomial
representatives are used, as fixed by issue #0004, rather than quotienting by
functional equality.  Blueprint: `def:low-degree-encoding`; paper origin:
`references/qpbt-paper/04_preliminaries.tex:832-897`.
-/
noncomputable def lowDegreeEncoding {K : Type*} [CommRing K] {m : ℕ}
    (a : Cube m → K) : MvPolynomial (Fin m) K :=
  ∑ y : Cube m, a y • indicatorPoly y

-- source: MIPStarRE/QPBT/Algebra/LowDegreeCode.lean:59-65  (MIPStarRE.QPBT.lowDegreeEnc)
/-- Evaluation shorthand for the low-degree encoding.  Blueprint
`def:low-degree-encoding`, paper origin
`references/qpbt-paper/04_preliminaries.tex:832-897`.
-/
noncomputable def lowDegreeEnc {K : Type*} [CommRing K] {m : ℕ}
    (a : Cube m → K) (x : Fin m → K) : K :=
  eval x (lowDegreeEncoding a)

-- source: MIPStarRE/QPBT/Algebra/LowDegreeCode.lean:67-74  (MIPStarRE.QPBT.indicatorVec)
/--
The indicator vector `ind_m(x)` of `def:indicator-vector`.
Blueprint: `def:indicator-vector`; paper origin:
`references/qpbt-paper/04_preliminaries.tex:832-897`.
-/
noncomputable def indicatorVec {K : Type*} [CommRing K] {m : ℕ}
    (x : Fin m → K) : Cube m → K :=
  fun y => eval x (indicatorPoly y)
end  -- module scope
end MIPStarRE.QPBT
