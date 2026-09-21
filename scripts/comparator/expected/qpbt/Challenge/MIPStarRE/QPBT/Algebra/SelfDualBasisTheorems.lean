import Mathlib
import Challenge.MIPStarRE.QPBT.Algebra.SelfDualBasis

/-! Challenge mirror of `MIPStarRE/QPBT/Algebra/SelfDualBasisTheorems.lean`.

One challenge module per contributing library module, importing the
mirrors of the library modules this one imports.  The partition is
what makes Lean generate the same auxiliary declarations, under the
same names, as the library does. -/

open scoped BigOperators MatrixOrder Matrix ComplexOrder
namespace MIPStarRE.QPBT

-- elaboration context of MIPStarRE/QPBT/Algebra/SelfDualBasisTheorems.lean
section
open MIPStarRE.LDT

-- source: MIPStarRE/QPBT/Algebra/SelfDualBasisTheorems.lean:144-149  (MIPStarRE.QPBT.kappaVec)
/-- Fixed-model coordinate vector for item 3 of
blueprint `lem:downsize_field`, paper
`04_preliminaries.tex:509-550`. -/
noncomputable def kappaVec {q : ℕ} {ι : Type*} (F : FixedFieldModel q)
    (v : ι → F.K) : ι × Fin F.basisDim → ZMod 2 :=
  basisCoordVec F.basis v
end  -- module scope
end MIPStarRE.QPBT
