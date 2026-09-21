import Mathlib

/-! Challenge mirror of `MIPStarRE/LDT/Basic/ParametersBase.lean`.

One challenge module per contributing library module, importing the
mirrors of the library modules this one imports.  The partition is
what makes Lean generate the same auxiliary declarations, under the
same names, as the library does. -/

open scoped BigOperators MatrixOrder Matrix ComplexOrder
namespace MIPStarRE.LDT

-- source: MIPStarRE/LDT/Basic/ParametersBase.lean:18-18  (MIPStarRE.LDT.Error)
abbrev Error := ℝ

-- source: MIPStarRE/LDT/Basic/ParametersBase.lean:210-217  (MIPStarRE.LDT.FieldModel)
/-- A bundled field model for the paper's `F_q`, together with a coding equivalence
to the repository's finite carrier `Fin q`. -/
class FieldModel (q : ℕ) where
  K : Type*
  instField : Field K
  instFintype : Fintype K
  instDecidableEq : DecidableEq K
  equiv : K ≃ Fin q

-- source: MIPStarRE/LDT/Basic/ParametersBase.lean (attribute command)
attribute [instance_reducible, instance] FieldModel.instField FieldModel.instFintype
  FieldModel.instDecidableEq
end MIPStarRE.LDT
