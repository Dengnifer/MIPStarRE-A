import MIPStarRE.LDT.MakingMeasurementsProjective.NaimarkFull
import MIPStarRE.QPBT.Test.MagicSquareTheorems.Rigidity.Relations

open scoped BigOperators Matrix MatrixOrder ComplexOrder

namespace MIPStarRE.QPBT.MagicSquareRigidity

open MIPStarRE.LDT MIPStarRE.Quantum
open MIPStarRE.LDT.MakingMeasurementsProjective

noncomputable section

variable {ι α : Type} [Fintype ι] [DecidableEq ι] [Fintype α] [DecidableEq α]

/-- test -/
noncomputable def groundEmbedLin (ι α : Type) [Fintype ι] [DecidableEq ι]
    [Fintype α] [DecidableEq α] :
    EuclideanSpace ℂ ι →ₗ[ℂ] EuclideanSpace ℂ (ι × Option α) where
  toFun x := (EuclideanSpace.equiv (ι × Option α) ℂ).symm
    (fun p => if p.2 = none then x p.1 else 0)
  map_add' x y := by
    ext p
    by_cases h : p.2 = none <;> simp [h]
  map_smul' c x := by
    ext p
    by_cases h : p.2 = none <;> simp [h]

example (x : EuclideanSpace ℂ ι) (p : ι × Option α) :
    groundEmbedLin ι α x p = if p.2 = none then x p.1 else 0 := rfl

example (x y : EuclideanSpace ℂ ι) :
    inner ℂ (groundEmbedLin ι α x) (groundEmbedLin ι α y) = inner ℂ x y := by
  simp [PiLp.inner_apply, Fintype.sum_prod_type, groundEmbedLin]

end

end MIPStarRE.QPBT.MagicSquareRigidity
