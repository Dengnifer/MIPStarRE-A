import Mathlib
import Challenge.MIPStarRE.QPBT.Games.Defs
import Challenge.MIPStarRE.QPBT.Games.DistributionAux
import Challenge.MIPStarRE.QPBT.State

/-! Challenge mirror of `MIPStarRE/QPBT/Games/Consistency.lean`.

One challenge module per contributing library module, importing the
mirrors of the library modules this one imports.  The partition is
what makes Lean generate the same auxiliary declarations, under the
same names, as the library does. -/

open scoped BigOperators MatrixOrder Matrix ComplexOrder
namespace MIPStarRE.QPBT

-- elaboration context of MIPStarRE/QPBT/Games/Consistency.lean
section
open MIPStarRE.LDT MIPStarRE.Quantum

-- source: MIPStarRE/QPBT/Games/Consistency.lean:19-30  (MIPStarRE.QPBT.consistencyDefect)
/-- The off-diagonal defect in blueprint
`def:consistency`, paper `06_nonlocal_games_and_mipstar.tex:232-248`. -/
noncomputable def consistencyDefect {X α ι : Type*}
    [Fintype X] [DecidableEq X] [Fintype α] [DecidableEq α]
    [Fintype ι] [DecidableEq ι]
    (μ : Distribution X) (A B : X → α → Op ι)
    (ψ : EuclideanSpace ℂ ι) : ℝ :=
  avgOver μ (fun x =>
    ∑ a : α, ∑ b : α,
      if a = b then 0 else
        (inner ℂ ψ ((EuclideanSpace.equiv ι ℂ).symm
          ((A x a * B x b).mulVec ψ))).re)
end  -- module scope
end MIPStarRE.QPBT
