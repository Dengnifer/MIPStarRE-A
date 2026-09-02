import MIPStarRE.QPBT.Games.Distance
import MIPStarRE.QPBT.Games.DistributionAux
import MIPStarRE.QPBT.State

/-! # State-dependent consistency and strategy closeness

The definitions are the finite-dimensional forms of `def:consistency` and
`def:strategy-distance` in `blueprint/src/chapter/ch12_qpbt_games.tex:180-220`,
from `references/qpbt-paper/06_nonlocal_games_and_mipstar.tex:219-271`.
-/

open scoped BigOperators

namespace MIPStarRE.QPBT

open MIPStarRE.LDT MIPStarRE.Quantum

/-- The off-diagonal defect in `def:consistency`, blueprint
`ch12_qpbt_games.tex:181-191`, paper `06_nonlocal_games_and_mipstar.tex:232-248`. -/
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

/-- The quantitative relation in `def:consistency`, blueprint
`ch12_qpbt_games.tex:181-191`, paper `06_nonlocal_games_and_mipstar.tex:232-248`. -/
def IsConsistentWithin {X α ι : Type*}
    [Fintype X] [DecidableEq X] [Fintype α] [DecidableEq α]
    [Fintype ι] [DecidableEq ι]
    (μ : Distribution X) (A B : X → α → Op ι)
    (ψ : EuclideanSpace ℂ ι) (δ : ℝ) : Prop :=
  consistencyDefect μ A B ψ ≤ δ

/-- Unit-alphabet specialization of `def:povm-distance`, blueprint
`ch12_qpbt_games.tex:203-210`, paper `06_nonlocal_games_and_mipstar.tex:258-271`. -/
noncomputable def opDistSq {X ι : Type*}
    [Fintype X] [DecidableEq X] [Fintype ι] [DecidableEq ι]
    (μ : Distribution X) (M N : X → Op ι) (ψ : EuclideanSpace ℂ ι) : ℝ :=
  opFamilyDistSq μ (fun x (_ : Unit) => M x) (fun x (_ : Unit) => N x) ψ

/-- The unit-alphabet operator distance equals its one-outcome family form from
`def:povm-distance`, blueprint `ch12_qpbt_games.tex:203-210`, paper
`06_nonlocal_games_and_mipstar.tex:258-271`. -/
theorem opDistSq_eq_opFamilyDistSq {X ι : Type*}
    [Fintype X] [DecidableEq X] [Fintype ι] [DecidableEq ι]
    (μ : Distribution X) (M N : X → Op ι) (ψ : EuclideanSpace ℂ ι) :
    opDistSq μ M N ψ = opFamilyDistSq μ (fun x (_ : Unit) => M x)
      (fun x (_ : Unit) => N x) ψ := rfl

/-- The strategy-distance relation `def:strategy-distance`, with local
identifications induced by explicit type equalities; blueprint
`ch12_qpbt_games.tex:212-219`, paper `06_nonlocal_games_and_mipstar.tex:273-285`.
Both operator distances use the source-permitted state vector `S.ψ`. -/
structure AreCloseStrategies (G : Game) (S S' : Strategy G) (δ : ℝ) : Prop where
  /-- Explicit equality of Alice's local spaces. -/
  hA : S.ιA = S'.ιA
  /-- Explicit equality of Bob's local spaces. -/
  hB : S.ιB = S'.ιB
  state : stateDistSq S.ψ (reindexState
      (Equiv.prodCongr (Equiv.cast hA).symm (Equiv.cast hB).symm) S'.ψ) ≤ δ
  alice : opFamilyDistSq (G.μ.map Prod.fst)
      (fun x a => heteroKron ((S.A x).effect a) 1)
      (fun x a => heteroKron (reindexOp (Equiv.cast hA) ((S'.A x).effect a)) 1)
      S.ψ ≤ δ
  bob : opFamilyDistSq (G.μ.map Prod.snd)
      (fun y b => heteroKron 1 ((S.B y).effect b))
      (fun y b => heteroKron 1 (reindexOp (Equiv.cast hB) ((S'.B y).effect b)))
      S.ψ ≤ δ

end MIPStarRE.QPBT
