import MIPStarRE.LDT.Basic.DistributionAvg
import MIPStarRE.QPBT.Games.Distance
import MIPStarRE.QPBT.Games.DistributionAux
import MIPStarRE.QPBT.State

/-! # State-dependent consistency and strategy closeness

The definitions are the finite-dimensional forms of `def:consistency` and
`def:strategy-distance` in `blueprint/src/chapter/ch12_qpbt_games.tex:195-237`,
from `references/qpbt-paper/06_nonlocal_games_and_mipstar.tex:219-288`.
-/

open scoped BigOperators

namespace MIPStarRE.QPBT

open MIPStarRE.LDT MIPStarRE.Quantum

/-- The off-diagonal defect in `def:consistency`, blueprint
`ch12_qpbt_games.tex:195-208`, paper `06_nonlocal_games_and_mipstar.tex:232-248`. -/
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

/-- A uniform consistency defect is invariant under a bijective relabeling of
its question type. -/
theorem consistencyDefect_uniform_question_equiv
    {X Y Outcome iota : Type*}
    [Fintype X] [DecidableEq X] [Nonempty X]
    [Fintype Y] [DecidableEq Y] [Nonempty Y]
    [Fintype Outcome] [DecidableEq Outcome]
    [Fintype iota] [DecidableEq iota]
    (e : X ≃ Y) (A B : Y → Outcome → Op iota)
    (psi : EuclideanSpace ℂ iota) :
    consistencyDefect (uniformDistribution X)
        (fun x a => A (e x) a) (fun x a => B (e x) a) psi =
      consistencyDefect (uniformDistribution Y) A B psi := by
  unfold consistencyDefect
  simpa using avgOver_uniform_equiv e (fun x =>
    ∑ a : Outcome, ∑ b : Outcome,
      if a = b then 0 else
        (inner ℂ psi ((EuclideanSpace.equiv iota ℂ).symm
          (((A (e x) a) * (B (e x) b)).mulVec psi))).re)

/-- A consistency defect is invariant under a bijective relabeling of both
outcome families. -/
theorem consistencyDefect_outcome_equiv
    {X Alpha Beta iota : Type*}
    [Fintype X] [DecidableEq X]
    [Fintype Alpha] [DecidableEq Alpha]
    [Fintype Beta] [DecidableEq Beta]
    [Fintype iota] [DecidableEq iota]
    (mu : Distribution X) (e : Beta ≃ Alpha)
    (A B : X → Alpha → Op iota) (psi : EuclideanSpace ℂ iota) :
    consistencyDefect mu
        (fun x b => A x (e b)) (fun x b => B x (e b)) psi =
      consistencyDefect mu A B psi := by
  unfold consistencyDefect
  apply avgOver_congr
  intro x
  let term : Alpha → Alpha → ℝ := fun a b =>
    if a = b then 0 else
      (inner ℂ psi ((EuclideanSpace.equiv iota ℂ).symm
        (((A x a) * (B x b)).mulVec psi))).re
  calc
    _ = ∑ a : Beta, ∑ b : Beta, term (e a) (e b) := by
      apply Finset.sum_congr rfl
      intro a _
      apply Finset.sum_congr rfl
      intro b _
      unfold term
      by_cases hab : a = b
      · subst b
        simp
      · have heab : e a ≠ e b := fun h => hab (e.injective h)
        simp [hab, heab]
    _ =
        ∑ a : Beta, ∑ b : Alpha, term (e a) b := by
      apply Finset.sum_congr rfl
      intro a _
      exact Equiv.sum_comp e (fun b => term (e a) b)
    _ = ∑ a : Alpha, ∑ b : Alpha, term a b :=
      Equiv.sum_comp e (fun a => ∑ b : Alpha, term a b)
    _ = _ := rfl

/-- Simultaneous bijective relabeling of uniform questions and outcomes leaves
the consistency defect unchanged. -/
theorem consistencyDefect_uniform_question_outcome_equiv
    {X Y Alpha Beta iota : Type*}
    [Fintype X] [DecidableEq X] [Nonempty X]
    [Fintype Y] [DecidableEq Y] [Nonempty Y]
    [Fintype Alpha] [DecidableEq Alpha]
    [Fintype Beta] [DecidableEq Beta]
    [Fintype iota] [DecidableEq iota]
    (questionEquiv : X ≃ Y) (outcomeEquiv : Beta ≃ Alpha)
    (A B : Y → Alpha → Op iota) (psi : EuclideanSpace ℂ iota) :
    consistencyDefect (uniformDistribution X)
        (fun x b => A (questionEquiv x) (outcomeEquiv b))
        (fun x b => B (questionEquiv x) (outcomeEquiv b)) psi =
      consistencyDefect (uniformDistribution Y) A B psi := by
  calc
    consistencyDefect (uniformDistribution X)
        (fun x b => A (questionEquiv x) (outcomeEquiv b))
        (fun x b => B (questionEquiv x) (outcomeEquiv b)) psi =
      consistencyDefect (uniformDistribution X)
        (fun x a => A (questionEquiv x) a)
        (fun x a => B (questionEquiv x) a) psi :=
      consistencyDefect_outcome_equiv (uniformDistribution X)
        outcomeEquiv _ _ psi
    _ = consistencyDefect (uniformDistribution Y) A B psi :=
      consistencyDefect_uniform_question_equiv questionEquiv A B psi

/-- Pointwise equality of both operator families gives equality of their
consistency defects. -/
theorem consistencyDefect_congr
    {X Outcome iota : Type*}
    [Fintype X] [DecidableEq X]
    [Fintype Outcome] [DecidableEq Outcome]
    [Fintype iota] [DecidableEq iota]
    (mu : Distribution X) (A A' B B' : X → Outcome → Op iota)
    (psi : EuclideanSpace ℂ iota)
    (hA : ∀ x a, A x a = A' x a) (hB : ∀ x a, B x a = B' x a) :
    consistencyDefect mu A B psi = consistencyDefect mu A' B' psi := by
  unfold consistencyDefect
  apply avgOver_congr
  intro x
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  by_cases hab : a = b
  · simp [hab]
  · simp only [hab, if_false]
    rw [hA x a, hB x b]

/-- The quantitative relation in `def:consistency`, blueprint
`ch12_qpbt_games.tex:195-208`, paper `06_nonlocal_games_and_mipstar.tex:232-248`. -/
def IsConsistentWithin {X α ι : Type*}
    [Fintype X] [DecidableEq X] [Fintype α] [DecidableEq α]
    [Fintype ι] [DecidableEq ι]
    (μ : Distribution X) (A B : X → α → Op ι)
    (ψ : EuclideanSpace ℂ ι) (δ : ℝ) : Prop :=
  consistencyDefect μ A B ψ ≤ δ

/-- Unit-alphabet specialization of `def:povm-distance`, blueprint
`ch12_qpbt_games.tex:219-226`, paper `06_nonlocal_games_and_mipstar.tex:258-271`. -/
noncomputable def opDistSq {X ι : Type*}
    [Fintype X] [DecidableEq X] [Fintype ι] [DecidableEq ι]
    (μ : Distribution X) (M N : X → Op ι) (ψ : EuclideanSpace ℂ ι) : ℝ :=
  opFamilyDistSq μ (fun x (_ : Unit) => M x) (fun x (_ : Unit) => N x) ψ

/-- The unit-alphabet operator distance equals its one-outcome family form from
`def:povm-distance`, blueprint `ch12_qpbt_games.tex:219-226`, paper
`06_nonlocal_games_and_mipstar.tex:258-271`. -/
theorem opDistSq_eq_opFamilyDistSq {X ι : Type*}
    [Fintype X] [DecidableEq X] [Fintype ι] [DecidableEq ι]
    (μ : Distribution X) (M N : X → Op ι) (ψ : EuclideanSpace ℂ ι) :
    opDistSq μ M N ψ = opFamilyDistSq μ (fun x (_ : Unit) => M x)
      (fun x (_ : Unit) => N x) ψ := rfl

/-- The strategy-distance relation `def:strategy-distance`. The two strategies'
local Hilbert spaces are identified, and both measurement distances are
evaluated on the first strategy's state. Blueprint
`ch12_qpbt_games.tex:228-237`, paper `06_nonlocal_games_and_mipstar.tex:273-285`. -/
structure AreCloseStrategies (G : Game) (S S' : Strategy G) (δ : ℝ) : Prop where
  /-- Identification of Alice's local Hilbert spaces. -/
  hA : S.ιA = S'.ιA
  /-- Identification of Bob's local Hilbert spaces. -/
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
