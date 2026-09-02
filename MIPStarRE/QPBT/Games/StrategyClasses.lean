import MIPStarRE.QPBT.Games.Defs
import MIPStarRE.QPBT.Games.Consistency
import MIPStarRE.QPBT.State

/-! # Strategy classes and symmetric games

This module defines projective, commuting, consistent, PCC, and SPCC strategy
predicates from `blueprint/src/chapter/ch12_qpbt_games.tex:89-169`, with source
definitions in `references/qpbt-paper/06_nonlocal_games_and_mipstar.tex:68-180`.
-/

namespace MIPStarRE.QPBT

universe u

open MIPStarRE.LDT MIPStarRE.Quantum

/-- Projectivity from `def:projective-strategy-general`, blueprint
`ch12_qpbt_games.tex:90-101`, paper `06_nonlocal_games_and_mipstar.tex:68-72`. -/
def Strategy.IsProjective {G : Game} (S : Strategy G) : Prop :=
  (∀ x, MIPStarRE.QPBT.Measurement.IsProjective (S.A x)) ∧
    ∀ y, MIPStarRE.QPBT.Measurement.IsProjective (S.B y)

/-- Symmetric games from `def:symmetric-game`, blueprint
`ch12_qpbt_games.tex:98-107`, paper `06_nonlocal_games_and_mipstar.tex:74-92`.
The question and answer alphabets are each represented by a single shared type,
matching the source notation. -/
structure SymmetricGame where
  Question : Type
  Answer : Type
  [questionFintype : Fintype Question]
  [answerFintype : Fintype Answer]
  [questionDecidableEq : DecidableEq Question]
  [answerDecidableEq : DecidableEq Answer]
  μ : Distribution (Question × Question)
  μ_prob : μ.IsProbability
  μ_symm : ∀ x y, μ.weight (x, y) = μ.weight (y, x)
  decide : Question → Question → Answer → Answer → Bool
  decide_symm : ∀ x y a b, decide x y a b = decide y x b a

attribute [instance] SymmetricGame.questionFintype SymmetricGame.answerFintype
  SymmetricGame.questionDecidableEq SymmetricGame.answerDecidableEq

/-- Regard a symmetric game as a game with equal question and answer types;
`def:symmetric-game`, blueprint
`ch12_qpbt_games.tex:98-107`, paper `06_nonlocal_games_and_mipstar.tex:74-92`. -/
def SymmetricGame.toGame (G : SymmetricGame) : Game where
  QuestionA := G.Question
  QuestionB := G.Question
  AnswerA := G.Answer
  AnswerB := G.Answer
  μ := G.μ
  μ_prob := G.μ_prob
  decide := G.decide

/-- Symmetric strategies from `def:symmetric-game`, blueprint
`ch12_qpbt_games.tex:98-107`, paper `06_nonlocal_games_and_mipstar.tex:74-92`.
The two local spaces and measurement families are identified, as in the source
definition. -/
structure SymmetricStrategy (G : SymmetricGame) where
  ι : Type
  [ιFintype : Fintype ι]
  [ιDecidableEq : DecidableEq ι]
  ψ : EuclideanSpace ℂ (ι × ι)
  ψ_norm : ‖ψ‖ = 1
  ψ_swap : reindexState (Equiv.prodComm ι ι) ψ = ψ
  M : G.Question → Measurement G.Answer ι

attribute [instance] SymmetricStrategy.ιFintype SymmetricStrategy.ιDecidableEq

/-- Regard a symmetric strategy as a strategy using the same local space and
measurement family for both players; `def:symmetric-game`, blueprint
`ch12_qpbt_games.tex:98-107`, paper `06_nonlocal_games_and_mipstar.tex:74-92`. -/
def SymmetricStrategy.toStrategy {G : SymmetricGame} (S : SymmetricStrategy G) :
    Strategy G.toGame where
  ιA := S.ι
  ιB := S.ι
  ψ := S.ψ
  ψ_norm := S.ψ_norm
  A := S.M
  B := S.M

/-- Common-space commutation from `def:comm-strategy`, blueprint
`ch12_qpbt_games.tex:135-142`, paper `06_nonlocal_games_and_mipstar.tex:132-142`. -/
def IsCommutingOn {X Y α β ι : Type*}
    [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]
    [Fintype α] [DecidableEq α] [Fintype β]
    [DecidableEq β] [Fintype ι] [DecidableEq ι]
    (μ : Distribution (X × Y)) (A : X → Measurement α ι)
    (B : Y → Measurement β ι) : Prop :=
  ∀ x y, 0 < μ.weight (x, y) → ∀ a b, Commute ((A x).effect a) ((B y).effect b)

private def transportOp {d₁ d₂ : Type u} (h : d₁ = d₂) (M : Op d₂) : Op d₁ :=
  h.symm ▸ M

/-- Transported common-space form of `def:comm-strategy`, blueprint
`ch12_qpbt_games.tex:135-142`, paper `06_nonlocal_games_and_mipstar.tex:132-142`. -/
def Strategy.IsCommuting {G : Game} (S : Strategy G) (hι : S.ιA = S.ιB) : Prop :=
  ∀ x y, 0 < G.μ.weight (x, y) → ∀ a b,
    Commute ((S.A x).effect a) (transportOp hι ((S.B y).effect b))

/-- Measurement consistency from `def:consistent-measurement`, blueprint
`ch12_qpbt_games.tex:144-157`, paper `06_nonlocal_games_and_mipstar.tex:144-160`. -/
def Measurement.IsConsistentOn {α ι : Type*}
    [Fintype α] [DecidableEq α] [Fintype ι] [DecidableEq ι]
    (M : Measurement α ι) (ψ : EuclideanSpace ℂ (ι × ι)) : Prop :=
  ∀ a, (heteroKron (M.effect a) 1).mulVec ψ =
    (heteroKron 1 (M.effect a)).mulVec ψ

/-- General strategy consistency from `def:consistent-strategy`, blueprint
`ch12_qpbt_games.tex:159-162`, paper `06_nonlocal_games_and_mipstar.tex:162-174`. -/
def IsConsistentStrategyOn {X Y α β ι : Type*}
    [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]
    [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    [Fintype ι] [DecidableEq ι]
    (A : X → Measurement α ι) (B : Y → Measurement β ι)
    (ψ : EuclideanSpace ℂ (ι × ι)) : Prop :=
  (∀ x, MIPStarRE.QPBT.Measurement.IsConsistentOn (A x) ψ) ∧
    ∀ y, MIPStarRE.QPBT.Measurement.IsConsistentOn (B y) ψ

/-- Symmetric strategy consistency from `def:consistent-strategy`, blueprint
`ch12_qpbt_games.tex:159-162`, paper `06_nonlocal_games_and_mipstar.tex:162-174`. -/
def SymmetricStrategy.IsConsistent {G : SymmetricGame}
    (S : SymmetricStrategy G) : Prop :=
  ∀ x, MIPStarRE.QPBT.Measurement.IsConsistentOn (S.M x) S.ψ

/-- The PCC predicate `def:spcc`, blueprint `ch12_qpbt_games.tex:166-169`,
paper `06_nonlocal_games_and_mipstar.tex:176-180`. -/
def Strategy.IsPCC {G : Game} {ι : Type*}
    [Fintype ι] [DecidableEq ι]
    (μ : Distribution (G.QuestionA × G.QuestionB))
    (A : G.QuestionA → Measurement G.AnswerA ι)
    (B : G.QuestionB → Measurement G.AnswerB ι)
  (ψ : EuclideanSpace ℂ (ι × ι)) : Prop :=
  (∀ x, MIPStarRE.QPBT.Measurement.IsProjective (A x)) ∧
    (∀ y, MIPStarRE.QPBT.Measurement.IsProjective (B y)) ∧
    IsConsistentStrategyOn A B ψ ∧ IsCommutingOn μ A B

/-- The SPCC predicate `def:spcc`, blueprint `ch12_qpbt_games.tex:166-169`,
paper `06_nonlocal_games_and_mipstar.tex:176-180`. -/
def SymmetricStrategy.IsSPCC {G : SymmetricGame}
  (S : SymmetricStrategy G) : Prop :=
  (∀ x, MIPStarRE.QPBT.Measurement.IsProjective (S.M x)) ∧ S.IsConsistent ∧
    IsCommutingOn G.μ S.M S.M

/-- Source symmetrization statement `lem:symmetric-strat`, blueprint
`ch12_qpbt_games.tex:112-132`, paper `06_nonlocal_games_and_mipstar.tex:94-130`.
The attainment defect is `rem:symmetric-strat-limit` and is tracked in
`docs/paper-gaps/qpbt_symmetrization-attainment.tex`. -/
theorem exists_symmetric_projective_strategy (G : SymmetricGame) (ε : ℝ)
    (hε : 0 ≤ ε) (h : G.toGame.value = 1 - ε) :
    ∃ S : SymmetricStrategy G, S.toStrategy.IsProjective ∧
      1 - ε ≤ S.toStrategy.value := by
  sorry

/-- Formalization-only form of `lem:symmetric-strat` starting from a specified
near-optimal strategy; blueprint
`ch12_qpbt_games.tex:112-132`, paper `06_nonlocal_games_and_mipstar.tex:94-130`.
The source attainment distinction is tracked in
`docs/paper-gaps/qpbt_symmetrization-attainment.tex`. -/
theorem exists_symmetric_projective_strategy_of_strategy (G : SymmetricGame)
    (ε : ℝ) (S₀ : Strategy G.toGame) (h : 1 - ε ≤ S₀.value) :
    ∃ S : SymmetricStrategy G, S.toStrategy.IsProjective ∧
      1 - ε ≤ S.toStrategy.value := by
  sorry

end MIPStarRE.QPBT
