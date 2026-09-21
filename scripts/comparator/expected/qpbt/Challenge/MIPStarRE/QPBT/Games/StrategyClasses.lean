import Mathlib
import Challenge.MIPStarRE.QPBT.Games.Consistency

/-! Challenge mirror of `MIPStarRE/QPBT/Games/StrategyClasses.lean`.

One challenge module per contributing library module, importing the
mirrors of the library modules this one imports.  The partition is
what makes Lean generate the same auxiliary declarations, under the
same names, as the library does. -/

open scoped BigOperators MatrixOrder Matrix ComplexOrder
namespace MIPStarRE.QPBT

-- elaboration context of MIPStarRE/QPBT/Games/StrategyClasses.lean:1-155
section
open scoped Matrix MatrixOrder ComplexOrder
open MIPStarRE.LDT MIPStarRE.Quantum

-- source: MIPStarRE/QPBT/Games/StrategyClasses.lean:25-29  (MIPStarRE.QPBT.Strategy.IsProjective)
/-- Projectivity from blueprint
`def:projective-strategy-general`, paper `06_nonlocal_games_and_mipstar.tex:68-72`. -/
def Strategy.IsProjective {G : Game} (S : Strategy G) : Prop :=
  (∀ x, MIPStarRE.QPBT.Measurement.IsProjective (S.A x)) ∧
    ∀ y, MIPStarRE.QPBT.Measurement.IsProjective (S.B y)

-- source: MIPStarRE/QPBT/Games/StrategyClasses.lean:31-46  (MIPStarRE.QPBT.SymmetricGame)
/-- Symmetric games from blueprint
`def:symmetric-game`, paper `06_nonlocal_games_and_mipstar.tex:74-92`.
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

-- source: MIPStarRE/QPBT/Games/StrategyClasses.lean (attribute command)
attribute [instance] SymmetricGame.questionFintype
  SymmetricGame.answerFintype SymmetricGame.questionDecidableEq
  SymmetricGame.answerDecidableEq

-- source: MIPStarRE/QPBT/Games/StrategyClasses.lean:51-61  (MIPStarRE.QPBT.SymmetricGame.toGame)
/-- Regard a symmetric game as a game with equal question and answer types;
blueprint
`def:symmetric-game`, paper `06_nonlocal_games_and_mipstar.tex:74-92`. -/
def SymmetricGame.toGame (G : SymmetricGame) : Game where
  QuestionA := G.Question
  QuestionB := G.Question
  AnswerA := G.Answer
  AnswerB := G.Answer
  μ := G.μ
  μ_prob := G.μ_prob
  decide := G.decide

-- source: MIPStarRE/QPBT/Games/StrategyClasses.lean:63-74  (MIPStarRE.QPBT.SymmetricStrategy)
/-- Symmetric strategies from blueprint
`def:symmetric-game`, paper `06_nonlocal_games_and_mipstar.tex:74-92`.
The two local spaces and measurement families are identified, as in the source
definition. -/
structure SymmetricStrategy (G : SymmetricGame) where
  ι : Type
  [ιFintype : Fintype ι]
  [ιDecidableEq : DecidableEq ι]
  ψ : EuclideanSpace ℂ (ι × ι)
  ψ_norm : ‖ψ‖ = 1
  ψ_swap : reindexState (Equiv.prodComm ι ι) ψ = ψ
  M : G.Question → MIPStarRE.Quantum.Measurement G.Answer ι

-- source: MIPStarRE/QPBT/Games/StrategyClasses.lean (attribute command)
attribute [instance] SymmetricStrategy.ιFintype
  SymmetricStrategy.ιDecidableEq

-- source: MIPStarRE/QPBT/Games/StrategyClasses.lean:78-88  (MIPStarRE.QPBT.SymmetricStrategy.toStrategy)
/-- Regard a symmetric strategy as a strategy using the same local space and
measurement family for both players; blueprint
`def:symmetric-game`, paper `06_nonlocal_games_and_mipstar.tex:74-92`. -/
def SymmetricStrategy.toStrategy {G : SymmetricGame} (S : SymmetricStrategy G) :
    Strategy G.toGame where
  ιA := S.ι
  ιB := S.ι
  ψ := S.ψ
  ψ_norm := S.ψ_norm
  A := S.M
  B := S.M

-- source: MIPStarRE/QPBT/Games/StrategyClasses.lean:90-99  (MIPStarRE.QPBT.IsCommutingOn)
/-- Common-space commutation from blueprint
`def:comm-strategy`, paper `06_nonlocal_games_and_mipstar.tex:132-142`. -/
def IsCommutingOn {X Y α β ι : Type*}
    [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]
    [Fintype α] [DecidableEq α] [Fintype β]
    [DecidableEq β] [Fintype ι] [DecidableEq ι]
    (μ : Distribution (X × Y))
    (A : X → MIPStarRE.Quantum.Measurement α ι)
    (B : Y → MIPStarRE.Quantum.Measurement β ι) : Prop :=
  ∀ x y, 0 < μ.weight (x, y) → ∀ a b, Commute ((A x).effect a) ((B y).effect b)

-- source: MIPStarRE/QPBT/Games/StrategyClasses.lean:110-117  (MIPStarRE.QPBT.Measurement.IsConsistentOn)
/-- Measurement consistency from blueprint
`def:consistent-measurement`, paper `06_nonlocal_games_and_mipstar.tex:144-160`. -/
def Measurement.IsConsistentOn {α ι : Type*}
    [Fintype α] [DecidableEq α] [Fintype ι] [DecidableEq ι]
    (M : MIPStarRE.Quantum.Measurement α ι)
    (ψ : EuclideanSpace ℂ (ι × ι)) : Prop :=
  ∀ a, (heteroKron (M.effect a) 1).mulVec ψ =
    (heteroKron 1 (M.effect a)).mulVec ψ

-- source: MIPStarRE/QPBT/Games/StrategyClasses.lean:131-135  (MIPStarRE.QPBT.SymmetricStrategy.IsConsistent)
/-- Symmetric strategy consistency from blueprint
`def:consistent-strategy`, paper `06_nonlocal_games_and_mipstar.tex:162-174`. -/
def SymmetricStrategy.IsConsistent {G : SymmetricGame}
    (S : SymmetricStrategy G) : Prop :=
  ∀ x, MIPStarRE.QPBT.Measurement.IsConsistentOn (S.M x) S.ψ

-- source: MIPStarRE/QPBT/Games/StrategyClasses.lean:149-154  (MIPStarRE.QPBT.SymmetricStrategy.IsSPCC)
/-- The SPCC predicate blueprint `def:spcc`,
paper `06_nonlocal_games_and_mipstar.tex:176-180`. -/
def SymmetricStrategy.IsSPCC {G : SymmetricGame}
  (S : SymmetricStrategy G) : Prop :=
  (∀ x, MIPStarRE.QPBT.Measurement.IsProjective (S.M x)) ∧ S.IsConsistent ∧
    IsCommutingOn G.μ S.M S.M
end  -- module scope
end MIPStarRE.QPBT
