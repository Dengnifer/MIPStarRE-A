import Mathlib
import Challenge.MIPStarRE.LDT.Basic.Distribution
import Challenge.MIPStarRE.Quantum.Measurement

/-! Challenge mirror of `MIPStarRE/QPBT/Games/Defs.lean`.

One challenge module per contributing library module, importing the
mirrors of the library modules this one imports.  The partition is
what makes Lean generate the same auxiliary declarations, under the
same names, as the library does. -/

open scoped BigOperators MatrixOrder Matrix ComplexOrder
namespace MIPStarRE.QPBT

-- elaboration context of MIPStarRE/QPBT/Games/Defs.lean
section
open MIPStarRE.LDT
open MIPStarRE.Quantum

-- source: MIPStarRE/QPBT/Games/Defs.lean:26-47  (MIPStarRE.QPBT.Game)
/--
A finite two-player one-round game with a probability distribution on question
pairs and a Boolean decision predicate.  This is blueprint
`def:game`, with paper origin
`references/qpbt-paper/06_nonlocal_games_and_mipstar.tex:10-24`.
-/
structure Game where
  QuestionA : Type
  QuestionB : Type
  AnswerA : Type
  AnswerB : Type
  [questionAFintype : Fintype QuestionA]
  [questionBFintype : Fintype QuestionB]
  [answerAFintype : Fintype AnswerA]
  [answerBFintype : Fintype AnswerB]
  [questionADecidableEq : DecidableEq QuestionA]
  [questionBDecidableEq : DecidableEq QuestionB]
  [answerADecidableEq : DecidableEq AnswerA]
  [answerBDecidableEq : DecidableEq AnswerB]
  μ : Distribution (QuestionA × QuestionB)
  μ_prob : μ.IsProbability
  decide : QuestionA → QuestionB → AnswerA → AnswerB → Bool

-- source: MIPStarRE/QPBT/Games/Defs.lean (attribute command)
attribute [instance] Game.questionAFintype Game.questionBFintype
  Game.answerAFintype Game.answerBFintype Game.questionADecidableEq
  Game.questionBDecidableEq Game.answerADecidableEq Game.answerBDecidableEq

-- source: MIPStarRE/QPBT/Games/Defs.lean:76-81  (MIPStarRE.QPBT.Measurement.IsProjective)
/-- Projectivity of every effect in a POVM (blueprint
`def:povm-conventions`; paper origin
`references/qpbt-paper/06_nonlocal_games_and_mipstar.tex:68-72`). -/
def Measurement.IsProjective {α d : Type*} [Fintype α] [Fintype d] [DecidableEq d]
    (M : Measurement α d) : Prop :=
  ∀ a, IsProj (M.effect a)

-- source: MIPStarRE/QPBT/Games/Defs.lean:83-98  (MIPStarRE.QPBT.Strategy)
/--
The tensor-product strategy of blueprint
`def:tensor-product-strategy` (paper origin
`references/qpbt-paper/06_nonlocal_games_and_mipstar.tex:26-38`).
-/
structure Strategy (G : Game) where
  ιA : Type
  ιB : Type
  [ιAFintype : Fintype ιA]
  [ιBFintype : Fintype ιB]
  [ιADecidableEq : DecidableEq ιA]
  [ιBDecidableEq : DecidableEq ιB]
  ψ : EuclideanSpace ℂ (ιA × ιB)
  ψ_norm : ‖ψ‖ = 1
  A : G.QuestionA → Measurement G.AnswerA ιA
  B : G.QuestionB → Measurement G.AnswerB ιB

-- source: MIPStarRE/QPBT/Games/Defs.lean (attribute command)
attribute [instance] Strategy.ιAFintype Strategy.ιBFintype
  Strategy.ιADecidableEq Strategy.ιBDecidableEq

-- source: MIPStarRE/QPBT/Games/Defs.lean:103-109  (MIPStarRE.QPBT.heteroKron)
/-- The rectangular tensor placement used in strategy probabilities.  This is
the finite-matrix realization of blueprint
`def:tensor-product-strategy`; paper origin
`references/qpbt-paper/06_nonlocal_games_and_mipstar.tex:26-38`.
-/
def heteroKron {ιA ιB : Type*} (A : Op ιA) (B : Op ιB) : Op (ιA × ιB) :=
  Matrix.kronecker A B

-- source: MIPStarRE/QPBT/Games/Defs.lean:207-212  (MIPStarRE.QPBT.applyOperatorToState)
/-- Apply a finite matrix to a Euclidean-space state.  This is the Hilbert-space
action underlying `def:tensor-product-value`, paper
`references/qpbt-paper/06_nonlocal_games_and_mipstar.tex:219-271`. -/
noncomputable def applyOperatorToState {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : Op ι) (ψ : EuclideanSpace ℂ ι) : EuclideanSpace ℂ ι :=
  Matrix.toEuclideanLin M ψ

-- source: MIPStarRE/QPBT/Games/Defs.lean:214-222  (MIPStarRE.QPBT.outcomeWeight)
/-- The Born weight of an answer pair for a strategy.  Lean-only support for
blueprint `def:tensor-product-value`, paper
`references/qpbt-paper/06_nonlocal_games_and_mipstar.tex:40-48`. -/
noncomputable def outcomeWeight {G : Game} (S : Strategy G)
    (x : G.QuestionA) (y : G.QuestionB) (a : G.AnswerA) (b : G.AnswerB) : ℝ :=
  let M : MIPStarRE.Quantum.Op (S.ιA × S.ιB) :=
    heteroKron ((S.A x).effect a) ((S.B y).effect b)
  let acted := applyOperatorToState M S.ψ
  (inner ℂ S.ψ acted).re

-- source: MIPStarRE/QPBT/Games/Defs.lean:483-492  (MIPStarRE.QPBT.Strategy.value)
/--
The tensor-product value, expressed as the distribution average of the Born
probabilities.  This is blueprint
`def:tensor-product-value`, with paper origin
`references/qpbt-paper/06_nonlocal_games_and_mipstar.tex:40-57`.
-/
noncomputable def Strategy.value {G : Game} (S : Strategy G) : ℝ :=
  avgOver G.μ (fun xy =>
    ∑ a : G.AnswerA, ∑ b : G.AnswerB,
      if G.decide xy.1 xy.2 a b then outcomeWeight S xy.1 xy.2 a b else 0)
end  -- module scope
end MIPStarRE.QPBT
