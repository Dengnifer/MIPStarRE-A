import Mathlib
import MIPStarRE.Quantum.Measurement
import MIPStarRE.QPBT.Algebra.Pauli
import MIPStarRE.LDT.Basic.Distribution

/-!
# Games, tensor-product strategies, and value

This file provides the finite game carrier used by the Pauli basis test.  Pure
states are vectors in `EuclideanSpace`, and POVMs use the project's matrix
`Measurement` structure.

## References

The source-facing nodes are `def:game`, `def:povm-conventions`,
`def:tensor-product-strategy`, and `def:tensor-product-value` in
`blueprint/src/chapter/ch12_qpbt_games.tex:47-82` and `8-26`.
The paper origin is `references/qpbt-paper/06_nonlocal_games_and_mipstar.tex:10-57`.
-/

open scoped BigOperators Matrix ComplexOrder

namespace MIPStarRE.QPBT

open MIPStarRE.LDT
open MIPStarRE.Quantum

/--
A finite two-player one-round game with a probability distribution on question
pairs and a Boolean decision predicate.  This is `def:game` in
`blueprint/src/chapter/ch12_qpbt_games.tex:51-59`, with paper origin
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

attribute [instance] Game.questionAFintype Game.questionBFintype
  Game.answerAFintype Game.answerBFintype Game.questionADecidableEq
  Game.questionBDecidableEq Game.answerADecidableEq Game.answerBDecidableEq

/--
The marginal of a joint POVM obtained by post-processing its answer pair.  This
is the POVM convention of `def:povm-conventions` in
`blueprint/src/chapter/ch12_qpbt_games.tex:8-26`; the post-processing operation
is the already formalized `Measurement.postprocess`, with paper origin
`references/qpbt-paper/06_nonlocal_games_and_mipstar.tex:26-38`.
-/
noncomputable def marginalLeft {α β d : Type*}
    [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]
    [Fintype d] [DecidableEq d]
    (M : Measurement (α × β) d) : Measurement α d :=
  M.postprocess Prod.fst

/-- The right marginal of a joint POVM, obtained using `Prod.snd` in
`def:povm-conventions`, `blueprint/src/chapter/ch12_qpbt_games.tex:8-26`,
paper origin `references/qpbt-paper/06_nonlocal_games_and_mipstar.tex:26-38`.
-/
noncomputable def marginalRight {α β d : Type*}
    [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]
    [Fintype d] [DecidableEq d]
    (M : Measurement (α × β) d) : Measurement β d :=
  M.postprocess Prod.snd

/-- Projectivity of every effect in a POVM (`def:povm-conventions`, blueprint
`blueprint/src/chapter/ch12_qpbt_games.tex:8-26`; paper origin
`references/qpbt-paper/06_nonlocal_games_and_mipstar.tex:68-72`). -/
def Measurement.IsProjective {α d : Type*} [Fintype α] [Fintype d] [DecidableEq d]
    (M : Measurement α d) : Prop :=
  ∀ a, IsProj (M.effect a)

/--
The tensor-product strategy of `def:tensor-product-strategy` in
`blueprint/src/chapter/ch12_qpbt_games.tex:61-69` (paper origin
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

attribute [instance] Strategy.ιAFintype Strategy.ιBFintype
  Strategy.ιADecidableEq Strategy.ιBDecidableEq

/-- The rectangular tensor placement used in strategy probabilities.  This is
the finite-matrix realization of `def:tensor-product-strategy`, blueprint
`blueprint/src/chapter/ch12_qpbt_games.tex:61-69`; paper origin
`references/qpbt-paper/06_nonlocal_games_and_mipstar.tex:26-38`.
-/
def heteroKron {ιA ιB : Type*} (A : Op ιA) (B : Op ιB) : Op (ιA × ιB) :=
  Matrix.kronecker A B

/- The Euclidean linear map is the shared action used by the value and distance
functionals.  Keeping it at the Euclidean-space level avoids accidentally
using the function-space supremum norm of `Matrix.mulVec`. -/
/-- Apply a finite matrix to a Euclidean-space state.  This is the Hilbert-space
action underlying `def:tensor-product-value`, paper
`references/qpbt-paper/06_nonlocal_games_and_mipstar.tex:219-271`. -/
noncomputable def applyOperatorToState {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : Op ι) (ψ : EuclideanSpace ℂ ι) : EuclideanSpace ℂ ι :=
  Matrix.toEuclideanLin M ψ

/-- The Born weight of an answer pair for a strategy.  Lean-only support for
`def:tensor-product-value`, blueprint `ch12_qpbt_games.tex:71-82`, paper
`references/qpbt-paper/06_nonlocal_games_and_mipstar.tex:219-271`. -/
private noncomputable def outcomeWeight {G : Game} (S : Strategy G)
    (x : G.QuestionA) (y : G.QuestionB) (a : G.AnswerA) (b : G.AnswerB) : ℝ :=
  let M : MIPStarRE.Quantum.Op (S.ιA × S.ιB) :=
    heteroKron ((S.A x).effect a) ((S.B y).effect b)
  let acted := applyOperatorToState M S.ψ
  (inner ℂ S.ψ acted).re

/--
The tensor-product value, expressed as the distribution average of the Born
probabilities.  This is `def:tensor-product-value` in
`blueprint/src/chapter/ch12_qpbt_games.tex:71-82`, with paper origin
`references/qpbt-paper/06_nonlocal_games_and_mipstar.tex:40-57`.
-/
noncomputable def Strategy.value {G : Game} (S : Strategy G) : ℝ :=
  avgOver G.μ (fun xy =>
    ∑ a : G.AnswerA, ∑ b : G.AnswerB,
      if G.decide xy.1 xy.2 a b then outcomeWeight S xy.1 xy.2 a b else 0)

/--
The tensor-product game value as a conditional supremum over all finite
strategies.  The `sSup (Set.range ...)` form is the csSup formulation requested
for `def:tensor-product-value`, blueprint
`blueprint/src/chapter/ch12_qpbt_games.tex:71-82`, paper origin
`references/qpbt-paper/06_nonlocal_games_and_mipstar.tex:40-57`; attainment is
intentionally not asserted here.
-/
noncomputable def Game.value (G : Game) : ℝ :=
  sSup (Set.range (fun S : Strategy G => S.value))

end MIPStarRE.QPBT
