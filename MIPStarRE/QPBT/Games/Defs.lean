import MIPStarRE.Quantum.Measurement
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
`references/qpbt-paper/06_nonlocal_games_and_mipstar.tex:40-48`. -/
noncomputable def outcomeWeight {G : Game} (S : Strategy G)
    (x : G.QuestionA) (y : G.QuestionB) (a : G.AnswerA) (b : G.AnswerB) : ℝ :=
  let M : MIPStarRE.Quantum.Op (S.ιA × S.ιB) :=
    heteroKron ((S.A x).effect a) ((S.B y).effect b)
  let acted := applyOperatorToState M S.ψ
  (inner ℂ S.ψ acted).re

/-- Alice's marginal Born weight for an answer at a fixed question. -/
noncomputable def aliceOutcomeWeight {G : Game} (S : Strategy G)
    (x : G.QuestionA) (a : G.AnswerA) : ℝ :=
  let M : MIPStarRE.Quantum.Op (S.ιA × S.ιB) :=
    heteroKron ((S.A x).effect a) 1
  (inner ℂ S.ψ (applyOperatorToState M S.ψ)).re

/-- Bob's marginal Born weight for an answer at a fixed question. -/
noncomputable def bobOutcomeWeight {G : Game} (S : Strategy G)
    (y : G.QuestionB) (b : G.AnswerB) : ℝ :=
  let M : MIPStarRE.Quantum.Op (S.ιA × S.ιB) :=
    heteroKron 1 ((S.B y).effect b)
  (inner ℂ S.ψ (applyOperatorToState M S.ψ)).re

/-- The Born weight of a decidable event on the two answers at fixed questions. -/
noncomputable def outcomeEventWeight {G : Game} (S : Strategy G)
    (x : G.QuestionA) (y : G.QuestionB)
    (E : G.AnswerA → G.AnswerB → Prop) [DecidableRel E] : ℝ :=
  ∑ a : G.AnswerA, ∑ b : G.AnswerB,
    if E a b then outcomeWeight S x y a b else 0

/-- The marginal Born weight of a decidable event on Alice's answer. -/
noncomputable def aliceEventWeight {G : Game} (S : Strategy G)
    (x : G.QuestionA) (E : G.AnswerA → Prop) [DecidablePred E] : ℝ :=
  ∑ a : G.AnswerA, if E a then aliceOutcomeWeight S x a else 0

/-- The marginal Born weight of a decidable event on Bob's answer. -/
noncomputable def bobEventWeight {G : Game} (S : Strategy G)
    (y : G.QuestionB) (E : G.AnswerB → Prop) [DecidablePred E] : ℝ :=
  ∑ b : G.AnswerB, if E b then bobOutcomeWeight S y b else 0

/-- Every answer-pair Born weight is nonnegative.  This is formalization-only
support for the probability expression in `def:tensor-product-value`. -/
theorem outcome_weight_nonneg {G : Game} (S : Strategy G)
    (x : G.QuestionA) (y : G.QuestionB) (a : G.AnswerA) (b : G.AnswerB) :
    0 ≤ outcomeWeight S x y a b := by
  unfold outcomeWeight applyOperatorToState heteroKron
  exact
    (Matrix.isPositive_toEuclideanLin_iff.mpr
      (Matrix.nonneg_iff_posSemidef.mp
        (kronecker_nonneg ((S.A x).pos a) ((S.B y).pos b)))).re_inner_nonneg_right S.ψ

/-- The Born weights of all answer pairs at fixed questions sum to one.  This
is formalization-only support for the POVM normalization implicit in
`def:tensor-product-value`. -/
theorem outcome_weight_sum_eq_one {G : Game} (S : Strategy G)
    (x : G.QuestionA) (y : G.QuestionB) :
    ∑ a : G.AnswerA, ∑ b : G.AnswerB, outcomeWeight S x y a b = 1 := by
  have hsum :
      (∑ a : G.AnswerA, ∑ b : G.AnswerB,
        heteroKron ((S.A x).effect a) ((S.B y).effect b)) =
          (1 : Op (S.ιA × S.ιB)) := by
    ext i j
    simp only [Matrix.sum_apply, heteroKron, Matrix.kronecker,
      Matrix.kroneckerMap_apply]
    simp_rw [← Finset.mul_sum, ← Finset.sum_mul]
    rw [show (∑ a : G.AnswerA, (S.A x).effect a i.1 j.1) =
        (1 : Op S.ιA) i.1 j.1 by
      simpa only [Matrix.sum_apply] using congrFun (congrFun (S.A x).sum_eq_one i.1) j.1]
    rw [show (∑ b : G.AnswerB, (S.B y).effect b i.2 j.2) =
        (1 : Op S.ιB) i.2 j.2 by
      simpa only [Matrix.sum_apply] using congrFun (congrFun (S.B y).sum_eq_one i.2) j.2]
    exact congrFun (congrFun
      (Matrix.one_kronecker_one (m := S.ιA) (n := S.ιB) (α := ℂ)) i) j
  calc
    ∑ a : G.AnswerA, ∑ b : G.AnswerB, outcomeWeight S x y a b =
        (inner ℂ S.ψ
          (applyOperatorToState
            (∑ a : G.AnswerA, ∑ b : G.AnswerB,
              heteroKron ((S.A x).effect a) ((S.B y).effect b)) S.ψ)).re := by
          simp [outcomeWeight, applyOperatorToState]
    _ = (inner ℂ S.ψ (applyOperatorToState 1 S.ψ)).re := by rw [hsum]
    _ = 1 := by
      simp [applyOperatorToState, S.ψ_norm]

/-- Summing over Bob's answers gives Alice's marginal Born weight. -/
theorem sum_outcome_weight_right {G : Game} (S : Strategy G)
    (x : G.QuestionA) (y : G.QuestionB) (a : G.AnswerA) :
    (∑ b : G.AnswerB, outcomeWeight S x y a b) = aliceOutcomeWeight S x a := by
  have hsum :
      (∑ b : G.AnswerB, heteroKron ((S.A x).effect a) ((S.B y).effect b)) =
        heteroKron ((S.A x).effect a) 1 := by
    ext i j
    simp only [Matrix.sum_apply, heteroKron, Matrix.kronecker,
      Matrix.kroneckerMap_apply]
    rw [← Finset.mul_sum]
    rw [show (∑ b : G.AnswerB, (S.B y).effect b i.2 j.2) =
        (1 : Op S.ιB) i.2 j.2 by
      simpa only [Matrix.sum_apply] using congrFun (congrFun (S.B y).sum_eq_one i.2) j.2]
  calc
    (∑ b : G.AnswerB, outcomeWeight S x y a b) =
        (inner ℂ S.ψ
          (applyOperatorToState
            (∑ b : G.AnswerB,
              heteroKron ((S.A x).effect a) ((S.B y).effect b)) S.ψ)).re := by
          simp [outcomeWeight, applyOperatorToState]
    _ = (inner ℂ S.ψ
        (applyOperatorToState (heteroKron ((S.A x).effect a) 1) S.ψ)).re := by
      rw [hsum]
    _ = aliceOutcomeWeight S x a := rfl

/-- Summing over Alice's answers gives Bob's marginal Born weight. -/
theorem sum_outcome_weight_left {G : Game} (S : Strategy G)
    (x : G.QuestionA) (y : G.QuestionB) (b : G.AnswerB) :
    (∑ a : G.AnswerA, outcomeWeight S x y a b) = bobOutcomeWeight S y b := by
  have hsum :
      (∑ a : G.AnswerA, heteroKron ((S.A x).effect a) ((S.B y).effect b)) =
        heteroKron 1 ((S.B y).effect b) := by
    ext i j
    simp only [Matrix.sum_apply, heteroKron, Matrix.kronecker,
      Matrix.kroneckerMap_apply]
    rw [← Finset.sum_mul]
    rw [show (∑ a : G.AnswerA, (S.A x).effect a i.1 j.1) =
        (1 : Op S.ιA) i.1 j.1 by
      simpa only [Matrix.sum_apply] using congrFun (congrFun (S.A x).sum_eq_one i.1) j.1]
  calc
    (∑ a : G.AnswerA, outcomeWeight S x y a b) =
        (inner ℂ S.ψ
          (applyOperatorToState
            (∑ a : G.AnswerA,
              heteroKron ((S.A x).effect a) ((S.B y).effect b)) S.ψ)).re := by
          simp [outcomeWeight, applyOperatorToState]
    _ = (inner ℂ S.ψ
        (applyOperatorToState (heteroKron 1 ((S.B y).effect b)) S.ψ)).re := by
      rw [hsum]
    _ = bobOutcomeWeight S y b := rfl

/-- Every answer event has nonnegative Born weight. -/
theorem outcome_event_weight_nonneg {G : Game} (S : Strategy G)
    (x : G.QuestionA) (y : G.QuestionB)
    (E : G.AnswerA → G.AnswerB → Prop) [DecidableRel E] :
    0 ≤ outcomeEventWeight S x y E := by
  unfold outcomeEventWeight
  exact Finset.sum_nonneg fun a _ => Finset.sum_nonneg fun b _ => by
    split_ifs
    · exact outcome_weight_nonneg S x y a b
    · exact le_rfl

/-- An answer event depending only on Alice has its Alice marginal weight. -/
theorem outcome_event_weight_left_eq {G : Game} (S : Strategy G)
    (x : G.QuestionA) (y : G.QuestionB)
    (E : G.AnswerA → Prop) [DecidablePred E] :
    outcomeEventWeight S x y (fun a _ => E a) = aliceEventWeight S x E := by
  unfold outcomeEventWeight aliceEventWeight
  apply Finset.sum_congr rfl
  intro a _
  by_cases ha : E a
  · simp [ha, sum_outcome_weight_right S x y a]
  · simp [ha]

/-- An answer event depending only on Bob has its Bob marginal weight. -/
theorem outcome_event_weight_right_eq {G : Game} (S : Strategy G)
    (x : G.QuestionA) (y : G.QuestionB)
    (E : G.AnswerB → Prop) [DecidablePred E] :
    outcomeEventWeight S x y (fun _ b => E b) = bobEventWeight S y E := by
  unfold outcomeEventWeight bobEventWeight
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro b _
  by_cases hb : E b
  · simp [hb, sum_outcome_weight_left S x y b]
  · simp [hb]

/-- Inclusion of answer events implies the corresponding Born-weight inequality. -/
theorem outcome_event_weight_mono {G : Game} (S : Strategy G)
    (x : G.QuestionA) (y : G.QuestionB)
    (E F : G.AnswerA → G.AnswerB → Prop) [DecidableRel E] [DecidableRel F]
    (hEF : ∀ a b, E a b → F a b) :
    outcomeEventWeight S x y E ≤ outcomeEventWeight S x y F := by
  unfold outcomeEventWeight
  apply Finset.sum_le_sum
  intro a _
  apply Finset.sum_le_sum
  intro b _
  by_cases hE : E a b
  · simp [hE, hEF a b hE]
  · simp only [hE, ↓reduceIte]
    split_ifs
    · exact outcome_weight_nonneg S x y a b
    · exact le_rfl

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
