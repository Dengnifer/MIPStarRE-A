import MIPStarRE.QPBT.Games.Defs
import MIPStarRE.QPBT.Games.Consistency
import MIPStarRE.QPBT.State
import MIPStarRE.LDT.MakingMeasurementsProjective.NaimarkFull
import MIPStarRE.LDT.Preliminaries.Completion
import MIPStarRE.LDT.Test.StrategyBiProj.DirectSum

/-! # Strategy classes and symmetric games

This module defines projective, commuting, consistent, PCC, and SPCC strategy
predicates from `blueprint/src/chapter/ch12_qpbt_games.tex:89-183`, with source
definitions in `references/qpbt-paper/06_nonlocal_games_and_mipstar.tex:68-180`.
-/

namespace MIPStarRE.QPBT

universe u

open scoped BigOperators Matrix MatrixOrder ComplexOrder

open MIPStarRE.LDT MIPStarRE.Quantum

/-- Projectivity from `def:projective-strategy-general`, blueprint
`ch12_qpbt_games.tex:89-94`, paper `06_nonlocal_games_and_mipstar.tex:68-72`. -/
def Strategy.IsProjective {G : Game} (S : Strategy G) : Prop :=
  (∀ x, MIPStarRE.QPBT.Measurement.IsProjective (S.A x)) ∧
    ∀ y, MIPStarRE.QPBT.Measurement.IsProjective (S.B y)

/-- Symmetric games from `def:symmetric-game`, blueprint
`ch12_qpbt_games.tex:100-109`, paper `06_nonlocal_games_and_mipstar.tex:74-92`.
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
`ch12_qpbt_games.tex:100-109`, paper `06_nonlocal_games_and_mipstar.tex:74-92`. -/
def SymmetricGame.toGame (G : SymmetricGame) : Game where
  QuestionA := G.Question
  QuestionB := G.Question
  AnswerA := G.Answer
  AnswerB := G.Answer
  μ := G.μ
  μ_prob := G.μ_prob
  decide := G.decide

/-- Symmetric strategies from `def:symmetric-game`, blueprint
`ch12_qpbt_games.tex:100-109`, paper `06_nonlocal_games_and_mipstar.tex:74-92`.
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

attribute [instance] SymmetricStrategy.ιFintype SymmetricStrategy.ιDecidableEq

/-- Regard a symmetric strategy as a strategy using the same local space and
measurement family for both players; `def:symmetric-game`, blueprint
`ch12_qpbt_games.tex:100-109`, paper `06_nonlocal_games_and_mipstar.tex:74-92`. -/
def SymmetricStrategy.toStrategy {G : SymmetricGame} (S : SymmetricStrategy G) :
    Strategy G.toGame where
  ιA := S.ι
  ιB := S.ι
  ψ := S.ψ
  ψ_norm := S.ψ_norm
  A := S.M
  B := S.M

/-- Common-space commutation from `def:comm-strategy`, blueprint
`ch12_qpbt_games.tex:141-150`, paper `06_nonlocal_games_and_mipstar.tex:132-142`. -/
def IsCommutingOn {X Y α β ι : Type*}
    [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]
    [Fintype α] [DecidableEq α] [Fintype β]
    [DecidableEq β] [Fintype ι] [DecidableEq ι]
    (μ : Distribution (X × Y))
    (A : X → MIPStarRE.Quantum.Measurement α ι)
    (B : Y → MIPStarRE.Quantum.Measurement β ι) : Prop :=
  ∀ x y, 0 < μ.weight (x, y) → ∀ a b, Commute ((A x).effect a) ((B y).effect b)

private def transportOp {d₁ d₂ : Type u} (h : d₁ = d₂) (M : Op d₂) : Op d₁ :=
  h.symm ▸ M

/-- Transported common-space form of `def:comm-strategy`, blueprint
`ch12_qpbt_games.tex:141-150`, paper `06_nonlocal_games_and_mipstar.tex:132-142`. -/
def Strategy.IsCommuting {G : Game} (S : Strategy G) (hι : S.ιA = S.ιB) : Prop :=
  ∀ x y, 0 < G.μ.weight (x, y) → ∀ a b,
    Commute ((S.A x).effect a) (transportOp hι ((S.B y).effect b))

/-- Measurement consistency from `def:consistent-measurement`, blueprint
`ch12_qpbt_games.tex:152-161`, paper `06_nonlocal_games_and_mipstar.tex:144-160`. -/
def Measurement.IsConsistentOn {α ι : Type*}
    [Fintype α] [DecidableEq α] [Fintype ι] [DecidableEq ι]
    (M : MIPStarRE.Quantum.Measurement α ι)
    (ψ : EuclideanSpace ℂ (ι × ι)) : Prop :=
  ∀ a, (heteroKron (M.effect a) 1).mulVec ψ =
    (heteroKron 1 (M.effect a)).mulVec ψ

/-- General strategy consistency from `def:consistent-strategy`, blueprint
`ch12_qpbt_games.tex:169-174`, paper `06_nonlocal_games_and_mipstar.tex:162-174`. -/
def IsConsistentStrategyOn {X Y α β ι : Type*}
    [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]
    [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    [Fintype ι] [DecidableEq ι]
    (A : X → MIPStarRE.Quantum.Measurement α ι)
    (B : Y → MIPStarRE.Quantum.Measurement β ι)
    (ψ : EuclideanSpace ℂ (ι × ι)) : Prop :=
  (∀ x, MIPStarRE.QPBT.Measurement.IsConsistentOn (A x) ψ) ∧
    ∀ y, MIPStarRE.QPBT.Measurement.IsConsistentOn (B y) ψ

/-- Symmetric strategy consistency from `def:consistent-strategy`, blueprint
`ch12_qpbt_games.tex:169-174`, paper `06_nonlocal_games_and_mipstar.tex:162-174`. -/
def SymmetricStrategy.IsConsistent {G : SymmetricGame}
    (S : SymmetricStrategy G) : Prop :=
  ∀ x, MIPStarRE.QPBT.Measurement.IsConsistentOn (S.M x) S.ψ

/-- The PCC predicate `def:spcc`, blueprint `ch12_qpbt_games.tex:178-183`,
paper `06_nonlocal_games_and_mipstar.tex:176-180`. -/
def Strategy.IsPCC {G : Game} {ι : Type*}
    [Fintype ι] [DecidableEq ι]
    (μ : Distribution (G.QuestionA × G.QuestionB))
    (A : G.QuestionA → MIPStarRE.Quantum.Measurement G.AnswerA ι)
    (B : G.QuestionB → MIPStarRE.Quantum.Measurement G.AnswerB ι)
  (ψ : EuclideanSpace ℂ (ι × ι)) : Prop :=
  (∀ x, MIPStarRE.QPBT.Measurement.IsProjective (A x)) ∧
    (∀ y, MIPStarRE.QPBT.Measurement.IsProjective (B y)) ∧
    IsConsistentStrategyOn A B ψ ∧ IsCommutingOn μ A B

/-- The SPCC predicate `def:spcc`, blueprint `ch12_qpbt_games.tex:178-183`,
paper `06_nonlocal_games_and_mipstar.tex:176-180`. -/
def SymmetricStrategy.IsSPCC {G : SymmetricGame}
  (S : SymmetricStrategy G) : Prop :=
  (∀ x, MIPStarRE.QPBT.Measurement.IsProjective (S.M x)) ∧ S.IsConsistent ∧
    IsCommutingOn G.μ S.M S.M

noncomputable section

open MIPStarRE.LDT.MakingMeasurementsProjective
open MIPStarRE.LDT.Preliminaries

/-- The real quadratic form of an operator evaluated on a finite vector. -/
private def vectorQForm {I : Type*} [Fintype I] [DecidableEq I]
    (ψ : EuclideanSpace ℂ I) (A : Op I) : ℝ :=
  (inner ℂ ψ (Matrix.toEuclideanLin A ψ)).re

/-- Embed a bipartite state into the distinguished Naimark ancilla coordinates. -/
private def padState
    {I J α β : Type*} [Fintype I] [DecidableEq I]
    [Fintype J] [DecidableEq J] [Fintype α] [DecidableEq α]
    [Fintype β] [DecidableEq β]
    (ψ : EuclideanSpace ℂ (I × J)) :
    EuclideanSpace ℂ ((I × Option α) × (J × Option β)) :=
  (EuclideanSpace.equiv ((I × Option α) × (J × Option β)) ℂ).symm
    (fun p => if p.1.2 = none ∧ p.2.2 = none then ψ.ofLp (p.1.1, p.2.1) else 0)

/-- Padding a state by zero ancilla coordinates preserves its norm. -/
private theorem padState_norm
    {I J α β : Type*} [Fintype I] [DecidableEq I]
    [Fintype J] [DecidableEq J] [Fintype α] [DecidableEq α]
    [Fintype β] [DecidableEq β]
    (ψ : EuclideanSpace ℂ (I × J)) :
    ‖padState (α := α) (β := β) ψ‖ = ‖ψ‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq]
  simp [padState, Fintype.sum_prod_type]

/-- The padded-state quadratic form depends only on the distinguished
compression of each local operator. -/
private theorem stateQForm_padState
    {I J α β : Type*} [Fintype I] [DecidableEq I]
    [Fintype J] [DecidableEq J] [Fintype α] [DecidableEq α]
    [Fintype β] [DecidableEq β]
    (ψ : EuclideanSpace ℂ (I × J))
    (A : Op I) (B : Op J)
    (A' : Op (I × Option α)) (B' : Op (J × Option β))
    (hA : ∀ i j, A' (i, none) (j, none) = A i j)
    (hB : ∀ i j, B' (i, none) (j, none) = B i j) :
    vectorQForm (padState (α := α) (β := β) ψ) (heteroKron A' B') =
      vectorQForm ψ (heteroKron A B) := by
  unfold vectorQForm
  rw [EuclideanSpace.inner_eq_star_dotProduct, EuclideanSpace.inner_eq_star_dotProduct]
  change Complex.re (∑ p : (I × Option α) × (J × Option β),
      (∑ q : (I × Option α) × (J × Option β),
        heteroKron A' B' p q *
          (padState (α := α) (β := β) ψ).ofLp q) *
        star (padState (α := α) (β := β) ψ).ofLp p) =
    Complex.re (∑ p : I × J,
      (∑ q : I × J, heteroKron A B p q * ψ.ofLp q) * star ψ.ofLp p)
  simp [padState, heteroKron, Matrix.kronecker, Fintype.sum_prod_type, hA, hB]

/-- Choose the one-measurement Naimark dilation data for a POVM. -/
private def oneMeasData
    {α I : Type} [Fintype α] [DecidableEq α]
    [Fintype I] [DecidableEq I]
    (M : MIPStarRE.Quantum.Measurement α I) : OneMeasNaimarkData α I :=
  Classical.choose (oneMeasNaimark M.toSubmeasurement)

/-- The source submeasurement of the chosen Naimark data is the original POVM. -/
private theorem oneMeasData_source_effect
    {α I : Type} [Fintype α] [DecidableEq α]
    [Fintype I] [DecidableEq I]
    (M : MIPStarRE.Quantum.Measurement α I) :
    (oneMeasData M).source.effect = M.effect := by
  exact congrArg MIPStarRE.Quantum.Submeasurement.effect
    (Classical.choose_spec (oneMeasNaimark M.toSubmeasurement))

/-- Complete the Naimark projectors at one outcome to obtain a projective POVM. -/
private def dilatedMeasurement
    {α I : Type} [Fintype α] [DecidableEq α]
    [Fintype I] [DecidableEq I]
    (a₀ : α) (M : MIPStarRE.Quantum.Measurement α I) :
    MIPStarRE.Quantum.Measurement α (I × Option α) :=
  let P := completeAtOutcomeProj (oneMeasData M).toProjSubMeas a₀
  MIPStarRE.Quantum.Measurement.ofSumEqOne P.outcome P.outcome_pos <| by
    rw [P.sum_eq_total, P.total_eq_one]

/-- Every effect of the completed Naimark measurement is a projection. -/
private theorem dilatedMeasurement_isProjective
    {α I : Type} [Fintype α] [DecidableEq α]
    [Fintype I] [DecidableEq I]
    (a₀ : α) (M : MIPStarRE.Quantum.Measurement α I) :
    MIPStarRE.QPBT.Measurement.IsProjective (dilatedMeasurement a₀ M) := by
  intro a
  let P := completeAtOutcomeProj (oneMeasData M).toProjSubMeas a₀
  change IsProj (P.outcome a)
  exact
    { isIdempotentElem := P.proj a
      isSelfAdjoint :=
        (Matrix.nonneg_iff_posSemidef.mp (P.outcome_pos a)).isHermitian.eq }

/-- Compressing a completed Naimark effect to the distinguished ancilla
coordinate recovers the original POVM effect. -/
private theorem dilatedMeasurement_compression
    {α I : Type} [Fintype α] [DecidableEq α]
    [Fintype I] [DecidableEq I]
    (a₀ a : α) (M : MIPStarRE.Quantum.Measurement α I) (i j : I) :
    (dilatedMeasurement a₀ M).effect a (i, none) (j, none) = M.effect a i j := by
  let D := oneMeasData M
  let P := D.toProjSubMeas
  have hcompress (b : α) : P.outcome b (i, none) (j, none) = M.effect b i j := by
    change D.liftedEffect (some b) (i, none) (j, none) = M.effect b i j
    rw [D.compression_none_none]
    exact congrArg (fun X : Op I => X i j)
      (congrFun (oneMeasData_source_effect M) b)
  have htotal : P.total (i, none) (j, none) = (1 : Op I) i j := by
    rw [← P.sum_eq_total]
    simp_rw [Matrix.sum_apply, hcompress]
    simpa [Matrix.sum_apply] using congrArg (fun X : Op I => X i j) M.sum_eq_one
  simp only [dilatedMeasurement, MIPStarRE.Quantum.Measurement.ofSumEqOne]
  change ((completeAtOutcomeProj P a₀).toMeasurement).outcome a
      (i, none) (j, none) = M.effect a i j
  rw [completeAtOutcomeProj_toMeasurement]
  simp only [completeAtOutcome]
  by_cases ha : a = a₀
  · subst a
    rw [dif_pos rfl]
    rw [Matrix.add_apply, hcompress, Matrix.sub_apply, Matrix.one_apply, htotal]
    by_cases hij : i = j <;> simp [hij, Matrix.one_apply]
  · rw [dif_neg ha]
    exact hcompress a

/-- A unit vector has a nonempty coordinate type. -/
private theorem nonempty_of_unit_vector
    {I : Type*} [Fintype I] [DecidableEq I]
    (ψ : EuclideanSpace ℂ I) (hψ : ‖ψ‖ = 1) : Nonempty I := by
  classical
  by_contra hI
  haveI : IsEmpty I := not_nonempty_iff.mp hI
  have hzero : ψ = 0 := Subsingleton.elim _ _
  rw [hzero, norm_zero] at hψ
  norm_num at hψ

/-- A POVM on a nonzero finite-dimensional space has an outcome. -/
private theorem measurement_outcome_nonempty
    {α I : Type*} [Fintype α] [Fintype I] [DecidableEq I] [Nonempty I]
    (M : MIPStarRE.Quantum.Measurement α I) : Nonempty α := by
  classical
  by_contra hα
  haveI : IsEmpty α := not_nonempty_iff.mp hα
  let i : I := Classical.choice inferInstance
  have heq := congrArg (fun X : Op I => X i i) M.sum_eq_one
  simp [Matrix.sum_apply] at heq

/-- Dilate both local POVM families of a strategy and pad its state by the two
distinguished ancilla coordinates. -/
private def projectiveDilation {G : Game} (S : Strategy G)
    (a₀ : G.AnswerA) (b₀ : G.AnswerB) : Strategy G where
  ιA := S.ιA × Option G.AnswerA
  ιB := S.ιB × Option G.AnswerB
  ψ := padState S.ψ
  ψ_norm := (padState_norm S.ψ).trans S.ψ_norm
  A := fun x => dilatedMeasurement a₀ (S.A x)
  B := fun y => dilatedMeasurement b₀ (S.B y)

/-- The local measurements of the Naimark-dilated strategy are projective. -/
private theorem projectiveDilation_isProjective {G : Game} (S : Strategy G)
    (a₀ : G.AnswerA) (b₀ : G.AnswerB) :
    (projectiveDilation S a₀ b₀).IsProjective := by
  constructor
  · intro x
    exact dilatedMeasurement_isProjective a₀ (S.A x)
  · intro y
    exact dilatedMeasurement_isProjective b₀ (S.B y)

/-- Naimark dilation and state padding preserve every game correlation and
hence preserve the strategy value. -/
private theorem projectiveDilation_value {G : Game} (S : Strategy G)
    (a₀ : G.AnswerA) (b₀ : G.AnswerB) :
    (projectiveDilation S a₀ b₀).value = S.value := by
  unfold Strategy.value
  apply avgOver_congr
  intro xy
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  by_cases hw : G.decide xy.1 xy.2 a b
  · simp only [hw, if_true]
    exact stateQForm_padState (α := G.AnswerA) (β := G.AnswerB)
      S.ψ ((S.A xy.1).effect a) ((S.B xy.2).effect b)
      ((dilatedMeasurement a₀ (S.A xy.1)).effect a)
      ((dilatedMeasurement b₀ (S.B xy.2)).effect b)
      (dilatedMeasurement_compression a₀ a (S.A xy.1))
      (dilatedMeasurement_compression b₀ b (S.B xy.2))
  · simp [hw]

/-- Form the block-diagonal direct sum of two POVMs with the same outcome type. -/
private def blockMeasurement
    {α I J : Type*} [Fintype α] [Fintype I] [DecidableEq I]
    [Fintype J] [DecidableEq J]
    (A : MIPStarRE.Quantum.Measurement α I)
    (B : MIPStarRE.Quantum.Measurement α J) :
    MIPStarRE.Quantum.Measurement α (Sum I J) :=
  MIPStarRE.Quantum.Measurement.ofSumEqOne
    (fun a => MIPStarRE.LDT.ProjStrat.localDirectSumBlock (A.effect a) (B.effect a))
    (fun a => MIPStarRE.LDT.ProjStrat.localDirectSumBlock_nonneg (A.pos a) (B.pos a))
    (by
      calc
        (∑ a : α, MIPStarRE.LDT.ProjStrat.localDirectSumBlock
            (A.effect a) (B.effect a)) =
          MIPStarRE.LDT.ProjStrat.localDirectSumBlock
            (∑ a : α, A.effect a) (∑ a : α, B.effect a) := by
              simpa using MIPStarRE.LDT.ProjStrat.localDirectSumBlock_finset_sum
                Finset.univ A.effect B.effect
        _ = 1 := by
          rw [A.sum_eq_one, B.sum_eq_one,
            MIPStarRE.LDT.ProjStrat.localDirectSumBlock_one])

/-- A direct sum of projective POVMs is projective. -/
private theorem blockMeasurement_isProjective
    {α I J : Type*} [Fintype α] [Fintype I] [DecidableEq I]
    [Fintype J] [DecidableEq J]
    (A : MIPStarRE.Quantum.Measurement α I)
    (B : MIPStarRE.Quantum.Measurement α J)
    (hA : MIPStarRE.QPBT.Measurement.IsProjective A)
    (hB : MIPStarRE.QPBT.Measurement.IsProjective B) :
    MIPStarRE.QPBT.Measurement.IsProjective (blockMeasurement A B) := by
  intro a
  change IsProj (MIPStarRE.LDT.ProjStrat.localDirectSumBlock
    (A.effect a) (B.effect a))
  refine { isIdempotentElem := ?_, isSelfAdjoint := ?_ }
  · change MIPStarRE.LDT.ProjStrat.localDirectSumBlock (A.effect a) (B.effect a) *
        MIPStarRE.LDT.ProjStrat.localDirectSumBlock (A.effect a) (B.effect a) = _
    rw [MIPStarRE.LDT.ProjStrat.localDirectSumBlock_mul,
      (hA a).isIdempotentElem.eq, (hB a).isIdempotentElem.eq]
  · change (MIPStarRE.LDT.ProjStrat.localDirectSumBlock
        (A.effect a) (B.effect a))ᴴ = _
    rw [MIPStarRE.LDT.ProjStrat.localDirectSumBlock_conjTranspose,
      (hA a).isSelfAdjoint.isHermitian.eq,
      (hB a).isSelfAdjoint.isHermitian.eq]

/-- Put a bipartite vector in the two exchanged off-diagonal sectors of the
local direct sum, with equal amplitudes. -/
private def symmState
    {I J : Type*} [Fintype I] [DecidableEq I]
    [Fintype J] [DecidableEq J]
    (ψ : EuclideanSpace ℂ (I × J)) :
    EuclideanSpace ℂ (Sum I J × Sum I J) :=
  (EuclideanSpace.equiv (Sum I J × Sum I J) ℂ).symm fun p =>
    match p with
    | (Sum.inl i, Sum.inr j) => (Real.sqrt 2 / 2 : ℂ) * ψ.ofLp (i, j)
    | (Sum.inr j, Sum.inl i) => (Real.sqrt 2 / 2 : ℂ) * ψ.ofLp (i, j)
    | _ => 0

/-- The direct-sum state is fixed by exchanging its two local tensor factors. -/
private theorem symmState_swap
    {I J : Type*} [Fintype I] [DecidableEq I]
    [Fintype J] [DecidableEq J]
    (ψ : EuclideanSpace ℂ (I × J)) :
    reindexState (Equiv.prodComm (Sum I J) (Sum I J)) (symmState ψ) =
      symmState ψ := by
  apply (EuclideanSpace.equiv (Sum I J × Sum I J) ℂ).injective
  funext p
  rcases p with ⟨p, q⟩
  cases p <;> cases q <;> rfl

/-- Coordinate formula for the direct-sum symmetric state. -/
private theorem symmState_apply
    {I J : Type*} [Fintype I] [DecidableEq I]
    [Fintype J] [DecidableEq J]
    (ψ : EuclideanSpace ℂ (I × J)) (p : Sum I J × Sum I J) :
    (symmState ψ).ofLp p =
      match p with
      | (Sum.inl i, Sum.inr j) => (Real.sqrt 2 / 2 : ℂ) * ψ.ofLp (i, j)
      | (Sum.inr j, Sum.inl i) => (Real.sqrt 2 / 2 : ℂ) * ψ.ofLp (i, j)
      | _ => 0 := by
  simp [symmState]

/-- The equal-amplitude direct-sum symmetrization preserves the vector norm. -/
private theorem symmState_norm
    {I J : Type*} [Fintype I] [DecidableEq I]
    [Fintype J] [DecidableEq J]
    (ψ : EuclideanSpace ℂ (I × J)) : ‖symmState ψ‖ = ‖ψ‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq]
  simp [Fintype.sum_prod_type, Fintype.sum_sum_type, symmState_apply]
  rw [abs_of_nonneg (Real.sqrt_nonneg 2)]
  have hsqrt : (Real.sqrt 2 / 2) ^ 2 = (1 / 2 : ℝ) := by
    rw [div_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
    norm_num
  simp_rw [mul_pow, hsqrt]
  rw [Finset.sum_comm]
  simp_rw [← Finset.mul_sum]
  ring_nf
  exact Finset.sum_comm

/-- Scaling both entries of a finite sesquilinear sum contributes the scalar
`c * star c`. -/
private theorem sesquilinear_sum_smul
    {K L : Type*} [Fintype K] [Fintype L]
    (c : ℂ) (f : K → L → ℂ) (v : L → ℂ) (w : K → ℂ) :
    (∑ p : K, (∑ q : L, f p q * (c * v q)) * star (c * w p)) =
      c * star c * ∑ p : K, (∑ q : L, f p q * v q) * star (w p) := by
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro p _
  rw [star_mul]
  have hinner : (∑ q : L, f p q * (c * v q)) =
      c * ∑ q : L, f p q * v q := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro q _
    ring
  rw [hinner]
  ring

/-- A block tensor quadratic form on the symmetric state is the average of the
two crossed quadratic forms on the original state. -/
private theorem vectorQForm_symmState_block
    {I J : Type*} [Fintype I] [DecidableEq I]
    [Fintype J] [DecidableEq J]
    (ψ : EuclideanSpace ℂ (I × J))
    (A C : Op I) (B D : Op J) :
    vectorQForm (symmState ψ)
        (heteroKron
          (MIPStarRE.LDT.ProjStrat.localDirectSumBlock A B)
          (MIPStarRE.LDT.ProjStrat.localDirectSumBlock C D)) =
      (1 / 2 : ℝ) *
        (vectorQForm ψ (heteroKron A D) + vectorQForm ψ (heteroKron C B)) := by
  unfold vectorQForm
  rw [EuclideanSpace.inner_eq_star_dotProduct, EuclideanSpace.inner_eq_star_dotProduct,
    EuclideanSpace.inner_eq_star_dotProduct]
  change Complex.re (∑ p : Sum I J × Sum I J,
      (∑ q : Sum I J × Sum I J,
        heteroKron
          (MIPStarRE.LDT.ProjStrat.localDirectSumBlock A B)
          (MIPStarRE.LDT.ProjStrat.localDirectSumBlock C D) p q *
            (symmState ψ).ofLp q) * star (symmState ψ).ofLp p) =
    (1 / 2 : ℝ) *
      (Complex.re (∑ p : I × J,
          (∑ q : I × J, heteroKron A D p q * ψ.ofLp q) * star ψ.ofLp p) +
        Complex.re (∑ p : I × J,
          (∑ q : I × J, heteroKron C B p q * ψ.ofLp q) * star ψ.ofLp p))
  simp only [Fintype.sum_prod_type, Fintype.sum_sum_type]
  simp only [Pi.star_apply, symmState_apply]
  simp only [heteroKron, Matrix.kronecker, Matrix.kroneckerMap_apply]
  simp only [
    MIPStarRE.LDT.ProjStrat.localDirectSumBlock_inl_inl,
    MIPStarRE.LDT.ProjStrat.localDirectSumBlock_inl_inr,
    MIPStarRE.LDT.ProjStrat.localDirectSumBlock_inr_inl,
    MIPStarRE.LDT.ProjStrat.localDirectSumBlock_inr_inr,
    zero_mul, mul_zero, Finset.sum_const_zero, zero_add, add_zero]
  let c : ℂ := Real.sqrt 2 / 2
  have hfirst :
      (∑ i : I, ∑ j : J,
        (∑ k : I, ∑ l : J, A i k * D j l * (c * ψ.ofLp (k, l))) *
          star (c * ψ.ofLp (i, j))) =
        c * star c *
          ∑ i : I, ∑ j : J,
            (∑ k : I, ∑ l : J, A i k * D j l * ψ.ofLp (k, l)) *
              star (ψ.ofLp (i, j)) := by
    simpa only [Fintype.sum_prod_type, heteroKron, Matrix.kronecker,
      Matrix.kroneckerMap_apply] using
      (sesquilinear_sum_smul c (heteroKron A D) ψ.ofLp ψ.ofLp)
  have hsecond :
      (∑ j : J, ∑ i : I,
        (∑ l : J, ∑ k : I, B j l * C i k * (c * ψ.ofLp (k, l))) *
          star (c * ψ.ofLp (i, j))) =
        c * star c *
          ∑ j : J, ∑ i : I,
            (∑ l : J, ∑ k : I, B j l * C i k * ψ.ofLp (k, l)) *
              star (ψ.ofLp (i, j)) := by
    simpa only [Fintype.sum_prod_type, heteroKron, Matrix.kronecker,
      Matrix.kroneckerMap_apply] using
      (sesquilinear_sum_smul c (heteroKron B C)
        (fun p : J × I => ψ.ofLp (p.2, p.1))
        (fun p : J × I => ψ.ofLp (p.2, p.1)))
  have hswap :
      (∑ j : J, ∑ i : I,
        (∑ l : J, ∑ k : I, B j l * C i k * ψ.ofLp (k, l)) *
          star (ψ.ofLp (i, j))) =
        ∑ i : I, ∑ j : J,
          (∑ k : I, ∑ l : J, C i k * B j l * ψ.ofLp (k, l)) *
            star (ψ.ofLp (i, j)) := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    congr 1
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro k _
    apply Finset.sum_congr rfl
    intro l _
    ring
  change Complex.re (_ + _) = _
  rw [hfirst, hsecond, hswap]
  have hstar : star c = c := by
    simp [c]
  rw [hstar]
  have hsqrt : (Real.sqrt 2 / 2 : ℂ) * (Real.sqrt 2 / 2 : ℂ) = (1 / 2 : ℂ) := by
    norm_cast
    rw [← pow_two, div_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
    norm_num
  change Complex.re ((c * c) * _ + (c * c) * _) = _
  rw [show c * c = (1 / 2 : ℂ) by simpa [c] using hsqrt]
  norm_num [Complex.mul_re]
  ring

/-- A symmetric distribution gives the same average after exchanging the two
coordinates, independently of redundant zero-weight support entries. -/
private theorem avgOver_prod_swap_of_weight_symm
    {X : Type*} [Fintype X] [DecidableEq X]
    (μ : Distribution (X × X))
    (hμ : ∀ x y, μ.weight (x, y) = μ.weight (y, x))
    (f : X × X → ℝ) :
    avgOver μ (fun xy => f (xy.2, xy.1)) = avgOver μ f := by
  unfold avgOver
  calc
    (∑ xy ∈ μ.support, μ.weight xy * f (xy.2, xy.1)) =
        ∑ xy : X × X, μ.weight xy * f (xy.2, xy.1) := by
          symm
          exact Distribution.sum_univ_eq_sum_support μ _ fun xy hxy => by
            rw [μ.outsideSupport xy hxy, zero_mul]
    _ = ∑ x : X, ∑ y : X, μ.weight (x, y) * f (y, x) := by
          rw [Fintype.sum_prod_type]
    _ = ∑ y : X, ∑ x : X, μ.weight (x, y) * f (y, x) := Finset.sum_comm
    _ = ∑ y : X, ∑ x : X, μ.weight (y, x) * f (y, x) := by
          apply Finset.sum_congr rfl
          intro y _
          apply Finset.sum_congr rfl
          intro x _
          rw [hμ]
    _ = ∑ xy : X × X, μ.weight xy * f xy := by
          rw [Fintype.sum_prod_type]
    _ = ∑ xy ∈ μ.support, μ.weight xy * f xy :=
      Distribution.sum_univ_eq_sum_support μ _ fun xy hxy => by
        rw [μ.outsideSupport xy hxy, zero_mul]

/-- Symmetrize a strategy by putting its two local spaces in a common direct
sum and occupying the two exchanged tensor sectors with equal amplitude. -/
private def symmetrizedStrategy {G : SymmetricGame}
    (S : Strategy G.toGame) : SymmetricStrategy G where
  ι := Sum S.ιA S.ιB
  ψ := symmState S.ψ
  ψ_norm := (symmState_norm S.ψ).trans S.ψ_norm
  ψ_swap := symmState_swap S.ψ
  M := fun x => blockMeasurement (S.A x) (S.B x)

/-- Projectivity is preserved by direct-sum symmetrization. -/
private theorem symmetrizedStrategy_isProjective {G : SymmetricGame}
    (S : Strategy G.toGame) (hS : S.IsProjective) :
    (symmetrizedStrategy S).toStrategy.IsProjective := by
  constructor <;> intro x <;>
    exact blockMeasurement_isProjective (S.A x) (S.B x) (hS.1 x) (hS.2 x)

/-- The winning contribution of one question pair for a fixed strategy. -/
private def strategyPayoff {G : Game} (S : Strategy G)
    (xy : G.QuestionA × G.QuestionB) : ℝ :=
  ∑ a : G.AnswerA, ∑ b : G.AnswerB,
    if G.decide xy.1 xy.2 a b then
      vectorQForm S.ψ (heteroKron ((S.A xy.1).effect a) ((S.B xy.2).effect b))
    else 0

/-- Strategy value is the question-distribution average of its pairwise payoff. -/
private theorem strategy_value_eq_avgOver_payoff {G : Game} (S : Strategy G) :
    S.value = avgOver G.μ (strategyPayoff S) := by
  rfl

/-- At a question pair, the symmetrized payoff is the average of the original
payoff in the two question orders. -/
private theorem symmetrizedStrategy_payoff {G : SymmetricGame}
    (S : Strategy G.toGame) (x y : G.Question) :
    strategyPayoff (symmetrizedStrategy S).toStrategy (x, y) =
      (1 / 2 : ℝ) *
        (strategyPayoff S (x, y) + strategyPayoff S (y, x)) := by
  unfold strategyPayoff
  simp only [SymmetricStrategy.toStrategy, symmetrizedStrategy]
  calc
    (∑ a : G.Answer, ∑ b : G.Answer,
      if G.decide x y a b then
        vectorQForm (symmState S.ψ)
          (heteroKron
            ((blockMeasurement (S.A x) (S.B x)).effect a)
            ((blockMeasurement (S.A y) (S.B y)).effect b))
      else 0) =
        ∑ a : G.Answer, ∑ b : G.Answer,
          if G.decide x y a b then
            (1 / 2 : ℝ) *
              (vectorQForm S.ψ
                  (heteroKron ((S.A x).effect a) ((S.B y).effect b)) +
                vectorQForm S.ψ
                  (heteroKron ((S.A y).effect b) ((S.B x).effect a)))
          else 0 := by
            apply Finset.sum_congr rfl
            intro a _
            apply Finset.sum_congr rfl
            intro b _
            by_cases hab : G.decide x y a b
            · simp only [hab, if_true]
              simpa only [blockMeasurement,
                MIPStarRE.Quantum.Measurement.ofSumEqOne] using
                vectorQForm_symmState_block S.ψ
                  ((S.A x).effect a) ((S.A y).effect b)
                  ((S.B x).effect a) ((S.B y).effect b)
            · simp [hab]
    _ = (1 / 2 : ℝ) *
        ((∑ a : G.Answer, ∑ b : G.Answer,
          if G.decide x y a b then
            vectorQForm S.ψ
              (heteroKron ((S.A x).effect a) ((S.B y).effect b))
          else 0) +
        (∑ a : G.Answer, ∑ b : G.Answer,
          if G.decide x y a b then
            vectorQForm S.ψ
              (heteroKron ((S.A y).effect b) ((S.B x).effect a))
          else 0)) := by
            simp_rw [mul_add, Finset.mul_sum]
            rw [← Finset.sum_add_distrib]
            apply Finset.sum_congr rfl
            intro a _
            rw [← Finset.sum_add_distrib]
            apply Finset.sum_congr rfl
            intro b _
            by_cases hab : G.decide x y a b <;> simp [hab]
    _ = (1 / 2 : ℝ) *
        ((∑ a : G.Answer, ∑ b : G.Answer,
          if G.decide x y a b then
            vectorQForm S.ψ
              (heteroKron ((S.A x).effect a) ((S.B y).effect b))
          else 0) +
        (∑ b : G.Answer, ∑ a : G.Answer,
          if G.decide y x b a then
            vectorQForm S.ψ
              (heteroKron ((S.A y).effect b) ((S.B x).effect a))
          else 0)) := by
            congr 2
            rw [Finset.sum_comm]
            apply Finset.sum_congr rfl
            intro b _
            apply Finset.sum_congr rfl
            intro a _
            rw [← G.decide_symm]

/-- Symmetrization preserves the value of a strategy in a symmetric game. -/
private theorem symmetrizedStrategy_value {G : SymmetricGame}
    (S : Strategy G.toGame) :
    (symmetrizedStrategy S).toStrategy.value = S.value := by
  rw [strategy_value_eq_avgOver_payoff, strategy_value_eq_avgOver_payoff]
  calc
    avgOver G.μ (strategyPayoff (symmetrizedStrategy S).toStrategy) =
        avgOver G.μ (fun xy => (1 / 2 : ℝ) *
          (strategyPayoff S xy + strategyPayoff S (xy.2, xy.1))) := by
            apply avgOver_congr
            intro xy
            exact symmetrizedStrategy_payoff S xy.1 xy.2
    _ = (1 / 2 : ℝ) *
        (avgOver G.μ (strategyPayoff S) +
          avgOver G.μ (fun xy => strategyPayoff S (xy.2, xy.1))) := by
            rw [avgOver_const_mul, avgOver_add]
    _ = avgOver G.μ (strategyPayoff S) := by
          change (1 / 2 : ℝ) *
            (avgOver G.μ (fun xy : G.Question × G.Question => strategyPayoff S xy) +
              avgOver G.μ
                (fun xy : G.Question × G.Question => strategyPayoff S (xy.2, xy.1))) =
            avgOver G.μ (fun xy : G.Question × G.Question => strategyPayoff S xy)
          have hswapavg := avgOver_prod_swap_of_weight_symm G.μ G.μ_symm
            (fun xy : G.Question × G.Question => strategyPayoff S xy)
          calc
            (1 / 2 : ℝ) *
                (avgOver G.μ
                    (fun xy : G.Question × G.Question => strategyPayoff S xy) +
                  avgOver G.μ (fun xy : G.Question × G.Question =>
                    strategyPayoff S (xy.2, xy.1))) =
              (1 / 2 : ℝ) *
                (avgOver G.μ
                    (fun xy : G.Question × G.Question => strategyPayoff S xy) +
                  avgOver G.μ
                    (fun xy : G.Question × G.Question => strategyPayoff S xy)) :=
                congrArg (fun z : ℝ => (1 / 2 : ℝ) *
                  (avgOver G.μ (fun xy : G.Question × G.Question =>
                    strategyPayoff S xy) + z)) hswapavg
            _ = avgOver G.μ
                (fun xy : G.Question × G.Question => strategyPayoff S xy) := by
                  ring

/-- A probability distribution has a nonempty ambient sample type. -/
private theorem nonempty_of_probability {α : Type*}
    (μ : Distribution α) (hμ : μ.IsProbability) : Nonempty α := by
  classical
  by_contra hα
  haveI : IsEmpty α := not_nonempty_iff.mp hα
  have hs : μ.support = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro a
    exact isEmptyElim a
  have hsum := hμ.weight_sum_eq_one
  rw [hs] at hsum
  norm_num at hsum

/-- Source symmetrization statement `lem:symmetric-strat`, blueprint
`ch12_qpbt_games.tex:116-135`, paper `06_nonlocal_games_and_mipstar.tex:94-130`.
The attainment defect is `rem:symmetric-strat-limit` and is tracked in
`docs/paper-gaps/qpbt_symmetrization-attainment.tex`.

**Unfaithful:** The `sorry` is the source's unattested attainment step:
`Game.value` is a supremum over unbounded finite dimensions, whereas the cited
argument, `06_nonlocal_games_and_mipstar.tex:101-132`, constructs a strategy
only above every strict lower bound. What is proved is the value-preserving
given-strategy form `exists_symmetric_projective_strategy_of_strategy`, hence
the approximate form; what remains is the passage from that family to a single
strategy of value at least `1 - ε`. Documented in
`docs/paper-gaps/qpbt_symmetrization-attainment.tex` and issue `#98`.
Elimination: prove an independent finite-dimensional attainment theorem for
`Game.value` and discharge the `sorry` with it. The source statement is kept
as printed; it may be weakened only by a future documented statement
correction, not by this proof. -/
theorem exists_symmetric_projective_strategy (G : SymmetricGame) (ε : ℝ)
    (hε : 0 ≤ ε) (h : G.toGame.value = 1 - ε) :
    ∃ S : SymmetricStrategy G, S.toStrategy.IsProjective ∧
      1 - ε ≤ S.toStrategy.value := by
  sorry

/-- Value-preserving formalization-only form of `lem:symmetric-strat` starting
from a specified near-optimal strategy; blueprint
`ch12_qpbt_games.tex:140-154`, paper `06_nonlocal_games_and_mipstar.tex:94-130`.
The source attainment distinction is tracked in
`docs/paper-gaps/qpbt_symmetrization-attainment.tex`. -/
theorem exists_symmetric_projective_strategy_of_strategy (G : SymmetricGame)
    (ε : ℝ) (S₀ : Strategy G.toGame) (h : 1 - ε ≤ S₀.value) :
    ∃ S : SymmetricStrategy G, S.toStrategy.IsProjective ∧
      S.toStrategy.value = S₀.value ∧ 1 - ε ≤ S.toStrategy.value := by
  have hι := nonempty_of_unit_vector S₀.ψ S₀.ψ_norm
  letI : Nonempty S₀.ιA := hι.map Prod.fst
  letI : Nonempty S₀.ιB := hι.map Prod.snd
  have hq := nonempty_of_probability G.μ G.μ_prob
  have ha := measurement_outcome_nonempty (S₀.A hq.some.1)
  let a₀ : G.Answer := Classical.choice ha
  let T : Strategy G.toGame := projectiveDilation S₀ a₀ a₀
  let S : SymmetricStrategy G := symmetrizedStrategy T
  have hT_proj : T.IsProjective := projectiveDilation_isProjective S₀ a₀ a₀
  have hvalue : S.toStrategy.value = S₀.value := by
    calc
      S.toStrategy.value = T.value := symmetrizedStrategy_value T
      _ = S₀.value := projectiveDilation_value S₀ a₀ a₀
  exact ⟨S, symmetrizedStrategy_isProjective T hT_proj,
    hvalue, h.trans_eq hvalue.symm⟩

end

end MIPStarRE.QPBT
