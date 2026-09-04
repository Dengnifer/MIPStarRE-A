import MIPStarRE.QPBT.Test.MagicSquareTheorems.Rigidity.GroundSlice

/-!
# Transfer of rigidity bounds along the projective dilation

The self-testing argument behind `thm:ms-rigidity` is carried out for the
projective dilation `msDilatedStrategy S` of an arbitrary Magic Square strategy
`S`.  Its conclusions are state-dependent bounds for the *dilated* projectors,
conjugated by local isometries `φ_A`, `φ_B` out of the enlarged local spaces.
The witness for the original strategy is obtained by composing these isometries
with the ground embeddings, and the operators appearing in its bounds are the
conjugates of the *original* effects, that is, of the compressions `Π P Π` of
the dilated projectors `P` to the ground slice (`Π` the ground projection).

Naimark dilation preserves Born probabilities but not state-dependent `≈_δ`
estimates in general (`references/ldt-paper/orthonormalization.tex:82-101`,
blueprint `ch04_projective.tex:255-270`), so `Π P Π` and `P` need not act
alike on the dilated state.  Their difference on the dilated state `ψ'` is the
*leakage* `(1 - Π) P ψ'` of `P` out of the ground slice, and the point of this
file is that in the Magic Square game this leakage is controlled by the
cell-consistency defect of the value-to-parity layer: the dilated effect
`P ⊗ 1` almost agrees with the partner effect `1 ⊗ Q` on the other side, and
`(1 - Π) ⊗ 1` annihilates `1 ⊗ Q ψ'`.  Combined with the closeness of
`(φ_A ⊗ φ_B) ψ'` to the ideal state and the fact that all operators involved
are contractions, this pulls every bound of `thm:ms-rigidity` back from the
dilated strategy to the original one with explicit constants.

## Main statements

* `ms_effect_transfer_A`, `ms_effect_transfer_B`: the bit-measurement distances
  of the original strategy are bounded by three times those of the dilated
  strategy plus `216 ε + 24 η²`, where `η` bounds the state closeness.
* `ms_anticommutator_transfer_A`, `ms_anticommutator_transfer_B`: the
  anticommutator defects transfer with the bound `3 · (dilated) + 15552 ε +
  48 η²`.
* `ms_state_transfer`: the state closeness is unchanged.

## References

`thm:ms-rigidity`, blueprint `blueprint/src/chapter/ch13_qpbt_test.tex:224-253`,
paper `references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:612-652`.
-/

open scoped BigOperators Matrix MatrixOrder ComplexOrder

namespace MIPStarRE.QPBT.MagicSquareRigidity

open MIPStarRE.LDT hiding Measurement
open MIPStarRE.Quantum MIPStarRE.QPBT.DistanceCalculus

noncomputable section

/-! ## Cell consistency of the postprocessed effects -/

/-- The Born overlap of Alice's totalized variable bit with Bob's totalized
constraint bit, summed over the bit, is the complement of the reverse
cell-mismatch mass. -/
theorem sum_stateQForm_reverse_eq (S : Strategy msGame) (i : Fin 6) (k : Fin 3) :
    ∑ b : ZMod 2, stateQForm S.ψ (heteroKron
        (((S.A (.var (msConstraintVars i k))).postprocess msBitOrZero).effect b)
        (((S.B (.constraint i)).postprocess (constraintBitOrZero k)).effect b)) =
      1 - reverseCellMismatchMass S i k := by
  classical
  have hterm : ∀ b : ZMod 2, stateQForm S.ψ (heteroKron
        (((S.A (.var (msConstraintVars i k))).postprocess msBitOrZero).effect b)
        (((S.B (.constraint i)).postprocess (constraintBitOrZero k)).effect b)) =
      ∑ a : msGame.AnswerA, ∑ c : msGame.AnswerB,
        if msBitOrZero a = b then
          (if constraintBitOrZero k c = b then
            outcomeWeight S (.var (msConstraintVars i k)) (.constraint i) a c else 0)
        else 0 := by
    intro b
    rw [MIPStarRE.Quantum.Measurement.postprocess_effect,
      MIPStarRE.Quantum.Measurement.postprocess_effect,
      heteroKron_finset_sum_left, stateQForm_finset_sum, Finset.sum_filter]
    refine Finset.sum_congr rfl fun a _ => ?_
    split_ifs
    · rw [heteroKron_finset_sum_right, stateQForm_finset_sum, Finset.sum_filter]
      rfl
    · simp
  have htotal := outcome_weight_sum_eq_one S (.var (msConstraintVars i k)) (.constraint i)
  unfold reverseCellMismatchMass outcomeEventWeight
  simp_rw [hterm]
  rw [Finset.sum_comm, eq_sub_iff_add_eq, ← htotal, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.sum_comm, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [Finset.sum_ite_eq]
  simp only [Finset.mem_univ, if_true]
  by_cases h : msBitOrZero a = constraintBitOrZero k c
  · simp [h]
  · simp [h, Ne.symm h]

/-- The Born overlap of Alice's totalized constraint bit with Bob's totalized
variable bit, summed over the bit, is the complement of the forward
cell-mismatch mass. -/
theorem sum_stateQForm_forward_eq (S : Strategy msGame) (i : Fin 6) (k : Fin 3) :
    ∑ b : ZMod 2, stateQForm S.ψ (heteroKron
        (((S.A (.constraint i)).postprocess (constraintBitOrZero k)).effect b)
        (((S.B (.var (msConstraintVars i k))).postprocess msBitOrZero).effect b)) =
      1 - forwardCellMismatchMass S i k := by
  classical
  have hterm : ∀ b : ZMod 2, stateQForm S.ψ (heteroKron
        (((S.A (.constraint i)).postprocess (constraintBitOrZero k)).effect b)
        (((S.B (.var (msConstraintVars i k))).postprocess msBitOrZero).effect b)) =
      ∑ a : msGame.AnswerA, ∑ c : msGame.AnswerB,
        if constraintBitOrZero k a = b then
          (if msBitOrZero c = b then
            outcomeWeight S (.constraint i) (.var (msConstraintVars i k)) a c else 0)
        else 0 := by
    intro b
    rw [MIPStarRE.Quantum.Measurement.postprocess_effect,
      MIPStarRE.Quantum.Measurement.postprocess_effect,
      heteroKron_finset_sum_left, stateQForm_finset_sum, Finset.sum_filter]
    refine Finset.sum_congr rfl fun a _ => ?_
    split_ifs
    · rw [heteroKron_finset_sum_right, stateQForm_finset_sum, Finset.sum_filter]
      rfl
    · simp
  have htotal := outcome_weight_sum_eq_one S (.constraint i) (.var (msConstraintVars i k))
  unfold forwardCellMismatchMass outcomeEventWeight
  simp_rw [hterm]
  rw [Finset.sum_comm, eq_sub_iff_add_eq, ← htotal, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.sum_comm, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [Finset.sum_ite_eq]
  simp only [Finset.mem_univ, if_true]
  by_cases h : constraintBitOrZero k a = msBitOrZero c
  · simp [h]
  · simp [h, Ne.symm h]

/-! ## The dilated effects on the enlarged ground spaces -/

/-- Alice's dilated postprocessed effect, typed on the enlarged local space
`ℂ^{ιA × Option MsAnswer}`.  Formalization-only abbreviation. -/
abbrev dilatedEffectA (S : Strategy msGame) (x : MsType) (f : MsAnswer → ZMod 2)
    (b : ZMod 2) : Op (S.ιA × Option MsAnswer) :=
  (((msDilatedStrategy S).A x).postprocess f).effect b

/-- Bob's dilated postprocessed effect, typed on the enlarged local space
`ℂ^{ιB × Option MsAnswer}`.  Formalization-only abbreviation. -/
abbrev dilatedEffectB (S : Strategy msGame) (y : MsType) (f : MsAnswer → ZMod 2)
    (b : ZMod 2) : Op (S.ιB × Option MsAnswer) :=
  (((msDilatedStrategy S).B y).postprocess f).effect b

/-- Alice's dilated variable bit approximately intertwines with Bob's dilated
constraint bit: the summed squared defect is at most twice the reverse
cell-mismatch mass of the original strategy.  This is the first item of
`fact:agreement` (blueprint `ch12_qpbt_games.tex:245-254`) applied to the
dilated strategy, whose Born masses are those of the original one. -/
theorem sum_norm_sq_intertwining_le_reverse (S : Strategy msGame) (i : Fin 6) (k : Fin 3) :
    ∑ b : ZMod 2, ‖applyOperatorToState
        (heteroKron (dilatedEffectA S (.var (msConstraintVars i k)) msBitOrZero b) 1 -
          heteroKron 1 (dilatedEffectB S (.constraint i) (constraintBitOrZero k) b))
        (naimarkDilatedState MsAnswer S.ψ)‖ ^ 2 ≤ 2 * reverseCellMismatchMass S i k := by
  set S' := msDilatedStrategy S
  set PA := (S'.A (.var (msConstraintVars i k))).postprocess msBitOrZero
  set QB := (S'.B (.constraint i)).postprocess (constraintBitOrZero k)
  have h1 := point_distance_le_two_defect (leftPlacedMeasurement (ιB := S'.ιB) PA)
    (rightPlacedMeasurement (ιA := S'.ιA) QB) S'.ψ
  rw [point_defect_eq] at h1
  have hnorm : ‖S'.ψ‖ = 1 := S'.ψ_norm
  have hover : ∑ a : ZMod 2, stateQForm S'.ψ
      ((leftPlacedMeasurement (ιB := S'.ιB) PA).effect a *
        (rightPlacedMeasurement (ιA := S'.ιA) QB).effect a) =
      1 - reverseCellMismatchMass S i k := by
    rw [← ms_dilated_strategy_reverse_cell_mismatch_mass S i k,
      ← sum_stateQForm_reverse_eq S' i k]
    refine Finset.sum_congr rfl fun a _ => ?_
    change stateQForm S'.ψ (heteroKron (PA.effect a) 1 * heteroKron 1 (QB.effect a)) =
      stateQForm S'.ψ (heteroKron (PA.effect a) (QB.effect a))
    rw [heteroKron_mul, Matrix.mul_one, Matrix.one_mul]
  rw [hnorm, hover] at h1
  have h2 : ∑ b : ZMod 2, ‖applyOperatorToState
      (heteroKron (dilatedEffectA S (.var (msConstraintVars i k)) msBitOrZero b) 1 -
        heteroKron 1 (dilatedEffectB S (.constraint i) (constraintBitOrZero k) b))
      (naimarkDilatedState MsAnswer S.ψ)‖ ^ 2 ≤
      2 * (1 ^ 2 - (1 - reverseCellMismatchMass S i k)) := h1
  linarith

/-- Alice's dilated constraint bit approximately intertwines with Bob's dilated
variable bit: the summed squared defect is at most twice the forward
cell-mismatch mass of the original strategy. -/
theorem sum_norm_sq_intertwining_le_forward (S : Strategy msGame) (i : Fin 6) (k : Fin 3) :
    ∑ b : ZMod 2, ‖applyOperatorToState
        (heteroKron (dilatedEffectA S (.constraint i) (constraintBitOrZero k) b) 1 -
          heteroKron 1 (dilatedEffectB S (.var (msConstraintVars i k)) msBitOrZero b))
        (naimarkDilatedState MsAnswer S.ψ)‖ ^ 2 ≤ 2 * forwardCellMismatchMass S i k := by
  set S' := msDilatedStrategy S
  set PA := (S'.A (.constraint i)).postprocess (constraintBitOrZero k)
  set QB := (S'.B (.var (msConstraintVars i k))).postprocess msBitOrZero
  have h1 := point_distance_le_two_defect (leftPlacedMeasurement (ιB := S'.ιB) PA)
    (rightPlacedMeasurement (ιA := S'.ιA) QB) S'.ψ
  rw [point_defect_eq] at h1
  have hnorm : ‖S'.ψ‖ = 1 := S'.ψ_norm
  have hover : ∑ a : ZMod 2, stateQForm S'.ψ
      ((leftPlacedMeasurement (ιB := S'.ιB) PA).effect a *
        (rightPlacedMeasurement (ιA := S'.ιA) QB).effect a) =
      1 - forwardCellMismatchMass S i k := by
    rw [← ms_dilated_strategy_forward_cell_mismatch_mass S i k,
      ← sum_stateQForm_forward_eq S' i k]
    refine Finset.sum_congr rfl fun a _ => ?_
    change stateQForm S'.ψ (heteroKron (PA.effect a) 1 * heteroKron 1 (QB.effect a)) =
      stateQForm S'.ψ (heteroKron (PA.effect a) (QB.effect a))
    rw [heteroKron_mul, Matrix.mul_one, Matrix.one_mul]
  rw [hnorm, hover] at h1
  have h2 : ∑ b : ZMod 2, ‖applyOperatorToState
      (heteroKron (dilatedEffectA S (.constraint i) (constraintBitOrZero k) b) 1 -
        heteroKron 1 (dilatedEffectB S (.var (msConstraintVars i k)) msBitOrZero b))
      (naimarkDilatedState MsAnswer S.ψ)‖ ^ 2 ≤
      2 * (1 ^ 2 - (1 - forwardCellMismatchMass S i k)) := h1
  linarith

/-! ## Compressions of the dilated postprocessed effects -/

/-- Compressing one of Alice's dilated postprocessed effects returns her original
postprocessed effect. -/
theorem naimarkCompression_dilatedEffectA (S : Strategy msGame) (x : MsType)
    (f : MsAnswer → ZMod 2) (b : ZMod 2) :
    naimarkCompression (dilatedEffectA S x f b) = ((S.A x).postprocess f).effect b := by
  have h := (naimarkCompression_finset_sum (Finset.univ.filter fun a : MsAnswer => f a = b)
    fun a => ((msDilatedStrategy S).A x).effect a).trans
    (Finset.sum_congr rfl fun a _ => naimarkCompression_msDilatedStrategy_A_effect S x a)
  exact h

/-- Compressing one of Bob's dilated postprocessed effects returns his original
postprocessed effect. -/
theorem naimarkCompression_dilatedEffectB (S : Strategy msGame) (y : MsType)
    (f : MsAnswer → ZMod 2) (b : ZMod 2) :
    naimarkCompression (dilatedEffectB S y f b) = ((S.B y).postprocess f).effect b := by
  have h := (naimarkCompression_finset_sum (Finset.univ.filter fun a : MsAnswer => f a = b)
    fun a => ((msDilatedStrategy S).B y).effect a).trans
    (Finset.sum_congr rfl fun a _ => naimarkCompression_msDilatedStrategy_B_effect S y a)
  exact h

/-- The inflation of Alice's original postprocessed effect is the ground
compression `Π P Π` of her dilated one. -/
theorem naimarkInflation_postprocess_A (S : Strategy msGame) (x : MsType)
    (f : MsAnswer → ZMod 2) (b : ZMod 2) :
    naimarkInflation (α := MsAnswer) (((S.A x).postprocess f).effect b) =
      groundProjection S.ιA MsAnswer * dilatedEffectA S x f b *
        groundProjection S.ιA MsAnswer := by
  rw [← naimarkCompression_dilatedEffectA, naimarkInflation_naimarkCompression]

/-- The inflation of Bob's original postprocessed effect is the ground
compression `Π Q Π` of his dilated one. -/
theorem naimarkInflation_postprocess_B (S : Strategy msGame) (y : MsType)
    (f : MsAnswer → ZMod 2) (b : ZMod 2) :
    naimarkInflation (α := MsAnswer) (((S.B y).postprocess f).effect b) =
      groundProjection S.ιB MsAnswer * dilatedEffectB S y f b *
        groundProjection S.ιB MsAnswer := by
  rw [← naimarkCompression_dilatedEffectB, naimarkInflation_naimarkCompression]

/-- Alice's dilated effects are contractions. -/
theorem conjTranspose_mul_le_one_dilatedEffectA (S : Strategy msGame) (x : MsType)
    (f : MsAnswer → ZMod 2) (b : ZMod 2) :
    (dilatedEffectA S x f b)ᴴ * dilatedEffectA S x f b ≤ 1 :=
  conjTranspose_mul_le_one_of_effect (((msDilatedStrategy S).A x).postprocess f) b

/-- Bob's dilated effects are contractions. -/
theorem conjTranspose_mul_le_one_dilatedEffectB (S : Strategy msGame) (y : MsType)
    (f : MsAnswer → ZMod 2) (b : ZMod 2) :
    (dilatedEffectB S y f b)ᴴ * dilatedEffectB S y f b ≤ 1 :=
  conjTranspose_mul_le_one_of_effect (((msDilatedStrategy S).B y).postprocess f) b

/-- On the dilated state, the difference between a left-placed dilated operator
and its ground compression is its leakage out of the ground slice. -/
theorem applyOperatorToState_leftTensor_sub_compression (α : Type) [Fintype α]
    [DecidableEq α] {ιA ιB : Type} [Fintype ιA] [DecidableEq ιA] [Fintype ιB]
    [DecidableEq ιB] (ψ : EuclideanSpace ℂ (ιA × ιB)) (P : Op (ιA × Option α)) :
    applyOperatorToState
        (heteroKron (P - groundProjection ιA α * P * groundProjection ιA α) 1)
        (naimarkDilatedState α ψ) =
      applyOperatorToState (heteroKron ((1 - groundProjection ιA α) * P) 1)
        (naimarkDilatedState α ψ) := by
  have hsplit : P - groundProjection ιA α * P * groundProjection ιA α =
      (1 - groundProjection ιA α) * P +
        (groundProjection ιA α * P) * (1 - groundProjection ιA α) := by
    noncomm_ring
  rw [hsplit, heteroKron_add_left, applyOperatorToState_add_op]
  have hzero : applyOperatorToState
      (heteroKron ((groundProjection ιA α * P) * (1 - groundProjection ιA α)) 1)
      (naimarkDilatedState α ψ) = 0 := by
    rw [show heteroKron ((groundProjection ιA α * P) * (1 - groundProjection ιA α))
        (1 : Op (ιB × Option α)) =
        heteroKron (groundProjection ιA α * P) 1 * heteroKron (1 - groundProjection ιA α) 1 by
      rw [heteroKron_mul, Matrix.mul_one]]
    rw [applyOperatorToState_mul, applyOperatorToState_leftTensor_one_sub_groundProjection,
      applyOperatorToState_zero]
  rw [hzero, add_zero]

/-- On the dilated state, the difference between a right-placed dilated operator
and its ground compression is its leakage out of the ground slice. -/
theorem applyOperatorToState_rightTensor_sub_compression (α : Type) [Fintype α]
    [DecidableEq α] {ιA ιB : Type} [Fintype ιA] [DecidableEq ιA] [Fintype ιB]
    [DecidableEq ιB] (ψ : EuclideanSpace ℂ (ιA × ιB)) (Q : Op (ιB × Option α)) :
    applyOperatorToState
        (heteroKron 1 (Q - groundProjection ιB α * Q * groundProjection ιB α))
        (naimarkDilatedState α ψ) =
      applyOperatorToState (heteroKron 1 ((1 - groundProjection ιB α) * Q))
        (naimarkDilatedState α ψ) := by
  have hsplit : Q - groundProjection ιB α * Q * groundProjection ιB α =
      (1 - groundProjection ιB α) * Q +
        (groundProjection ιB α * Q) * (1 - groundProjection ιB α) := by
    noncomm_ring
  rw [hsplit, heteroKron_add_right, applyOperatorToState_add_op]
  have hzero : applyOperatorToState
      (heteroKron 1 ((groundProjection ιB α * Q) * (1 - groundProjection ιB α)))
      (naimarkDilatedState α ψ) = 0 := by
    rw [show heteroKron (1 : Op (ιA × Option α))
        ((groundProjection ιB α * Q) * (1 - groundProjection ιB α)) =
        heteroKron 1 (groundProjection ιB α * Q) * heteroKron 1 (1 - groundProjection ιB α) by
      rw [heteroKron_mul, Matrix.mul_one]]
    rw [applyOperatorToState_mul, applyOperatorToState_rightTensor_one_sub_groundProjection,
      applyOperatorToState_zero]
  rw [hzero, add_zero]

/-! ## Transfer of the effect estimates -/

/-- Per-outcome transfer estimate on Alice's side.  For any target operator `T`,
the distance of the conjugated original effect from `T` on the target state
`ξ` is at most the distance of the conjugated dilated effect from `T`, plus the
intertwining defect of the dilated effect against Bob's partner effect `Q` on
the dilated state, plus twice the distance from `ξ` to the transported dilated
state.  Blueprint `ch13_qpbt_test.tex:224-253`. -/
theorem norm_effect_transfer_term_le_A {κA κB : Type} [Fintype κA] [DecidableEq κA]
    [Fintype κB] [DecidableEq κB] (S : Strategy msGame)
    (φA : EuclideanSpace ℂ (S.ιA × Option MsAnswer) →ₗᵢ[ℂ] EuclideanSpace ℂ κA)
    (φB : EuclideanSpace ℂ (S.ιB × Option MsAnswer) →ₗᵢ[ℂ] EuclideanSpace ℂ κB)
    (ξ : EuclideanSpace ℂ (κA × κB)) (T : Op (κA × κB)) (x y : MsType)
    (f g : MsAnswer → ZMod 2) (b : ZMod 2) :
    ‖applyOperatorToState (heteroKron (conjIsometry (φA.comp (naimarkEmbedding S.ιA MsAnswer))
        (((S.A x).postprocess f).effect b)) 1 - T) ξ‖ ≤
      ‖applyOperatorToState (heteroKron (conjIsometry φA (dilatedEffectA S x f b)) 1 - T) ξ‖ +
      ‖applyOperatorToState
        (heteroKron (dilatedEffectA S x f b) 1 - heteroKron 1 (dilatedEffectB S y g b))
        (naimarkDilatedState MsAnswer S.ψ)‖ +
      2 * ‖isometryTensor φA φB (naimarkDilatedState MsAnswer S.ψ) - ξ‖ := by
  rw [conjIsometry_comp_naimarkEmbedding, naimarkInflation_postprocess_A]
  have hP := conjTranspose_mul_le_one_dilatedEffectA S x f b
  have hG : (groundProjection S.ιA MsAnswer)ᴴ * groundProjection S.ιA MsAnswer ≤ 1 :=
    conjTranspose_mul_le_one_of_isProj (isProj_groundProjection S.ιA MsAnswer)
  have hAd : (heteroKron (conjIsometry φA (dilatedEffectA S x f b)) (1 : Op κB))ᴴ *
      heteroKron (conjIsometry φA (dilatedEffectA S x f b)) 1 ≤ 1 :=
    conjTranspose_mul_le_one_leftTensor (conjTranspose_mul_le_one_conjIsometry φA hP)
  have hAo : (heteroKron (conjIsometry φA (groundProjection S.ιA MsAnswer *
      dilatedEffectA S x f b * groundProjection S.ιA MsAnswer)) (1 : Op κB))ᴴ *
      heteroKron (conjIsometry φA (groundProjection S.ιA MsAnswer *
        dilatedEffectA S x f b * groundProjection S.ιA MsAnswer)) 1 ≤ 1 :=
    conjTranspose_mul_le_one_leftTensor (conjTranspose_mul_le_one_conjIsometry φA
      (conjTranspose_mul_le_one_mul (conjTranspose_mul_le_one_mul hG hP) hG))
  set Ao : Op (κA × κB) := heteroKron (conjIsometry φA (groundProjection S.ιA MsAnswer *
    dilatedEffectA S x f b * groundProjection S.ιA MsAnswer)) 1 with hAo_def
  set Ad : Op (κA × κB) := heteroKron (conjIsometry φA (dilatedEffectA S x f b)) 1 with hAd_def
  set ψ'' := isometryTensor φA φB (naimarkDilatedState MsAnswer S.ψ) with hψ''
  have h1 : applyOperatorToState (Ao - T) ξ =
      applyOperatorToState (Ad - T) ξ - applyOperatorToState (Ad - Ao) ξ := by
    simp [applyOperatorToState]
  have h2 : applyOperatorToState (Ad - Ao) ξ =
      applyOperatorToState (Ad - Ao) ψ'' - applyOperatorToState (Ad - Ao) (ψ'' - ξ) := by
    rw [applyOperatorToState_sub, sub_sub_cancel]
  have h3 : ‖applyOperatorToState (Ad - Ao) ψ''‖ ≤
      ‖applyOperatorToState
        (heteroKron (dilatedEffectA S x f b) 1 - heteroKron 1 (dilatedEffectB S y g b))
        (naimarkDilatedState MsAnswer S.ψ)‖ := by
    have hdiff : Ad - Ao = heteroKron (conjIsometry φA (dilatedEffectA S x f b -
        groundProjection S.ιA MsAnswer * dilatedEffectA S x f b *
          groundProjection S.ιA MsAnswer)) 1 := by
      rw [hAd_def, hAo_def, conjIsometry_sub, heteroKron_sub_left]
    rw [hdiff, hψ'', applyOperatorToState_leftTensor_conjIsometry, norm_isometryTensor,
      applyOperatorToState_leftTensor_sub_compression]
    exact norm_leftTensor_one_sub_groundProjection_mul_le MsAnswer S.ψ _ _
  have h4 : ‖applyOperatorToState (Ad - Ao) (ψ'' - ξ)‖ ≤ 2 * ‖ψ'' - ξ‖ :=
    norm_applyOperatorToState_sub_le hAd hAo _
  calc ‖applyOperatorToState (Ao - T) ξ‖ =
        ‖applyOperatorToState (Ad - T) ξ - applyOperatorToState (Ad - Ao) ξ‖ := by rw [h1]
    _ ≤ ‖applyOperatorToState (Ad - T) ξ‖ + ‖applyOperatorToState (Ad - Ao) ξ‖ :=
        norm_sub_le _ _
    _ ≤ _ := by
        rw [h2]
        linarith [norm_sub_le (applyOperatorToState (Ad - Ao) ψ'')
          (applyOperatorToState (Ad - Ao) (ψ'' - ξ)), h3, h4]

/-- Per-outcome transfer estimate on Bob's side. -/
theorem norm_effect_transfer_term_le_B {κA κB : Type} [Fintype κA] [DecidableEq κA]
    [Fintype κB] [DecidableEq κB] (S : Strategy msGame)
    (φA : EuclideanSpace ℂ (S.ιA × Option MsAnswer) →ₗᵢ[ℂ] EuclideanSpace ℂ κA)
    (φB : EuclideanSpace ℂ (S.ιB × Option MsAnswer) →ₗᵢ[ℂ] EuclideanSpace ℂ κB)
    (ξ : EuclideanSpace ℂ (κA × κB)) (T : Op (κA × κB)) (x y : MsType)
    (f g : MsAnswer → ZMod 2) (b : ZMod 2) :
    ‖applyOperatorToState (heteroKron 1 (conjIsometry (φB.comp (naimarkEmbedding S.ιB MsAnswer))
        (((S.B y).postprocess g).effect b)) - T) ξ‖ ≤
      ‖applyOperatorToState (heteroKron 1 (conjIsometry φB (dilatedEffectB S y g b)) - T) ξ‖ +
      ‖applyOperatorToState
        (heteroKron (dilatedEffectA S x f b) 1 - heteroKron 1 (dilatedEffectB S y g b))
        (naimarkDilatedState MsAnswer S.ψ)‖ +
      2 * ‖isometryTensor φA φB (naimarkDilatedState MsAnswer S.ψ) - ξ‖ := by
  rw [conjIsometry_comp_naimarkEmbedding, naimarkInflation_postprocess_B]
  have hQ := conjTranspose_mul_le_one_dilatedEffectB S y g b
  have hG : (groundProjection S.ιB MsAnswer)ᴴ * groundProjection S.ιB MsAnswer ≤ 1 :=
    conjTranspose_mul_le_one_of_isProj (isProj_groundProjection S.ιB MsAnswer)
  have hBd : (heteroKron (1 : Op κA) (conjIsometry φB (dilatedEffectB S y g b)))ᴴ *
      heteroKron 1 (conjIsometry φB (dilatedEffectB S y g b)) ≤ 1 :=
    conjTranspose_mul_le_one_rightTensor (conjTranspose_mul_le_one_conjIsometry φB hQ)
  have hBo : (heteroKron (1 : Op κA) (conjIsometry φB (groundProjection S.ιB MsAnswer *
      dilatedEffectB S y g b * groundProjection S.ιB MsAnswer)))ᴴ *
      heteroKron 1 (conjIsometry φB (groundProjection S.ιB MsAnswer *
        dilatedEffectB S y g b * groundProjection S.ιB MsAnswer)) ≤ 1 :=
    conjTranspose_mul_le_one_rightTensor (conjTranspose_mul_le_one_conjIsometry φB
      (conjTranspose_mul_le_one_mul (conjTranspose_mul_le_one_mul hG hQ) hG))
  set Bo : Op (κA × κB) := heteroKron 1 (conjIsometry φB (groundProjection S.ιB MsAnswer *
    dilatedEffectB S y g b * groundProjection S.ιB MsAnswer)) with hBo_def
  set Bd : Op (κA × κB) := heteroKron 1 (conjIsometry φB (dilatedEffectB S y g b)) with hBd_def
  set ψ'' := isometryTensor φA φB (naimarkDilatedState MsAnswer S.ψ) with hψ''
  have h1 : applyOperatorToState (Bo - T) ξ =
      applyOperatorToState (Bd - T) ξ - applyOperatorToState (Bd - Bo) ξ := by
    simp [applyOperatorToState]
  have h2 : applyOperatorToState (Bd - Bo) ξ =
      applyOperatorToState (Bd - Bo) ψ'' - applyOperatorToState (Bd - Bo) (ψ'' - ξ) := by
    rw [applyOperatorToState_sub, sub_sub_cancel]
  have h3 : ‖applyOperatorToState (Bd - Bo) ψ''‖ ≤
      ‖applyOperatorToState
        (heteroKron (dilatedEffectA S x f b) 1 - heteroKron 1 (dilatedEffectB S y g b))
        (naimarkDilatedState MsAnswer S.ψ)‖ := by
    have hdiff : Bd - Bo = heteroKron 1 (conjIsometry φB (dilatedEffectB S y g b -
        groundProjection S.ιB MsAnswer * dilatedEffectB S y g b *
          groundProjection S.ιB MsAnswer)) := by
      rw [hBd_def, hBo_def, conjIsometry_sub, heteroKron_sub_right]
    rw [hdiff, hψ'', applyOperatorToState_rightTensor_conjIsometry, norm_isometryTensor,
      applyOperatorToState_rightTensor_sub_compression]
    exact norm_rightTensor_one_sub_groundProjection_mul_le MsAnswer S.ψ _ _
  have h4 : ‖applyOperatorToState (Bd - Bo) (ψ'' - ξ)‖ ≤ 2 * ‖ψ'' - ξ‖ :=
    norm_applyOperatorToState_sub_le hBd hBo _
  calc ‖applyOperatorToState (Bo - T) ξ‖ =
        ‖applyOperatorToState (Bd - T) ξ - applyOperatorToState (Bd - Bo) ξ‖ := by rw [h1]
    _ ≤ ‖applyOperatorToState (Bd - T) ξ‖ + ‖applyOperatorToState (Bd - Bo) ξ‖ :=
        norm_sub_le _ _
    _ ≤ _ := by
        rw [h2]
        linarith [norm_sub_le (applyOperatorToState (Bd - Bo) ψ'')
          (applyOperatorToState (Bd - Bo) (ψ'' - ξ)), h3, h4]

/-- Squaring a three-term estimate. -/
theorem sq_le_three_mul_of_le {w x y z : ℝ} (hw : 0 ≤ w) (h : w ≤ x + y + z) :
    w ^ 2 ≤ 3 * x ^ 2 + 3 * y ^ 2 + 3 * z ^ 2 := by
  have h1 : w ^ 2 ≤ (x + y + z) ^ 2 := pow_le_pow_left₀ hw h 2
  nlinarith [sq_nonneg (x - y), sq_nonneg (y - z), sq_nonneg (x - z)]

/-- Summing the per-outcome estimates over the two outcomes. -/
theorem sum_sq_le_of_le (d ℓ o : ZMod 2 → ℝ) (η ε m : ℝ)
    (ho : ∀ b, 0 ≤ o b) (h : ∀ b, o b ≤ d b + ℓ b + 2 * η)
    (hL : ∑ b, ℓ b ^ 2 ≤ 2 * m) (hm : m ≤ 36 * ε) :
    ∑ b, o b ^ 2 ≤ 3 * ∑ b, d b ^ 2 + 216 * ε + 24 * η ^ 2 := by
  have hterm : ∀ b, o b ^ 2 ≤ 3 * d b ^ 2 + 3 * ℓ b ^ 2 + 3 * (2 * η) ^ 2 :=
    fun b => sq_le_three_mul_of_le (ho b) (h b)
  calc ∑ b, o b ^ 2 ≤ ∑ b, (3 * d b ^ 2 + 3 * ℓ b ^ 2 + 3 * (2 * η) ^ 2) :=
        Finset.sum_le_sum fun b _ => hterm b
    _ = 3 * ∑ b, d b ^ 2 + 3 * ∑ b, ℓ b ^ 2 + 24 * η ^ 2 := by
        rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum,
          ← Finset.mul_sum, Finset.sum_const, Finset.card_univ, ZMod.card, nsmul_eq_mul]
        push_cast
        ring
    _ ≤ 3 * ∑ b, d b ^ 2 + 216 * ε + 24 * η ^ 2 := by nlinarith [hL, hm]

/-- Transfer of Alice's bit-measurement estimate of `thm:ms-rigidity` from the
dilated strategy to the original one.  For every target family `I` and target
state `ξ`, the distance of Alice's conjugated original variable bits from `I`
is at most three times the distance of the conjugated dilated bits, plus
`216 ε` from the cell-consistency masses of a strategy of value `1 - ε`, plus
`24 η²` where `η` bounds the distance of the transported dilated state from
`ξ`.  The isometry of the original strategy is the composite of the dilation
embedding and `φ_A`, exactly as in the witness of `exists_ms_rigidity`; the
left-hand side is `msOperatorDistanceA S w j W` for that witness, and the
distance on the right is `msOperatorDistanceA (msDilatedStrategy S) w' j W`.
Blueprint `ch13_qpbt_test.tex:224-253`, paper
`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:612-652`. -/
theorem ms_effect_transfer_A {κA κB : Type} [Fintype κA] [DecidableEq κA]
    [Fintype κB] [DecidableEq κB] (S : Strategy msGame)
    (φA : EuclideanSpace ℂ (S.ιA × Option MsAnswer) →ₗᵢ[ℂ] EuclideanSpace ℂ κA)
    (φB : EuclideanSpace ℂ (S.ιB × Option MsAnswer) →ₗᵢ[ℂ] EuclideanSpace ℂ κB)
    (ξ : EuclideanSpace ℂ (κA × κB)) (I : ZMod 2 → Op (κA × κB)) (ε η : ℝ)
    (hwin : 1 - ε ≤ S.value) (j : Fin 9)
    (hξ : ‖isometryTensor φA φB (msDilatedStrategy S).ψ - ξ‖ ≤ η) :
    opFamilyDistSq (uniformDistribution Unit)
        (fun _ b => heteroKron (conjIsometry (φA.comp (naimarkEmbedding S.ιA MsAnswer))
          (((S.A (.var j)).postprocess msBitOrZero).effect b)) 1)
        (fun _ b => I b) ξ ≤
      3 * opFamilyDistSq (uniformDistribution Unit)
        (fun _ b => heteroKron (conjIsometry φA
          ((((msDilatedStrategy S).A (.var j)).postprocess msBitOrZero).effect b)) 1)
        (fun _ b => I b) ξ + 216 * ε + 24 * η ^ 2 := by
  obtain ⟨i, k, rfl⟩ := every_variable_is_incident j
  rw [opFamilyDistSq_uniform_unit, opFamilyDistSq_uniform_unit]
  have hL := sum_norm_sq_intertwining_le_reverse S i k
  have hmis := reverse_cell_mismatch_mass_le S ε hwin i k
  have hξ' : ‖isometryTensor φA φB (naimarkDilatedState MsAnswer S.ψ) - ξ‖ ≤ η := hξ
  have h := sum_sq_le_of_le
    (fun b => ‖applyOperatorToState (heteroKron (conjIsometry φA
      (dilatedEffectA S (.var (msConstraintVars i k)) msBitOrZero b)) 1 - I b) ξ‖)
    (fun b => ‖applyOperatorToState
      (heteroKron (dilatedEffectA S (.var (msConstraintVars i k)) msBitOrZero b) 1 -
        heteroKron 1 (dilatedEffectB S (.constraint i) (constraintBitOrZero k) b))
      (naimarkDilatedState MsAnswer S.ψ)‖)
    (fun b => ‖applyOperatorToState (heteroKron
      (conjIsometry (φA.comp (naimarkEmbedding S.ιA MsAnswer))
        (((S.A (.var (msConstraintVars i k))).postprocess msBitOrZero).effect b)) 1 - I b) ξ‖)
    η ε (reverseCellMismatchMass S i k) (fun b => norm_nonneg _)
    (fun b => by
      have hb := norm_effect_transfer_term_le_A S φA φB ξ (I b) (.var (msConstraintVars i k))
        (.constraint i) msBitOrZero (constraintBitOrZero k) b
      linarith [hb, hξ'])
    hL hmis
  linarith [h]

/-- Transfer of Bob's bit-measurement estimate of `thm:ms-rigidity` from the
dilated strategy to the original one; see `ms_effect_transfer_A`. -/
theorem ms_effect_transfer_B {κA κB : Type} [Fintype κA] [DecidableEq κA]
    [Fintype κB] [DecidableEq κB] (S : Strategy msGame)
    (φA : EuclideanSpace ℂ (S.ιA × Option MsAnswer) →ₗᵢ[ℂ] EuclideanSpace ℂ κA)
    (φB : EuclideanSpace ℂ (S.ιB × Option MsAnswer) →ₗᵢ[ℂ] EuclideanSpace ℂ κB)
    (ξ : EuclideanSpace ℂ (κA × κB)) (I : ZMod 2 → Op (κA × κB)) (ε η : ℝ)
    (hwin : 1 - ε ≤ S.value) (j : Fin 9)
    (hξ : ‖isometryTensor φA φB (msDilatedStrategy S).ψ - ξ‖ ≤ η) :
    opFamilyDistSq (uniformDistribution Unit)
        (fun _ b => heteroKron 1 (conjIsometry (φB.comp (naimarkEmbedding S.ιB MsAnswer))
          (((S.B (.var j)).postprocess msBitOrZero).effect b)))
        (fun _ b => I b) ξ ≤
      3 * opFamilyDistSq (uniformDistribution Unit)
        (fun _ b => heteroKron 1 (conjIsometry φB
          ((((msDilatedStrategy S).B (.var j)).postprocess msBitOrZero).effect b)))
        (fun _ b => I b) ξ + 216 * ε + 24 * η ^ 2 := by
  obtain ⟨i, k, rfl⟩ := every_variable_is_incident j
  rw [opFamilyDistSq_uniform_unit, opFamilyDistSq_uniform_unit]
  have hL := sum_norm_sq_intertwining_le_forward S i k
  have hmis := forward_cell_mismatch_mass_le S ε hwin i k
  have hξ' : ‖isometryTensor φA φB (naimarkDilatedState MsAnswer S.ψ) - ξ‖ ≤ η := hξ
  have h := sum_sq_le_of_le
    (fun b => ‖applyOperatorToState (heteroKron 1 (conjIsometry φB
      (dilatedEffectB S (.var (msConstraintVars i k)) msBitOrZero b)) - I b) ξ‖)
    (fun b => ‖applyOperatorToState
      (heteroKron (dilatedEffectA S (.constraint i) (constraintBitOrZero k) b) 1 -
        heteroKron 1 (dilatedEffectB S (.var (msConstraintVars i k)) msBitOrZero b))
      (naimarkDilatedState MsAnswer S.ψ)‖)
    (fun b => ‖applyOperatorToState (heteroKron 1
      (conjIsometry (φB.comp (naimarkEmbedding S.ιB MsAnswer))
        (((S.B (.var (msConstraintVars i k))).postprocess msBitOrZero).effect b)) - I b) ξ‖)
    η ε (forwardCellMismatchMass S i k) (fun b => norm_nonneg _)
    (fun b => by
      have hb := norm_effect_transfer_term_le_B S φA φB ξ (I b) (.constraint i)
        (.var (msConstraintVars i k)) (constraintBitOrZero k) msBitOrZero b
      linarith [hb, hξ'])
    hL hmis
  linarith [h]

/-- The state estimate of `thm:ms-rigidity` transfers verbatim: the composite
isometries carry the original state exactly where `φ_A ⊗ φ_B` carries the
dilated state. -/
theorem ms_state_transfer {κA κB : Type} [Fintype κA] [DecidableEq κA]
    [Fintype κB] [DecidableEq κB] (S : Strategy msGame)
    (φA : EuclideanSpace ℂ (S.ιA × Option MsAnswer) →ₗᵢ[ℂ] EuclideanSpace ℂ κA)
    (φB : EuclideanSpace ℂ (S.ιB × Option MsAnswer) →ₗᵢ[ℂ] EuclideanSpace ℂ κB)
    (ξ : EuclideanSpace ℂ (κA × κB)) :
    ‖isometryTensor (φA.comp (naimarkEmbedding S.ιA MsAnswer))
        (φB.comp (naimarkEmbedding S.ιB MsAnswer)) S.ψ - ξ‖ =
      ‖isometryTensor φA φB (msDilatedStrategy S).ψ - ξ‖ := by
  rw [isometryTensor_comp_naimarkEmbedding]
  rfl

end

end MIPStarRE.QPBT.MagicSquareRigidity
