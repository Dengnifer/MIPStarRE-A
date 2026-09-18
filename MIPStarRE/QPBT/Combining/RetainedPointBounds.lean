import MIPStarRE.QPBT.Combining.PolynomialFiberBounds

/-!
# Retained point mismatch from ordered estimates

The incorrect point projection is the outer factor of the ordered product.
The scalar collision identity then bounds its average image norm without an
outcome-count factor. All vectors remain unnormalized.

## References

Paper `references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1360-1404`,
`eq:qld-s-good-and-bad` through `eq:qld-sgg-mhat-sandwich`;
blueprint `lem:qld-4-7`.
-/

open scoped BigOperators Matrix MatrixOrder ComplexOrder

namespace MIPStarRE.QPBT.PolynomialImageBounds

open MIPStarRE.LDT hiding Measurement
open MIPStarRE.Quantum DistanceCalculus

noncomputable section

variable {F ι : Type*} [Field F] [Fintype F] [DecidableEq F]
  [Fintype ι] [DecidableEq ι]

omit [Field F] in
private theorem wrong_mul_effect (X : Quantum.Measurement F ι)
    (hX : Measurement.IsProjective X) (r b : F) :
    (1 - X.effect r) * X.effect b = if b = r then 0 else X.effect b := by
  by_cases h : b = r
  · simp [h, sub_mul, (hX r).isIdempotentElem.eq]
  · rw [sub_mul, one_mul, projective_effect_mul_effect_eq_zero X hX (Ne.symm h)]
    simp [h]

private theorem wrong_ordered_gram (X Z : Quantum.Measurement F ι)
    (hX : Measurement.IsProjective X) (r α β a : F) (hβ : β ≠ 0) :
    let T := (1 - X.effect r) * orderedIndicator X Z α β a
    Tᴴ * T = ∑ bc : F × F,
      if α * bc.1 + β * bc.2 = a ∧ bc.1 ≠ r then
        Z.effect bc.2 * X.effect bc.1 * Z.effect bc.2 else 0 := by
  classical
  have hexpand : (1 - X.effect r) * orderedIndicator X Z α β a =
      ∑ bc : F × F, if α * bc.1 + β * bc.2 = a ∧ bc.1 ≠ r then
        X.effect bc.1 * Z.effect bc.2 else 0 := by
    rw [orderedIndicator, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro bc _
    by_cases h : α * bc.1 + β * bc.2 = a
    · simp only [h, if_true, true_and, ← mul_assoc, wrong_mul_effect X hX]
      split_ifs <;> simp_all
    · simp [h]
  dsimp only
  rw [hexpand, Matrix.conjTranspose_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun bc _ => ?_
  rw [Finset.mul_sum, Finset.sum_eq_single bc]
  · by_cases h : α * bc.1 + β * bc.2 = a ∧ bc.1 ≠ r
    · simp only [if_pos h, Matrix.conjTranspose_mul, measurement_effect_hermitian]
      rw [mul_assoc (Z.effect bc.2), ← mul_assoc (X.effect bc.1),
        (hX bc.1).isIdempotentElem.eq, ← mul_assoc]
    · simp [h]
  · intro bc' _ hne
    by_cases h : α * bc.1 + β * bc.2 = a ∧ bc.1 ≠ r
    · by_cases h' : α * bc'.1 + β * bc'.2 = a ∧ bc'.1 ≠ r
      · have hb : bc.1 ≠ bc'.1 := by
          intro hb
          have hc : bc.2 = bc'.2 := mul_left_cancel₀ hβ (by
            apply add_left_cancel (a := α * bc.1)
            simpa only [hb] using h.1.trans h'.1.symm)
          exact hne (Prod.ext hb hc).symm
        simp only [if_pos h, if_pos h', Matrix.conjTranspose_mul,
          measurement_effect_hermitian]
        calc
          _ = Z.effect bc.2 * (X.effect bc.1 * X.effect bc'.1) * Z.effect bc'.2 := by
            simp only [mul_assoc]
          _ = 0 := by rw [projective_effect_mul_effect_eq_zero X hX hb]; simp
      · simp [h']
    · simp [h]
  · simp

/-- The wrong outer projection of a scalar-linear ordered product has
average squared norm at most `2/q` times the actual vector mass. One `1/q`
comes from scalar collisions and one from the zero second coefficient.
This is the retained-outcome calculation supporting `eq:qld-sgg-mhat-sandwich`.
-/
theorem avg_wrong_ordered_norm_sq_le (X Z : Quantum.Measurement F ι)
    (hX : Measurement.IsProjective X) (hZ : Measurement.IsProjective Z)
    (r t : F) (ψ : EuclideanSpace ℂ ι) :
    avgOver (uniformDistribution (Fin 2 → F)) (fun v =>
      ‖applyOperatorToState ((1 - X.effect r) *
        orderedIndicator X Z (v 0) (v 1) (v 0 * r + v 1 * t)) ψ‖ ^ 2) ≤
      2 * (Fintype.card F : ℝ)⁻¹ * ‖ψ‖ ^ 2 := by
  classical
  let w (bc : F × F) := stateQForm ψ
    (Z.effect bc.2 * X.effect bc.1 * Z.effect bc.2)
  have hw (bc : F × F) : 0 ≤ w bc :=
    stateQForm_nonneg ψ ((pastedMeasurement_isMeasurement X Z hZ).1 bc)
  have hsum : ∑ bc, w bc = ‖ψ‖ ^ 2 := by
    rw [← stateQForm_one ψ, ← (pastedMeasurement_isMeasurement X Z hZ).2,
      stateQForm_finset_sum]
    rfl
  have hpoint (v : Fin 2 → F) :
      ‖applyOperatorToState ((1 - X.effect r) *
        orderedIndicator X Z (v 0) (v 1) (v 0 * r + v 1 * t)) ψ‖ ^ 2 ≤
      (if v 1 = 0 then ‖ψ‖ ^ 2 else 0) + ∑ bc : F × F,
        (if v 0 * bc.1 + v 1 * bc.2 = v 0 * r + v 1 * t ∧ bc.1 ≠ r
          then 1 else 0) * w bc := by
    by_cases hv : v 1 = 0
    · rw [if_pos hv]
      apply le_trans (b := ‖ψ‖ ^ 2)
      · apply pow_le_pow_left₀ (norm_nonneg _)
        rw [applyOperatorToState_mul]
        exact (MagicSquareRigidity.norm_applyOperatorToState_le
          (MagicSquareRigidity.conjTranspose_mul_le_one_of_isProj (hX r).one_sub) _).trans
          (MagicSquareRigidity.norm_applyOperatorToState_le
            (orderedIndicator_gram_le_one X Z hX hZ _ _ _) ψ)
      · exact le_add_of_nonneg_right (Finset.sum_nonneg fun bc _ =>
          mul_nonneg (by split_ifs <;> norm_num) (hw bc))
    · rw [if_neg hv, zero_add, MagicSquareRigidity.norm_applyOperatorToState_sq]
      change stateQForm ψ _ ≤ _
      rw [wrong_ordered_gram X Z hX r _ _ _ hv, stateQForm_finset_sum]
      apply le_of_eq
      apply Finset.sum_congr rfl
      intro bc _
      split_ifs <;> simp [w, stateQForm, applyOperatorToState]
  have hexc : avgOver (uniformDistribution (Fin 2 → F))
      (fun v => if v 1 = 0 then ‖ψ‖ ^ 2 else 0) =
        (Fintype.card F : ℝ)⁻¹ * ‖ψ‖ ^ 2 := by
    change avgOver (uniformDistribution (Fin 2 → F))
      (fun v => if ((finTwoArrowEquiv F) v).2 = 0 then ‖ψ‖ ^ 2 else 0) = _
    rw [avgOver_uniform_equiv (finTwoArrowEquiv F)]
    simp only [Equiv.apply_symm_apply]
    rw [avgOver_uniform_snd (fun β : F => if β = 0 then ‖ψ‖ ^ 2 else 0)]
    simp [avgOver_uniform_eq_inv_card_mul_sum]
  have hcollision (bc : F × F) :
      avgOver (uniformDistribution (Fin 2 → F)) (fun v =>
        if v 0 * bc.1 + v 1 * bc.2 = v 0 * r + v 1 * t ∧ bc.1 ≠ r
          then (1 : ℝ) else 0) ≤ (Fintype.card F : ℝ)⁻¹ := by
    by_cases hb : bc.1 = r
    · simp [hb, avgOver_uniform_const]
    · rw [avgOver_uniform_equiv (finTwoArrowEquiv F)]
      have h := affine_collision_average bc (r, t)
      have hne : bc ≠ (r, t) := fun h => hb (congrArg Prod.fst h)
      simpa [finTwoArrowEquiv, hb, hne] using h.le
  have h := avgOver_mono (uniformDistribution (Fin 2 → F)) _ _ hpoint
  simp only [avgOver_add, avgOver_sum, avgOver_mul_const, hexc] at h
  refine h.trans ?_
  have hc := Finset.sum_le_sum (s := Finset.univ) fun bc _ =>
    mul_le_mul_of_nonneg_right (hcollision bc) (hw bc)
  rw [← Finset.mul_sum, hsum] at hc
  linarith

/-- Point mismatch on a retained polynomial is at most twice its ordered
residual plus `4/q` times its unnormalized mass. Reverse the point order to
obtain the other Pauli marginal. This supports `eq:qld-sgg-mhat-sandwich`.
-/
theorem point_mismatch_le_ordered_error (X Z : Quantum.Measurement F ι)
    (hX : Measurement.IsProjective X) (hZ : Measurement.IsProjective Z)
    (r t : F) (ψ : EuclideanSpace ℂ ι) :
    ‖applyOperatorToState (1 - X.effect r) ψ‖ ^ 2 ≤
      2 * avgOver (uniformDistribution (Fin 2 → F)) (fun v =>
        ‖ψ - applyOperatorToState
          (orderedIndicator X Z (v 0) (v 1) (v 0 * r + v 1 * t)) ψ‖ ^ 2) +
      4 * (Fintype.card F : ℝ)⁻¹ * ‖ψ‖ ^ 2 := by
  have hpoint (v : Fin 2 → F) :
      ‖applyOperatorToState (1 - X.effect r) ψ‖ ^ 2 ≤
        2 * ‖ψ - applyOperatorToState
          (orderedIndicator X Z (v 0) (v 1) (v 0 * r + v 1 * t)) ψ‖ ^ 2 +
        2 * ‖applyOperatorToState ((1 - X.effect r) *
          orderedIndicator X Z (v 0) (v 1) (v 0 * r + v 1 * t)) ψ‖ ^ 2 := by
    let T := orderedIndicator X Z (v 0) (v 1) (v 0 * r + v 1 * t)
    have h := sum_mass_le_residual_add_image (Finset.univ : Finset Unit)
      (fun _ => applyOperatorToState (1 - X.effect r) ψ)
      (fun _ => applyOperatorToState ((1 - X.effect r) * T) ψ)
    simp only [Finset.univ_unique, Finset.sum_singleton] at h
    have hcontract :
        ‖applyOperatorToState (1 - X.effect r) ψ -
          applyOperatorToState ((1 - X.effect r) * T) ψ‖ ≤
        ‖ψ - applyOperatorToState T ψ‖ := by
      rw [applyOperatorToState_mul]
      have heq : applyOperatorToState (1 - X.effect r) ψ -
          applyOperatorToState (1 - X.effect r) (applyOperatorToState T ψ) =
          applyOperatorToState (1 - X.effect r) (ψ - applyOperatorToState T ψ) := by
        simp only [applyOperatorToState, map_sub]
      rw [heq]
      exact MagicSquareRigidity.norm_applyOperatorToState_le
        (MagicSquareRigidity.conjTranspose_mul_le_one_of_isProj (hX r).one_sub) _
    exact h.trans (add_le_add
      (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hcontract 2)
        (by norm_num)) le_rfl)
  have h := avgOver_mono (uniformDistribution (Fin 2 → F)) _ _ hpoint
  simp only [avgOver_uniform_const, avgOver_add, avgOver_const_mul] at h
  have hm := avg_wrong_ordered_norm_sq_le X Z hX hZ r t ψ
  linarith

end

end MIPStarRE.QPBT.PolynomialImageBounds
