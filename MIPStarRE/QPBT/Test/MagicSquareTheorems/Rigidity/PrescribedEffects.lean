import MIPStarRE.QPBT.Test.MagicSquareTheorems

/-!
# Prescribed Magic Square effects

The prescribed bit effects exclude malformed triple answers. Their difference
from the completed binary effects is controlled by the rejected-answer mass.
All estimates below derive that mass from the existing game value.

## References

`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:620-646`,
`docs/paper-gaps/qpbt_ms-rigidity-symmetric-strategies.tex`, issue #701.
-/

open scoped BigOperators Matrix MatrixOrder ComplexOrder

namespace MIPStarRE.QPBT.MagicSquareRigidity

open MIPStarRE.LDT hiding Measurement
open MIPStarRE.Quantum DistanceCalculus

noncomputable section

/-- The sum of the triple-answer effects of a Magic Square measurement. -/
def msWrongFormEffect {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : Measurement MsAnswer ι) : Op ι :=
  (M.postprocess wrongVariableAnswer).effect true

/-- Completion adds the triple-answer effect to bit zero only. -/
theorem ms_completed_effect_eq {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : Measurement MsAnswer ι) (b : ZMod 2) :
    (M.postprocess msBitOrZero).effect b =
      M.effect (.bit b) + if b = 0 then msWrongFormEffect M else 0 := by
  classical
  rw [Measurement.postprocess_effect, Finset.sum_filter]
  have ht (a : MsAnswer) :
      (if msBitOrZero a = b then M.effect a else 0) =
        (if a = .bit b then M.effect a else 0) +
          if b = 0 then (if wrongVariableAnswer a = true then M.effect a else 0) else 0 := by
    cases a <;> by_cases hb : b = 0 <;> simp [msBitOrZero, wrongVariableAnswer, hb, eq_comm]
  simp_rw [ht]
  rw [Finset.sum_add_distrib]
  by_cases hb : b = 0
  · simp only [hb, ↓reduceIte, Finset.sum_ite_eq', Finset.mem_univ,
      msWrongFormEffect, Measurement.postprocess, Submeasurement.postprocess,
      Finset.sum_filter]
  · simp [hb]

/-- The wrong-form effect is a positive contraction. -/
theorem msWrongFormEffect_bounds {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : Measurement MsAnswer ι) :
    0 ≤ msWrongFormEffect M ∧ msWrongFormEffect M ≤ 1 :=
  ⟨(M.postprocess wrongVariableAnswer).pos true,
    measurement_effect_le_one (M.postprocess wrongVariableAnswer) true⟩

/-- Alice's wrong-form effect has squared action at most `36 * ε`. -/
theorem ms_wrong_form_norm_sq_A (S : Strategy msGame) (ε : ℝ)
    (hwin : 1 - ε ≤ S.value) (j : Fin 9) :
    ‖applyOperatorToState (heteroKron (msWrongFormEffect (S.A (.var j)))
      (1 : Op S.ιB)) S.ψ‖ ^ 2 ≤ 36 * ε := by
  have hpos : 0 ≤ heteroKron (msWrongFormEffect (S.A (.var j))) (1 : Op S.ιB) :=
    kronecker_nonneg (msWrongFormEffect_bounds (S.A (.var j))).1
    (show (0 : Op S.ιB) ≤ 1 by simp)
  have hle : heteroKron (msWrongFormEffect (S.A (.var j))) (1 : Op S.ιB) ≤ 1 := by
    rw [← Matrix.one_kronecker_one]
    exact kronecker_mono_left (msWrongFormEffect_bounds (S.A (.var j))).2 (by simp)
  rw [norm_applyOperatorToState_sq,
    (Matrix.nonneg_iff_posSemidef.mp hpos).isHermitian.eq]
  refine (quadratic_form_mono (sq_le_self hpos hle) S.ψ).trans ?_
  change stateQForm S.ψ (heteroKron (msWrongFormEffect (S.A (.var j))) 1) ≤ _
  simp only [msWrongFormEffect, Measurement.postprocess, Submeasurement.postprocess,
    heteroKron_finset_sum_left, stateQForm_finset_sum, Finset.sum_filter]
  convert alice_variable_wrong_form_mass_le S ε hwin j using 1
  unfold aliceVariableWrongFormMass aliceEventWeight
  apply Finset.sum_congr rfl
  intro b _
  by_cases hb : wrongVariableAnswer b = true <;>
    simp [hb, stateQForm, aliceOutcomeWeight, heteroKron, applyOperatorToState]

/-- Bob's wrong-form effect has squared action at most `36 * ε`. -/
theorem ms_wrong_form_norm_sq_B (S : Strategy msGame) (ε : ℝ)
    (hwin : 1 - ε ≤ S.value) (j : Fin 9) :
    ‖applyOperatorToState (heteroKron (1 : Op S.ιA)
      (msWrongFormEffect (S.B (.var j)))) S.ψ‖ ^ 2 ≤ 36 * ε := by
  have hpos : 0 ≤ heteroKron (1 : Op S.ιA) (msWrongFormEffect (S.B (.var j))) :=
    kronecker_nonneg (show (0 : Op S.ιA) ≤ 1 by simp)
    (msWrongFormEffect_bounds (S.B (.var j))).1
  have hle : heteroKron (1 : Op S.ιA) (msWrongFormEffect (S.B (.var j))) ≤ 1 := by
    change rightTensor (ι₁ := S.ιA) (msWrongFormEffect (S.B (.var j))) ≤ 1
    exact rightTensor_le_one (msWrongFormEffect_bounds (S.B (.var j))).2
  rw [norm_applyOperatorToState_sq,
    (Matrix.nonneg_iff_posSemidef.mp hpos).isHermitian.eq]
  refine (quadratic_form_mono (sq_le_self hpos hle) S.ψ).trans ?_
  change stateQForm S.ψ (heteroKron 1 (msWrongFormEffect (S.B (.var j)))) ≤ _
  simp only [msWrongFormEffect, Measurement.postprocess, Submeasurement.postprocess,
    heteroKron_finset_sum_right, stateQForm_finset_sum, Finset.sum_filter]
  convert bob_variable_wrong_form_mass_le S ε hwin j using 1
  unfold bobVariableWrongFormMass bobEventWeight
  apply Finset.sum_congr rfl
  intro b _
  by_cases hb : wrongVariableAnswer b = true <;>
    simp [hb, stateQForm, bobOutcomeWeight, heteroKron, applyOperatorToState]

/-- A contractive error operator with squared action at most `r` has squared
action at most `2*r + 2*s^2` on a state at distance at most `s`. -/
theorem norm_sq_on_close_state_le {ι : Type*} [Fintype ι] [DecidableEq ι]
    (K : Op ι) (u v : EuclideanSpace ℂ ι) (r s : ℝ)
    (hK : Kᴴ * K ≤ 1) (hu : ‖applyOperatorToState K u‖ ^ 2 ≤ r)
    (hs : ‖u - v‖ ≤ s) :
    ‖applyOperatorToState K v‖ ^ 2 ≤ 2 * r + 2 * s ^ 2 := by
  have h1 : ‖applyOperatorToState K (v - u)‖ ≤ s :=
    (norm_applyOperatorToState_le hK _).trans (by rwa [norm_sub_rev])
  have h2 : ‖applyOperatorToState K v‖ ≤
      ‖applyOperatorToState K (v - u)‖ + ‖applyOperatorToState K u‖ := by
    rw [applyOperatorToState_sub]
    simpa only [sub_neg_eq_add, sub_add_cancel, norm_neg] using
      norm_sub_le (applyOperatorToState K v - applyOperatorToState K u)
        (-applyOperatorToState K u)
  nlinarith [norm_nonneg (applyOperatorToState K (v - u)),
    norm_nonneg (applyOperatorToState K u), norm_nonneg (applyOperatorToState K v),
    sq_nonneg (s - ‖applyOperatorToState K u‖)]

end

end MIPStarRE.QPBT.MagicSquareRigidity
