import MIPStarRE.QPBT.Test.MagicSquareTheorems.Agreement
import MIPStarRE.QPBT.Test.MagicSquareTheorems.Rigidity.PrescribedEffects

/-!
# Extraction of prescribed Magic Square answers

The four effect distances use the prescribed single-bit effects themselves.
Malformed answers remain part of the strategy and are bounded from its value.

## References

`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:620-646`,
`docs/paper-gaps/qpbt_ms-rigidity-symmetric-strategies.tex`, issue #701.
-/

open scoped BigOperators Matrix MatrixOrder ComplexOrder

namespace MIPStarRE.QPBT

open MIPStarRE.LDT hiding Measurement
open MIPStarRE.Quantum MagicSquareRigidity

noncomputable section

/-- Alice's squared prescribed-bit distance on the ideal extracted state. -/
def msPrescribedOperatorDistanceA (S : Strategy msGame) (w : MsRigidityWitness S)
    (j : Fin 9) (W : PauliKind) : ℝ :=
  opFamilyDistSq (uniformDistribution Unit)
    (fun _ b => heteroKron (conjIsometry w.φA ((S.A (.var j)).effect (.bit b))) 1)
    (fun _ b => heteroKron (heteroKron (idealMagicBitProj W b) (1 : Op w.ιA'')) 1)
    (idealMsState w.aux)

/-- Bob's squared prescribed-bit distance on the ideal extracted state. -/
def msPrescribedOperatorDistanceB (S : Strategy msGame) (w : MsRigidityWitness S)
    (j : Fin 9) (W : PauliKind) : ℝ :=
  opFamilyDistSq (uniformDistribution Unit)
    (fun _ b => heteroKron 1 (conjIsometry w.φB ((S.B (.var j)).effect (.bit b))))
    (fun _ b => heteroKron 1 (heteroKron (idealMagicBitProj W b) (1 : Op w.ιB'')))
    (idealMsState w.aux)

/-- The observable formed from the two prescribed single-bit effects. It
excludes every triple-answer effect. -/
def msPrescribedObservable {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : Measurement MsAnswer ι) : Op ι := M.effect (.bit 0) - M.effect (.bit 1)

/-- Alice's prescribed-observable anticommutator, in the printed squared
norm convention on the ideal extracted state. -/
def msPrescribedAnticommutatorDistanceA (S : Strategy msGame)
    (w : MsRigidityWitness S) : ℝ :=
  let X := heteroKron (conjIsometry w.φA (msPrescribedObservable (S.A (.var 0))))
    (1 : Op ((Fin 2 → ZMod 2) × w.ιB''))
  let Z := heteroKron (conjIsometry w.φA (msPrescribedObservable (S.A (.var 4))))
    (1 : Op ((Fin 2 → ZMod 2) × w.ιB''))
  opDistSq (uniformDistribution Unit) (fun _ => X * Z) (fun _ => -(Z * X))
    (idealMsState w.aux)

/-- Bob's prescribed-observable anticommutator, in the printed squared
norm convention on the ideal extracted state. -/
def msPrescribedAnticommutatorDistanceB (S : Strategy msGame)
    (w : MsRigidityWitness S) : ℝ :=
  let X := heteroKron (1 : Op ((Fin 2 → ZMod 2) × w.ιA''))
    (conjIsometry w.φB (msPrescribedObservable (S.B (.var 0))))
  let Z := heteroKron (1 : Op ((Fin 2 → ZMod 2) × w.ιA''))
    (conjIsometry w.φB (msPrescribedObservable (S.B (.var 4))))
  opDistSq (uniformDistribution Unit) (fun _ => X * Z) (fun _ => -(Z * X))
    (idealMsState w.aux)

namespace MagicSquareRigidity

/-- Removing a single error vector from outcome zero costs twice its squared
norm and at most doubles the original squared family distance. -/
theorem sum_sq_single_sub_le {ι : Type*} [Fintype ι]
    (f : ZMod 2 → EuclideanSpace ℂ ι) (r : EuclideanSpace ℂ ι) :
    (∑ b : ZMod 2, ‖f b - if b = 0 then r else 0‖ ^ 2) ≤
      2 * (∑ b : ZMod 2, ‖f b‖ ^ 2) + 2 * ‖r‖ ^ 2 := by
  simp only [sum_zmod_two, ↓reduceIte, one_ne_zero, sub_zero]
  nlinarith [parallelogram_law_with_norm ℂ (f 0) r,
    sq_nonneg ‖f 0 + r‖, sq_nonneg ‖f 1‖]

/-- The prescribed effect is the completed effect minus its wrong-form part. -/
theorem ms_prescribed_effect_eq {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : Measurement MsAnswer ι) (b : ZMod 2) :
    M.effect (.bit b) = (M.postprocess msBitOrZero).effect b -
      if b = 0 then msWrongFormEffect M else 0 := by
  rw [ms_completed_effect_eq, add_sub_cancel_right]

/-- The prescribed observable is the completed observable minus triple mass. -/
theorem ms_prescribed_observable_eq {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : Measurement MsAnswer ι) :
    msPrescribedObservable M = obsOf (M.postprocess msBitOrZero) - msWrongFormEffect M := by
  simp only [msPrescribedObservable, obsOf, ms_completed_effect_eq, ↓reduceIte,
    one_ne_zero, add_zero]
  abel

end MagicSquareRigidity

/-- Transfer Alice's completed effects to the prescribed answers. The malformed
mass is derived from value, including on the ideal extracted state. -/
theorem ms_prescribed_operator_distance_A_le (S : Strategy msGame)
    (w : MsRigidityWitness S) (ε s : ℝ) (hwin : 1 - ε ≤ S.value)
    (hs : ‖isometryTensor w.φA w.φB S.ψ - idealMsState w.aux‖ ≤ s)
    (j : Fin 9) (W : PauliKind) :
    msPrescribedOperatorDistanceA S w j W ≤
      2 * msOperatorDistanceA S w j W + 144 * ε + 4 * s ^ 2 := by
  let R := heteroKron (conjIsometry w.φA (msWrongFormEffect (S.A (.var j))))
    (1 : Op ((Fin 2 → ZMod 2) × w.ιB''))
  have hr : ‖applyOperatorToState R (idealMsState w.aux)‖ ^ 2 ≤
      72 * ε + 2 * s ^ 2 := by
    refine (norm_sq_on_close_state_le R (isometryTensor w.φA w.φB S.ψ)
      (idealMsState w.aux) (36 * ε) s
      (conjTranspose_mul_le_one_leftTensor (conjTranspose_mul_le_one_conjIsometry _
        (conjTranspose_mul_le_one_of_effect ((S.A (.var j)).postprocess wrongVariableAnswer)
          true))) ?_ hs).trans_eq (by ring)
    dsimp only [R]
    rw [applyOperatorToState_leftTensor_conjIsometry, norm_isometryTensor]
    exact ms_wrong_form_norm_sq_A S ε hwin j
  have hf (b : ZMod 2) :
      applyOperatorToState
        (heteroKron (conjIsometry w.φA ((S.A (.var j)).effect (.bit b))) 1 -
          heteroKron (heteroKron (idealMagicBitProj W b) (1 : Op w.ιA'')) 1)
        (idealMsState w.aux) =
      applyOperatorToState
        (heteroKron (conjIsometry w.φA
          (((S.A (.var j)).postprocess msBitOrZero).effect b)) 1 -
          heteroKron (heteroKron (idealMagicBitProj W b) (1 : Op w.ιA'')) 1)
        (idealMsState w.aux) -
        if b = 0 then applyOperatorToState R (idealMsState w.aux) else 0 := by
    rw [ms_prescribed_effect_eq]
    by_cases hb : b = 0
    · rw [if_pos hb, conjIsometry_sub, heteroKron_sub_left]
      simp only [applyOperatorToState_sub_op, R, if_pos hb]
      exact sub_right_comm _ _ _
    · simp only [if_neg hb, sub_zero]
      rfl
  simp only [msPrescribedOperatorDistanceA, msOperatorDistanceA, opFamilyDistSq_uniform_unit]
  simp_rw [hf]
  exact (sum_sq_single_sub_le _ _).trans (by linarith)

/-- Transfer Bob's completed effects to the prescribed answers. -/
theorem ms_prescribed_operator_distance_B_le (S : Strategy msGame)
    (w : MsRigidityWitness S) (ε s : ℝ) (hwin : 1 - ε ≤ S.value)
    (hs : ‖isometryTensor w.φA w.φB S.ψ - idealMsState w.aux‖ ≤ s)
    (j : Fin 9) (W : PauliKind) :
    msPrescribedOperatorDistanceB S w j W ≤
      2 * msOperatorDistanceB S w j W + 144 * ε + 4 * s ^ 2 := by
  let R := heteroKron (1 : Op ((Fin 2 → ZMod 2) × w.ιA''))
    (conjIsometry w.φB (msWrongFormEffect (S.B (.var j))))
  have hr : ‖applyOperatorToState R (idealMsState w.aux)‖ ^ 2 ≤
      72 * ε + 2 * s ^ 2 := by
    refine (norm_sq_on_close_state_le R (isometryTensor w.φA w.φB S.ψ)
      (idealMsState w.aux) (36 * ε) s
      (conjTranspose_mul_le_one_rightTensor (conjTranspose_mul_le_one_conjIsometry _
        (conjTranspose_mul_le_one_of_effect ((S.B (.var j)).postprocess wrongVariableAnswer)
          true))) ?_ hs).trans_eq (by ring)
    dsimp only [R]
    rw [applyOperatorToState_rightTensor_conjIsometry, norm_isometryTensor]
    exact ms_wrong_form_norm_sq_B S ε hwin j
  have hf (b : ZMod 2) :
      applyOperatorToState
        (heteroKron 1 (conjIsometry w.φB ((S.B (.var j)).effect (.bit b))) -
          heteroKron 1 (heteroKron (idealMagicBitProj W b) (1 : Op w.ιB'')))
        (idealMsState w.aux) =
      applyOperatorToState
        (heteroKron 1 (conjIsometry w.φB
          (((S.B (.var j)).postprocess msBitOrZero).effect b)) -
          heteroKron 1 (heteroKron (idealMagicBitProj W b) (1 : Op w.ιB'')))
        (idealMsState w.aux) -
        if b = 0 then applyOperatorToState R (idealMsState w.aux) else 0 := by
    rw [ms_prescribed_effect_eq]
    by_cases hb : b = 0
    · rw [if_pos hb, conjIsometry_sub, heteroKron_sub_right]
      simp only [applyOperatorToState_sub_op, R, if_pos hb]
      exact sub_right_comm _ _ _
    · simp only [if_neg hb, sub_zero]
      rfl
  simp only [msPrescribedOperatorDistanceB, msOperatorDistanceB, opFamilyDistSq_uniform_unit]
  simp_rw [hf]
  exact (sum_sq_single_sub_le _ _).trans (by linarith)

/-- A value-only witness for prescribed answers, with a separate linear
agreement term for Alice's variables. All four distances are squared. -/
theorem exists_ms_prescribed_measurements_with_agreement (S : Strategy msGame)
    (ε : ℝ) (hε : 0 ≤ ε) (hwin : 1 - ε ≤ S.value) :
    ∃ w : MsRigidityWitness S,
      ‖isometryTensor w.φA w.φB S.ψ - idealMsState w.aux‖ ≤ 155904 * Real.sqrt ε ∧
      (∀ W : PauliKind, msPrescribedOperatorDistanceB S w (msPauliCell W) W ≤
        5 * 10 ^ 12 * ε) ∧
      ∀ W : PauliKind, msPrescribedOperatorDistanceA S w (msPauliCell W) W ≤
        15 * 10 ^ 12 * ε + 6 * msVariableConsistencyDefect S (msPauliCell W) := by
  obtain ⟨w, hs, hb, ha⟩ := exists_ms_one_way_rigidity_with_agreement S ε hε hwin
  refine ⟨w, hs, fun W => ?_, fun W => ?_⟩
  · have ht := ms_prescribed_operator_distance_B_le S w ε _ hwin hs (msPauliCell W) W
    nlinarith [Real.sq_sqrt hε, hb W]
  · have ht := ms_prescribed_operator_distance_A_le S w ε _ hwin hs (msPauliCell W) W
    nlinarith [Real.sq_sqrt hε, ha W]

end

end MIPStarRE.QPBT
