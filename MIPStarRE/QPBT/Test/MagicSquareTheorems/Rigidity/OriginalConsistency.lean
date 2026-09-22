import MIPStarRE.QPBT.Test.MagicSquareTheorems.Rigidity.Transfer
import MIPStarRE.QPBT.Algebra.Pauli

/-!
# Tested Magic Square comparisons on the original state

The sampled incidences control completed effects and observables for arbitrary
POVM strategies, before dilation. These estimates permit product transfer to
the opposite player's constraint measurements.

## References

`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:512-652`,
`docs/paper-gaps/qpbt_ms-rigidity-symmetric-strategies.tex`, issue #701.
-/

open scoped BigOperators Matrix MatrixOrder ComplexOrder

namespace MIPStarRE.QPBT.MagicSquareRigidity

open MIPStarRE.LDT hiding Measurement
open MIPStarRE.Quantum DistanceCalculus

noncomputable section

/-- The tested forward incidence controls original completed effects. -/
theorem ms_original_cell_distance_forward (S : Strategy msGame) (ε : ℝ)
    (hwin : 1 - ε ≤ S.value) (i : Fin 6) (k : Fin 3) :
    (∑ b : ZMod 2, ‖applyOperatorToState
      (heteroKron (((S.A (.constraint i)).postprocess (constraintBitOrZero k)).effect b) 1 -
        heteroKron 1 (((S.B (.var (msConstraintVars i k))).postprocess msBitOrZero).effect b))
      S.ψ‖ ^ 2) ≤ 72 * ε := by
  have h := point_distance_le_two_defect
    (leftPlacedMeasurement (ιB := S.ιB)
      ((S.A (.constraint i)).postprocess (constraintBitOrZero k)))
    (rightPlacedMeasurement (ιA := S.ιA)
      ((S.B (.var (msConstraintVars i k))).postprocess msBitOrZero)) S.ψ
  rw [point_defect_eq, S.ψ_norm, one_pow] at h
  change (∑ b : ZMod 2, ‖applyOperatorToState
    (heteroKron (((S.A (.constraint i)).postprocess (constraintBitOrZero k)).effect b) 1 -
      heteroKron 1 (((S.B (.var (msConstraintVars i k))).postprocess msBitOrZero).effect b))
    S.ψ‖ ^ 2) ≤ 2 * (1 - ∑ b : ZMod 2, stateQForm S.ψ
      (heteroKron (((S.A (.constraint i)).postprocess (constraintBitOrZero k)).effect b) 1 *
        heteroKron 1 (((S.B (.var (msConstraintVars i k))).postprocess msBitOrZero).effect b))) at h
  simp only [heteroKron_mul, mul_one, one_mul] at h
  rw [sum_stateQForm_forward_eq] at h
  linarith [forward_cell_mismatch_mass_le S ε hwin i k]

/-- The tested reverse incidence controls original completed effects. -/
theorem ms_original_cell_distance_reverse (S : Strategy msGame) (ε : ℝ)
    (hwin : 1 - ε ≤ S.value) (i : Fin 6) (k : Fin 3) :
    (∑ b : ZMod 2, ‖applyOperatorToState
      (heteroKron (((S.A (.var (msConstraintVars i k))).postprocess msBitOrZero).effect b) 1 -
        heteroKron 1 (((S.B (.constraint i)).postprocess (constraintBitOrZero k)).effect b))
      S.ψ‖ ^ 2) ≤ 72 * ε := by
  have h := point_distance_le_two_defect
    (leftPlacedMeasurement (ιB := S.ιB)
      ((S.A (.var (msConstraintVars i k))).postprocess msBitOrZero))
    (rightPlacedMeasurement (ιA := S.ιA)
      ((S.B (.constraint i)).postprocess (constraintBitOrZero k))) S.ψ
  rw [point_defect_eq, S.ψ_norm, one_pow] at h
  change (∑ b : ZMod 2, ‖applyOperatorToState
    (heteroKron (((S.A (.var (msConstraintVars i k))).postprocess msBitOrZero).effect b) 1 -
      heteroKron 1 (((S.B (.constraint i)).postprocess (constraintBitOrZero k)).effect b))
    S.ψ‖ ^ 2) ≤ 2 * (1 - ∑ b : ZMod 2, stateQForm S.ψ
      (heteroKron (((S.A (.var (msConstraintVars i k))).postprocess msBitOrZero).effect b) 1 *
        heteroKron 1 (((S.B (.constraint i)).postprocess (constraintBitOrZero k)).effect b))) at h
  simp only [heteroKron_mul, mul_one, one_mul] at h
  rw [sum_stateQForm_reverse_eq] at h
  linarith [reverse_cell_mismatch_mass_le S ε hwin i k]

/-- The difference of binary observables has squared norm at most twice the
summed squared difference of their effects. -/
theorem binary_difference_norm_sq_le {ι : Type*} [Fintype ι] [DecidableEq ι]
    (P Q : ZMod 2 → Op ι) (ψ : EuclideanSpace ℂ ι) :
    ‖applyOperatorToState ((P 0 - P 1) - (Q 0 - Q 1)) ψ‖ ^ 2 ≤
      2 * ∑ b : ZMod 2, ‖applyOperatorToState (P b - Q b) ψ‖ ^ 2 := by
  rw [show (P 0 - P 1) - (Q 0 - Q 1) = (P 0 - Q 0) - (P 1 - Q 1) by abel,
    applyOperatorToState_sub_op, sum_zmod_two]
  nlinarith [parallelogram_law_with_norm ℂ (applyOperatorToState (P 0 - Q 0) ψ)
    (applyOperatorToState (P 1 - Q 1) ψ),
    sq_nonneg ‖applyOperatorToState (P 0 - Q 0) ψ +
      applyOperatorToState (P 1 - Q 1) ψ‖]

/-- Alice's original variable observable is close to Bob's tested constraint
observable, with norm error `12 * sqrt ε`. -/
theorem ms_original_variable_close_constraint_A (S : Strategy msGame) (ε : ℝ)
    (hε : 0 ≤ ε) (hwin : 1 - ε ≤ S.value) (i : Fin 6) (k : Fin 3) :
    ‖applyOperatorToState
      (heteroKron (obsOf ((S.A (.var (msConstraintVars i k))).postprocess msBitOrZero)) 1 -
        heteroKron 1 (obsOf ((S.B (.constraint i)).postprocess (constraintBitOrZero k))))
      S.ψ‖ ≤ 12 * Real.sqrt ε := by
  have h := binary_difference_norm_sq_le
    (fun b => heteroKron
      (((S.A (.var (msConstraintVars i k))).postprocess msBitOrZero).effect b) 1)
    (fun b => heteroKron 1
      (((S.B (.constraint i)).postprocess (constraintBitOrZero k)).effect b)) S.ψ
  rw [← heteroKron_sub_left, ← heteroKron_sub_right] at h
  have hd := ms_original_cell_distance_reverse S ε hwin i k
  apply (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp
  have hsq := Real.sq_sqrt hε
  change _ ≤ _ at h
  dsimp only [obsOf]
  nlinarith only [h, hd, hsq]

/-- Bob's original variable observable is close to Alice's tested constraint
observable, with norm error `12 * sqrt ε`. -/
theorem ms_original_variable_close_constraint_B (S : Strategy msGame) (ε : ℝ)
    (hε : 0 ≤ ε) (hwin : 1 - ε ≤ S.value) (i : Fin 6) (k : Fin 3) :
    ‖applyOperatorToState
      (heteroKron 1 (obsOf ((S.B (.var (msConstraintVars i k))).postprocess msBitOrZero)) -
        heteroKron (obsOf ((S.A (.constraint i)).postprocess (constraintBitOrZero k))) 1)
      S.ψ‖ ≤ 12 * Real.sqrt ε := by
  have h := binary_difference_norm_sq_le
    (fun b => heteroKron
      (((S.A (.constraint i)).postprocess (constraintBitOrZero k)).effect b) 1)
    (fun b => heteroKron 1
      (((S.B (.var (msConstraintVars i k))).postprocess msBitOrZero).effect b)) S.ψ
  rw [← heteroKron_sub_left, ← heteroKron_sub_right] at h
  have hd := ms_original_cell_distance_forward S ε hwin i k
  rw [applyOperatorToState_sub_op, norm_sub_rev, ← applyOperatorToState_sub_op]
  apply (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp
  have hsq := Real.sq_sqrt hε
  dsimp only [obsOf]
  nlinarith only [h, hd, hsq]

end

end MIPStarRE.QPBT.MagicSquareRigidity
