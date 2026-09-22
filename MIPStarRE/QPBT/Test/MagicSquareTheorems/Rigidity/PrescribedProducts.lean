import MIPStarRE.QPBT.Test.MagicSquareTheorems.Prescribed
import MIPStarRE.QPBT.Test.MagicSquareTheorems.Rigidity.OriginalConsistency
import MIPStarRE.QPBT.Observables.WinImplications.AnticommutingObs

/-!
# Prescribed Magic Square anticommutators

Removing malformed-answer effects from products requires an opposite-player
constraint comparison. A bound on the error operator acting on the state
alone does not justify its action after another variable observable.

## References

`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:638-646`,
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:326-350`,
`docs/paper-gaps/qpbt_ms-rigidity-symmetric-strategies.tex`, issue #701.
The original completed-observable estimates are reused from the existing
`WinImplications` support module; their proofs depend only on the game value.
-/

open scoped BigOperators Matrix MatrixOrder ComplexOrder

namespace MIPStarRE.QPBT.MagicSquareRigidity

open MIPStarRE.LDT hiding Measurement
open MIPStarRE.Quantum DistanceCalculus

noncomputable section

/-- Move the second factor to a commuting opposite-player contraction before
using an error operator's action on the state. -/
theorem norm_product_via_opposite_le {ι : Type*} [Fintype ι] [DecidableEq ι]
    (R Z D : Op ι) (ψ : EuclideanSpace ℂ ι) (a r : ℝ)
    (hR : Rᴴ * R ≤ 1) (hD : Dᴴ * D ≤ 1) (hc : R * D = D * R)
    (hz : ‖applyOperatorToState (Z - D) ψ‖ ≤ a)
    (hr : ‖applyOperatorToState R ψ‖ ≤ r) :
    ‖applyOperatorToState (R * Z) ψ‖ ≤ a + r := by
  have he : R * Z = R * (Z - D) + D * R := by rw [← hc]; noncomm_ring
  rw [he, applyOperatorToState_add_op, applyOperatorToState_mul,
    applyOperatorToState_mul]
  exact (norm_add_le _ _).trans (add_le_add
    ((norm_applyOperatorToState_le hR _).trans hz)
    ((norm_applyOperatorToState_le hD _).trans hr))

/-- The anticommutator changes by at most `2*a + 6*r` when two contractive
errors are removed. The hypotheses compare each original observable with an
opposite-player contraction; no product-error certificate is assumed. -/
theorem norm_anticommutator_sub_errors_le {ι : Type*} [Fintype ι] [DecidableEq ι]
    (X Z R T C D : Op ι) (ψ : EuclideanSpace ℂ ι) (a r : ℝ)
    (hX : Xᴴ * X ≤ 1) (hZ : Zᴴ * Z ≤ 1)
    (hR : Rᴴ * R ≤ 1) (hT : Tᴴ * T ≤ 1)
    (hC : Cᴴ * C ≤ 1) (hD : Dᴴ * D ≤ 1)
    (hRD : R * D = D * R) (hTC : T * C = C * T)
    (hx : ‖applyOperatorToState (X - C) ψ‖ ≤ a)
    (hz : ‖applyOperatorToState (Z - D) ψ‖ ≤ a)
    (hr : ‖applyOperatorToState R ψ‖ ≤ r)
    (ht : ‖applyOperatorToState T ψ‖ ≤ r) :
    ‖applyOperatorToState ((X - R) * (Z - T) + (Z - T) * (X - R)) ψ‖ ≤
      ‖applyOperatorToState (X * Z + Z * X) ψ‖ + 2 * a + 6 * r := by
  have h1 := norm_product_via_opposite_le R Z D ψ a r hR hD hRD hz hr
  have h3 := norm_product_via_opposite_le T X C ψ a r hT hC hTC hx ht
  have h2 : ‖applyOperatorToState ((X - R) * T) ψ‖ ≤ 2 * r := by
    rw [applyOperatorToState_mul]
    exact (norm_applyOperatorToState_sub_le hX hR _).trans (by linarith)
  have h4 : ‖applyOperatorToState ((Z - T) * R) ψ‖ ≤ 2 * r := by
    rw [applyOperatorToState_mul]
    exact (norm_applyOperatorToState_sub_le hZ hT _).trans (by linarith)
  have he : (X - R) * (Z - T) + (Z - T) * (X - R) =
      (X * Z + Z * X) - (R * Z + (X - R) * T + T * X + (Z - T) * R) := by
    noncomm_ring
  rw [he, applyOperatorToState_sub_op]
  refine (norm_sub_le _ _).trans ?_
  simp only [applyOperatorToState_add_op]
  have hn1 := norm_add_le (applyOperatorToState (R * Z) ψ)
    (applyOperatorToState ((X - R) * T) ψ)
  have hn2 := norm_add_le (applyOperatorToState (R * Z) ψ +
    applyOperatorToState ((X - R) * T) ψ) (applyOperatorToState (T * X) ψ)
  have hn3 := norm_add_le (applyOperatorToState (R * Z) ψ +
    applyOperatorToState ((X - R) * T) ψ + applyOperatorToState (T * X) ψ)
    (applyOperatorToState ((Z - T) * R) ψ)
  linarith

/-- A difference of contractions has norm at most two; its anticommutator
with another such difference has norm at most eight on any vector. -/
theorem norm_anticommutator_sub_apply_le {ι : Type*} [Fintype ι] [DecidableEq ι]
    (X Z R T : Op ι) (ψ : EuclideanSpace ℂ ι)
    (hX : Xᴴ * X ≤ 1) (hZ : Zᴴ * Z ≤ 1)
    (hR : Rᴴ * R ≤ 1) (hT : Tᴴ * T ≤ 1) :
    ‖applyOperatorToState ((X - R) * (Z - T) + (Z - T) * (X - R)) ψ‖ ≤ 8 * ‖ψ‖ := by
  rw [applyOperatorToState_add_op, applyOperatorToState_mul, applyOperatorToState_mul]
  have h1 := norm_applyOperatorToState_sub_le hX hR (applyOperatorToState (Z - T) ψ)
  have h2 := norm_applyOperatorToState_sub_le hZ hT (applyOperatorToState (X - R) ψ)
  have h3 := norm_applyOperatorToState_sub_le hX hR ψ
  have h4 := norm_applyOperatorToState_sub_le hZ hT ψ
  exact (norm_add_le _ _).trans (by linarith)

/-- Alice's prescribed-observable anticommutator on the original state is
bounded using tested opposite-player constraints, without agreement. -/
theorem ms_prescribed_anticommutator_norm_A (S : Strategy msGame) (ε : ℝ)
    (hε : 0 ≤ ε) (hwin : 1 - ε ≤ S.value) :
    ‖applyOperatorToState
      (heteroKron (msPrescribedObservable (S.A (.var 0)) *
        msPrescribedObservable (S.A (.var 4)) +
        msPrescribedObservable (S.A (.var 4)) *
        msPrescribedObservable (S.A (.var 0))) (1 : Op S.ιB)) S.ψ‖ ≤ 1148 * Real.sqrt ε := by
  let X := heteroKron (obsOf ((S.A (.var 0)).postprocess msBitOrZero)) (1 : Op S.ιB)
  let Z := heteroKron (obsOf ((S.A (.var 4)).postprocess msBitOrZero)) (1 : Op S.ιB)
  let R := heteroKron (msWrongFormEffect (S.A (.var 0))) (1 : Op S.ιB)
  let T := heteroKron (msWrongFormEffect (S.A (.var 4))) (1 : Op S.ιB)
  let C := heteroKron (1 : Op S.ιA)
    (obsOf ((S.B (.constraint 0)).postprocess (constraintBitOrZero 0)))
  let D := heteroKron (1 : Op S.ιA)
    (obsOf ((S.B (.constraint 1)).postprocess (constraintBitOrZero 1)))
  have hR (j : Fin 9) :
      ‖applyOperatorToState (heteroKron (msWrongFormEffect (S.A (.var j))) (1 : Op S.ιB)) S.ψ‖ ≤
        6 * Real.sqrt ε := by
    apply (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp
    nlinarith only [ms_wrong_form_norm_sq_A S ε hwin j, Real.sq_sqrt hε]
  have h := norm_anticommutator_sub_errors_le X Z R T C D S.ψ
    (12 * Real.sqrt ε) (6 * Real.sqrt ε)
    (conjTranspose_mul_le_one_leftTensor (conjTranspose_mul_le_one_of_obsOf _))
    (conjTranspose_mul_le_one_leftTensor (conjTranspose_mul_le_one_of_obsOf _))
    (conjTranspose_mul_le_one_leftTensor (conjTranspose_mul_le_one_of_effect
      ((S.A (.var 0)).postprocess wrongVariableAnswer) true))
    (conjTranspose_mul_le_one_leftTensor (conjTranspose_mul_le_one_of_effect
      ((S.A (.var 4)).postprocess wrongVariableAnswer) true))
    (conjTranspose_mul_le_one_rightTensor (conjTranspose_mul_le_one_of_obsOf _))
    (conjTranspose_mul_le_one_rightTensor (conjTranspose_mul_le_one_of_obsOf _))
    (heteroKron_comm _ _) (heteroKron_comm _ _)
    (ms_original_variable_close_constraint_A S ε hε hwin 0 0)
    (ms_original_variable_close_constraint_A S ε hε hwin 1 1) (hR 0) (hR 4)
  have hcomp : ‖applyOperatorToState (X * Z + Z * X) S.ψ‖ ≤ 1088 * Real.sqrt ε := by
    apply (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp
    have hc := WinImplications.msVarObsA_anticommutator_le S ε hε hwin
    dsimp only [X, Z]
    simp only [heteroKron_mul, one_mul, ← heteroKron_add_left]
    nlinarith only [hc, Real.sq_sqrt hε, hε]
  have he : heteroKron (msPrescribedObservable (S.A (.var 0)) *
      msPrescribedObservable (S.A (.var 4)) +
      msPrescribedObservable (S.A (.var 4)) *
      msPrescribedObservable (S.A (.var 0))) (1 : Op S.ιB) =
      (X - R) * (Z - T) + (Z - T) * (X - R) := by
    dsimp only [X, Z, R, T]
    simp only [ms_prescribed_observable_eq, ← heteroKron_sub_left,
      heteroKron_mul, one_mul, ← heteroKron_add_left]
    rfl
  rw [he]
  linarith

/-- Bob's prescribed-observable anticommutator on the original state is
bounded using tested opposite-player constraints, without agreement. -/
theorem ms_prescribed_anticommutator_norm_B (S : Strategy msGame) (ε : ℝ)
    (hε : 0 ≤ ε) (hwin : 1 - ε ≤ S.value) :
    ‖applyOperatorToState
      (heteroKron (1 : Op S.ιA) (msPrescribedObservable (S.B (.var 0)) *
        msPrescribedObservable (S.B (.var 4)) +
        msPrescribedObservable (S.B (.var 4)) *
        msPrescribedObservable (S.B (.var 0)))) S.ψ‖ ≤ 1148 * Real.sqrt ε := by
  let X := heteroKron (1 : Op S.ιA) (obsOf ((S.B (.var 0)).postprocess msBitOrZero))
  let Z := heteroKron (1 : Op S.ιA) (obsOf ((S.B (.var 4)).postprocess msBitOrZero))
  let R := heteroKron (1 : Op S.ιA) (msWrongFormEffect (S.B (.var 0)))
  let T := heteroKron (1 : Op S.ιA) (msWrongFormEffect (S.B (.var 4)))
  let C := heteroKron (obsOf ((S.A (.constraint 0)).postprocess (constraintBitOrZero 0)))
    (1 : Op S.ιB)
  let D := heteroKron (obsOf ((S.A (.constraint 1)).postprocess (constraintBitOrZero 1)))
    (1 : Op S.ιB)
  have hR (j : Fin 9) :
      ‖applyOperatorToState (heteroKron (1 : Op S.ιA) (msWrongFormEffect (S.B (.var j)))) S.ψ‖ ≤
        6 * Real.sqrt ε := by
    apply (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp
    nlinarith only [ms_wrong_form_norm_sq_B S ε hwin j, Real.sq_sqrt hε]
  have h := norm_anticommutator_sub_errors_le X Z R T C D S.ψ
    (12 * Real.sqrt ε) (6 * Real.sqrt ε)
    (conjTranspose_mul_le_one_rightTensor (conjTranspose_mul_le_one_of_obsOf _))
    (conjTranspose_mul_le_one_rightTensor (conjTranspose_mul_le_one_of_obsOf _))
    (conjTranspose_mul_le_one_rightTensor (conjTranspose_mul_le_one_of_effect
      ((S.B (.var 0)).postprocess wrongVariableAnswer) true))
    (conjTranspose_mul_le_one_rightTensor (conjTranspose_mul_le_one_of_effect
      ((S.B (.var 4)).postprocess wrongVariableAnswer) true))
    (conjTranspose_mul_le_one_leftTensor (conjTranspose_mul_le_one_of_obsOf _))
    (conjTranspose_mul_le_one_leftTensor (conjTranspose_mul_le_one_of_obsOf _))
    (heteroKron_comm _ _).symm (heteroKron_comm _ _).symm
    (ms_original_variable_close_constraint_B S ε hε hwin 0 0)
    (ms_original_variable_close_constraint_B S ε hε hwin 1 1) (hR 0) (hR 4)
  have hcomp : ‖applyOperatorToState (X * Z + Z * X) S.ψ‖ ≤ 1088 * Real.sqrt ε := by
    apply (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp
    have hc := WinImplications.msVarObs_anticommutator_le S ε hε hwin
    dsimp only [X, Z]
    simp only [heteroKron_mul, one_mul, ← heteroKron_add_right]
    nlinarith only [hc, Real.sq_sqrt hε, hε]
  have he : heteroKron (1 : Op S.ιA) (msPrescribedObservable (S.B (.var 0)) *
      msPrescribedObservable (S.B (.var 4)) +
      msPrescribedObservable (S.B (.var 4)) *
      msPrescribedObservable (S.B (.var 0))) =
      (X - R) * (Z - T) + (Z - T) * (X - R) := by
    dsimp only [X, Z, R, T]
    simp only [ms_prescribed_observable_eq, ← heteroKron_sub_right,
      heteroKron_mul, one_mul, ← heteroKron_add_right]
    rfl
  rw [he]
  linarith

end

end MIPStarRE.QPBT.MagicSquareRigidity
