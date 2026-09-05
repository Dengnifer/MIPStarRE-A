import MIPStarRE.QPBT.Test.MagicSquareTheorems.Rigidity.TwoQubitIntertwine
import MIPStarRE.QPBT.Test.MagicSquareTheorems.Rigidity.Constants
import MIPStarRE.QPBT.Test.MagicSquareTheorems.Rigidity.SecondPair
import MIPStarRE.QPBT.Test.MagicSquareTheorems.Rigidity.Anticommutation
import MIPStarRE.QPBT.Test.MagicSquareTheorems.Rigidity.TwoQubitSwap

/-!
# Assembling the small-error regime of Magic Square rigidity

This file feeds the two logical pairs of each player of a Magic Square strategy
of value at least `1 - ε` whose variable measurements at the cells `0` and `4`
agree between the players up to `δ` into the joint state estimate of
`Rigidity/JointState.lean`.

The two pairs of Alice are her variable reflections at the cells `0` and `4`
and her constraint reflections at the cells `1` and `3`; those of Bob are his
variable reflections at the same four cells.  The hypotheses of the joint
estimate are the approximate anticommutation of each pair, the approximate
commutation of the two pairs of one player, and the cross-player agreement of
corresponding reflections; each of them is available at a scale bounded by
`msRigidityDefect ε δ`.

## References

`thm:ms-rigidity`, blueprint `blueprint/src/chapter/ch13_qpbt_test.tex:224-253`,
paper `references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:612-652`.
-/

open scoped BigOperators Matrix MatrixOrder ComplexOrder

namespace MIPStarRE.QPBT.MagicSquareRigidity

open MIPStarRE.LDT MIPStarRE.Quantum

noncomputable section

/-! ## The common scale of the small-error hypotheses -/

/-- The common scale at which every hypothesis of the joint state estimate holds
for a Magic Square strategy of value at least `1 - ε` whose variable
measurements at the cells `0` and `4` agree between the players up to `δ`. -/
def msRigidityDefect (ε δ : ℝ) : ℝ :=
  4 * Real.sqrt (864 * ε + 6 * δ) + 624 * Real.sqrt ε

/-- The common scale is nonnegative. -/
theorem msRigidityDefect_nonneg (ε δ : ℝ) : 0 ≤ msRigidityDefect ε δ := by
  have h1 := Real.sqrt_nonneg (864 * ε + 6 * δ)
  have h2 := Real.sqrt_nonneg ε
  simp only [msRigidityDefect]
  linarith

/-- The cross-player scale is bounded by the common scale. -/
theorem sqrt_consistency_le_msRigidityDefect (ε δ : ℝ) :
    Real.sqrt (864 * ε + 6 * δ) ≤ msRigidityDefect ε δ := by
  have h1 := Real.sqrt_nonneg (864 * ε + 6 * δ)
  have h2 := Real.sqrt_nonneg ε
  simp only [msRigidityDefect]
  linarith

/-- The solution-group scale is bounded by the common scale. -/
theorem sqrt_value_le_msRigidityDefect (ε δ : ℝ) :
    624 * Real.sqrt ε ≤ msRigidityDefect ε δ := by
  have h1 := Real.sqrt_nonneg (864 * ε + 6 * δ)
  simp only [msRigidityDefect]
  linarith

/-- The commutation scale is bounded by the common scale. -/
theorem comm_le_msRigidityDefect (ε δ : ℝ) :
    4 * Real.sqrt (864 * ε + 6 * δ) + 96 * Real.sqrt ε ≤ msRigidityDefect ε δ := by
  have h2 := Real.sqrt_nonneg ε
  simp only [msRigidityDefect]
  linarith

/-- The common scale is bounded by a universal multiple of the asserted scale of
`thm:ms-rigidity`. -/
theorem msRigidityDefect_le (ε δ : ℝ) (hε : 0 ≤ ε) (hδ : 0 ≤ δ) :
    msRigidityDefect ε δ ≤ 744 * (Real.sqrt ε + Real.sqrt δ) := by
  have hse := Real.sqrt_nonneg ε
  have hsd := Real.sqrt_nonneg δ
  have he : Real.sqrt ε ^ 2 = ε := Real.sq_sqrt hε
  have hd : Real.sqrt δ ^ 2 = δ := Real.sq_sqrt hδ
  have hb : 864 * ε + 6 * δ ≤ (30 * Real.sqrt ε + 3 * Real.sqrt δ) ^ 2 := by
    nlinarith [hse, hsd, he, hd, mul_nonneg hse hsd]
  have hsplit : Real.sqrt (864 * ε + 6 * δ) ≤ 30 * Real.sqrt ε + 3 * Real.sqrt δ := by
    have h := Real.sqrt_le_sqrt hb
    rwa [Real.sqrt_sq (by positivity)] at h
  simp only [msRigidityDefect]
  linarith

/-! ## Placing the local relations on the joint space -/

/-- Tensor placement carries a commutator of the left factor to the commutator
of the placed operators. -/
theorem heteroKron_left_commutator {ι κ : Type} [Fintype ι] [DecidableEq ι]
    [Fintype κ] [DecidableEq κ] (M N : Op ι) :
    heteroKron M (1 : Op κ) * heteroKron N 1 - heteroKron N 1 * heteroKron M 1 =
      heteroKron (M * N - N * M) (1 : Op κ) := by
  rw [heteroKron_mul, heteroKron_mul, one_mul, ← heteroKron_sub_left]

/-- Tensor placement carries an anticommutator of the left factor to the
anticommutator of the placed operators. -/
theorem heteroKron_left_anticommutator {ι κ : Type} [Fintype ι] [DecidableEq ι]
    [Fintype κ] [DecidableEq κ] (M N : Op ι) :
    heteroKron M (1 : Op κ) * heteroKron N 1 - -(heteroKron N 1 * heteroKron M 1) =
      heteroKron (M * N + N * M) (1 : Op κ) := by
  rw [heteroKron_mul, heteroKron_mul, one_mul, sub_neg_eq_add, ← heteroKron_add_left]

/-- Tensor placement carries a commutator of the right factor to the commutator
of the placed operators. -/
theorem heteroKron_right_commutator {ι κ : Type} [Fintype ι] [DecidableEq ι]
    [Fintype κ] [DecidableEq κ] (M N : Op κ) :
    heteroKron (1 : Op ι) M * heteroKron 1 N - heteroKron 1 N * heteroKron 1 M =
      heteroKron (1 : Op ι) (M * N - N * M) := by
  rw [heteroKron_mul, heteroKron_mul, one_mul, ← heteroKron_sub_right]

/-! ## The state estimate on the projective dilation -/

/-- The state estimate of `thm:ms-rigidity` on the projective dilation: the
tensor of the two players' two-qubit controlled-swap embeddings carries the
dilated state to within a universal multiple of `msRigidityDefect ε δ` of two
EPR pairs tensored with a residual bipartite vector. -/
theorem ms_dilated_state_residual (S : Strategy msGame) (ε δ : ℝ)
    (hwin : 1 - ε ≤ S.value)
    (hd0 : msVariableConsistencyDefect S 0 ≤ δ)
    (hd4 : msVariableConsistencyDefect S 4 ≤ δ) :
    ∃ r : EuclideanSpace ℂ ((msDilatedStrategy S).ιA × (msDilatedStrategy S).ιB),
      ‖isometryTensor (msAliceTwoQubitSwapIsometry S) (msBobTwoQubitSwapIsometry S)
            (msDilatedStrategy S).ψ -
          reindexState prodShuffle (vecTensor (eprState (Fin 2 → ZMod 2)) r)‖ ≤
        116 * msRigidityDefect ε δ := by
  have hb : (96 : ℝ) * Real.sqrt ε ≤ msRigidityDefect ε δ := by
    linarith [sqrt_value_le_msRigidityDefect ε δ, Real.sqrt_nonneg ε]
  have hcross : ∀ j : Fin 9, msVariableConsistencyDefect S j ≤ δ →
      NormCloseOn (msDilatedStrategy S).ψ (msRigidityDefect ε δ)
        (msVarObsA S j) (msVarObsB S j) := fun j hj =>
    (msVarObsA_close_msVarObsB S ε δ hwin j hj).mono
      (sqrt_consistency_le_msRigidityDefect ε δ)
  refine exists_residual_of_two_pairs
    (msLocalVarObsA S 0) (msLocalVarObsA S 4)
    (msLocalCellObsA S 0 1) (msLocalCellObsA S 1 0)
    (msLocalVarObsB S 0) (msLocalVarObsB S 4)
    (msLocalVarObsB S 1) (msLocalVarObsB S 3)
    (isBinaryObservable_msLocalVarObsA S 0) (isBinaryObservable_msLocalVarObsA S 4)
    (isBinaryObservable_msLocalCellObsA S 0 1) (isBinaryObservable_msLocalCellObsA S 1 0)
    (isBinaryObservable_msLocalVarObsB S 0) (isBinaryObservable_msLocalVarObsB S 4)
    (isBinaryObservable_msLocalVarObsB S 1) (isBinaryObservable_msLocalVarObsB S 3)
    (msDilatedStrategy S).ψ (msRigidityDefect ε δ) (msRigidityDefect_nonneg ε δ)
    (hcross 0 hd0) (hcross 4 hd4) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · exact (msCellObsA_close_msVarObsB_second_x S ε hwin).mono (by
      linarith [sqrt_value_le_msRigidityDefect ε δ, Real.sqrt_nonneg ε])
  · exact (msCellObsA_close_msVarObsB_second_z S ε hwin).mono (by
      linarith [sqrt_value_le_msRigidityDefect ε δ, Real.sqrt_nonneg ε])
  · have h := (msVarObsA_anticommute S ε hwin).mono (sqrt_value_le_msRigidityDefect ε δ)
    rw [← heteroKron_left_anticommutator]
    exact h
  · have h :=
      (msCellObsA_second_pair_anticommute S ε hwin).mono (sqrt_value_le_msRigidityDefect ε δ)
    rw [← heteroKron_left_anticommutator]
    exact h
  · have h := (msVarObsA_comm_msCellObsA_of_shared_constraint S ε δ hwin 0 hd0 0 0 1
      (by decide) 0 1 (by decide)).symm.mono (comm_le_msRigidityDefect ε δ)
    rw [← heteroKron_left_commutator]
    exact h
  · have h := (msVarObsA_comm_msCellObsA_of_shared_constraint S ε δ hwin 4 hd4 4 1 0
      (by decide) 0 1 (by decide)).symm.mono (comm_le_msRigidityDefect ε δ)
    rw [← heteroKron_left_commutator]
    exact h
  · have h := (msVarObsA_comm_msCellObsA_of_shared_constraint S ε δ hwin 0 hd0 3 0 1
      (by decide) 1 0 (by decide)).symm.mono (comm_le_msRigidityDefect ε δ)
    rw [← heteroKron_left_commutator]
    exact h
  · have h := (msVarObsA_comm_msCellObsA_of_shared_constraint S ε δ hwin 4 hd4 1 1 0
      (by decide) 1 0 (by decide)).symm.mono (comm_le_msRigidityDefect ε δ)
    rw [← heteroKron_left_commutator]
    exact h
  · have h := (msVarObsB_comm_of_shared_constraint S ε hwin 0 1 0).mono hb
    rw [show msConstraintVars 0 1 = 1 from by decide,
      show msConstraintVars 0 0 = 0 from by decide] at h
    rw [← heteroKron_right_commutator]
    exact h
  · have h := (msVarObsB_comm_of_shared_constraint S ε hwin 4 0 1).mono hb
    rw [show msConstraintVars 4 0 = 1 from by decide,
      show msConstraintVars 4 1 = 4 from by decide] at h
    rw [← heteroKron_right_commutator]
    exact h
  · have h := (msVarObsB_comm_of_shared_constraint S ε hwin 3 1 0).mono hb
    rw [show msConstraintVars 3 1 = 3 from by decide,
      show msConstraintVars 3 0 = 0 from by decide] at h
    rw [← heteroKron_right_commutator]
    exact h
  · have h := (msVarObsB_comm_of_shared_constraint S ε hwin 1 0 1).mono hb
    rw [show msConstraintVars 1 0 = 3 from by decide,
      show msConstraintVars 1 1 = 4 from by decide] at h
    rw [← heteroKron_right_commutator]
    exact h

/-- The state estimate of `thm:ms-rigidity` on the projective dilation with a
unit auxiliary vector: the tensor of the two two-qubit controlled-swap
embeddings carries the dilated state to within a universal multiple of
`sqrt ε + sqrt δ` of two EPR pairs tensored with a unit residual state. -/
theorem ms_dilated_state_estimate (S : Strategy msGame) (ε δ : ℝ)
    (hε : 0 ≤ ε) (hδ : 0 ≤ δ) (hwin : 1 - ε ≤ S.value)
    (hd0 : msVariableConsistencyDefect S 0 ≤ δ)
    (hd4 : msVariableConsistencyDefect S 4 ≤ δ) :
    ∃ r : EuclideanSpace ℂ ((msDilatedStrategy S).ιA × (msDilatedStrategy S).ιB),
      ‖r‖ = 1 ∧
      ‖isometryTensor (msAliceTwoQubitSwapIsometry S) (msBobTwoQubitSwapIsometry S)
            (msDilatedStrategy S).ψ -
          reindexState prodShuffle (vecTensor (eprState (Fin 2 → ZMod 2)) r)‖ ≤
        172608 * (Real.sqrt ε + Real.sqrt δ) := by
  obtain ⟨r0, hr0⟩ := ms_dilated_state_residual S ε δ hwin hd0 hd4
  have hu : ‖isometryTensor (msAliceTwoQubitSwapIsometry S) (msBobTwoQubitSwapIsometry S)
      (msDilatedStrategy S).ψ‖ = 1 := by
    rw [norm_isometryTensor]
    exact (msDilatedStrategy S).ψ_norm
  obtain ⟨r, hrnorm, hr⟩ := exists_unit_residual (V := Fin 2 → ZMod 2) _ hu
    (msDilatedStrategy S).ψ (msDilatedStrategy S).ψ_norm _ r0 hr0
  refine ⟨r, hrnorm, hr.trans ?_⟩
  have h := msRigidityDefect_le ε δ hε hδ
  have h0 := msRigidityDefect_nonneg ε δ
  linarith

end

end MIPStarRE.QPBT.MagicSquareRigidity
