import MIPStarRE.QPBT.Test.MagicSquareTheorems.Rigidity.Assembly

/-!
# One-way Magic Square state extraction

Alice uses constraint-read reflections for both logical pairs, and Bob uses
variable reflections. Every cross-player comparison is therefore tested by
the game. The resulting state estimate needs only the winning probability.

## References

The one-way conclusion underlying `thm:ms-rigidity` is discussed in
`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:620-652`
and `docs/paper-gaps/qpbt_ms-rigidity-symmetric-strategies.tex`, issue #701.
This construction does not assert simultaneous extraction of both players'
bare-variable measurements.
-/

open scoped BigOperators Matrix MatrixOrder ComplexOrder

namespace MIPStarRE.QPBT.MagicSquareRigidity

open MIPStarRE.LDT MIPStarRE.Quantum

noncomputable section

/-- Alice's one-way extractor reads cells `0,4,1,3` from the first two rows.
Unlike `msAliceTwoQubitSwapIsometry`, it uses no bare-variable measurement. -/
def msAliceOneWaySwapIsometry (S : Strategy msGame) :
    EuclideanSpace ℂ (msDilatedStrategy S).ιA →ₗᵢ[ℂ]
      EuclideanSpace ℂ ((Fin 2 → ZMod 2) × (msDilatedStrategy S).ιA) :=
  twoBinarySwapIsometry
    (msLocalCellObsA S 0 0) (msLocalCellObsA S 1 1)
    (msLocalCellObsA S 0 1) (msLocalCellObsA S 1 0)
    (isBinaryObservable_msLocalCellObsA S 0 0)
    (isBinaryObservable_msLocalCellObsA S 1 1)
    (isBinaryObservable_msLocalCellObsA S 0 1)
    (isBinaryObservable_msLocalCellObsA S 1 0)

/-- Tested constraint-variable comparisons transfer Bob's first-pair
anticommutation to Alice's chosen constraint representatives. -/
theorem msCellObsA_first_pair_anticommute (S : Strategy msGame) (ε : ℝ)
    (hwin : 1 - ε ≤ S.value) :
    NormCloseOn (msDilatedStrategy S).ψ (672 * Real.sqrt ε)
      (msCellObsA S 0 0 * msCellObsA S 1 1)
      (-(msCellObsA S 1 1 * msCellObsA S 0 0)) := by
  have h1 := msCellObsA_mul_close S ε hwin 0 1 0 1
  have h2 := msCellObsA_mul_close S ε hwin 1 0 1 0
  rw [show msConstraintVars 0 0 = 0 from by decide,
    show msConstraintVars 1 1 = 4 from by decide] at h1 h2
  exact ((h1.trans (normCloseOn_neg_swap (msVarObsB_anticommute S ε hwin))).trans
    h2.neg.symm).mono (by linarith)

/-- Constraint representatives inherit commutation whenever their cells share
a constraint. Both product transfers use the opposite player's variables. -/
theorem msCellObsA_comm_of_shared_constraint (S : Strategy msGame) (ε : ℝ)
    (hwin : 1 - ε ≤ S.value) (I J : Fin 6) (k l : Fin 3)
    (i : Fin 6) (p q : Fin 3)
    (hp : msConstraintVars I k = msConstraintVars i p)
    (hq : msConstraintVars J l = msConstraintVars i q) :
    NormCloseOn (msDilatedStrategy S).ψ (144 * Real.sqrt ε)
      (msCellObsA S I k * msCellObsA S J l)
      (msCellObsA S J l * msCellObsA S I k) := by
  have h1 := msCellObsA_mul_close S ε hwin I J k l
  have h2 := msCellObsA_mul_close S ε hwin J I l k
  rw [hp, hq] at h1 h2
  exact ((h1.trans (msVarObsB_comm_of_shared_constraint S ε hwin i q p)).trans
    h2.symm).mono (by linarith)

/-- Winning probability alone supplies a unit auxiliary vector for the
one-way pair of local swap isometries, with Euclidean error `155904 * sqrt ε`.
No agreement between the two bare-variable families is assumed. -/
theorem ms_one_way_dilated_state_estimate (S : Strategy msGame) (ε : ℝ)
    (hwin : 1 - ε ≤ S.value) :
    ∃ r : EuclideanSpace ℂ ((msDilatedStrategy S).ιA × (msDilatedStrategy S).ιB),
      ‖r‖ = 1 ∧
      ‖isometryTensor (msAliceOneWaySwapIsometry S) (msBobTwoQubitSwapIsometry S)
            (msDilatedStrategy S).ψ -
          reindexState prodShuffle (vecTensor (eprState (Fin 2 → ZMod 2)) r)‖ ≤
        155904 * Real.sqrt ε := by
  have hs := Real.sqrt_nonneg ε
  have hcell (i : Fin 6) (k : Fin 3) :=
    (msCellObsA_close_msVarObsB S ε hwin i k).mono
      (show 12 * Real.sqrt ε ≤ 672 * Real.sqrt ε by linarith)
  have hcomm (I J : Fin 6) (k l : Fin 3) (i : Fin 6) (p q : Fin 3)
      (hp : msConstraintVars I k = msConstraintVars i p)
      (hq : msConstraintVars J l = msConstraintVars i q) :=
    (msCellObsA_comm_of_shared_constraint S ε hwin I J k l i p q hp hq).mono
      (show 144 * Real.sqrt ε ≤ 672 * Real.sqrt ε by linarith)
  have hb (i : Fin 6) (p q : Fin 3) :=
    (msVarObsB_comm_of_shared_constraint S ε hwin i p q).mono
      (show 96 * Real.sqrt ε ≤ 672 * Real.sqrt ε by linarith)
  have hr : ∃ r : EuclideanSpace ℂ
      ((msDilatedStrategy S).ιA × (msDilatedStrategy S).ιB),
      ‖isometryTensor (msAliceOneWaySwapIsometry S) (msBobTwoQubitSwapIsometry S)
            (msDilatedStrategy S).ψ -
          reindexState prodShuffle (vecTensor (eprState (Fin 2 → ZMod 2)) r)‖ ≤
        116 * (672 * Real.sqrt ε) := by
    refine exists_residual_of_two_pairs
      (msLocalCellObsA S 0 0) (msLocalCellObsA S 1 1)
      (msLocalCellObsA S 0 1) (msLocalCellObsA S 1 0)
      (msLocalVarObsB S 0) (msLocalVarObsB S 4)
      (msLocalVarObsB S 1) (msLocalVarObsB S 3)
      (isBinaryObservable_msLocalCellObsA S 0 0)
      (isBinaryObservable_msLocalCellObsA S 1 1)
      (isBinaryObservable_msLocalCellObsA S 0 1)
      (isBinaryObservable_msLocalCellObsA S 1 0)
      (isBinaryObservable_msLocalVarObsB S 0) (isBinaryObservable_msLocalVarObsB S 4)
      (isBinaryObservable_msLocalVarObsB S 1) (isBinaryObservable_msLocalVarObsB S 3)
      (msDilatedStrategy S).ψ (672 * Real.sqrt ε) (by positivity)
      (hcell 0 0) (hcell 1 1) (hcell 0 1) (hcell 1 0) ?_ ?_ ?_ ?_ ?_ ?_
      ?_ ?_ ?_ ?_
    · rw [← heteroKron_left_anticommutator]
      exact msCellObsA_first_pair_anticommute S ε hwin
    · rw [← heteroKron_left_anticommutator]
      exact (msCellObsA_second_pair_anticommute S ε hwin).mono (by linarith)
    · rw [← heteroKron_left_commutator]
      exact hcomm 0 0 1 0 0 1 0 rfl rfl
    · rw [← heteroKron_left_commutator]
      exact hcomm 0 1 1 1 4 0 1 (by decide) (by decide)
    · rw [← heteroKron_left_commutator]
      exact hcomm 1 0 0 0 3 1 0 (by decide) (by decide)
    · rw [← heteroKron_left_commutator]
      exact hcomm 1 1 0 1 1 0 1 rfl rfl
    · rw [← heteroKron_right_commutator]
      exact hb 0 1 0
    · rw [← heteroKron_right_commutator]
      exact hb 4 0 1
    · rw [← heteroKron_right_commutator]
      exact hb 3 1 0
    · rw [← heteroKron_right_commutator]
      exact hb 1 0 1
  obtain ⟨r0, hr0⟩ := hr
  have hu : ‖isometryTensor (msAliceOneWaySwapIsometry S)
      (msBobTwoQubitSwapIsometry S) (msDilatedStrategy S).ψ‖ = 1 := by
    rw [norm_isometryTensor, (msDilatedStrategy S).ψ_norm]
  obtain ⟨r, hrnorm, hr⟩ := exists_unit_residual (V := Fin 2 → ZMod 2) _ hu
    (msDilatedStrategy S).ψ (msDilatedStrategy S).ψ_norm _ r0 hr0
  exact ⟨r, hrnorm, hr.trans (by ring_nf; rfl)⟩

end

end MIPStarRE.QPBT.MagicSquareRigidity
