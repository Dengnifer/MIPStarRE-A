import MIPStarRE.QPBT.Test.MagicSquareTheorems
import MIPStarRE.QPBT.Test.MagicSquareTheorems.Rigidity.OneWayState

/-!
# One-way Magic Square measurement extraction

The state and Bob's distinguished variable measurements can be extracted using
winning probability alone. Alice's extractor uses constraint measurements.
The squared measurement errors retain order `ε`, separately from the Euclidean
state error of order `sqrt ε`.

## References

`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:620-652`,
`docs/paper-gaps/qpbt_ms-rigidity-symmetric-strategies.tex`, issue #701.
This is the one-way scope of the cited self-test, not the refuted simultaneous
four-variable conclusion.
-/

open scoped BigOperators Matrix MatrixOrder ComplexOrder

namespace MIPStarRE.QPBT

open MIPStarRE.LDT MIPStarRE.Quantum MagicSquareRigidity

noncomputable section

namespace MagicSquareRigidity

/-- The two distinguished cells associated with the extracted Pauli kinds.
The indices are zero-based: the paper uses variables `1` and `5`. -/
def msPauliCell : PauliKind → Fin 9
  | .X => 0
  | .Z => 4

/-- Bob's swap intertwines his first pair independently of Alice's choice of
isometry. This form permits the one-way constraint-based extractor on Alice. -/
theorem norm_ms_one_way_effect_defect_B (S : Strategy msGame) (W : PauliKind)
    (b : ZMod 2) :
    ‖applyOperatorToState
        (heteroKron (1 : Op ((Fin 2 → ZMod 2) × (msDilatedStrategy S).ιA))
          (heteroKron (reflectionEffect (twoQubitPauliObs W) b) 1))
        (isometryTensor (msAliceOneWaySwapIsometry S) (msBobTwoQubitSwapIsometry S)
          (msDilatedStrategy S).ψ) -
      isometryTensor (msAliceOneWaySwapIsometry S) (msBobTwoQubitSwapIsometry S)
        (applyOperatorToState
          (heteroKron 1 (reflectionEffect (msLocalVarObsB S (msPauliCell W)) b))
          (msDilatedStrategy S).ψ)‖ ≤
      ‖applyOperatorToState (msJointAnticommutatorB S) (msDilatedStrategy S).ψ‖ := by
  let V := msBobTwoQubitSwapIsometry S
  let G := msLocalVarObsB S 0 * msLocalVarObsB S 4 +
    msLocalVarObsB S 4 * msLocalVarObsB S 0
  have hF : ∃ c : ℝ, 0 ≤ c ∧ c ≤ 1 ∧
      (heteroKron (twoQubitPauliObs W) (1 : Op (msDilatedStrategy S).ιB) *
          isometryMatrix V - isometryMatrix V * msLocalVarObsB S (msPauliCell W))ᴴ *
        (heteroKron (twoQubitPauliObs W) (1 : Op (msDilatedStrategy S).ιB) *
          isometryMatrix V - isometryMatrix V * msLocalVarObsB S (msPauliCell W)) =
        (c : ℂ) • (Gᴴ * G) := by
    cases W with
    | X =>
      refine ⟨1 / 2, by norm_num, by norm_num, ?_⟩
      have h := twoSwap_shift_defect_conjTranspose_mul (msLocalVarObsB S 0)
        (msLocalVarObsB S 4) (msLocalVarObsB S 1) (msLocalVarObsB S 3)
        (isBinaryObservable_msLocalVarObsB S 0) (isBinaryObservable_msLocalVarObsB S 4)
        (isBinaryObservable_msLocalVarObsB S 1) (isBinaryObservable_msLocalVarObsB S 3)
      rw [← isometryMatrix_msBobTwoQubitSwapIsometry] at h
      simpa [V, G, msPauliCell] using h
    | Z =>
      refine ⟨0, by norm_num, by norm_num, ?_⟩
      have h := twoSwap_matrix_intertwines_Z (msLocalVarObsB S 0)
        (msLocalVarObsB S 4) (msLocalVarObsB S 1) (msLocalVarObsB S 3)
        (isBinaryObservable_msLocalVarObsB S 0) (isBinaryObservable_msLocalVarObsB S 4)
        (isBinaryObservable_msLocalVarObsB S 1) (isBinaryObservable_msLocalVarObsB S 3)
      rw [← isometryMatrix_msBobTwoQubitSwapIsometry] at h
      simp only [msPauliCell, V, h, Matrix.conjTranspose_zero, Matrix.zero_mul,
        Complex.ofReal_zero, zero_smul]
  obtain ⟨c, hc0, hc1, hF⟩ := hF
  have hE := reflectionEffect_defect_conjTranspose_mul
    (heteroKron (twoQubitPauliObs W) (1 : Op (msDilatedStrategy S).ιB))
    (isometryMatrix V) (msLocalVarObsB S (msPauliCell W)) b _ _ hF
  rw [← reflectionEffect_heteroKron_left] at hE
  have he : (4 : ℂ)⁻¹ * (c : ℂ) = ((c / 4 : ℝ) : ℂ) := by push_cast; ring
  rw [he] at hE
  have hsq := norm_sq_rightTensor_isometryTensor_defect (msAliceOneWaySwapIsometry S)
    V (heteroKron (reflectionEffect (twoQubitPauliObs W) b) 1)
    (reflectionEffect (msLocalVarObsB S (msPauliCell W)) b) G (c / 4) hE
    (msDilatedStrategy S).ψ
  apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  change _ ≤ ‖applyOperatorToState (heteroKron 1 G) (msDilatedStrategy S).ψ‖ ^ 2
  calc _ = c / 4 *
        ‖applyOperatorToState (heteroKron 1 G) (msDilatedStrategy S).ψ‖ ^ 2 := hsq
    _ ≤ _ := mul_le_of_le_one_left (sq_nonneg _) (by linarith)

/-- On the ideal extracted state, Bob's dilated effect errors are controlled
by his anticommutator and the value-only state error. -/
theorem ms_one_way_dilated_operator_distance_B (S : Strategy msGame) (ε : ℝ)
    (hwin : 1 - ε ≤ S.value) (W : PauliKind)
    (r : EuclideanSpace ℂ ((msDilatedStrategy S).ιA × (msDilatedStrategy S).ιB))
    (hξ : ‖isometryTensor (msAliceOneWaySwapIsometry S) (msBobTwoQubitSwapIsometry S)
        (msDilatedStrategy S).ψ - idealMsState r‖ ≤ 155904 * Real.sqrt ε) :
    opFamilyDistSq (uniformDistribution Unit)
      (fun _ b => heteroKron 1 (conjIsometry (msBobTwoQubitSwapIsometry S)
        ((((msDilatedStrategy S).B (.var (msPauliCell W))).postprocess
          msBitOrZero).effect b)))
      (fun _ b => heteroKron 1 (heteroKron (idealMagicBitProj W b) 1))
      (idealMsState r) ≤ 2 * (312432 * Real.sqrt ε) ^ 2 := by
  rw [opFamilyDistSq_uniform_unit]
  refine sum_sq_le_two_mul _ _ fun b => ?_
  have h := norm_applyOperatorToState_sub_le_of_close
    (heteroKron 1 (conjIsometry (msBobTwoQubitSwapIsometry S)
      ((((msDilatedStrategy S).B (.var (msPauliCell W))).postprocess
        msBitOrZero).effect b)))
    (heteroKron 1 (heteroKron (idealMagicBitProj W b) 1))
    (isometryTensor (msAliceOneWaySwapIsometry S) (msBobTwoQubitSwapIsometry S)
      (msDilatedStrategy S).ψ) (idealMsState r) (624 * Real.sqrt ε)
    (155904 * Real.sqrt ε)
    (conjTranspose_mul_le_one_rightTensor
      (conjTranspose_mul_le_one_conjIsometry _
        (conjTranspose_mul_le_one_dilatedEffectB S _ _ b)))
    (conjTranspose_mul_le_one_rightTensor
      (conjTranspose_mul_le_one_leftTensor
        (conjTranspose_mul_le_one_sum_ite_pauliProj (K := ZMod 2) (ι := Fin 2) W
          (fun e => e 0) b))) ?_ hξ
  · linarith
  · rw [applyOperatorToState_sub_op, applyOperatorToState_rightTensor_conjIsometry,
      norm_sub_rev, idealMagicBitProj, sum_ite_pauliProj_eq_reflectionEffect,
      dilatedEffect_var_B_eq]
    exact (norm_ms_one_way_effect_defect_B S W b).trans
      (norm_msJointAnticommutatorB_le S ε hwin)

end MagicSquareRigidity

/-- Value-only one-way extraction: a common witness extracts the state and
Bob's two completed variable measurements. Alice's isometry is constructed
from constraint measurements. The reverse orientation may have a different
witness. Squared effect errors are `O(ε)`; no agreement hypothesis occurs.

**Scope restriction:** This is the one-way conclusion underlying the cited
self-test, not the printed four-variable assertion. See
`docs/paper-gaps/qpbt_ms-rigidity-symmetric-strategies.tex`, issue #701. -/
theorem exists_ms_one_way_rigidity (S : Strategy msGame) (ε : ℝ) (hε : 0 ≤ ε)
    (hwin : 1 - ε ≤ S.value) :
    ∃ w : MsRigidityWitness S,
      ‖isometryTensor w.φA w.φB S.ψ - idealMsState w.aux‖ ≤ 155904 * Real.sqrt ε ∧
      ∀ W : PauliKind, msOperatorDistanceB S w (msPauliCell W) W ≤ 2 * 10 ^ 12 * ε := by
  obtain ⟨r, hrnorm, hstate⟩ := ms_one_way_dilated_state_estimate S ε hwin
  refine ⟨{ ιA'' := (msDilatedStrategy S).ιA
            ιB'' := (msDilatedStrategy S).ιB
            φA := (msAliceOneWaySwapIsometry S).comp (naimarkEmbedding S.ιA MsAnswer)
            φB := (msBobTwoQubitSwapIsometry S).comp (naimarkEmbedding S.ιB MsAnswer)
            aux := r
            aux_norm := hrnorm }, ?_, ?_⟩
  · exact (le_of_eq (ms_state_transfer S _ _ _)).trans hstate
  · intro W
    have ht := ms_effect_transfer_B S (msAliceOneWaySwapIsometry S)
      (msBobTwoQubitSwapIsometry S) (idealMsState r)
      (fun b => heteroKron 1 (heteroKron (idealMagicBitProj W b) 1)) ε
      (155904 * Real.sqrt ε) hwin (msPauliCell W) hstate
    have hd := ms_one_way_dilated_operator_distance_B S ε hwin W r hstate
    dsimp only [msOperatorDistanceB]
    have hs := Real.sq_sqrt hε
    refine ht.trans ?_
    calc _ ≤ 3 * (2 * (312432 * Real.sqrt ε) ^ 2) + 216 * ε +
          24 * (155904 * Real.sqrt ε) ^ 2 := by
            gcongr
            exact hd
      _ ≤ _ := by nlinarith only [hε, hs]

end

end MIPStarRE.QPBT
