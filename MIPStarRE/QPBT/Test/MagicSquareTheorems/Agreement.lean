import MIPStarRE.QPBT.Test.MagicSquareTheorems.OneWay
import MIPStarRE.QPBT.Test.MagicSquareTheorems.Rigidity.OriginalConsistency

/-!
# Separate agreement transfer for Magic Square extraction

Agreement affects the other player's variable estimates linearly in squared
distance. It does not enlarge the value-only state or one-way estimates.

## References

`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:620-646`,
`docs/paper-gaps/qpbt_ms-rigidity-symmetric-strategies.tex`, issue #701.
-/

open scoped BigOperators Matrix MatrixOrder ComplexOrder

namespace MIPStarRE.QPBT

open MIPStarRE.LDT hiding Measurement
open MIPStarRE.Quantum MagicSquareRigidity DistanceCalculus

noncomputable section

/-- The two ideal Pauli effects act identically on the two extracted EPR
registers, with arbitrary auxiliary registers in local player order. -/
theorem idealMsState_pauli_actions_eq {I J : Type*}
    [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
    (aux : EuclideanSpace ℂ (I × J)) (W : PauliKind) (b : ZMod 2) :
    applyOperatorToState
        (heteroKron (heteroKron (idealMagicBitProj W b) (1 : Op I))
          (1 : Op ((Fin 2 → ZMod 2) × J))) (idealMsState aux) =
      applyOperatorToState
        (heteroKron (1 : Op ((Fin 2 → ZMod 2) × I))
          (heteroKron (idealMagicBitProj W b) (1 : Op J))) (idealMsState aux) := by
  have ht : (idealMagicBitProj W b)ᵀ = idealMagicBitProj W b := by
    simp only [idealMagicBitProj, Matrix.transpose_sum]
    apply Finset.sum_congr rfl
    intro e _
    split_ifs <;> simp [pauliProj_transpose]
  ext p
  simp only [applyOperatorToState, Matrix.toEuclideanLin, Matrix.toLpLin_apply,
    Matrix.mulVec, dotProduct, Fintype.sum_prod_type]
  simp [heteroKron, Matrix.kronecker, Matrix.one_apply, idealMsState, reindexState,
    vecTensor, eprState, prodShuffle, mul_ite, ite_mul, Prod.ext_iff, ite_and]
  rw [show idealMagicBitProj W b p.2.1 p.1.1 = idealMagicBitProj W b p.1.1 p.2.1 from
    congrFun (congrFun ht p.1.1) p.2.1]
  simp

/-- Transfer an ideal measurement comparison across the players. The source
distance is measured on the original state and enters linearly. -/
theorem ms_ideal_measurement_transfer (S : Strategy msGame) (w : MsRigidityWitness S)
    (A : Measurement (ZMod 2) S.ιA) (B : Measurement (ZMod 2) S.ιB)
    (W : PauliKind) (s : ℝ)
    (hs : ‖isometryTensor w.φA w.φB S.ψ - idealMsState w.aux‖ ≤ s) :
    opFamilyDistSq (uniformDistribution Unit)
      (fun _ b => heteroKron (conjIsometry w.φA (A.effect b)) 1)
      (fun _ b => heteroKron (heteroKron (idealMagicBitProj W b) (1 : Op w.ιA'')) 1)
      (idealMsState w.aux) ≤ 24 * s ^ 2 +
      3 * opFamilyDistSq (uniformDistribution Unit)
        (fun _ b => heteroKron (A.effect b) 1)
        (fun _ b => heteroKron 1 (B.effect b)) S.ψ +
      3 * opFamilyDistSq (uniformDistribution Unit)
        (fun _ b => heteroKron 1 (conjIsometry w.φB (B.effect b)))
        (fun _ b => heteroKron 1 (heteroKron (idealMagicBitProj W b) (1 : Op w.ιB'')))
        (idealMsState w.aux) := by
  let u := isometryTensor w.φA w.φB S.ψ
  let v := idealMsState w.aux
  let P (b : ZMod 2) := heteroKron (conjIsometry w.φA (A.effect b))
    (1 : Op ((Fin 2 → ZMod 2) × w.ιB''))
  let Q (b : ZMod 2) := heteroKron (1 : Op ((Fin 2 → ZMod 2) × w.ιA''))
    (conjIsometry w.φB (B.effect b))
  let IA (b : ZMod 2) := heteroKron
    (heteroKron (idealMagicBitProj W b) (1 : Op w.ιA''))
      (1 : Op ((Fin 2 → ZMod 2) × w.ιB''))
  let IB (b : ZMod 2) := heteroKron (1 : Op ((Fin 2 → ZMod 2) × w.ιA''))
    (heteroKron (idealMagicBitProj W b) (1 : Op w.ιB''))
  have hp (b : ZMod 2) :
      ‖applyOperatorToState (P b - IA b) v‖ ^ 2 ≤
        3 * ((2 * s) ^ 2 +
          ‖applyOperatorToState (heteroKron (A.effect b) 1 -
            heteroKron 1 (B.effect b)) S.ψ‖ ^ 2 +
          ‖applyOperatorToState (Q b - IB b) v‖ ^ 2) := by
    have hsplit : applyOperatorToState (P b - IA b) v =
        applyOperatorToState (P b - Q b) (v - u) +
          applyOperatorToState (P b - Q b) u +
            applyOperatorToState (Q b - IB b) v := by
      simp only [applyOperatorToState_sub, applyOperatorToState_sub_op]
      have he := idealMsState_pauli_actions_eq w.aux W b
      change applyOperatorToState (IA b) v = applyOperatorToState (IB b) v at he
      rw [he]
      abel
    have hsmall : ‖applyOperatorToState (P b - Q b) (v - u)‖ ≤ 2 * s := by
      refine (norm_applyOperatorToState_sub_le
        (conjTranspose_mul_le_one_leftTensor (conjTranspose_mul_le_one_conjIsometry _
          (conjTranspose_mul_le_one_of_effect A b)))
        (conjTranspose_mul_le_one_rightTensor (conjTranspose_mul_le_one_conjIsometry _
          (conjTranspose_mul_le_one_of_effect B b))) _).trans ?_
      have hvu : ‖v - u‖ ≤ s := by rwa [norm_sub_rev]
      linarith
    have htransport : ‖applyOperatorToState (P b - Q b) u‖ =
        ‖applyOperatorToState (heteroKron (A.effect b) 1 -
          heteroKron 1 (B.effect b)) S.ψ‖ := by
      dsimp only [P, Q, u]
      rw [applyOperatorToState_sub_op, applyOperatorToState_leftTensor_conjIsometry,
        applyOperatorToState_rightTensor_conjIsometry]
      simp only [isometryTensor_eq_toEuclideanLin, ← map_sub]
      rw [← isometryTensor_eq_toEuclideanLin, norm_isometryTensor,
        applyOperatorToState_sub_op]
    simp only [mul_add]
    apply sq_le_three_mul_of_le (norm_nonneg _)
    rw [hsplit]
    exact ((norm_add_le _ _).trans
      (add_le_add ((norm_add_le _ _).trans
        (add_le_add hsmall (le_of_eq htransport))) (le_refl _)))
  simp only [opFamilyDistSq_uniform_unit]
  calc _ ≤ ∑ b : ZMod 2, 3 * ((2 * s) ^ 2 +
          ‖applyOperatorToState (heteroKron (A.effect b) 1 -
            heteroKron 1 (B.effect b)) S.ψ‖ ^ 2 +
          ‖applyOperatorToState (Q b - IB b) v‖ ^ 2) :=
        Finset.sum_le_sum fun b _ => hp b
    _ = _ := by
      simp only [Finset.sum_add_distrib, ← Finset.mul_sum,
        Finset.sum_const, Finset.card_univ, ZMod.card, nsmul_eq_mul]
      ring

/-- The missing variable comparison costs its actual agreement defect, with
no square root of that defect. This theorem changes no state estimate. -/
theorem ms_variable_distance_le_agreement (S : Strategy msGame)
    (w : MsRigidityWitness S) (j : Fin 9) (W : PauliKind) (s : ℝ)
    (hs : ‖isometryTensor w.φA w.φB S.ψ - idealMsState w.aux‖ ≤ s) :
    msOperatorDistanceA S w j W ≤ 24 * s ^ 2 +
      3 * msVariableConsistencyDefect S j + 3 * msOperatorDistanceB S w j W :=
  ms_ideal_measurement_transfer S w ((S.A (.var j)).postprocess msBitOrZero)
    ((S.B (.var j)).postprocess msBitOrZero) W s hs

/-- Value-only one-way extraction with a separate bound for Alice's variables.
The exact agreement distances occur only in the two Alice measurement bounds. -/
theorem exists_ms_one_way_rigidity_with_agreement (S : Strategy msGame)
    (ε : ℝ) (hε : 0 ≤ ε) (hwin : 1 - ε ≤ S.value) :
    ∃ w : MsRigidityWitness S,
      ‖isometryTensor w.φA w.φB S.ψ - idealMsState w.aux‖ ≤ 155904 * Real.sqrt ε ∧
      (∀ W : PauliKind, msOperatorDistanceB S w (msPauliCell W) W ≤ 2 * 10 ^ 12 * ε) ∧
      ∀ W : PauliKind, msOperatorDistanceA S w (msPauliCell W) W ≤
        7 * 10 ^ 12 * ε + 3 * msVariableConsistencyDefect S (msPauliCell W) := by
  obtain ⟨w, hs, hb⟩ := exists_ms_one_way_rigidity S ε hε hwin
  refine ⟨w, hs, hb, fun W => ?_⟩
  have ht := ms_variable_distance_le_agreement S w (msPauliCell W) W _ hs
  have hsq := Real.sq_sqrt hε
  nlinarith [hb W, ht]

/-- Alice's completed constraint-read measurement distance. Wrong-form
single-bit answers are assigned zero by `constraintBitOrZero`. -/
def msConstraintOperatorDistanceA (S : Strategy msGame) (w : MsRigidityWitness S)
    (i : Fin 6) (k : Fin 3) (W : PauliKind) : ℝ :=
  opFamilyDistSq (uniformDistribution Unit)
    (fun _ b => heteroKron (conjIsometry w.φA
      (((S.A (.constraint i)).postprocess (constraintBitOrZero k)).effect b)) 1)
    (fun _ b => heteroKron (heteroKron (idealMagicBitProj W b) (1 : Op w.ιA'')) 1)
    (idealMsState w.aux)

/-- The one-way constraint-read estimate follows from the sampled incidence,
with no agreement premise about Alice's bare-variable measurements. -/
theorem ms_constraint_distance_A_le (S : Strategy msGame) (w : MsRigidityWitness S)
    (ε s : ℝ) (hwin : 1 - ε ≤ S.value)
    (hs : ‖isometryTensor w.φA w.φB S.ψ - idealMsState w.aux‖ ≤ s)
    (i : Fin 6) (k : Fin 3) (W : PauliKind) :
    msConstraintOperatorDistanceA S w i k W ≤ 216 * ε + 24 * s ^ 2 +
      3 * msOperatorDistanceB S w (msConstraintVars i k) W := by
  refine (ms_ideal_measurement_transfer S w
    ((S.A (.constraint i)).postprocess (constraintBitOrZero k))
    ((S.B (.var (msConstraintVars i k))).postprocess msBitOrZero) W s hs).trans ?_
  simp only [msOperatorDistanceB, opFamilyDistSq_uniform_unit]
  have hd := ms_original_cell_distance_forward S ε hwin i k
  linarith only [hd]

/-- The full completed one-way comparison: the same value-only witness
compares Bob's variables and Alice's constraint-read counterparts. -/
theorem exists_ms_one_way_rigidity_with_constraints (S : Strategy msGame)
    (ε : ℝ) (hε : 0 ≤ ε) (hwin : 1 - ε ≤ S.value) :
    ∃ w : MsRigidityWitness S,
      ‖isometryTensor w.φA w.φB S.ψ - idealMsState w.aux‖ ≤ 155904 * Real.sqrt ε ∧
      (∀ W : PauliKind, msOperatorDistanceB S w (msPauliCell W) W ≤ 2 * 10 ^ 12 * ε) ∧
      msConstraintOperatorDistanceA S w 0 0 .X ≤ 7 * 10 ^ 12 * ε ∧
      msConstraintOperatorDistanceA S w 1 1 .Z ≤ 7 * 10 ^ 12 * ε := by
  obtain ⟨w, hs, hb⟩ := exists_ms_one_way_rigidity S ε hε hwin
  refine ⟨w, hs, hb, ?_, ?_⟩
  · have ht := ms_constraint_distance_A_le S w ε _ hwin hs 0 0 .X
    have hB := hb .X
    change msOperatorDistanceB S w 0 .X ≤ _ at hB
    change msConstraintOperatorDistanceA S w 0 0 .X ≤
      216 * ε + 24 * (155904 * Real.sqrt ε) ^ 2 +
        3 * msOperatorDistanceB S w 0 .X at ht
    nlinarith [Real.sq_sqrt hε]
  · have ht := ms_constraint_distance_A_le S w ε _ hwin hs 1 1 .Z
    have hB := hb .Z
    change msOperatorDistanceB S w 4 .Z ≤ _ at hB
    change msConstraintOperatorDistanceA S w 1 1 .Z ≤
      216 * ε + 24 * (155904 * Real.sqrt ε) ^ 2 +
        3 * msOperatorDistanceB S w 4 .Z at ht
    nlinarith [Real.sq_sqrt hε]

end

end MIPStarRE.QPBT
