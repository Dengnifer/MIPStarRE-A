import MIPStarRE.QPBT.Observables.WinImplications.LowDegree
import MIPStarRE.QPBT.Observables.WinImplications.Interchange
import MIPStarRE.QPBT.Observables.Defs
import MIPStarRE.QPBT.Combining.ActualErrorBounds
import MIPStarRE.QPBT.Test.Soundness.NaimarkAssembly
import MIPStarRE.QPBT.Test.Soundness.EpsReduction

/-!
# Transfer from completed to raw Pauli effects

The extraction proof uses the complete Pauli-register measurement obtained by
folding malformed answers into outcome zero. The source theorem instead
compares the raw effects attached to answers of the form `.pauliOutcome u`.
This module bounds the malformed-answer mass by rejection on the two oriented
point/Pauli edges and transfers the completed-family estimates to the raw
families without adding a hypothesis to the source theorem.

## References

Paper `thm:pauli`,
`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:1431-1445`,
and its proof at
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1862-1876`.
-/

open scoped BigOperators Matrix MatrixOrder ComplexOrder

namespace MIPStarRE.QPBT

open MIPStarRE.LDT hiding Measurement
open MIPStarRE.Quantum

noncomputable section

/-- Completing the Pauli-answer measurement changes only outcome zero, where
it adds the total effect of malformed answers. -/
theorem completedPauliEffect_eq_raw_add_wrongForm {P : AdmissibleParams} {ι : Type*}
    [Fintype ι] [DecidableEq ι] (M : Measurement (PauliAnswer P) ι)
    (W : PauliKind) (u : PauliRegister P) :
    (M.postprocess pauliAnswerOrZero).effect u =
      M.effect (.pauliOutcome u) +
        if u = 0 then ProjectiveSetting.wrongFormEffect (.pauli W) M else 0 := by
  classical
  rw [Measurement.postprocess_effect, ProjectiveSetting.wrongFormEffect,
    Finset.sum_filter]
  by_cases hu : u = 0
  · subst u
    simp only [ite_true]
    calc
      (∑ answer, if pauliAnswerOrZero answer = 0 then M.effect answer else 0) =
          ∑ answer, ((if answer = .pauliOutcome 0 then M.effect answer else 0) +
            (if validPauliAnswer (.pauli W) answer = false then M.effect answer else 0)) := by
        apply Finset.sum_congr rfl
        intro answer _
        cases answer <;> simp [pauliAnswerOrZero, validPauliAnswer]
      _ = _ := by
        rw [Finset.sum_add_distrib]
        congr 1
        · simp
        · rw [← Finset.sum_filter]
  · simp only [hu, ite_false, add_zero]
    rw [Finset.sum_eq_single (.pauliOutcome u)]
    · simp [pauliAnswerOrZero]
    · intro answer _ hanswer
      cases answer with
      | value _ | alinePoly _ | dlinePoly _ | pairBits _ | bit _ | msTriple _ =>
          simp only [pauliAnswerOrZero, ite_eq_right_iff]
          intro hzero
          exact (hu hzero.symm).elim
      | pauliOutcome v =>
          simp only [pauliAnswerOrZero, ite_eq_right_iff]
          intro hv
          exact (hanswer (by simp [hv])).elim
    · simp

namespace WinImplications

/-- A strategy winning with probability at least `1 - ε` has average Pauli-edge
rejection probability at most `ε`. -/
theorem pauliRejectionAverage_le_error_of_win {P : AdmissibleParams} {ε : ℝ}
    (S : Strategy (pauliBasisTest P)) (hwin : 1 - ε ≤ S.value) :
    avgOver (uniformDistribution (PauliEdge × PauliSpace P))
        (fun ez => pauliRejectionAt S ez.1 ez.2) ≤ ε := by
  have havg : avgOver (uniformDistribution (PauliEdge × PauliSpace P))
      (fun ez => pauliRejectionAt S ez.1 ez.2) = 1 - S.value := by
    rw [← rejectionEventAverage_eq_one_sub_value S]
    unfold pauliBasisTest pauliQuestionDistribution
    rw [Distribution.avgOver_map]
    rfl
  rw [havg]
  linarith

/-- Rejection on one fixed oriented edge is at most the number of edge types
times the total rejection probability. -/
theorem fixedEdgeRejection_le_error_of_win {P : AdmissibleParams} {ε : ℝ}
    (S : Strategy (pauliBasisTest P)) (hwin : 1 - ε ≤ S.value) (e : PauliEdge) :
    avgOver (uniformDistribution (PauliSpace P)) (pauliRejectionAt S e) ≤
      (Fintype.card PauliEdge : ℝ) * ε := by
  calc
    avgOver (uniformDistribution (PauliSpace P)) (pauliRejectionAt S e) ≤
        (Fintype.card PauliEdge : ℝ) *
          avgOver (uniformDistribution (PauliEdge × PauliSpace P))
            (fun ez => pauliRejectionAt S ez.1 ez.2) := by
      exact avgOver_uniform_fixed_le_card_mul_prod _
        (fun edge z => pauliRejectionAt_nonneg S edge z) e
    _ ≤ (Fintype.card PauliEdge : ℝ) * ε := by
      exact mul_le_mul_of_nonneg_left (pauliRejectionAverage_le_error_of_win S hwin)
        (Nat.cast_nonneg _)

end WinImplications

open DistanceCalculus

/-- Alice's malformed Pauli-answer mass is bounded by rejection on the
Pauli-to-point edge. -/
theorem wrongFormPauliMass_alice_le_error {P : AdmissibleParams} {ε : ℝ}
    (S : Strategy (pauliBasisTest P)) (hwin : 1 - ε ≤ S.value) (W : PauliKind) :
    stateQForm S.ψ
        (heteroKron
          (ProjectiveSetting.wrongFormEffect (.pauli W) (S.A (pauliQuestion P W))) 1) ≤
      (Fintype.card PauliEdge : ℝ) * ε := by
  have hpoint (z : PauliSpace P) :
      stateQForm S.ψ
          (heteroKron
            (ProjectiveSetting.wrongFormEffect (.pauli W) (S.A (pauliQuestion P W))) 1) ≤
        WinImplications.pauliRejectionAt S (WinImplications.pauliPointEdge W) z := by
    have hmass :
        stateQForm S.ψ
            (heteroKron
              (ProjectiveSetting.wrongFormEffect (.pauli W)
                (S.A (pauliQuestion P W))) 1) =
          aliceEventWeight S (pauliQuestion P W)
            (fun a => validPauliAnswer (.pauli W) a = false) := by
      unfold ProjectiveSetting.wrongFormEffect aliceEventWeight
      rw [heteroKron_finset_sum_left, stateQForm_finset_sum, Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro a _
      by_cases ha : validPauliAnswer (.pauli W) a = false
      · simp [ha, stateQForm, aliceOutcomeWeight]
      · simp [ha]
    rw [hmass]
    rw [← outcome_event_weight_left_eq S (pauliQuestion P W)
      ((.point W), pauliCL P (.point W) z)]
    unfold WinImplications.pauliRejectionAt WinImplications.pauliSourceQuestions
    simp only [WinImplications.pauliPointEdge, pauliCL, pauliQuestion]
    apply outcome_event_weight_mono
    intro a b ha
    unfold pauliBasisTest
    simp [pauliWinPredicate, ha]
  calc
    stateQForm S.ψ
        (heteroKron
          (ProjectiveSetting.wrongFormEffect (.pauli W) (S.A (pauliQuestion P W))) 1) =
        avgOver (uniformDistribution (PauliSpace P)) (fun _ =>
          stateQForm S.ψ
            (heteroKron
              (ProjectiveSetting.wrongFormEffect (.pauli W)
                (S.A (pauliQuestion P W))) 1)) := by
      symm
      exact avgOver_uniform_const _
    _ ≤ avgOver (uniformDistribution (PauliSpace P))
        (WinImplications.pauliRejectionAt S (WinImplications.pauliPointEdge W)) := by
      exact avgOver_mono _ _ _ hpoint
    _ ≤ _ := WinImplications.fixedEdgeRejection_le_error_of_win S hwin _

/-- Bob's malformed Pauli-answer mass is bounded by rejection on the
point-to-Pauli edge. -/
theorem wrongFormPauliMass_bob_le_error {P : AdmissibleParams} {ε : ℝ}
    (S : Strategy (pauliBasisTest P)) (hwin : 1 - ε ≤ S.value) (W : PauliKind) :
    stateQForm S.ψ
        (heteroKron 1
          (ProjectiveSetting.wrongFormEffect (.pauli W) (S.B (pauliQuestion P W)))) ≤
      (Fintype.card PauliEdge : ℝ) * ε := by
  have hpoint (z : PauliSpace P) :
      stateQForm S.ψ
          (heteroKron 1
            (ProjectiveSetting.wrongFormEffect (.pauli W) (S.B (pauliQuestion P W)))) ≤
        WinImplications.pauliRejectionAt S (WinImplications.pointPauliEdge W) z := by
    have hmass :
        stateQForm S.ψ
            (heteroKron 1
              (ProjectiveSetting.wrongFormEffect (.pauli W)
                (S.B (pauliQuestion P W)))) =
          bobEventWeight S (pauliQuestion P W)
            (fun b => validPauliAnswer (.pauli W) b = false) := by
      unfold ProjectiveSetting.wrongFormEffect bobEventWeight
      rw [heteroKron_finset_sum_right, stateQForm_finset_sum, Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro b _
      by_cases hb : validPauliAnswer (.pauli W) b = false
      · simp [hb, stateQForm, bobOutcomeWeight]
      · simp [hb]
    rw [hmass]
    rw [← outcome_event_weight_right_eq S
      ((.point W), pauliCL P (.point W) z) (pauliQuestion P W)]
    unfold WinImplications.pauliRejectionAt WinImplications.pauliSourceQuestions
    simp only [WinImplications.pointPauliEdge, pauliCL, pauliQuestion]
    apply outcome_event_weight_mono
    intro a b hb
    unfold pauliBasisTest
    simp [pauliWinPredicate, hb]
  calc
    stateQForm S.ψ
        (heteroKron 1
          (ProjectiveSetting.wrongFormEffect (.pauli W) (S.B (pauliQuestion P W)))) =
        avgOver (uniformDistribution (PauliSpace P)) (fun _ =>
          stateQForm S.ψ
            (heteroKron 1
              (ProjectiveSetting.wrongFormEffect (.pauli W)
                (S.B (pauliQuestion P W))))) := by
      symm
      exact avgOver_uniform_const _
    _ ≤ avgOver (uniformDistribution (PauliSpace P))
        (WinImplications.pauliRejectionAt S (WinImplications.pointPauliEdge W)) := by
      exact avgOver_mono _ _ _ hpoint
    _ ≤ _ := WinImplications.fixedEdgeRejection_le_error_of_win S hwin _

private theorem raw_transfer_liftedAEffect_eq_tensor {P : AdmissibleParams} {G : Game}
    (S : Strategy G) {ιA' ιB' : Type*} [Fintype ιA'] [DecidableEq ιA']
    [Fintype ιB'] [DecidableEq ιB']
    (φA : EuclideanSpace ℂ S.ιA →ₗᵢ[ℂ]
      EuclideanSpace ℂ (ιA' × PauliRegister P)) (M : Op S.ιA) :
    liftedAEffect S (ιB' := ιB') φA M =
      heteroKron (conjIsometry φA M) (1 : Op (ιB' × PauliRegister P)) := by
  ext i j
  simp [liftedAEffect, heteroKron, Matrix.kronecker, Matrix.one_apply]

private theorem raw_transfer_liftedBEffect_eq_tensor {P : AdmissibleParams} {G : Game}
    (S : Strategy G) {ιA' ιB' : Type*} [Fintype ιA'] [DecidableEq ιA']
    [Fintype ιB'] [DecidableEq ιB']
    (φB : EuclideanSpace ℂ S.ιB →ₗᵢ[ℂ]
      EuclideanSpace ℂ (ιB' × PauliRegister P)) (M : Op S.ιB) :
    liftedBEffect S (ιA' := ιA') φB M =
      heteroKron (1 : Op (ιA' × PauliRegister P)) (conjIsometry φB M) := by
  ext i j
  simp [liftedBEffect, heteroKron, Matrix.kronecker, Matrix.one_apply]

private theorem raw_transfer_liftedAEffect_add {P : AdmissibleParams} {G : Game}
    (S : Strategy G) {ιA' ιB' : Type*} [Fintype ιA'] [DecidableEq ιA']
    [Fintype ιB'] [DecidableEq ιB']
    (φA : EuclideanSpace ℂ S.ιA →ₗᵢ[ℂ]
      EuclideanSpace ℂ (ιA' × PauliRegister P)) (A B : Op S.ιA) :
    liftedAEffect S (ιB' := ιB') φA (A + B) =
      liftedAEffect S φA A + liftedAEffect S φA B := by
  rw [raw_transfer_liftedAEffect_eq_tensor, raw_transfer_liftedAEffect_eq_tensor,
    raw_transfer_liftedAEffect_eq_tensor, ← heteroKron_add_left]
  congr 1
  simp [conjIsometry, Matrix.mul_add, Matrix.add_mul]

private theorem raw_transfer_liftedBEffect_add {P : AdmissibleParams} {G : Game}
    (S : Strategy G) {ιA' ιB' : Type*} [Fintype ιA'] [DecidableEq ιA']
    [Fintype ιB'] [DecidableEq ιB']
    (φB : EuclideanSpace ℂ S.ιB →ₗᵢ[ℂ]
      EuclideanSpace ℂ (ιB' × PauliRegister P)) (A B : Op S.ιB) :
    liftedBEffect S (ιA' := ιA') φB (A + B) =
      liftedBEffect S φB A + liftedBEffect S φB B := by
  rw [raw_transfer_liftedBEffect_eq_tensor, raw_transfer_liftedBEffect_eq_tensor,
    raw_transfer_liftedBEffect_eq_tensor, ← heteroKron_add_right]
  congr 1
  simp [conjIsometry, Matrix.mul_add, Matrix.add_mul]

private theorem wrongFormEffect_eq_validity_effect {P : AdmissibleParams} {ι : Type*}
    [Fintype ι] [DecidableEq ι] (M : Measurement (PauliAnswer P) ι)
    (W : PauliKind) :
    ProjectiveSetting.wrongFormEffect (.pauli W) M =
      (M.postprocess (validPauliAnswer (.pauli W))).effect false := by
  rw [ProjectiveSetting.wrongFormEffect, Measurement.postprocess_effect]

private theorem wrongFormEffect_ideal_norm_alice_le {P : AdmissibleParams}
    (S : Strategy (pauliBasisTest P)) (w : PauliSoundnessWitness P S)
    (W : PauliKind) (δ r : ℝ)
    (hstate : ‖isometryTensor w.φA w.φB S.ψ - idealState P w.aux‖ ≤ δ)
    (hmass : stateQForm S.ψ
        (heteroKron
          (ProjectiveSetting.wrongFormEffect (.pauli W) (S.A (pauliQuestion P W))) 1) ≤ r) :
    ‖applyOperatorToState
        (liftedAEffect S w.φA
          (ProjectiveSetting.wrongFormEffect (.pauli W) (S.A (pauliQuestion P W))))
        (idealState P w.aux)‖ ^ 2 ≤ 2 * δ ^ 2 + 2 * r := by
  let M : Measurement (PauliAnswer P) S.ιA := S.A (pauliQuestion P W)
  let E := ProjectiveSetting.wrongFormEffect (.pauli W) M
  let Q := liftedAEffect S (ιB' := w.ιB') w.φA E
  let theta := isometryTensor w.φA w.φB S.ψ
  let Delta := idealState P w.aux
  let N := M.postprocess (validPauliAnswer (.pauli W))
  have hE : E = N.effect false := by
    exact wrongFormEffect_eq_validity_effect M W
  have hEcontr : Eᴴ * E ≤ 1 := by
    rw [hE]
    exact MagicSquareRigidity.conjTranspose_mul_le_one_of_effect N false
  have hQcontr : Qᴴ * Q ≤ 1 := by
    dsimp only [Q]
    rw [raw_transfer_liftedAEffect_eq_tensor]
    exact MagicSquareRigidity.conjTranspose_mul_le_one_leftTensor
      (MagicSquareRigidity.conjTranspose_mul_le_one_conjIsometry w.φA hEcontr)
  have htheta : ‖applyOperatorToState Q theta‖ ^ 2 ≤ r := by
    dsimp only [Q, theta]
    rw [raw_transfer_liftedAEffect_eq_tensor,
      MagicSquareRigidity.applyOperatorToState_leftTensor_conjIsometry,
      MagicSquareRigidity.norm_isometryTensor]
    have hEpos : 0 ≤ E := by rw [hE]; exact N.pos false
    have hEle : E ≤ 1 := by rw [hE]; exact measurement_effect_le_one N false
    have hKpos : 0 ≤ heteroKron E (1 : Op S.ιB) :=
      kronecker_nonneg hEpos (by simp)
    have hKle : heteroKron E (1 : Op S.ιB) ≤ 1 := by
      rw [← Matrix.one_kronecker_one]
      exact kronecker_mono_left hEle (by simp)
    rw [MagicSquareRigidity.norm_applyOperatorToState_sq]
    have hKH : (heteroKron E (1 : Op S.ιB))ᴴ = heteroKron E 1 :=
      (Matrix.nonneg_iff_posSemidef.mp hKpos).isHermitian.eq
    rw [hKH]
    exact (quadratic_form_mono (MIPStarRE.Quantum.sq_le_self hKpos hKle) S.ψ).trans
      hmass
  have hdecomp : applyOperatorToState Q Delta =
      applyOperatorToState Q (Delta - theta) + applyOperatorToState Q theta := by
    simp [applyOperatorToState]
  rw [hdecomp]
  have hfirst : ‖applyOperatorToState Q (Delta - theta)‖ ≤ δ := by
    exact (MagicSquareRigidity.norm_applyOperatorToState_le hQcontr _).trans (by
      rw [norm_sub_rev]
      exact hstate)
  have htri := norm_add_le (applyOperatorToState Q (Delta - theta))
    (applyOperatorToState Q theta)
  have hsquare := pow_le_pow_left₀ (norm_nonneg _) htri 2
  have hfirstsq := pow_le_pow_left₀
    (norm_nonneg (applyOperatorToState Q (Delta - theta))) hfirst 2
  nlinarith [sq_nonneg (‖applyOperatorToState Q (Delta - theta)‖ -
    ‖applyOperatorToState Q theta‖)]

private theorem wrongFormEffect_ideal_norm_bob_le {P : AdmissibleParams}
    (S : Strategy (pauliBasisTest P)) (w : PauliSoundnessWitness P S)
    (W : PauliKind) (δ r : ℝ)
    (hstate : ‖isometryTensor w.φA w.φB S.ψ - idealState P w.aux‖ ≤ δ)
    (hmass : stateQForm S.ψ
        (heteroKron 1
          (ProjectiveSetting.wrongFormEffect (.pauli W) (S.B (pauliQuestion P W)))) ≤ r) :
    ‖applyOperatorToState
        (liftedBEffect S w.φB
          (ProjectiveSetting.wrongFormEffect (.pauli W) (S.B (pauliQuestion P W))))
        (idealState P w.aux)‖ ^ 2 ≤ 2 * δ ^ 2 + 2 * r := by
  let M := S.B (pauliQuestion P W)
  let E := ProjectiveSetting.wrongFormEffect (.pauli W) M
  let Q := liftedBEffect S (ιA' := w.ιA') w.φB E
  let theta := isometryTensor w.φA w.φB S.ψ
  let Delta := idealState P w.aux
  let N := M.postprocess (validPauliAnswer (.pauli W))
  have hE : E = N.effect false := by
    exact wrongFormEffect_eq_validity_effect M W
  have hEcontr : Eᴴ * E ≤ 1 := by
    rw [hE]
    exact MagicSquareRigidity.conjTranspose_mul_le_one_of_effect N false
  have hQcontr : Qᴴ * Q ≤ 1 := by
    dsimp only [Q]
    rw [raw_transfer_liftedBEffect_eq_tensor]
    exact MagicSquareRigidity.conjTranspose_mul_le_one_rightTensor
      (MagicSquareRigidity.conjTranspose_mul_le_one_conjIsometry w.φB hEcontr)
  have htheta : ‖applyOperatorToState Q theta‖ ^ 2 ≤ r := by
    dsimp only [Q, theta]
    rw [raw_transfer_liftedBEffect_eq_tensor,
      MagicSquareRigidity.applyOperatorToState_rightTensor_conjIsometry,
      MagicSquareRigidity.norm_isometryTensor]
    have hEpos : 0 ≤ E := by rw [hE]; exact N.pos false
    have hEle : E ≤ 1 := by rw [hE]; exact measurement_effect_le_one N false
    have hKpos : 0 ≤ heteroKron (1 : Op S.ιA) E :=
      kronecker_nonneg (by simp) hEpos
    have hKle : heteroKron (1 : Op S.ιA) E ≤ 1 := by
      rw [← Matrix.one_kronecker_one]
      exact kronecker_le_kronecker_right_one (by simp) hEle
    rw [MagicSquareRigidity.norm_applyOperatorToState_sq]
    have hKH : (heteroKron (1 : Op S.ιA) E)ᴴ = heteroKron 1 E :=
      (Matrix.nonneg_iff_posSemidef.mp hKpos).isHermitian.eq
    rw [hKH]
    exact (quadratic_form_mono (MIPStarRE.Quantum.sq_le_self hKpos hKle) S.ψ).trans
      hmass
  have hdecomp : applyOperatorToState Q Delta =
      applyOperatorToState Q (Delta - theta) + applyOperatorToState Q theta := by
    simp [applyOperatorToState]
  rw [hdecomp]
  have hfirst : ‖applyOperatorToState Q (Delta - theta)‖ ≤ δ := by
    exact (MagicSquareRigidity.norm_applyOperatorToState_le hQcontr _).trans (by
      rw [norm_sub_rev]
      exact hstate)
  have htri := norm_add_le (applyOperatorToState Q (Delta - theta))
    (applyOperatorToState Q theta)
  have hsquare := pow_le_pow_left₀ (norm_nonneg _) htri 2
  have hfirstsq := pow_le_pow_left₀
    (norm_nonneg (applyOperatorToState Q (Delta - theta))) hfirst 2
  nlinarith [sq_nonneg (‖applyOperatorToState Q (Delta - theta)‖ -
    ‖applyOperatorToState Q theta‖)]

/-- Alice's raw prescribed-answer distance is controlled by the completed
distance, state error, and malformed-answer rejection mass. -/
theorem raw_pauli_operator_distanceA_le_completed {P : AdmissibleParams} {ε δ : ℝ}
    (S : Strategy (pauliBasisTest P)) (hwin : 1 - ε ≤ S.value)
    (w : PauliSoundnessWitness P S)
    (hstate : ‖isometryTensor w.φA w.φB S.ψ - idealState P w.aux‖ ≤ δ)
    (W : PauliKind) :
    rawPauliOperatorDistanceA P S w W ≤
      2 * pauliOperatorDistanceA P S w W + 4 * δ ^ 2 +
        4 * (Fintype.card PauliEdge : ℝ) * ε := by
  let M : Measurement (PauliAnswer P) S.ιA := S.A (pauliQuestion P W)
  let E := ProjectiveSetting.wrongFormEffect (.pauli W) M
  let bad := ‖applyOperatorToState (liftedAEffect S w.φA E)
    (idealState P w.aux)‖ ^ 2
  have hmass := wrongFormPauliMass_alice_le_error S hwin W
  have hbad : bad ≤ 2 * δ ^ 2 + 2 * (Fintype.card PauliEdge : ℝ) * ε := by
    simpa only [bad, E, M, mul_assoc] using
      wrongFormEffect_ideal_norm_alice_le S w W δ _ hstate hmass
  have hpoint (u : PauliRegister P) :
      ‖applyOperatorToState
          (liftedAEffect S w.φA (M.effect (.pauliOutcome u)) -
            pauliProjOnA'' P W u) (idealState P w.aux)‖ ^ 2 ≤
        2 * ‖applyOperatorToState
          (liftedAEffect S w.φA
              ((M.postprocess pauliAnswerOrZero).effect u) -
            pauliProjOnA'' P W u) (idealState P w.aux)‖ ^ 2 +
          if u = 0 then 2 * bad else 0 := by
    by_cases hu : u = 0
    · subst u
      rw [if_pos rfl, completedPauliEffect_eq_raw_add_wrongForm M W 0]
      simp only [ite_true]
      have hvec :
          applyOperatorToState
              (liftedAEffect S w.φA
                  (M.effect (.pauliOutcome 0)) -
                pauliProjOnA'' P W 0) (idealState P w.aux) =
            applyOperatorToState
                (liftedAEffect S w.φA
                    (M.effect (.pauliOutcome 0) + E) -
                  pauliProjOnA'' P W 0) (idealState P w.aux) -
              applyOperatorToState (liftedAEffect S w.φA E)
                (idealState P w.aux) := by
        rw [raw_transfer_liftedAEffect_add]
        simp only [applyOperatorToState, map_sub, LinearMap.sub_apply, map_add,
          LinearMap.add_apply]
        abel
      rw [hvec]
      have htri := norm_sub_le
        (applyOperatorToState
          (liftedAEffect S w.φA
              (M.effect (.pauliOutcome 0) + E) -
            pauliProjOnA'' P W 0) (idealState P w.aux))
        (applyOperatorToState (liftedAEffect S w.φA E) (idealState P w.aux))
      have hsquare := pow_le_pow_left₀ (norm_nonneg _) htri 2
      dsimp only [bad]
      nlinarith [sq_nonneg
        (‖applyOperatorToState
          (liftedAEffect S w.φA
              (M.effect (.pauliOutcome 0) + E) -
            pauliProjOnA'' P W 0) (idealState P w.aux)‖ -
          ‖applyOperatorToState (liftedAEffect S w.φA E) (idealState P w.aux)‖)]
    · rw [if_neg hu, completedPauliEffect_eq_raw_add_wrongForm M W u]
      simp only [hu, ite_false, add_zero]
      nlinarith [sq_nonneg
        ‖applyOperatorToState
          (liftedAEffect S w.φA (M.effect (.pauliOutcome u)) -
            pauliProjOnA'' P W u) (idealState P w.aux)‖]
  unfold rawPauliOperatorDistanceA pauliOperatorDistanceA
  change (∑ u : PauliRegister P,
      ‖applyOperatorToState
        (liftedAEffect S w.φA (M.effect (.pauliOutcome u)) - pauliProjOnA'' P W u)
        (idealState P w.aux)‖ ^ 2) ≤
    2 * (∑ u : PauliRegister P,
      ‖applyOperatorToState
        (liftedAEffect S w.φA ((M.postprocess pauliAnswerOrZero).effect u) -
          pauliProjOnA'' P W u) (idealState P w.aux)‖ ^ 2) +
      4 * δ ^ 2 + 4 * (Fintype.card PauliEdge : ℝ) * ε
  calc
    (∑ u : PauliRegister P,
        ‖applyOperatorToState
          (liftedAEffect S w.φA (M.effect (.pauliOutcome u)) -
            pauliProjOnA'' P W u) (idealState P w.aux)‖ ^ 2) ≤
        ∑ u : PauliRegister P,
          (2 * ‖applyOperatorToState
            (liftedAEffect S w.φA
                ((M.postprocess pauliAnswerOrZero).effect u) -
              pauliProjOnA'' P W u) (idealState P w.aux)‖ ^ 2 +
            if u = 0 then 2 * bad else 0) :=
      Finset.sum_le_sum fun u _ => hpoint u
    _ = 2 * (∑ u : PauliRegister P,
          ‖applyOperatorToState
            (liftedAEffect S w.φA
                ((M.postprocess pauliAnswerOrZero).effect u) -
              pauliProjOnA'' P W u) (idealState P w.aux)‖ ^ 2) + 2 * bad := by
      rw [Finset.sum_add_distrib, ← Finset.mul_sum]
      simp
    _ ≤ 2 * (∑ u : PauliRegister P,
          ‖applyOperatorToState
            (liftedAEffect S w.φA
                ((M.postprocess pauliAnswerOrZero).effect u) -
              pauliProjOnA'' P W u) (idealState P w.aux)‖ ^ 2) +
          2 * (2 * δ ^ 2 + 2 * (Fintype.card PauliEdge : ℝ) * ε) := by
      linarith
    _ = _ := by
      ring

/-- Bob's raw prescribed-answer distance is controlled by the completed
distance, state error, and malformed-answer rejection mass. -/
theorem raw_pauli_operator_distanceB_le_completed {P : AdmissibleParams} {ε δ : ℝ}
    (S : Strategy (pauliBasisTest P)) (hwin : 1 - ε ≤ S.value)
    (w : PauliSoundnessWitness P S)
    (hstate : ‖isometryTensor w.φA w.φB S.ψ - idealState P w.aux‖ ≤ δ)
    (W : PauliKind) :
    rawPauliOperatorDistanceB P S w W ≤
      2 * pauliOperatorDistanceB P S w W + 4 * δ ^ 2 +
        4 * (Fintype.card PauliEdge : ℝ) * ε := by
  let M : Measurement (PauliAnswer P) S.ιB := S.B (pauliQuestion P W)
  let E := ProjectiveSetting.wrongFormEffect (.pauli W) M
  let bad := ‖applyOperatorToState (liftedBEffect S w.φB E)
    (idealState P w.aux)‖ ^ 2
  have hmass := wrongFormPauliMass_bob_le_error S hwin W
  have hbad : bad ≤ 2 * δ ^ 2 + 2 * (Fintype.card PauliEdge : ℝ) * ε := by
    simpa only [bad, E, M, mul_assoc] using
      wrongFormEffect_ideal_norm_bob_le S w W δ _ hstate hmass
  have hpoint (u : PauliRegister P) :
      ‖applyOperatorToState
          (liftedBEffect S w.φB (M.effect (.pauliOutcome u)) -
            pauliProjOnB'' P W u) (idealState P w.aux)‖ ^ 2 ≤
        2 * ‖applyOperatorToState
          (liftedBEffect S w.φB
              ((M.postprocess pauliAnswerOrZero).effect u) -
            pauliProjOnB'' P W u) (idealState P w.aux)‖ ^ 2 +
          if u = 0 then 2 * bad else 0 := by
    by_cases hu : u = 0
    · subst u
      rw [if_pos rfl, completedPauliEffect_eq_raw_add_wrongForm M W 0]
      simp only [ite_true]
      have hvec :
          applyOperatorToState
              (liftedBEffect S w.φB (M.effect (.pauliOutcome 0)) -
                pauliProjOnB'' P W 0) (idealState P w.aux) =
            applyOperatorToState
                (liftedBEffect S w.φB (M.effect (.pauliOutcome 0) + E) -
                  pauliProjOnB'' P W 0) (idealState P w.aux) -
              applyOperatorToState (liftedBEffect S w.φB E)
                (idealState P w.aux) := by
        rw [raw_transfer_liftedBEffect_add]
        simp only [applyOperatorToState, map_sub, LinearMap.sub_apply, map_add,
          LinearMap.add_apply]
        abel
      rw [hvec]
      have htri := norm_sub_le
        (applyOperatorToState
          (liftedBEffect S w.φB (M.effect (.pauliOutcome 0) + E) -
            pauliProjOnB'' P W 0) (idealState P w.aux))
        (applyOperatorToState (liftedBEffect S w.φB E) (idealState P w.aux))
      have hsquare := pow_le_pow_left₀ (norm_nonneg _) htri 2
      dsimp only [bad]
      nlinarith [sq_nonneg
        (‖applyOperatorToState
          (liftedBEffect S w.φB (M.effect (.pauliOutcome 0) + E) -
            pauliProjOnB'' P W 0) (idealState P w.aux)‖ -
          ‖applyOperatorToState (liftedBEffect S w.φB E) (idealState P w.aux)‖)]
    · rw [if_neg hu, completedPauliEffect_eq_raw_add_wrongForm M W u]
      simp only [hu, ite_false, add_zero]
      nlinarith [sq_nonneg
        ‖applyOperatorToState
          (liftedBEffect S w.φB (M.effect (.pauliOutcome u)) -
            pauliProjOnB'' P W u) (idealState P w.aux)‖]
  unfold rawPauliOperatorDistanceB pauliOperatorDistanceB
  change (∑ u : PauliRegister P,
      ‖applyOperatorToState
        (liftedBEffect S w.φB (M.effect (.pauliOutcome u)) - pauliProjOnB'' P W u)
        (idealState P w.aux)‖ ^ 2) ≤
    2 * (∑ u : PauliRegister P,
      ‖applyOperatorToState
        (liftedBEffect S w.φB ((M.postprocess pauliAnswerOrZero).effect u) -
          pauliProjOnB'' P W u) (idealState P w.aux)‖ ^ 2) +
      4 * δ ^ 2 + 4 * (Fintype.card PauliEdge : ℝ) * ε
  calc
    (∑ u : PauliRegister P,
        ‖applyOperatorToState
          (liftedBEffect S w.φB (M.effect (.pauliOutcome u)) -
            pauliProjOnB'' P W u) (idealState P w.aux)‖ ^ 2) ≤
        ∑ u : PauliRegister P,
          (2 * ‖applyOperatorToState
            (liftedBEffect S w.φB
                ((M.postprocess pauliAnswerOrZero).effect u) -
              pauliProjOnB'' P W u) (idealState P w.aux)‖ ^ 2 +
            if u = 0 then 2 * bad else 0) :=
      Finset.sum_le_sum fun u _ => hpoint u
    _ = 2 * (∑ u : PauliRegister P,
          ‖applyOperatorToState
            (liftedBEffect S w.φB
                ((M.postprocess pauliAnswerOrZero).effect u) -
              pauliProjOnB'' P W u) (idealState P w.aux)‖ ^ 2) + 2 * bad := by
      rw [Finset.sum_add_distrib, ← Finset.mul_sum]
      simp
    _ ≤ 2 * (∑ u : PauliRegister P,
          ‖applyOperatorToState
            (liftedBEffect S w.φB
                ((M.postprocess pauliAnswerOrZero).effect u) -
              pauliProjOnB'' P W u) (idealState P w.aux)‖ ^ 2) +
          2 * (2 * δ ^ 2 + 2 * (Fintype.card PauliEdge : ℝ) * ε) := by
      linarith
    _ = _ := by
      ring

/-- Universal scalar used to absorb the completed-to-raw transfer loss. -/
private noncomputable def rawPauliTransferFactor : ℝ :=
  2 + 4 * (Fintype.card PauliEdge : ℝ)

private theorem epsilon_le_deltaQld {P : AdmissibleParams}
    {a b ε : ℝ} (ha : 1 ≤ a) (hb : 0 < b) (hb1 : b < 1)
    (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) :
    ε ≤ deltaQld a b ε P.m P.d P.q := by
  have hmd : (1 : ℝ) ≤ ((P.m * P.d : ℕ) : ℝ) :=
    Nat.one_le_cast.mpr (Nat.mul_pos P.one_le_m P.hd)
  have hmd0 : (0 : ℝ) ≤ ((P.m * P.d : ℕ) : ℝ) := zero_le_one.trans hmd
  have ha0 : 0 ≤ a := zero_le_one.trans ha
  have hpref : 1 ≤ a * ((P.m * P.d : ℕ) : ℝ) ^ a :=
    one_le_mul_of_one_le_of_one_le ha (Real.one_le_rpow hmd ha0)
  have hεpow : ε ≤ ε ^ b := by
    simpa using Real.rpow_le_rpow_of_exponent_ge' hε0 hε1 hb.le hb1.le
  have hq := Real.rpow_nonneg (Nat.cast_nonneg P.q) (-b)
  have htwo := Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 2)
    (-(b * ((P.m * P.d : ℕ) : ℝ)))
  unfold deltaQld
  simp only [Real.rpow_eq_pow]
  nlinarith [mul_nonneg (sub_nonneg.mpr hpref)
    (add_nonneg (add_nonneg (Real.rpow_nonneg hε0 b) hq) htwo)]

private theorem raw_pauli_error_absorb {P : AdmissibleParams}
    {a b ε : ℝ} (ha : 1 ≤ a) (hb : 0 < b) (hb1 : b < 1)
    (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) :
    2 * deltaQld a b ε P.m P.d P.q +
        4 * deltaQld a b ε P.m P.d P.q ^ 2 +
        4 * (Fintype.card PauliEdge : ℝ) * ε ≤
      deltaQld (rawPauliTransferFactor * (21 * a ^ 2)) b ε P.m P.d P.q := by
  let d := deltaQld a b ε P.m P.d P.q
  let K := rawPauliTransferFactor
  have hd : 0 ≤ d := deltaQld_nonneg (zero_le_one.trans ha) hε0
  have hεd : ε ≤ d := epsilon_le_deltaQld ha hb hb1 hε0 hε1
  have hK : 1 ≤ K := by
    dsimp only [K, rawPauliTransferFactor]
    have hcard : (0 : ℝ) ≤ Fintype.card PauliEdge := Nat.cast_nonneg _
    linarith
  have hbase : 3 * d + 6 * d ^ 2 ≤
      deltaQld (21 * a ^ 2) b ε P.m P.d P.q :=
    three_add_six_sq_deltaQld_le ha hb hε0 hε1
  calc
    2 * d + 4 * d ^ 2 + 4 * (Fintype.card PauliEdge : ℝ) * ε ≤
        (2 + 4 * (Fintype.card PauliEdge : ℝ)) * d + 4 * d ^ 2 := by
      have hcard : (0 : ℝ) ≤ Fintype.card PauliEdge := Nat.cast_nonneg _
      nlinarith [mul_nonneg hcard (sub_nonneg.mpr hεd)]
    _ ≤ K * (3 * d + 6 * d ^ 2) := by
      dsimp only [K, rawPauliTransferFactor]
      have hcard : (0 : ℝ) ≤ Fintype.card PauliEdge := Nat.cast_nonneg _
      nlinarith [mul_nonneg hcard hd, mul_nonneg hcard (sq_nonneg d), sq_nonneg d]
    _ ≤ K * deltaQld (21 * a ^ 2) b ε P.m P.d P.q :=
      mul_le_mul_of_nonneg_left hbase (zero_le_one.trans hK)
    _ ≤ deltaQld (K * (21 * a ^ 2)) b ε P.m P.d P.q := by
      exact scale_deltaQld_le (by nlinarith [sq_nonneg a]) hε0 hK

/-- The arbitrary-strategy soundness estimates for the raw prescribed Pauli
answer effects of `thm:pauli`. The completed-family Naimark estimates remain
internal and their transfer loss is absorbed into the existential prefactor. -/
theorem exists_arbitrary_strategy_raw_isometry_bounds :
    ∃ A b : ℝ, 1 ≤ A ∧ 0 < b ∧ b < 1 ∧
      ∀ (P : AdmissibleParams) (ε : ℝ), 0 ≤ ε →
        ∀ S : Strategy (pauliBasisTest P), 1 - ε ≤ S.value →
          ∃ w : PauliSoundnessWitness P S,
            ‖isometryTensor w.φA w.φB S.ψ - idealState P w.aux‖ ≤
                deltaQld A b ε P.m P.d P.q ∧
            (∀ W : PauliKind,
              rawPauliOperatorDistanceA P S w W ≤ deltaQld A b ε P.m P.d P.q) ∧
            (∀ W : PauliKind,
              rawPauliOperatorDistanceB P S w W ≤ deltaQld A b ε P.m P.d P.q) := by
  obtain ⟨a, b, ha, hb, hb1, hcompleted⟩ := exists_arbitrary_strategy_isometry_bounds
  let A := rawPauliTransferFactor * (21 * a ^ 2)
  have hfactor : 1 ≤ rawPauliTransferFactor := by
    dsimp only [rawPauliTransferFactor]
    have hcard : (0 : ℝ) ≤ Fintype.card PauliEdge := Nat.cast_nonneg _
    linarith
  have h21 : 1 ≤ 21 * a ^ 2 := by nlinarith [sq_nonneg a]
  have hA : 1 ≤ A := by
    dsimp only [A]
    calc
      (1 : ℝ) = 1 * 1 := by ring
      _ ≤ rawPauliTransferFactor * (21 * a ^ 2) :=
        mul_le_mul hfactor h21 zero_le_one (zero_le_one.trans hfactor)
  have ha21 : a ≤ 21 * a ^ 2 := by nlinarith [sq_nonneg a]
  have h21A : 21 * a ^ 2 ≤ A := by
    dsimp only [A]
    exact le_mul_of_one_le_left (by positivity) hfactor
  have haA : a ≤ A := ha21.trans h21A
  have hsmall : ∀ (P : AdmissibleParams) (ε : ℝ), 0 ≤ ε → ε ≤ 1 →
      ∀ S : Strategy (pauliBasisTest P), 1 - ε ≤ S.value →
        ∃ w : PauliSoundnessWitness P S,
          ‖isometryTensor w.φA w.φB S.ψ - idealState P w.aux‖ ≤
              deltaQld A b ε P.m P.d P.q ∧
          (∀ W : PauliKind,
            rawPauliOperatorDistanceA P S w W ≤ deltaQld A b ε P.m P.d P.q) ∧
          (∀ W : PauliKind,
            rawPauliOperatorDistanceB P S w W ≤ deltaQld A b ε P.m P.d P.q) := by
    intro P ε hε0 hε1 S hwin
    obtain ⟨w, hstate, hcompletedA, hcompletedB⟩ :=
      hcompleted P ε hε0 hε1 S hwin
    let d := deltaQld a b ε P.m P.d P.q
    have habsorb : 2 * d + 4 * d ^ 2 +
        4 * (Fintype.card PauliEdge : ℝ) * ε ≤
          deltaQld A b ε P.m P.d P.q := by
      dsimp only [d, A]
      exact raw_pauli_error_absorb ha hb hb1 hε0 hε1
    have hmono : d ≤ deltaQld A b ε P.m P.d P.q := by
      dsimp only [d]
      exact deltaQld_mono ha haA le_rfl hb hε0 hε1
    refine ⟨w, hstate.trans hmono, ?_, ?_⟩
    · intro W
      calc
        rawPauliOperatorDistanceA P S w W ≤
            2 * pauliOperatorDistanceA P S w W + 4 * d ^ 2 +
              4 * (Fintype.card PauliEdge : ℝ) * ε :=
          raw_pauli_operator_distanceA_le_completed S hwin w hstate W
        _ ≤ 2 * d + 4 * d ^ 2 + 4 * (Fintype.card PauliEdge : ℝ) * ε := by
          linarith [hcompletedA W]
        _ ≤ _ := habsorb
    · intro W
      calc
        rawPauliOperatorDistanceB P S w W ≤
            2 * pauliOperatorDistanceB P S w W + 4 * d ^ 2 +
              4 * (Fintype.card PauliEdge : ℝ) * ε :=
          raw_pauli_operator_distanceB_le_completed S hwin w hstate W
        _ ≤ 2 * d + 4 * d ^ 2 + 4 * (Fintype.card PauliEdge : ℝ) * ε := by
          linarith [hcompletedB W]
        _ ≤ _ := habsorb
  refine ⟨A, b, hA, hb, hb1, ?_⟩
  intro P ε hε0 S hwin
  rcases le_or_gt ε 1 with hε1 | hε1
  · exact hsmall P ε hε0 hε1 S hwin
  · obtain ⟨w, hstate, hAraw, hBraw⟩ :=
      hsmall P 1 zero_le_one le_rfl S (by simpa using S.value_nonneg)
    have hmono : deltaQld A b 1 P.m P.d P.q ≤
        deltaQld A b ε P.m P.d P.q :=
      deltaQld_mono_epsilon hA hb zero_le_one hε1.le
    exact ⟨w, hstate.trans hmono, fun W => (hAraw W).trans hmono,
      fun W => (hBraw W).trans hmono⟩

end

end MIPStarRE.QPBT
