import MIPStarRE.QPBT.Observables.WinImplications.LowDegree

/-!
# Commuting winning implications

This module proves the exact Pair/W and point-trace consistency bounds on
commuting Pauli tuples.

## References

The commuting-tuple consistency theorems prove items 4 and 5
of `lem:qld-win-implications`
from `references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:192-267`
and `blueprint/src/chapter/ch14_qpbt_observables.tex:505-660`.
-/

open scoped BigOperators Matrix ComplexOrder

namespace MIPStarRE.QPBT

open MIPStarRE.LDT hiding Measurement
open MIPStarRE.Quantum

noncomputable section

namespace WinImplications

/-- Select one component of a Pair answer. -/
def selectedPairBit (W : PauliKind) (bits : ZMod 2 × ZMod 2) : ZMod 2 :=
  match W with
  | .X => bits.1
  | .Z => bits.2

/-- Winning the commuting Pair/W branch forces equality of the selected bits. -/
theorem pairLabels_eq_of_win (P : AdmissibleParams) (W : PauliKind)
    (z : PauliSpace P) (A B : PauliAnswer P)
    (hcomm : IsCommuting (pauliSharedSplit P z).1)
    (hwin : pauliWinPredicate P
      ((.pairW W), pauliCL P (.pairW W) z)
      (.pair, pauliCL P .pair z) A B = true) :
    ProjectiveSetting.pairWAnswerOrZero A =
      selectedPairBit W (ProjectiveSetting.pairAnswerOrZero B) := by
  cases A <;> cases B <;>
    simp only [pauliWinPredicate, validPauliAnswer, Bool.and_true,
      Bool.and_self, Bool.and_false, Bool.false_eq_true, ↓reduceIte,
      reduceCtorEq, decide_eq_true_eq] at hwin
  rename_i bit bits
  simp only [ProjectiveSetting.pairWAnswerOrZero,
    ProjectiveSetting.pairAnswerOrZero]
  have hgamma : pauliPairGamma P (pauliCL P (.pairW W) z) = 0 := by
    change gammaValue P (pauliXBlock z) (pauliZBlock z)
      (pauliRXBlock z) (pauliRZBlock z) = 0 at hcomm
    rw [pauliCL_shared_eq P (.pairW W) rfl]
    change gammaValue P (pauliXBlock z) (pauliZBlock z)
      (pauliRXBlock z) (pauliRZBlock z) = 0
    exact hcomm
  cases W <;>
    simp only [pauliPairCondition, hgamma, ne_eq, not_true_eq_false,
      false_or, selectedPairBit] at hwin ⊢ <;>
    exact hwin.symm

/-- Commuting Pair/W mismatch is contained in rejection. -/
private theorem pairMismatch_le_rejection {P : AdmissibleParams} {ε : ℝ}
    (S : ProjectiveSetting P ε) (W : PauliKind) (z : PauliSpace P)
    (hcomm : IsCommuting (pauliSharedSplit P z).1) :
    outcomeEventWeight S.toStrategy
        ((.pairW W), pauliCL P (.pairW W) z)
        (.pair, pauliCL P .pair z)
        (fun A B => ProjectiveSetting.pairWAnswerOrZero A ≠
          selectedPairBit W (ProjectiveSetting.pairAnswerOrZero B)) ≤
      pauliRejectionAt S.toStrategy
        (pairWPairEdge W) z := by
  apply outcome_event_weight_mono
  intro A B hne
  change pauliWinPredicate P _ _ A B = false
  apply Bool.eq_false_iff.mpr
  intro htrue
  exact hne (pairLabels_eq_of_win P W z A B hcomm htrue)

/-- The commuting consistency defect is the mismatch probability of source answers. -/
private theorem commConsistency_eq_mismatch {P : AdmissibleParams} {ε : ℝ}
    (S : ProjectiveSetting P ε) (W : PauliKind) :
    consistencyDefect (commTupleDist P)
        (fun ω a => heteroKron
          ((S.pairWMeas .alice W ω.1 ω.2.1 ω.2.2.1 ω.2.2.2).effect a) 1)
        (fun ω a => heteroKron 1 ((S.pairComponentMeas .bob W ω).effect a))
        S.toStrategy.ψ =
      avgOver (commTupleDist P) (fun ω =>
        outcomeEventWeight S.toStrategy
          (ProjectiveSetting.pairWQuestion P W ω.1 ω.2.1 ω.2.2.1 ω.2.2.2)
          (ProjectiveSetting.pairQuestion P ω.1 ω.2.1 ω.2.2.1 ω.2.2.2)
          (fun A B => ProjectiveSetting.pairWAnswerOrZero A ≠
            selectedPairBit W (ProjectiveSetting.pairAnswerOrZero B))) := by
  let qA : PauliTuple P → PauliQuestion P := fun ω =>
    ProjectiveSetting.pairWQuestion P W ω.1 ω.2.1 ω.2.2.1 ω.2.2.2
  let qB : PauliTuple P → PauliQuestion P := fun ω =>
    ProjectiveSetting.pairQuestion P ω.1 ω.2.1 ω.2.2.1 ω.2.2.2
  let fA : PauliTuple P → PauliAnswer P → ZMod 2 := fun _ =>
    ProjectiveSetting.pairWAnswerOrZero
  let fB : PauliTuple P → PauliAnswer P → ZMod 2 := fun _ B =>
    selectedPairBit W (ProjectiveSetting.pairAnswerOrZero B)
  have h := consistencyDefect_postprocess_eq_mismatch
    (commTupleDist P) S.toStrategy qA qB fA fB
  have hA : ∀ ω c,
      heteroKron ((S.pairWMeas .alice W ω.1 ω.2.1 ω.2.2.1 ω.2.2.2).effect c)
          (1 : Op S.toStrategy.ιB) =
        heteroKron (((S.toStrategy.A (qA ω)).postprocess (fA ω)).effect c)
          (1 : Op S.toStrategy.ιB) := by
    intro ω c
    rfl
  have hB : ∀ ω c,
      heteroKron (1 : Op S.toStrategy.ιA) ((S.pairComponentMeas .bob W ω).effect c) =
        heteroKron (1 : Op S.toStrategy.ιA)
          (((S.toStrategy.B (qB ω)).postprocess (fB ω)).effect c) := by
    intro ω c
    congr 1
    unfold ProjectiveSetting.pairComponentMeas ProjectiveSetting.pairMeas fB qB
    rw [MIPStarRE.Quantum.Measurement.postprocess_comp]
    rfl
  calc
    _ = consistencyDefect (commTupleDist P)
        (fun ω c => heteroKron
          (((S.toStrategy.A (qA ω)).postprocess (fA ω)).effect c) 1)
        (fun ω c => heteroKron 1
          (((S.toStrategy.B (qB ω)).postprocess (fB ω)).effect c))
        S.toStrategy.ψ := consistencyDefect_congr _ _ _ _ _ _ hA hB
    _ = avgOver (commTupleDist P) (fun ω =>
        outcomeEventWeight S.toStrategy (qA ω) (qB ω)
          (fun A B => fA ω A ≠ fB ω B)) := h
    _ = _ := by rfl

/-- On commuting tuples, Pair/W answers agree with the corresponding
component of Pair answers. This is item 4 of `lem:qld-win-implications`, paper
`14_analysis_of_the_pauli_basis_test.tex:210-231`, blueprint
`ch14_qpbt_observables.tex:567-582`. -/
theorem win_comm :
    ∃ C : ℝ, 1 ≤ C ∧
      ∀ (P : AdmissibleParams) (ε : ℝ) (S : ProjectiveSetting P ε),
      0 ≤ ε → ∀ W : PauliKind,
      consistencyDefect (commTupleDist P)
        (fun ω a => heteroKron
          ((S.pairWMeas .alice W ω.1 ω.2.1 ω.2.2.1 ω.2.2.2).effect a) 1)
        (fun ω a => heteroKron 1 ((S.pairComponentMeas .bob W ω).effect a))
        S.toStrategy.ψ ≤ C * ε := by
  refine ⟨2 * (Fintype.card PauliEdge : ℝ), ?_, ?_⟩
  · have hcard : (1 : ℝ) ≤ Fintype.card PauliEdge := by
      exact_mod_cast (Fintype.card_pos : 0 < Fintype.card PauliEdge)
    linarith
  intro P ε S _ W
  rw [commConsistency_eq_mismatch]
  calc
    _ ≤ 2 * avgOver (uniformDistribution (PauliTuple P)) (fun ω =>
        if IsCommuting ω then
          outcomeEventWeight S.toStrategy
            (ProjectiveSetting.pairWQuestion P W
              ω.1 ω.2.1 ω.2.2.1 ω.2.2.2)
            (ProjectiveSetting.pairQuestion P
              ω.1 ω.2.1 ω.2.2.1 ω.2.2.2)
            (fun A B => ProjectiveSetting.pairWAnswerOrZero A ≠
              selectedPairBit W (ProjectiveSetting.pairAnswerOrZero B))
        else 0) := by
      apply avgOver_comm_le_two_mul_gated
      intro ω
      exact outcome_event_weight_nonneg S.toStrategy _ _ _
    _ ≤ 2 * avgOver (uniformDistribution (PauliSpace P))
        (pauliRejectionAt S.toStrategy
          (pairWPairEdge W)) := by
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      rw [← avgOver_pauliTuple_uniform]
      apply avgOver_mono
      intro z
      by_cases hcomm : IsCommuting (pauliSharedSplit P z).1
      · simp only [if_pos hcomm]
        have hs := pairMismatch_le_rejection S W z hcomm
        rw [pauliCL_shared_eq P (.pairW W) rfl,
          pauliCL_shared_eq P .pair rfl] at hs
        simpa [pauliSharedSplit, ProjectiveSetting.pairWQuestion,
          ProjectiveSetting.pairQuestion]
          using hs
      · simp only [if_neg hcomm]
        exact pauliRejectionAt_nonneg S.toStrategy _ z
    _ ≤ 2 * (Fintype.card PauliEdge : ℝ) * ε := by
      rw [mul_assoc]
      exact mul_le_mul_of_nonneg_left (fixedEdgeRejection_le_error S _) (by norm_num)

/-- Select the point coordinate of a shared Pauli tuple in one basis. -/
def selectedTuplePoint (W : PauliKind) {P : AdmissibleParams}
    (ω : PauliTuple P) : Fin P.m → PauliScalar P :=
  match W with
  | .X => ω.1
  | .Z => ω.2.1

/-- Select the scalar multiplier of a shared Pauli tuple in one basis. -/
def selectedTupleScalar (W : PauliKind) {P : AdmissibleParams}
    (ω : PauliTuple P) : PauliScalar P :=
  match W with
  | .X => ω.2.2.1
  | .Z => ω.2.2.2

/-- The binary trace label extracted from a point answer. -/
def pointTraceLabel (P : AdmissibleParams) (W : PauliKind)
    (ω : PauliTuple P) (A : PauliAnswer P) : ZMod 2 :=
  fixedBinTrace P.model
    (ProjectiveSetting.pointAnswerOrZero A * selectedTupleScalar W ω)

/-- The point coordinate of the low-degree projection is the selected shared block. -/
theorem pauliToLd_point_eq_selected (P : AdmissibleParams) (W : PauliKind)
    (z : PauliSpace P) :
    (pauliToLd P W z).point = selectedTuplePoint W (pauliSharedSplit P z).1 := by
  funext i
  cases W <;> rfl

/-- Winning the commuting point/Pair-W branch forces equality of trace labels. -/
theorem pointPairLabels_eq_of_win (P : AdmissibleParams) (W : PauliKind)
    (z : PauliSpace P) (A B : PauliAnswer P)
    (hcomm : IsCommuting (pauliSharedSplit P z).1)
    (hwin : pauliWinPredicate P
      ((.point W), pauliCL P (.point W) z)
      ((.pairW W), pauliCL P (.pairW W) z) A B = true) :
    fixedBinTrace P.model
        (ProjectiveSetting.pointAnswerOrZero A *
          selectedTupleScalar W (pauliSharedSplit P z).1) =
      ProjectiveSetting.pairWAnswerOrZero B := by
  cases A <;> cases B <;>
    simp only [pauliWinPredicate, validPauliAnswer, Bool.and_true,
      Bool.and_self, Bool.and_false, Bool.false_eq_true, ↓reduceIte,
      reduceCtorEq, decide_eq_true_eq] at hwin
  rename_i a bit
  simp only [ProjectiveSetting.pointAnswerOrZero,
    ProjectiveSetting.pairWAnswerOrZero]
  have hgamma : pauliPairGamma P (pauliCL P (.pairW W) z) = 0 := by
    change gammaValue P (pauliXBlock z) (pauliZBlock z)
      (pauliRXBlock z) (pauliRZBlock z) = 0 at hcomm
    rw [pauliCL_shared_eq P (.pairW W) rfl]
    change gammaValue P (pauliXBlock z) (pauliZBlock z)
      (pauliRXBlock z) (pauliRZBlock z) = 0
    exact hcomm
  rw [pauliCL_shared_eq P (.pairW W) rfl] at hgamma
  rw [pauliCL_shared_eq P (.pairW W) rfl] at hwin
  cases W with
  | X =>
      simp only [pauliPointPairCondition] at hwin
      rcases hwin with hne | heq
      · exact (hne hgamma).elim
      · simpa [selectedTupleScalar, pauliSharedSplit, pauliRXBlock,
          ProjectiveSetting.contentOfTuple] using heq
  | Z =>
      simp only [pauliPointPairCondition] at hwin
      rcases hwin with hne | heq
      · exact (hne hgamma).elim
      · simpa [selectedTupleScalar, pauliSharedSplit, pauliRZBlock,
          ProjectiveSetting.contentOfTuple] using heq

/-- Commuting point-trace/Pair-W mismatch is contained in rejection. -/
theorem pointPairMismatch_le_rejection {P : AdmissibleParams} {ε : ℝ}
    (S : ProjectiveSetting P ε) (W : PauliKind) (z : PauliSpace P)
    (hcomm : IsCommuting (pauliSharedSplit P z).1) :
    outcomeEventWeight S.toStrategy
        ((.point W), pauliCL P (.point W) z)
        ((.pairW W), pauliCL P (.pairW W) z)
        (fun A B =>
          pointTraceLabel P W (pauliSharedSplit P z).1 A ≠
            ProjectiveSetting.pairWAnswerOrZero B) ≤
      pauliRejectionAt S.toStrategy
        (pointPairWEdge W) z := by
  apply outcome_event_weight_mono
  intro A B hne
  change pauliWinPredicate P _ _ A B = false
  apply Bool.eq_false_iff.mpr
  intro htrue
  exact hne (pointPairLabels_eq_of_win P W z A B hcomm htrue)

/-- Point-trace/Pair-W consistency is the mismatch probability of source answers. -/
theorem commConsConsistency_eq_mismatch {P : AdmissibleParams} {ε : ℝ}
    (S : ProjectiveSetting P ε) (W : PauliKind) :
    consistencyDefect (commTupleDist P)
        (fun ω a => heteroKron
          ((S.pointTraceMeas .alice W (selectedTuplePoint W ω)
            (selectedTupleScalar W ω)).effect a) 1)
        (fun ω a => heteroKron 1
          ((S.pairWMeas .bob W ω.1 ω.2.1 ω.2.2.1 ω.2.2.2).effect a))
        S.toStrategy.ψ =
      avgOver (commTupleDist P) (fun ω =>
        outcomeEventWeight S.toStrategy
          (ProjectiveSetting.pointQuestion P W (selectedTuplePoint W ω))
          (ProjectiveSetting.pairWQuestion P W
            ω.1 ω.2.1 ω.2.2.1 ω.2.2.2)
          (fun A B => pointTraceLabel P W ω A ≠
            ProjectiveSetting.pairWAnswerOrZero B)) := by
  let qA : PauliTuple P → PauliQuestion P := fun ω =>
    ProjectiveSetting.pointQuestion P W (selectedTuplePoint W ω)
  let qB : PauliTuple P → PauliQuestion P := fun ω =>
    ProjectiveSetting.pairWQuestion P W ω.1 ω.2.1 ω.2.2.1 ω.2.2.2
  let fA : PauliTuple P → PauliAnswer P → ZMod 2 := fun ω A =>
    pointTraceLabel P W ω A
  let fB : PauliTuple P → PauliAnswer P → ZMod 2 := fun _ =>
    ProjectiveSetting.pairWAnswerOrZero
  have h := consistencyDefect_postprocess_eq_mismatch
    (commTupleDist P) S.toStrategy qA qB fA fB
  have hA : ∀ ω c,
      heteroKron
          ((S.pointTraceMeas .alice W (selectedTuplePoint W ω)
            (selectedTupleScalar W ω)).effect c)
          (1 : Op S.toStrategy.ιB) =
        heteroKron (((S.toStrategy.A (qA ω)).postprocess (fA ω)).effect c)
          (1 : Op S.toStrategy.ιB) := by
    intro ω c
    congr 1
    unfold ProjectiveSetting.pointTraceMeas ProjectiveSetting.pointMeas fA
    rw [MIPStarRE.Quantum.Measurement.postprocess_comp]
    rfl
  have hB : ∀ ω c,
      heteroKron (1 : Op S.toStrategy.ιA)
          ((S.pairWMeas .bob W ω.1 ω.2.1 ω.2.2.1 ω.2.2.2).effect c) =
        heteroKron (1 : Op S.toStrategy.ιA)
          (((S.toStrategy.B (qB ω)).postprocess (fB ω)).effect c) := by
    intro ω c
    rfl
  calc
    _ = consistencyDefect (commTupleDist P)
        (fun ω c => heteroKron
          (((S.toStrategy.A (qA ω)).postprocess (fA ω)).effect c) 1)
        (fun ω c => heteroKron 1
          (((S.toStrategy.B (qB ω)).postprocess (fB ω)).effect c))
        S.toStrategy.ψ := consistencyDefect_congr _ _ _ _ _ _ hA hB
    _ = avgOver (commTupleDist P) (fun ω =>
        outcomeEventWeight S.toStrategy (qA ω) (qB ω)
          (fun A B => fA ω A ≠ fB ω B)) := h
    _ = _ := by rfl

/-- On commuting tuples, trace-coarse-grained point answers agree with Pair/W
answers. This is item 5 of `lem:qld-win-implications`, paper
`14_analysis_of_the_pauli_basis_test.tex:232-239`, blueprint
`ch14_qpbt_observables.tex:583-598`. -/
theorem win_comm_cons :
    ∃ C : ℝ, 1 ≤ C ∧
      ∀ (P : AdmissibleParams) (ε : ℝ) (S : ProjectiveSetting P ε),
      0 ≤ ε → ∀ W : PauliKind,
      consistencyDefect (commTupleDist P)
        (fun ω a => heteroKron
          ((S.pointTraceMeas .alice W
            (match W with | .X => ω.1 | .Z => ω.2.1)
            (match W with | .X => ω.2.2.1 | .Z => ω.2.2.2)).effect a) 1)
        (fun ω a => heteroKron 1
          ((S.pairWMeas .bob W ω.1 ω.2.1 ω.2.2.1 ω.2.2.2).effect a))
        S.toStrategy.ψ ≤ C * ε := by
  refine ⟨2 * (Fintype.card PauliEdge : ℝ), ?_, ?_⟩
  · have hcard : (1 : ℝ) ≤ Fintype.card PauliEdge := by
      exact_mod_cast (Fintype.card_pos : 0 < Fintype.card PauliEdge)
    linarith
  intro P ε S _ W
  change consistencyDefect (commTupleDist P)
      (fun ω a => heteroKron
        ((S.pointTraceMeas .alice W (selectedTuplePoint W ω)
          (selectedTupleScalar W ω)).effect a) 1)
      (fun ω a => heteroKron 1
        ((S.pairWMeas .bob W ω.1 ω.2.1 ω.2.2.1 ω.2.2.2).effect a))
      S.toStrategy.ψ ≤ _
  rw [commConsConsistency_eq_mismatch]
  calc
    _ ≤ 2 * avgOver (uniformDistribution (PauliTuple P)) (fun ω =>
        if IsCommuting ω then
          outcomeEventWeight S.toStrategy
            (ProjectiveSetting.pointQuestion P W (selectedTuplePoint W ω))
            (ProjectiveSetting.pairWQuestion P W
              ω.1 ω.2.1 ω.2.2.1 ω.2.2.2)
            (fun A B => pointTraceLabel P W ω A ≠
              ProjectiveSetting.pairWAnswerOrZero B)
        else 0) := by
      apply avgOver_comm_le_two_mul_gated
      intro ω
      exact outcome_event_weight_nonneg S.toStrategy _ _ _
    _ ≤ 2 * avgOver (uniformDistribution (PauliSpace P))
        (pauliRejectionAt S.toStrategy
          (pointPairWEdge W)) := by
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      rw [← avgOver_pauliTuple_uniform]
      apply avgOver_mono
      intro z
      by_cases hcomm : IsCommuting (pauliSharedSplit P z).1
      · simp only [if_pos hcomm]
        have hs := pointPairMismatch_le_rejection S W z hcomm
        rw [pauliCL_point_eq,
          pauliCL_shared_eq P (.pairW W) rfl] at hs
        rw [pauliToLd_point_eq_selected] at hs
        simpa [pauliSharedSplit, selectedTuplePoint,
          ProjectiveSetting.pointQuestion, ProjectiveSetting.pairWQuestion]
          using hs
      · simp only [if_neg hcomm]
        exact pauliRejectionAt_nonneg S.toStrategy _ z
    _ ≤ 2 * (Fintype.card PauliEdge : ℝ) * ε := by
      rw [mul_assoc]
      exact mul_le_mul_of_nonneg_left (fixedEdgeRejection_le_error S _) (by norm_num)


end WinImplications

end

end MIPStarRE.QPBT
