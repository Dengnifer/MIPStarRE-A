import MIPStarRE.QPBT.Observables.WinImplications.ApproxLines

/-!
# Approximate winning implications for the tuple subtests

This module proves the operator-distance companions, with their
factor-interchanged forms, of the commutation check, the commutation
consistency check, and the Magic Square consistency check.

## References

The declarations support the trailing clause of `lem:qld-win-implications` in
`blueprint/src/chapter/ch14_qpbt_observables.tex:614-702`. Their paper source
is `references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:192-267`,
whose closing sentences at lines 227 and 263-264 state both companions.
-/

open scoped BigOperators Matrix ComplexOrder

namespace MIPStarRE.QPBT

open MIPStarRE.LDT hiding Measurement
open MIPStarRE.Quantum

noncomputable section

namespace WinImplications

local instance pauliEdgeNonemptyApprox : Nonempty PauliEdge := pauliEdge_nonempty

/-! ## Commutation check -/

/-- Reversed-orientation commuting Pair/Pair-W mismatch is inside rejection.
Paper `14_analysis_of_the_pauli_basis_test.tex:210-231,227`. -/
theorem pairMismatch_le_rejection_interchanged {P : AdmissibleParams} {ε : ℝ}
    (S : ProjectiveSetting P ε) (W : PauliKind) (z : PauliSpace P)
    (hcomm : IsCommuting (pauliSharedSplit P z).1) :
    outcomeEventWeight S.toStrategy
        (.pair, pauliCL P .pair z)
        ((.pairW W), pauliCL P (.pairW W) z)
        (fun A B =>
          selectedPairBit W (ProjectiveSetting.pairAnswerOrZero A) ≠
            ProjectiveSetting.pairWAnswerOrZero B) ≤
      pauliRejectionAt S.toStrategy (pairPairWEdge W) z := by
  apply outcome_event_weight_mono
  intro A B hne
  change pauliWinPredicate P _ _ A B = false
  apply Bool.eq_false_iff.mpr
  intro htrue
  exact hne (pairLabels_eq_of_win P W z B A hcomm
    ((win_symm_pair_pairW P W _ _ A B).symm.trans htrue)).symm

/-- Reversed-orientation commuting consistency is its mismatch mass. -/
theorem commConsistency_eq_mismatch_interchanged {P : AdmissibleParams} {ε : ℝ}
    (S : ProjectiveSetting P ε) (W : PauliKind) :
    consistencyDefect (commTupleDist P)
        (fun ω a => heteroKron
          ((S.pairComponentMeas .alice W ω).effect a) 1)
        (fun ω a => heteroKron 1
          ((S.pairWMeas .bob W ω.1 ω.2.1 ω.2.2.1 ω.2.2.2).effect a))
        S.toStrategy.ψ =
      avgOver (commTupleDist P) (fun ω =>
        outcomeEventWeight S.toStrategy
          (ProjectiveSetting.pairQuestion P ω.1 ω.2.1 ω.2.2.1 ω.2.2.2)
          (ProjectiveSetting.pairWQuestion P W ω.1 ω.2.1 ω.2.2.1 ω.2.2.2)
          (fun A B =>
            selectedPairBit W (ProjectiveSetting.pairAnswerOrZero A) ≠
              ProjectiveSetting.pairWAnswerOrZero B)) := by
  let qA : PauliTuple P → PauliQuestion P := fun ω =>
    ProjectiveSetting.pairQuestion P ω.1 ω.2.1 ω.2.2.1 ω.2.2.2
  let qB : PauliTuple P → PauliQuestion P := fun ω =>
    ProjectiveSetting.pairWQuestion P W ω.1 ω.2.1 ω.2.2.1 ω.2.2.2
  let fA : PauliTuple P → PauliAnswer P → ZMod 2 := fun _ A =>
    selectedPairBit W (ProjectiveSetting.pairAnswerOrZero A)
  let fB : PauliTuple P → PauliAnswer P → ZMod 2 := fun _ =>
    ProjectiveSetting.pairWAnswerOrZero
  have h := consistencyDefect_postprocess_eq_mismatch
    (commTupleDist P) S.toStrategy qA qB fA fB
  have hA : ∀ ω c,
      heteroKron ((S.pairComponentMeas .alice W ω).effect c)
          (1 : Op S.toStrategy.ιB) =
        heteroKron (((S.toStrategy.A (qA ω)).postprocess (fA ω)).effect c)
          (1 : Op S.toStrategy.ιB) := by
    intro ω c
    congr 1
    unfold ProjectiveSetting.pairComponentMeas ProjectiveSetting.pairMeas fA qA
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

/-- Factor-interchanged form of the commutation-check implication. Paper
`14_analysis_of_the_pauli_basis_test.tex:210-231,227`. -/
theorem win_comm_interchanged_proof :
    ∃ C : ℝ, 1 ≤ C ∧
      ∀ (P : AdmissibleParams) (ε : ℝ) (S : ProjectiveSetting P ε),
      0 ≤ ε → ∀ W : PauliKind,
      consistencyDefect (commTupleDist P)
        (fun ω a => heteroKron
          ((S.pairComponentMeas .alice W ω).effect a) 1)
        (fun ω a => heteroKron 1
          ((S.pairWMeas .bob W ω.1 ω.2.1 ω.2.2.1 ω.2.2.2).effect a))
        S.toStrategy.ψ ≤ C * ε := by
  refine ⟨2 * (Fintype.card PauliEdge : ℝ), ?_, ?_⟩
  · have hcard : (1 : ℝ) ≤ Fintype.card PauliEdge := by
      exact_mod_cast (Fintype.card_pos : 0 < Fintype.card PauliEdge)
    linarith
  intro P ε S _ W
  rw [commConsistency_eq_mismatch_interchanged]
  calc
    _ ≤ 2 * avgOver (uniformDistribution (PauliTuple P)) (fun ω =>
        if IsCommuting ω then
          outcomeEventWeight S.toStrategy
            (ProjectiveSetting.pairQuestion P ω.1 ω.2.1 ω.2.2.1 ω.2.2.2)
            (ProjectiveSetting.pairWQuestion P W ω.1 ω.2.1 ω.2.2.1 ω.2.2.2)
            (fun A B =>
              selectedPairBit W (ProjectiveSetting.pairAnswerOrZero A) ≠
                ProjectiveSetting.pairWAnswerOrZero B)
        else 0) := by
      apply avgOver_comm_le_two_mul_gated
      intro ω
      exact outcome_event_weight_nonneg S.toStrategy _ _ _
    _ ≤ 2 * avgOver (uniformDistribution (PauliSpace P))
        (pauliRejectionAt S.toStrategy (pairPairWEdge W)) := by
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      rw [← avgOver_pauliTuple_uniform]
      apply avgOver_mono
      intro z
      by_cases hcomm : IsCommuting (pauliSharedSplit P z).1
      · simp only [if_pos hcomm]
        have hs := pairMismatch_le_rejection_interchanged S W z hcomm
        rw [pauliCL_shared_eq P (.pairW W) rfl,
          pauliCL_shared_eq P .pair rfl] at hs
        simpa [pauliSharedSplit, ProjectiveSetting.pairWQuestion,
          ProjectiveSetting.pairQuestion]
          using hs
      · simp only [if_neg hcomm]
        exact pauliRejectionAt_nonneg S.toStrategy _ z
    _ ≤ 2 * (Fintype.card PauliEdge : ℝ) * ε := by
      rw [mul_assoc]
      exact mul_le_mul_of_nonneg_left (fixedEdgeRejection_le_error S _)
        (by norm_num)

/-- Operator-distance and factor-interchanged companions to the commuting
Pair check. This is the trailing clause of `lem:qld-win-implications`, paper
`14_analysis_of_the_pauli_basis_test.tex:227,263-264`, blueprint
`ch14_qpbt_observables.tex:699-701`. -/
theorem win_comm_approx_proof :
    ∃ C : ℝ, 1 ≤ C ∧
      ∀ (P : AdmissibleParams) (ε : ℝ) (S : ProjectiveSetting P ε),
      0 ≤ ε → ∀ W : PauliKind,
      opFamilyDistSq (commTupleDist P)
        (fun ω a => heteroKron
          ((S.pairWMeas .alice W ω.1 ω.2.1 ω.2.2.1 ω.2.2.2).effect a) 1)
        (fun ω a => heteroKron 1 ((S.pairComponentMeas .bob W ω).effect a))
        S.toStrategy.ψ ≤ C * ε ∧
      opFamilyDistSq (commTupleDist P)
        (fun ω a => heteroKron
          ((S.pairWMeas .bob W ω.1 ω.2.1 ω.2.2.1 ω.2.2.2).effect a) 1)
        (fun ω a => heteroKron 1 ((S.pairComponentMeas .alice W ω).effect a))
        S.swappedState ≤ C * ε := by
  obtain ⟨C₁, hC₁, h₁⟩ := win_comm
  obtain ⟨C₂, hC₂, h₂⟩ := win_comm_interchanged_proof
  refine ⟨2 * (C₁ + C₂), by linarith, ?_⟩
  intro P ε S hε W
  have hforward := opFamilyDistSq_placed_le_of_consistencyDefect_le
    (commTupleDist P)
    (fun ω => S.pairWMeas .alice W ω.1 ω.2.1 ω.2.2.1 ω.2.2.2)
    (fun ω => S.pairComponentMeas .bob W ω) S.toStrategy.ψ (h₁ P ε S hε W)
  have hreverse := opFamilyDistSq_placed_le_of_consistencyDefect_le
    (commTupleDist P)
    (fun ω => S.pairComponentMeas .alice W ω)
    (fun ω => S.pairWMeas .bob W ω.1 ω.2.1 ω.2.2.1 ω.2.2.2)
    S.toStrategy.ψ (h₂ P ε S hε W)
  refine ⟨approx_bound_of_left hC₂ hε hforward, ?_⟩
  have hswap := opFamilyDistSq_swappedState (ιA := S.toStrategy.ιA)
    (ιB := S.toStrategy.ιB) (commTupleDist P)
    (fun ω a => (S.pairComponentMeas .alice W ω).effect a)
    (fun ω a => (S.pairWMeas .bob W ω.1 ω.2.1 ω.2.2.1 ω.2.2.2).effect a)
    S.toStrategy.ψ
  exact hswap.trans_le (approx_bound_of_right hC₁ hε hreverse)

/-! ## Commutation consistency check -/

/-- Reversed-orientation commuting Pair-W/point mismatch is inside rejection.
Paper `14_analysis_of_the_pauli_basis_test.tex:232-239,227`. -/
theorem pointPairMismatch_le_rejection_interchanged {P : AdmissibleParams}
    {ε : ℝ} (S : ProjectiveSetting P ε) (W : PauliKind) (z : PauliSpace P)
    (hcomm : IsCommuting (pauliSharedSplit P z).1) :
    outcomeEventWeight S.toStrategy
        ((.pairW W), pauliCL P (.pairW W) z)
        ((.point W), pauliCL P (.point W) z)
        (fun A B =>
          ProjectiveSetting.pairWAnswerOrZero A ≠
            pointTraceLabel P W (pauliSharedSplit P z).1 B) ≤
      pauliRejectionAt S.toStrategy (pairWPointEdge W) z := by
  apply outcome_event_weight_mono
  intro A B hne
  change pauliWinPredicate P _ _ A B = false
  apply Bool.eq_false_iff.mpr
  intro htrue
  exact hne (pointPairLabels_eq_of_win P W z B A hcomm
    ((win_symm_pairW_point P W _ _ A B).symm.trans htrue)).symm

/-- Reversed-orientation Pair-W/point-trace consistency is its mismatch mass. -/
theorem commConsConsistency_eq_mismatch_interchanged {P : AdmissibleParams}
    {ε : ℝ} (S : ProjectiveSetting P ε) (W : PauliKind) :
    consistencyDefect (commTupleDist P)
        (fun ω a => heteroKron
          ((S.pairWMeas .alice W ω.1 ω.2.1 ω.2.2.1 ω.2.2.2).effect a) 1)
        (fun ω a => heteroKron 1
          ((S.pointTraceMeas .bob W (selectedTuplePoint W ω)
            (selectedTupleScalar W ω)).effect a))
        S.toStrategy.ψ =
      avgOver (commTupleDist P) (fun ω =>
        outcomeEventWeight S.toStrategy
          (ProjectiveSetting.pairWQuestion P W
            ω.1 ω.2.1 ω.2.2.1 ω.2.2.2)
          (ProjectiveSetting.pointQuestion P W (selectedTuplePoint W ω))
          (fun A B => ProjectiveSetting.pairWAnswerOrZero A ≠
            pointTraceLabel P W ω B)) := by
  let qA : PauliTuple P → PauliQuestion P := fun ω =>
    ProjectiveSetting.pairWQuestion P W ω.1 ω.2.1 ω.2.2.1 ω.2.2.2
  let qB : PauliTuple P → PauliQuestion P := fun ω =>
    ProjectiveSetting.pointQuestion P W (selectedTuplePoint W ω)
  let fA : PauliTuple P → PauliAnswer P → ZMod 2 := fun _ =>
    ProjectiveSetting.pairWAnswerOrZero
  let fB : PauliTuple P → PauliAnswer P → ZMod 2 := fun ω B =>
    pointTraceLabel P W ω B
  have h := consistencyDefect_postprocess_eq_mismatch
    (commTupleDist P) S.toStrategy qA qB fA fB
  have hA : ∀ ω c,
      heteroKron
          ((S.pairWMeas .alice W ω.1 ω.2.1 ω.2.2.1 ω.2.2.2).effect c)
          (1 : Op S.toStrategy.ιB) =
        heteroKron (((S.toStrategy.A (qA ω)).postprocess (fA ω)).effect c)
          (1 : Op S.toStrategy.ιB) := by
    intro ω c
    rfl
  have hB : ∀ ω c,
      heteroKron (1 : Op S.toStrategy.ιA)
          ((S.pointTraceMeas .bob W (selectedTuplePoint W ω)
            (selectedTupleScalar W ω)).effect c) =
        heteroKron (1 : Op S.toStrategy.ιA)
          (((S.toStrategy.B (qB ω)).postprocess (fB ω)).effect c) := by
    intro ω c
    congr 1
    unfold ProjectiveSetting.pointTraceMeas ProjectiveSetting.pointMeas fB
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

/-- Factor-interchanged form of the commutation-consistency implication. Paper
`14_analysis_of_the_pauli_basis_test.tex:232-239,227`. -/
theorem win_comm_cons_interchanged_proof :
    ∃ C : ℝ, 1 ≤ C ∧
      ∀ (P : AdmissibleParams) (ε : ℝ) (S : ProjectiveSetting P ε),
      0 ≤ ε → ∀ W : PauliKind,
      consistencyDefect (commTupleDist P)
        (fun ω a => heteroKron
          ((S.pairWMeas .alice W ω.1 ω.2.1 ω.2.2.1 ω.2.2.2).effect a) 1)
        (fun ω a => heteroKron 1
          ((S.pointTraceMeas .bob W (selectedTuplePoint W ω)
            (selectedTupleScalar W ω)).effect a))
        S.toStrategy.ψ ≤ C * ε := by
  refine ⟨2 * (Fintype.card PauliEdge : ℝ), ?_, ?_⟩
  · have hcard : (1 : ℝ) ≤ Fintype.card PauliEdge := by
      exact_mod_cast (Fintype.card_pos : 0 < Fintype.card PauliEdge)
    linarith
  intro P ε S _ W
  rw [commConsConsistency_eq_mismatch_interchanged]
  calc
    _ ≤ 2 * avgOver (uniformDistribution (PauliTuple P)) (fun ω =>
        if IsCommuting ω then
          outcomeEventWeight S.toStrategy
            (ProjectiveSetting.pairWQuestion P W
              ω.1 ω.2.1 ω.2.2.1 ω.2.2.2)
            (ProjectiveSetting.pointQuestion P W (selectedTuplePoint W ω))
            (fun A B => ProjectiveSetting.pairWAnswerOrZero A ≠
              pointTraceLabel P W ω B)
        else 0) := by
      apply avgOver_comm_le_two_mul_gated
      intro ω
      exact outcome_event_weight_nonneg S.toStrategy _ _ _
    _ ≤ 2 * avgOver (uniformDistribution (PauliSpace P))
        (pauliRejectionAt S.toStrategy (pairWPointEdge W)) := by
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      rw [← avgOver_pauliTuple_uniform]
      apply avgOver_mono
      intro z
      by_cases hcomm : IsCommuting (pauliSharedSplit P z).1
      · simp only [if_pos hcomm]
        have hs := pointPairMismatch_le_rejection_interchanged S W z hcomm
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
      exact mul_le_mul_of_nonneg_left (fixedEdgeRejection_le_error S _)
        (by norm_num)

/-- Operator-distance and factor-interchanged companions to commuting point
consistency. This is the trailing clause of `lem:qld-win-implications`, paper
`14_analysis_of_the_pauli_basis_test.tex:227,263-264`, blueprint
`ch14_qpbt_observables.tex:699-701`. -/
theorem win_comm_cons_approx_proof :
    ∃ C : ℝ, 1 ≤ C ∧
      ∀ (P : AdmissibleParams) (ε : ℝ) (S : ProjectiveSetting P ε),
      0 ≤ ε → ∀ W : PauliKind,
      opFamilyDistSq (commTupleDist P)
        (fun ω a => heteroKron
          ((S.pointTraceMeas .alice W
            (match W with | .X => ω.1 | .Z => ω.2.1)
            (match W with | .X => ω.2.2.1 | .Z => ω.2.2.2)).effect a) 1)
        (fun ω a => heteroKron 1
          ((S.pairWMeas .bob W ω.1 ω.2.1 ω.2.2.1 ω.2.2.2).effect a))
        S.toStrategy.ψ ≤ C * ε ∧
      opFamilyDistSq (commTupleDist P)
        (fun ω a => heteroKron
          ((S.pointTraceMeas .bob W
            (match W with | .X => ω.1 | .Z => ω.2.1)
            (match W with | .X => ω.2.2.1 | .Z => ω.2.2.2)).effect a) 1)
        (fun ω a => heteroKron 1
          ((S.pairWMeas .alice W ω.1 ω.2.1 ω.2.2.1 ω.2.2.2).effect a))
        S.swappedState ≤ C * ε := by
  obtain ⟨C₁, hC₁, h₁⟩ := win_comm_cons
  obtain ⟨C₂, hC₂, h₂⟩ := win_comm_cons_interchanged_proof
  refine ⟨2 * (C₁ + C₂), by linarith, ?_⟩
  intro P ε S hε W
  have hforward := opFamilyDistSq_placed_le_of_consistencyDefect_le
    (commTupleDist P)
    (fun ω => S.pointTraceMeas .alice W (selectedTuplePoint W ω)
      (selectedTupleScalar W ω))
    (fun ω => S.pairWMeas .bob W ω.1 ω.2.1 ω.2.2.1 ω.2.2.2)
    S.toStrategy.ψ (h₁ P ε S hε W)
  have hreverse := opFamilyDistSq_placed_le_of_consistencyDefect_le
    (commTupleDist P)
    (fun ω => S.pairWMeas .alice W ω.1 ω.2.1 ω.2.2.1 ω.2.2.2)
    (fun ω => S.pointTraceMeas .bob W (selectedTuplePoint W ω)
      (selectedTupleScalar W ω))
    S.toStrategy.ψ (h₂ P ε S hε W)
  refine ⟨approx_bound_of_left hC₂ hε hforward, ?_⟩
  have hswap := opFamilyDistSq_swappedState (ιA := S.toStrategy.ιA)
    (ιB := S.toStrategy.ιB) (commTupleDist P)
    (fun ω a => (S.pairWMeas .alice W ω.1 ω.2.1 ω.2.2.1 ω.2.2.2).effect a)
    (fun ω a => (S.pointTraceMeas .bob W (selectedTuplePoint W ω)
      (selectedTupleScalar W ω)).effect a)
    S.toStrategy.ψ
  exact hswap.trans_le (approx_bound_of_right hC₁ hε hreverse)

/-! ## Magic square consistency check -/

/-- Reversed-orientation anticommuting variable/point mismatch is inside
rejection. Paper `14_analysis_of_the_pauli_basis_test.tex:250-263,227`. -/
theorem pointMsMismatch_le_rejection_interchanged {P : AdmissibleParams}
    {ε : ℝ} (S : ProjectiveSetting P ε) (W : PauliKind) (z : PauliSpace P)
    (hanti : IsAnticommuting (pauliSharedSplit P z).1) :
    outcomeEventWeight S.toStrategy
        ((.ms (.var (selectedMsVar W))),
          pauliCL P (.ms (.var (selectedMsVar W))) z)
        ((.point W), pauliCL P (.point W) z)
        (fun A B => ProjectiveSetting.pairWAnswerOrZero A ≠
          pointTraceLabel P W (pauliSharedSplit P z).1 B) ≤
      pauliRejectionAt S.toStrategy (msVarPointEdge W) z := by
  cases W with
  | X =>
      apply outcome_event_weight_mono
      intro A B hne
      change pauliWinPredicate P _ _ A B = false
      apply Bool.eq_false_iff.mpr
      intro htrue
      exact hne (pointMsLabels_eq_of_win P .X z B A hanti
        ((win_symm_msvar_point P .X (selectedMsVar .X) _ _ A B).symm.trans
          htrue)).symm
  | Z =>
      apply outcome_event_weight_mono
      intro A B hne
      change pauliWinPredicate P _ _ A B = false
      apply Bool.eq_false_iff.mpr
      intro htrue
      exact hne (pointMsLabels_eq_of_win P .Z z B A hanti
        ((win_symm_msvar_point P .Z (selectedMsVar .Z) _ _ A B).symm.trans
          htrue)).symm

/-- Reversed-orientation variable/point-trace consistency is its mismatch mass. -/
theorem msConsConsistency_eq_mismatch_interchanged {P : AdmissibleParams}
    {ε : ℝ} (S : ProjectiveSetting P ε) (W : PauliKind) :
    consistencyDefect (anticommTupleDist P)
        (fun ω a => heteroKron
          ((S.msVarBitMeas .alice (selectedMsVar W) ω).effect a) 1)
        (fun ω a => heteroKron 1
          ((S.pointTraceMeas .bob W (selectedTuplePoint W ω)
            (selectedTupleScalar W ω)).effect a))
        S.toStrategy.ψ =
      avgOver (anticommTupleDist P) (fun ω =>
        outcomeEventWeight S.toStrategy
          (ProjectiveSetting.msQuestion P (.var (selectedMsVar W))
            ω.1 ω.2.1 ω.2.2.1 ω.2.2.2)
          (ProjectiveSetting.pointQuestion P W (selectedTuplePoint W ω))
          (fun A B => ProjectiveSetting.pairWAnswerOrZero A ≠
            pointTraceLabel P W ω B)) := by
  let qA : PauliTuple P → PauliQuestion P := fun ω =>
    ProjectiveSetting.msQuestion P (.var (selectedMsVar W))
      ω.1 ω.2.1 ω.2.2.1 ω.2.2.2
  let qB : PauliTuple P → PauliQuestion P := fun ω =>
    ProjectiveSetting.pointQuestion P W (selectedTuplePoint W ω)
  let fA : PauliTuple P → PauliAnswer P → ZMod 2 := fun _ =>
    ProjectiveSetting.pairWAnswerOrZero
  let fB : PauliTuple P → PauliAnswer P → ZMod 2 := fun ω B =>
    pointTraceLabel P W ω B
  have h := consistencyDefect_postprocess_eq_mismatch
    (anticommTupleDist P) S.toStrategy qA qB fA fB
  have hA : ∀ ω c,
      heteroKron ((S.msVarBitMeas .alice (selectedMsVar W) ω).effect c)
          (1 : Op S.toStrategy.ιB) =
        heteroKron (((S.toStrategy.A (qA ω)).postprocess (fA ω)).effect c)
          (1 : Op S.toStrategy.ιB) := by
    intro ω c
    congr 1
    unfold ProjectiveSetting.msVarBitMeas ProjectiveSetting.msMeas fA qA
    rw [MIPStarRE.Quantum.Measurement.postprocess_comp]
    have hmap : (msBitOrZero ∘
        ProjectiveSetting.msAnswerOrZero (P := P) (.var (selectedMsVar W))) =
        ProjectiveSetting.pairWAnswerOrZero (P := P) := by
      funext B
      cases B <;> rfl
    rw [Function.comp_def] at hmap
    rw [hmap]
    rfl
  have hB : ∀ ω c,
      heteroKron (1 : Op S.toStrategy.ιA)
          ((S.pointTraceMeas .bob W (selectedTuplePoint W ω)
            (selectedTupleScalar W ω)).effect c) =
        heteroKron (1 : Op S.toStrategy.ιA)
          (((S.toStrategy.B (qB ω)).postprocess (fB ω)).effect c) := by
    intro ω c
    congr 1
    unfold ProjectiveSetting.pointTraceMeas ProjectiveSetting.pointMeas fB
    rw [MIPStarRE.Quantum.Measurement.postprocess_comp]
    rfl
  calc
    _ = consistencyDefect (anticommTupleDist P)
        (fun ω c => heteroKron
          (((S.toStrategy.A (qA ω)).postprocess (fA ω)).effect c) 1)
        (fun ω c => heteroKron 1
          (((S.toStrategy.B (qB ω)).postprocess (fB ω)).effect c))
        S.toStrategy.ψ := consistencyDefect_congr _ _ _ _ _ _ hA hB
    _ = avgOver (anticommTupleDist P) (fun ω =>
        outcomeEventWeight S.toStrategy (qA ω) (qB ω)
          (fun A B => fA ω A ≠ fB ω B)) := h
    _ = _ := by rfl

/-- Factor-interchanged form of the Magic Square consistency implication. Paper
`14_analysis_of_the_pauli_basis_test.tex:250-263,227`. -/
theorem win_ms_cons_interchanged_proof :
    ∃ C : ℝ, 1 ≤ C ∧
      ∀ (P : AdmissibleParams) (ε : ℝ) (S : ProjectiveSetting P ε),
      0 ≤ ε → ∀ W : PauliKind,
      consistencyDefect (anticommTupleDist P)
        (fun ω a => heteroKron
          ((S.msVarBitMeas .alice (selectedMsVar W) ω).effect a) 1)
        (fun ω a => heteroKron 1
          ((S.pointTraceMeas .bob W (selectedTuplePoint W ω)
            (selectedTupleScalar W ω)).effect a))
        S.toStrategy.ψ ≤ C * ε := by
  refine ⟨16 * (Fintype.card PauliEdge : ℝ), ?_, ?_⟩
  · have hcard : (1 : ℝ) ≤ Fintype.card PauliEdge := by
      exact_mod_cast (Fintype.card_pos : 0 < Fintype.card PauliEdge)
    linarith
  intro P ε S _ W
  rw [msConsConsistency_eq_mismatch_interchanged]
  calc
    _ ≤ 16 * avgOver (uniformDistribution (PauliTuple P)) (fun ω =>
        if IsAnticommuting ω then
          outcomeEventWeight S.toStrategy
            (ProjectiveSetting.msQuestion P (.var (selectedMsVar W))
              ω.1 ω.2.1 ω.2.2.1 ω.2.2.2)
            (ProjectiveSetting.pointQuestion P W (selectedTuplePoint W ω))
            (fun A B => ProjectiveSetting.pairWAnswerOrZero A ≠
              pointTraceLabel P W ω B)
        else 0) := by
      apply avgOver_anticomm_le_sixteen_mul_gated
      intro ω
      exact outcome_event_weight_nonneg S.toStrategy _ _ _
    _ ≤ 16 * avgOver (uniformDistribution (PauliSpace P))
        (pauliRejectionAt S.toStrategy (msVarPointEdge W)) := by
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      rw [← avgOver_pauliTuple_uniform]
      apply avgOver_mono
      intro z
      by_cases hanti : IsAnticommuting (pauliSharedSplit P z).1
      · simp only [if_pos hanti]
        have hs := pointMsMismatch_le_rejection_interchanged S W z hanti
        rw [pauliCL_point_eq,
          pauliCL_shared_eq P (.ms (.var (selectedMsVar W))) rfl] at hs
        rw [pauliToLd_point_eq_selected] at hs
        simpa [pauliSharedSplit, selectedTuplePoint, selectedMsVar,
          ProjectiveSetting.pointQuestion, ProjectiveSetting.msQuestion]
          using hs
      · simp only [if_neg hanti]
        exact pauliRejectionAt_nonneg S.toStrategy _ z
    _ ≤ 16 * (Fintype.card PauliEdge : ℝ) * ε := by
      rw [mul_assoc]
      exact mul_le_mul_of_nonneg_left (fixedEdgeRejection_le_error S _)
        (by norm_num)

/-- Operator-distance and factor-interchanged companions to Magic Square
variable consistency. This is the trailing clause of
`lem:qld-win-implications`, paper
`14_analysis_of_the_pauli_basis_test.tex:227,263-264`, blueprint
`ch14_qpbt_observables.tex:699-701`. -/
theorem win_ms_cons_approx_proof :
    ∃ C : ℝ, 1 ≤ C ∧
      ∀ (P : AdmissibleParams) (ε : ℝ) (S : ProjectiveSetting P ε),
      0 ≤ ε → ∀ W : PauliKind,
      opFamilyDistSq (anticommTupleDist P)
        (fun ω a => heteroKron
          ((S.pointTraceMeas .alice W
            (match W with | .X => ω.1 | .Z => ω.2.1)
            (match W with | .X => ω.2.2.1 | .Z => ω.2.2.2)).effect a) 1)
        (fun ω a => heteroKron 1
          ((S.msVarBitMeas .bob (match W with | .X => 0 | .Z => 4) ω).effect a))
        S.toStrategy.ψ ≤ C * ε ∧
      opFamilyDistSq (anticommTupleDist P)
        (fun ω a => heteroKron
          ((S.pointTraceMeas .bob W
            (match W with | .X => ω.1 | .Z => ω.2.1)
            (match W with | .X => ω.2.2.1 | .Z => ω.2.2.2)).effect a) 1)
        (fun ω a => heteroKron 1
          ((S.msVarBitMeas .alice (match W with | .X => 0 | .Z => 4) ω).effect a))
        S.swappedState ≤ C * ε := by
  obtain ⟨C₁, hC₁, h₁⟩ := win_ms_cons
  obtain ⟨C₂, hC₂, h₂⟩ := win_ms_cons_interchanged_proof
  refine ⟨2 * (C₁ + C₂), by linarith, ?_⟩
  intro P ε S hε W
  have hforward := opFamilyDistSq_placed_le_of_consistencyDefect_le
    (anticommTupleDist P)
    (fun ω => S.pointTraceMeas .alice W (selectedTuplePoint W ω)
      (selectedTupleScalar W ω))
    (fun ω => S.msVarBitMeas .bob (selectedMsVar W) ω)
    S.toStrategy.ψ (h₁ P ε S hε W)
  have hreverse := opFamilyDistSq_placed_le_of_consistencyDefect_le
    (anticommTupleDist P)
    (fun ω => S.msVarBitMeas .alice (selectedMsVar W) ω)
    (fun ω => S.pointTraceMeas .bob W (selectedTuplePoint W ω)
      (selectedTupleScalar W ω))
    S.toStrategy.ψ (h₂ P ε S hε W)
  refine ⟨approx_bound_of_left hC₂ hε hforward, ?_⟩
  have hswap := opFamilyDistSq_swappedState (ιA := S.toStrategy.ιA)
    (ιB := S.toStrategy.ιB) (anticommTupleDist P)
    (fun ω a => (S.msVarBitMeas .alice (selectedMsVar W) ω).effect a)
    (fun ω a => (S.pointTraceMeas .bob W (selectedTuplePoint W ω)
      (selectedTupleScalar W ω)).effect a)
    S.toStrategy.ψ
  exact hswap.trans_le (approx_bound_of_right hC₁ hε hreverse)

end WinImplications

end

end MIPStarRE.QPBT
