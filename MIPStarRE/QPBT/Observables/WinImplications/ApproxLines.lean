import MIPStarRE.QPBT.Observables.WinImplications.Interchange

/-!
# Approximate winning implications for the line and point subtests

This module proves the operator-distance companions, with their
factor-interchanged forms, of the consistency check, the low-degree check,
and the Pauli basis consistency check.

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

local instance pauliEdgeNonemptyApproxLines : Nonempty PauliEdge := pauliEdge_nonempty

/-! ## Consistency check -/

/-- Operator-distance and factor-interchanged companions to the consistency
item of `lem:qld-win-implications`. This is the trailing clause at paper
`14_analysis_of_the_pauli_basis_test.tex:227,263-264`, blueprint
`ch14_qpbt_observables.tex:699-701`. -/
theorem win_cons_approx_proof :
    ∃ C : ℝ, 1 ≤ C ∧
      ∀ (P : AdmissibleParams) (ε : ℝ) (S : ProjectiveSetting P ε),
      0 ≤ ε →
      opFamilyDistSq (pauliQuestionMarginal P)
        (fun question a => heteroKron
          ((S.strategyMeasurement .alice question).effect a) 1)
        (fun question a => heteroKron 1
          ((S.strategyMeasurement .bob question).effect a))
        S.toStrategy.ψ ≤ C * ε ∧
      opFamilyDistSq (pauliQuestionMarginal P)
        (fun question a => heteroKron
          ((S.strategyMeasurement .bob question).effect a) 1)
        (fun question a => heteroKron 1
          ((S.strategyMeasurement .alice question).effect a))
        S.swappedState ≤ C * ε := by
  obtain ⟨C, hC, hbound⟩ := win_cons_proof
  refine ⟨2 * C, by linarith, ?_⟩
  intro P ε S hε
  have hkey := opFamilyDistSq_placed_le_of_consistencyDefect_le
    (pauliQuestionMarginal P)
    (fun question => S.strategyMeasurement .alice question)
    (fun question => S.strategyMeasurement .bob question) S.toStrategy.ψ
    (hbound P ε S hε)
  rw [show (2 : ℝ) * C * ε = 2 * (C * ε) by ring]
  refine ⟨hkey, ?_⟩
  have hswap := opFamilyDistSq_swappedState (ιA := S.toStrategy.ιA)
    (ιB := S.toStrategy.ιB) (pauliQuestionMarginal P)
    (fun question a => (S.strategyMeasurement .alice question).effect a)
    (fun question a => (S.strategyMeasurement .bob question).effect a)
    S.toStrategy.ψ
  exact hswap.trans_le hkey

/-! ## Low-degree check -/

/-- Reversed-orientation axis-line mismatch is contained in rejection. Paper
`14_analysis_of_the_pauli_basis_test.tex:200-204,227`. -/
theorem alineMismatch_le_rejection_interchanged {P : AdmissibleParams} {ε : ℝ}
    (S : ProjectiveSetting P ε) (W : PauliKind) (z : PauliSpace P) :
    outcomeEventWeight S.toStrategy
        ((.point W), pauliCL P (.point W) z)
        ((.aline W), pauliCL P (.aline W) z)
        (fun A B =>
          some (ProjectiveSetting.pointAnswerOrZero A) ≠
            evalOpt
              (aLineDescOf P.toLdParams
                (ldALineCL P.toLdParams (pauliToLd P W z)))
              (pauliToLd P W z).point
              (ProjectiveSetting.lineAnswerOrZero P
                (aLineDescOf P.toLdParams
                  (ldALineCL P.toLdParams (pauliToLd P W z))) B)) ≤
      pauliRejectionAt S.toStrategy (pointAlineEdge W) z := by
  apply outcome_event_weight_mono
  intro A B hne
  change pauliWinPredicate P _ _ A B = false
  apply Bool.eq_false_iff.mpr
  intro htrue
  exact hne (alineLabels_eq_of_win P W z B A
    ((win_symm_point_aline P W _ _ A B).symm.trans htrue)).symm

/-- Reversed-orientation diagonal-line mismatch is contained in rejection. Paper
`14_analysis_of_the_pauli_basis_test.tex:200-204,227`. -/
theorem dlineMismatch_le_rejection_interchanged {P : AdmissibleParams} {ε : ℝ}
    (S : ProjectiveSetting P ε) (W : PauliKind) (z : PauliSpace P) :
    outcomeEventWeight S.toStrategy
        ((.point W), pauliCL P (.point W) z)
        ((.dline W), pauliCL P (.dline W) z)
        (fun A B =>
          some (ProjectiveSetting.pointAnswerOrZero A) ≠
            evalOpt
              (dLineDescOf P.toLdParams
                (ldDLineCL P.toLdParams (pauliToLd P W z)))
              (pauliToLd P W z).point
              (ProjectiveSetting.lineAnswerOrZero P
                (dLineDescOf P.toLdParams
                  (ldDLineCL P.toLdParams (pauliToLd P W z))) B)) ≤
      pauliRejectionAt S.toStrategy (pointDlineEdge W) z := by
  apply outcome_event_weight_mono
  intro A B hne
  change pauliWinPredicate P _ _ A B = false
  apply Bool.eq_false_iff.mpr
  intro htrue
  exact hne (dlineLabels_eq_of_win P W z B A
    ((win_symm_point_dline P W _ _ A B).symm.trans htrue)).symm

/-- Reversed-orientation source-answer mismatch mass for the completed point and
line readouts. Paper `14_analysis_of_the_pauli_basis_test.tex:200-204,227`. -/
noncomputable def lowDegreeMismatchMassInterchanged {P : AdmissibleParams}
    {ε : ℝ} (S : ProjectiveSetting P ε) (W : PauliKind)
    (sample : LineDesc P.toLdParams × (Fin P.m → PauliScalar P)) : ℝ :=
  outcomeEventWeight S.toStrategy
    (ProjectiveSetting.pointQuestion P W sample.2)
    (ProjectiveSetting.lineQuestion P W sample.1)
    (fun A B =>
      some (ProjectiveSetting.pointAnswerOrZero A) ≠
        evalOpt sample.1 sample.2
          (ProjectiveSetting.lineAnswerOrZero P sample.1 B))

/-- The reversed axis component of the line sampler is the Pauli axis branch. -/
theorem avg_alineMismatch_eq_source_interchanged {P : AdmissibleParams} {ε : ℝ}
    (S : ProjectiveSetting P ε) (W : PauliKind) :
    avgOver (aLinePointDist P.toLdParams)
        (lowDegreeMismatchMassInterchanged S W) =
      avgOver (uniformDistribution (PauliSpace P)) (fun z =>
        outcomeEventWeight S.toStrategy
          ((.point W), pauliCL P (.point W) z)
          ((.aline W), pauliCL P (.aline W) z)
          (fun A B =>
            some (ProjectiveSetting.pointAnswerOrZero A) ≠
              evalOpt
                (aLineDescOf P.toLdParams
                  (ldALineCL P.toLdParams (pauliToLd P W z)))
                (pauliToLd P W z).point
                (ProjectiveSetting.lineAnswerOrZero P
                  (aLineDescOf P.toLdParams
                    (ldALineCL P.toLdParams (pauliToLd P W z))) B))) := by
  unfold aLinePointDist clDistribution
  rw [Distribution.avgOver_map, Distribution.avgOver_map]
  rw [← avgOver_pauliToLd_uniform P W]
  apply avgOver_congr
  intro z
  rw [pauliCL_aline_eq, pauliCL_point_eq]
  rfl

/-- The reversed diagonal component of the line sampler is the Pauli branch. -/
theorem avg_dlineMismatch_eq_source_interchanged {P : AdmissibleParams} {ε : ℝ}
    (S : ProjectiveSetting P ε) (W : PauliKind) :
    avgOver (dLinePointDist P.toLdParams)
        (lowDegreeMismatchMassInterchanged S W) =
      avgOver (uniformDistribution (PauliSpace P)) (fun z =>
        outcomeEventWeight S.toStrategy
          ((.point W), pauliCL P (.point W) z)
          ((.dline W), pauliCL P (.dline W) z)
          (fun A B =>
            some (ProjectiveSetting.pointAnswerOrZero A) ≠
              evalOpt
                (dLineDescOf P.toLdParams
                  (ldDLineCL P.toLdParams (pauliToLd P W z)))
                (pauliToLd P W z).point
                (ProjectiveSetting.lineAnswerOrZero P
                  (dLineDescOf P.toLdParams
                    (ldDLineCL P.toLdParams (pauliToLd P W z))) B))) := by
  unfold dLinePointDist clDistribution
  rw [Distribution.avgOver_map, Distribution.avgOver_map]
  rw [← avgOver_pauliToLd_uniform P W]
  apply avgOver_congr
  intro z
  rw [pauliCL_dline_eq, pauliCL_point_eq]
  rfl

/-- Reversed-orientation low-degree consistency is its mismatch mass. -/
theorem lowDegreeConsistency_eq_mismatch_interchanged {P : AdmissibleParams}
    {ε : ℝ} (S : ProjectiveSetting P ε) (W : PauliKind) :
    consistencyDefect (linePointDist P.toLdParams)
        (fun sample a => heteroKron
          ((S.pointMeasOption .alice W sample.2).effect a) 1)
        (fun sample a => heteroKron 1
          ((S.lineEvalMeas .bob W sample.1 sample.2).effect a))
        S.toStrategy.ψ =
      avgOver (linePointDist P.toLdParams)
        (lowDegreeMismatchMassInterchanged S W) := by
  let X := LineDesc P.toLdParams × (Fin P.m → PauliScalar P)
  let qA : X → PauliQuestion P := fun sample =>
    ProjectiveSetting.pointQuestion P W sample.2
  let qB : X → PauliQuestion P := fun sample =>
    ProjectiveSetting.lineQuestion P W sample.1
  let fA : X → PauliAnswer P → Option (PauliScalar P) := fun _ A =>
    some (ProjectiveSetting.pointAnswerOrZero A)
  let fB : X → PauliAnswer P → Option (PauliScalar P) := fun sample B =>
    evalOpt sample.1 sample.2 (ProjectiveSetting.lineAnswerOrZero P sample.1 B)
  have h := consistencyDefect_postprocess_eq_mismatch
    (X := X) (linePointDist P.toLdParams) S.toStrategy qA qB fA fB
  have hA : ∀ (sample : X) c,
      heteroKron ((S.pointMeasOption .alice W sample.2).effect c)
          (1 : Op S.toStrategy.ιB) =
        heteroKron
          (((S.toStrategy.A (qA sample)).postprocess (fA sample)).effect c)
          (1 : Op S.toStrategy.ιB) := by
    intro sample c
    congr 1
    unfold ProjectiveSetting.pointMeasOption ProjectiveSetting.pointMeas qA fA
    rw [measurement_postprocess_comp_effect]
    rfl
  have hB : ∀ (sample : X) c,
      heteroKron (1 : Op S.toStrategy.ιA)
          ((S.lineEvalMeas .bob W sample.1 sample.2).effect c) =
        heteroKron (1 : Op S.toStrategy.ιA)
          (((S.toStrategy.B (qB sample)).postprocess (fB sample)).effect c) := by
    intro sample c
    congr 1
    unfold ProjectiveSetting.lineEvalMeas ProjectiveSetting.lineMeas qB fB
    rw [measurement_postprocess_comp_effect]
    rfl
  calc
    _ = consistencyDefect (linePointDist P.toLdParams)
        (fun sample c => heteroKron
          (((S.toStrategy.A (qA sample)).postprocess (fA sample)).effect c) 1)
        (fun sample c => heteroKron 1
          (((S.toStrategy.B (qB sample)).postprocess (fB sample)).effect c))
        S.toStrategy.ψ := consistencyDefect_congr _ _ _ _ _ _ hA hB
    _ = avgOver (linePointDist P.toLdParams) (fun sample =>
        outcomeEventWeight S.toStrategy (qA sample) (qB sample)
          (fun A B => fA sample A ≠ fB sample B)) := h
    _ = _ := by rfl

/-- Factor-interchanged form of the low-degree winning implication. Paper
`14_analysis_of_the_pauli_basis_test.tex:200-204,227`, blueprint
`ch14_qpbt_observables.tex:699-701`. -/
theorem win_low_degree_interchanged_proof :
    ∃ C : ℝ, 1 ≤ C ∧
      ∀ (P : AdmissibleParams) (ε : ℝ) (S : ProjectiveSetting P ε),
      0 ≤ ε → ∀ W : PauliKind,
      consistencyDefect (linePointDist P.toLdParams)
        (fun sample a => heteroKron
          ((S.pointMeasOption .alice W sample.2).effect a) 1)
        (fun sample a => heteroKron 1
          ((S.lineEvalMeas .bob W sample.1 sample.2).effect a))
        S.toStrategy.ψ ≤ C * ε := by
  refine ⟨(Fintype.card PauliEdge : ℝ), ?_, ?_⟩
  · exact_mod_cast (Fintype.card_pos : 0 < Fintype.card PauliEdge)
  intro P ε S _ W
  rw [lowDegreeConsistency_eq_mismatch_interchanged]
  have ha : avgOver (aLinePointDist P.toLdParams)
      (lowDegreeMismatchMassInterchanged S W) ≤
      (Fintype.card PauliEdge : ℝ) * ε := by
    rw [avg_alineMismatch_eq_source_interchanged]
    calc
      _ ≤ avgOver (uniformDistribution (PauliSpace P))
          (pauliRejectionAt S.toStrategy (pointAlineEdge W)) := by
        apply avgOver_mono
        intro z
        exact alineMismatch_le_rejection_interchanged S W z
      _ ≤ (Fintype.card PauliEdge : ℝ) * ε :=
        fixedEdgeRejection_le_error S _
  have hd : avgOver (dLinePointDist P.toLdParams)
      (lowDegreeMismatchMassInterchanged S W) ≤
      (Fintype.card PauliEdge : ℝ) * ε := by
    rw [avg_dlineMismatch_eq_source_interchanged]
    calc
      _ ≤ avgOver (uniformDistribution (PauliSpace P))
          (pauliRejectionAt S.toStrategy (pointDlineEdge W)) := by
        apply avgOver_mono
        intro z
        exact dlineMismatch_le_rejection_interchanged S W z
      _ ≤ (Fintype.card PauliEdge : ℝ) * ε :=
        fixedEdgeRejection_le_error S _
  rw [linePointDist, avgOver_mix]
  linarith

/-- Operator-distance and factor-interchanged companions to the low-degree
item of `lem:qld-win-implications`. This is the trailing clause at paper
`14_analysis_of_the_pauli_basis_test.tex:227,263-264`, blueprint
`ch14_qpbt_observables.tex:699-701`. -/
theorem win_low_degree_approx_proof :
    ∃ C : ℝ, 1 ≤ C ∧
      ∀ (P : AdmissibleParams) (ε : ℝ) (S : ProjectiveSetting P ε),
      0 ≤ ε → ∀ W : PauliKind,
      opFamilyDistSq (linePointDist P.toLdParams)
        (fun sample a => heteroKron
          ((S.lineEvalMeas .alice W sample.1 sample.2).effect a) 1)
        (fun sample a => heteroKron 1
          ((S.pointMeasOption .bob W sample.2).effect a))
        S.toStrategy.ψ ≤ C * ε ∧
      opFamilyDistSq (linePointDist P.toLdParams)
        (fun sample a => heteroKron
          ((S.lineEvalMeas .bob W sample.1 sample.2).effect a) 1)
        (fun sample a => heteroKron 1
          ((S.pointMeasOption .alice W sample.2).effect a))
        S.swappedState ≤ C * ε := by
  obtain ⟨C₁, hC₁, h₁⟩ := win_low_degree_proof
  obtain ⟨C₂, hC₂, h₂⟩ := win_low_degree_interchanged_proof
  refine ⟨2 * (C₁ + C₂), by linarith, ?_⟩
  intro P ε S hε W
  have hforward := opFamilyDistSq_placed_le_of_consistencyDefect_le
    (linePointDist P.toLdParams)
    (fun sample => S.lineEvalMeas .alice W sample.1 sample.2)
    (fun sample => S.pointMeasOption .bob W sample.2) S.toStrategy.ψ
    (h₁ P ε S hε W)
  have hreverse := opFamilyDistSq_placed_le_of_consistencyDefect_le
    (linePointDist P.toLdParams)
    (fun sample => S.pointMeasOption .alice W sample.2)
    (fun sample => S.lineEvalMeas .bob W sample.1 sample.2) S.toStrategy.ψ
    (h₂ P ε S hε W)
  refine ⟨approxBound_of_left hC₂ hε hforward, ?_⟩
  have hswap := opFamilyDistSq_swappedState (ιA := S.toStrategy.ιA)
    (ιB := S.toStrategy.ιB) (linePointDist P.toLdParams)
    (fun sample a => (S.pointMeasOption .alice W sample.2).effect a)
    (fun sample a => (S.lineEvalMeas .bob W sample.1 sample.2).effect a)
    S.toStrategy.ψ
  exact hswap.trans_le (approxBound_of_right hC₁ hε hreverse)

/-! ## Pauli basis consistency check -/

/-- Reversed-orientation Pauli/point mismatch is contained in rejection. Paper
`14_analysis_of_the_pauli_basis_test.tex:205-209,227`. -/
theorem pauliBasisMismatch_le_rejection_interchanged {P : AdmissibleParams}
    {ε : ℝ} (S : ProjectiveSetting P ε) (W : PauliKind) (z : PauliSpace P) :
    outcomeEventWeight S.toStrategy
        ((.pauli W), pauliCL P (.pauli W) z)
        ((.point W), pauliCL P (.point W) z)
        (fun A B =>
          lowDegreeEnc (pauliAnswerOrZero A) (pauliToLd P W z).point ≠
            ProjectiveSetting.pointAnswerOrZero B) ≤
      pauliRejectionAt S.toStrategy (pauliPointEdge W) z := by
  apply outcome_event_weight_mono
  intro A B hne
  change pauliWinPredicate P _ _ A B = false
  apply Bool.eq_false_iff.mpr
  intro htrue
  exact hne (pauliBasisLabels_eq_of_win P W z B A
    ((win_symm_pauli_point P W _ _ A B).symm.trans htrue)).symm

/-- The reversed uniform point average is the sampled Pauli/point branch. -/
theorem avg_pauliBasisMismatch_eq_source_interchanged {P : AdmissibleParams}
    {ε : ℝ} (S : ProjectiveSetting P ε) (W : PauliKind) :
    avgOver (uniformDistribution (Fin P.m → PauliScalar P)) (fun u =>
        outcomeEventWeight S.toStrategy
          (pauliQuestion P W) (ProjectiveSetting.pointQuestion P W u)
          (fun A B => lowDegreeEnc (pauliAnswerOrZero A) u ≠
            ProjectiveSetting.pointAnswerOrZero B)) =
      avgOver (uniformDistribution (PauliSpace P)) (fun z =>
        outcomeEventWeight S.toStrategy
          (pauliQuestion P W)
          (ProjectiveSetting.pointQuestion P W (pauliToLd P W z).point)
          (fun A B =>
            lowDegreeEnc (pauliAnswerOrZero A) (pauliToLd P W z).point ≠
              ProjectiveSetting.pointAnswerOrZero B)) := by
  let f : (Fin P.m → PauliScalar P) → ℝ := fun u =>
    outcomeEventWeight S.toStrategy
      (pauliQuestion P W) (ProjectiveSetting.pointQuestion P W u)
      (fun A B => lowDegreeEnc (pauliAnswerOrZero A) u ≠
        ProjectiveSetting.pointAnswerOrZero B)
  have hld := avgOver_pauliToLd_uniform P W (fun z => f z.point)
  have hpoint := avgOver_ldPoint_uniform P.toLdParams f
  exact (hld.trans hpoint).symm

/-- Reversed-orientation Pauli-basis consistency is its mismatch mass. -/
theorem pauliBasisConsistency_eq_mismatch_interchanged {P : AdmissibleParams}
    {ε : ℝ} (S : ProjectiveSetting P ε) (W : PauliKind) :
    consistencyDefect (uniformDistribution (Fin P.m → PauliScalar P))
        (fun u a => heteroKron ((S.pauliEvalMeas .alice W u).effect a) 1)
        (fun u a => heteroKron 1 ((S.pointMeas .bob W u).effect a))
        S.toStrategy.ψ =
      avgOver (uniformDistribution (Fin P.m → PauliScalar P)) (fun u =>
        outcomeEventWeight S.toStrategy
          (pauliQuestion P W) (ProjectiveSetting.pointQuestion P W u)
          (fun A B => lowDegreeEnc (pauliAnswerOrZero A) u ≠
            ProjectiveSetting.pointAnswerOrZero B)) := by
  let X := Fin P.m → PauliScalar P
  let qA : X → PauliQuestion P := fun _ => pauliQuestion P W
  let qB : X → PauliQuestion P := fun u => ProjectiveSetting.pointQuestion P W u
  let fA : X → PauliAnswer P → PauliScalar P := fun u A =>
    lowDegreeEnc (pauliAnswerOrZero A) u
  let fB : X → PauliAnswer P → PauliScalar P := fun _ =>
    ProjectiveSetting.pointAnswerOrZero
  have h := consistencyDefect_postprocess_eq_mismatch
    (X := X) (uniformDistribution X) S.toStrategy qA qB fA fB
  have hA : ∀ (u : X) c,
      heteroKron ((S.pauliEvalMeas .alice W u).effect c)
          (1 : Op S.toStrategy.ιB) =
        heteroKron (((S.toStrategy.A (qA u)).postprocess (fA u)).effect c)
          (1 : Op S.toStrategy.ιB) := by
    intro u c
    congr 1
    unfold ProjectiveSetting.pauliEvalMeas ProjectiveSetting.pauliMeas fA qA
    rw [measurement_postprocess_comp_effect]
    rfl
  have hB : ∀ (u : X) c,
      heteroKron (1 : Op S.toStrategy.ιA) ((S.pointMeas .bob W u).effect c) =
        heteroKron (1 : Op S.toStrategy.ιA)
          (((S.toStrategy.B (qB u)).postprocess (fB u)).effect c) := by
    intro u c
    rfl
  calc
    _ = consistencyDefect (uniformDistribution X)
        (fun u c => heteroKron
          (((S.toStrategy.A (qA u)).postprocess (fA u)).effect c) 1)
        (fun u c => heteroKron 1
          (((S.toStrategy.B (qB u)).postprocess (fB u)).effect c))
        S.toStrategy.ψ := consistencyDefect_congr _ _ _ _ _ _ hA hB
    _ = avgOver (uniformDistribution X) (fun u =>
        outcomeEventWeight S.toStrategy (qA u) (qB u)
          (fun A B => fA u A ≠ fB u B)) := h
    _ = _ := by rfl

/-- Factor-interchanged form of the Pauli-basis consistency implication. Paper
`14_analysis_of_the_pauli_basis_test.tex:205-209,227`. -/
theorem win_pauli_basis_cons_interchanged_proof :
    ∃ C : ℝ, 1 ≤ C ∧
      ∀ (P : AdmissibleParams) (ε : ℝ) (S : ProjectiveSetting P ε),
      0 ≤ ε → ∀ W : PauliKind,
      consistencyDefect (uniformDistribution (Fin P.m → PauliScalar P))
        (fun u a => heteroKron ((S.pauliEvalMeas .alice W u).effect a) 1)
        (fun u a => heteroKron 1 ((S.pointMeas .bob W u).effect a))
        S.toStrategy.ψ ≤ C * ε := by
  refine ⟨(Fintype.card PauliEdge : ℝ), ?_, ?_⟩
  · exact_mod_cast (Fintype.card_pos : 0 < Fintype.card PauliEdge)
  intro P ε S _ W
  rw [pauliBasisConsistency_eq_mismatch_interchanged,
    avg_pauliBasisMismatch_eq_source_interchanged]
  calc
    _ ≤ avgOver (uniformDistribution (PauliSpace P))
        (pauliRejectionAt S.toStrategy (pauliPointEdge W)) := by
      apply avgOver_mono
      intro z
      have hs := pauliBasisMismatch_le_rejection_interchanged S W z
      rw [pauliCL_point_eq] at hs
      simpa only [pauliCL, ProjectiveSetting.pointQuestion, pauliQuestion]
        using hs
    _ ≤ (Fintype.card PauliEdge : ℝ) * ε :=
      fixedEdgeRejection_le_error S _

/-- Operator-distance and factor-interchanged companions to Pauli-basis
consistency. This is the trailing clause of `lem:qld-win-implications`, paper
`14_analysis_of_the_pauli_basis_test.tex:227,263-264`, blueprint
`ch14_qpbt_observables.tex:699-701`. -/
theorem win_pauli_basis_cons_approx_proof :
    ∃ C : ℝ, 1 ≤ C ∧
      ∀ (P : AdmissibleParams) (ε : ℝ) (S : ProjectiveSetting P ε),
      0 ≤ ε → ∀ W : PauliKind,
      opFamilyDistSq (uniformDistribution (Fin P.m → PauliScalar P))
        (fun u a => heteroKron ((S.pointMeas .alice W u).effect a) 1)
        (fun u a => heteroKron 1 ((S.pauliEvalMeas .bob W u).effect a))
        S.toStrategy.ψ ≤ C * ε ∧
      opFamilyDistSq (uniformDistribution (Fin P.m → PauliScalar P))
        (fun u a => heteroKron ((S.pointMeas .bob W u).effect a) 1)
        (fun u a => heteroKron 1 ((S.pauliEvalMeas .alice W u).effect a))
        S.swappedState ≤ C * ε := by
  obtain ⟨C₁, hC₁, h₁⟩ := win_pauli_basis_cons_proof
  obtain ⟨C₂, hC₂, h₂⟩ := win_pauli_basis_cons_interchanged_proof
  refine ⟨2 * (C₁ + C₂), by linarith, ?_⟩
  intro P ε S hε W
  have hforward := opFamilyDistSq_placed_le_of_consistencyDefect_le
    (uniformDistribution (Fin P.m → PauliScalar P))
    (fun u => S.pointMeas .alice W u)
    (fun u => S.pauliEvalMeas .bob W u) S.toStrategy.ψ (h₁ P ε S hε W)
  have hreverse := opFamilyDistSq_placed_le_of_consistencyDefect_le
    (uniformDistribution (Fin P.m → PauliScalar P))
    (fun u => S.pauliEvalMeas .alice W u)
    (fun u => S.pointMeas .bob W u) S.toStrategy.ψ (h₂ P ε S hε W)
  refine ⟨approxBound_of_left hC₂ hε hforward, ?_⟩
  have hswap := opFamilyDistSq_swappedState (ιA := S.toStrategy.ιA)
    (ιB := S.toStrategy.ιB) (uniformDistribution (Fin P.m → PauliScalar P))
    (fun u a => (S.pauliEvalMeas .alice W u).effect a)
    (fun u a => (S.pointMeas .bob W u).effect a) S.toStrategy.ψ
  exact hswap.trans_le (approxBound_of_right hC₁ hε hreverse)

end WinImplications

end

end MIPStarRE.QPBT
