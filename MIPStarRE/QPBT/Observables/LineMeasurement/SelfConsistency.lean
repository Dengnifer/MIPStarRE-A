import MIPStarRE.QPBT.Observables.PointConsistency
import MIPStarRE.QPBT.Observables.LineMeasurement.Expanded
import MIPStarRE.QPBT.Observables.LineMeasurement.SquareRootError

/-!
# Self-consistency of the expanded line measurements

This module proves item 1 of the expanded-line consistency lemma on the two
opposite-placement bipartitions. The strategy line measurements are
self-consistent between the two players on average over the line-point
distribution, because a disagreement on a sampled line is rejected by the
corresponding self-loop of the Pauli basis test; the Pauli line projectors are
perfectly consistent on an EPR pair; and the data-processing inequality
transfers the product estimate to the addition postprocessing that defines the
expanded line measurement.

## References

The declarations formalize item 1 of `lem:qld-comm-line-cons` in
`blueprint/src/chapter/ch14_qpbt_observables.tex:1082-1102`, whose paper
source is `references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:559-568`.
-/

open scoped BigOperators Matrix MatrixOrder ComplexOrder

namespace MIPStarRE.QPBT

open MIPStarRE.LDT hiding Measurement
open MIPStarRE.Quantum

noncomputable section

local instance pauliEdgeNonemptyLineConsistency : Nonempty PauliEdge :=
  pauliEdge_nonempty

/-! ## Self-consistency of the unexpanded line measurements -/

/-- Mismatch mass of the two folded line answers at one sampled line.
Formalization-only auxiliary for the strategy input to item 1 of
`lem:qld-comm-line-cons`, paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:559-568`. -/
noncomputable def lineSelfMismatchMass {P : AdmissibleParams} {ε : ℝ}
    (S : ProjectiveSetting P ε) (W : PauliKind)
    (sample : LineDesc P.toLdParams × (Fin P.m → PauliScalar P)) : ℝ :=
  outcomeEventWeight S.toStrategy
    (ProjectiveSetting.lineQuestion P W sample.1)
    (ProjectiveSetting.lineQuestion P W sample.1)
    (fun A B => ProjectiveSetting.lineAnswerOrZero P sample.1 A ≠
      ProjectiveSetting.lineAnswerOrZero P sample.1 B)

/-- Full line-measurement inconsistency is the probability that the two
folded line answers differ. This is the line self-loop specialization used in
item 1 of `lem:qld-comm-line-cons`, paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:559-568`. -/
theorem lineConsistency_eq_mismatch {P : AdmissibleParams} {ε : ℝ}
    (S : ProjectiveSetting P ε) (W : PauliKind) :
    consistencyDefect (linePointDist P.toLdParams)
        (fun sample f => heteroKron ((S.lineMeas .alice W sample.1).effect f) 1)
        (fun sample f => heteroKron 1 ((S.lineMeas .bob W sample.1).effect f))
        S.toStrategy.ψ =
      avgOver (linePointDist P.toLdParams) (lineSelfMismatchMass S W) := by
  let X := LineDesc P.toLdParams × (Fin P.m → PauliScalar P)
  let q : X → PauliQuestion P := fun sample =>
    ProjectiveSetting.lineQuestion P W sample.1
  let f : X → PauliAnswer P → DegPoly P.toLdParams (P.m * P.d) :=
    fun sample => ProjectiveSetting.lineAnswerOrZero P sample.1
  have h := WinImplications.consistencyDefect_postprocess_eq_mismatch
    (X := X) (linePointDist P.toLdParams) S.toStrategy q q f f
  have hA : ∀ (sample : X) c,
      heteroKron ((S.lineMeas .alice W sample.1).effect c)
          (1 : Op S.toStrategy.ιB) =
        heteroKron (((S.toStrategy.A (q sample)).postprocess (f sample)).effect c)
          (1 : Op S.toStrategy.ιB) := by
    intro sample c
    rfl
  have hB : ∀ (sample : X) c,
      heteroKron (1 : Op S.toStrategy.ιA)
          ((S.lineMeas .bob W sample.1).effect c) =
        heteroKron (1 : Op S.toStrategy.ιA)
          (((S.toStrategy.B (q sample)).postprocess (f sample)).effect c) := by
    intro sample c
    rfl
  calc
    _ = consistencyDefect (linePointDist P.toLdParams)
        (fun sample c => heteroKron
          (((S.toStrategy.A (q sample)).postprocess (f sample)).effect c) 1)
        (fun sample c => heteroKron 1
          (((S.toStrategy.B (q sample)).postprocess (f sample)).effect c))
        S.toStrategy.ψ :=
          WinImplications.consistencyDefect_congr _ _ _ _ _ _ hA hB
    _ = avgOver (linePointDist P.toLdParams) (fun sample =>
        outcomeEventWeight S.toStrategy (q sample) (q sample)
          (fun A B => f sample A ≠ f sample B)) := h
    _ = _ := by rfl

/-- The axis component of the line-point sampler is the axis-line self-loop
branch of the Pauli basis test. Formalization-only auxiliary for item 1 of
`lem:qld-comm-line-cons`, paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:559-568`. -/
theorem avg_alineSelfMismatch_eq_source {P : AdmissibleParams} {ε : ℝ}
    (S : ProjectiveSetting P ε) (W : PauliKind) :
    avgOver (aLinePointDist P.toLdParams) (lineSelfMismatchMass S W) =
      avgOver (uniformDistribution (PauliSpace P)) (fun z =>
        outcomeEventWeight S.toStrategy
          ((.aline W), pauliCL P (.aline W) z)
          ((.aline W), pauliCL P (.aline W) z)
          (fun A B =>
            ProjectiveSetting.lineAnswerOrZero P
                (aLineDescOf P.toLdParams
                  (ldALineCL P.toLdParams (pauliToLd P W z))) A ≠
              ProjectiveSetting.lineAnswerOrZero P
                (aLineDescOf P.toLdParams
                  (ldALineCL P.toLdParams (pauliToLd P W z))) B)) := by
  unfold aLinePointDist clDistribution
  rw [Distribution.avgOver_map, Distribution.avgOver_map]
  rw [← WinImplications.avgOver_pauliToLd_uniform P W]
  apply avgOver_congr
  intro z
  rw [WinImplications.pauliCL_aline_eq]
  rfl

/-- The diagonal component of the line-point sampler is the diagonal-line
self-loop branch of the Pauli basis test. Formalization-only auxiliary for
item 1 of `lem:qld-comm-line-cons`, paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:559-568`. -/
theorem avg_dlineSelfMismatch_eq_source {P : AdmissibleParams} {ε : ℝ}
    (S : ProjectiveSetting P ε) (W : PauliKind) :
    avgOver (dLinePointDist P.toLdParams) (lineSelfMismatchMass S W) =
      avgOver (uniformDistribution (PauliSpace P)) (fun z =>
        outcomeEventWeight S.toStrategy
          ((.dline W), pauliCL P (.dline W) z)
          ((.dline W), pauliCL P (.dline W) z)
          (fun A B =>
            ProjectiveSetting.lineAnswerOrZero P
                (dLineDescOf P.toLdParams
                  (ldDLineCL P.toLdParams (pauliToLd P W z))) A ≠
              ProjectiveSetting.lineAnswerOrZero P
                (dLineDescOf P.toLdParams
                  (ldDLineCL P.toLdParams (pauliToLd P W z))) B)) := by
  unfold dLinePointDist clDistribution
  rw [Distribution.avgOver_map, Distribution.avgOver_map]
  rw [← WinImplications.avgOver_pauliToLd_uniform P W]
  apply avgOver_congr
  intro z
  rw [WinImplications.pauliCL_dline_eq]
  rfl

/-- The two strategy line measurements are self-consistent on average over
the line-point distribution, with the rejection bound of the two line
self-loops. This is the strategy input to item 1 of `lem:qld-comm-line-cons`,
paper `references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:559-568`. -/
theorem line_self_consistency_le {P : AdmissibleParams} {ε : ℝ}
    (S : ProjectiveSetting P ε) (W : PauliKind) :
    consistencyDefect (linePointDist P.toLdParams)
        (fun sample f => heteroKron ((S.lineMeas .alice W sample.1).effect f) 1)
        (fun sample f => heteroKron 1 ((S.lineMeas .bob W sample.1).effect f))
        S.toStrategy.ψ ≤ (Fintype.card PauliEdge : ℝ) * ε := by
  rw [lineConsistency_eq_mismatch]
  have ha : avgOver (aLinePointDist P.toLdParams) (lineSelfMismatchMass S W) ≤
      (Fintype.card PauliEdge : ℝ) * ε := by
    rw [avg_alineSelfMismatch_eq_source]
    calc
      _ ≤ avgOver (uniformDistribution (PauliSpace P))
          (WinImplications.pauliRejectionAt S.toStrategy
            (WinImplications.pauliLoopEdge (.aline W))) := by
        apply avgOver_mono
        intro z
        refine le_trans ?_
          (WinImplications.loopMismatch_le_rejection S (.aline W) z)
        apply outcome_event_weight_mono
        intro A B hne hAB
        exact hne (congrArg _ hAB)
      _ ≤ (Fintype.card PauliEdge : ℝ) * ε :=
        WinImplications.fixedEdgeRejection_le_error S _
  have hd : avgOver (dLinePointDist P.toLdParams) (lineSelfMismatchMass S W) ≤
      (Fintype.card PauliEdge : ℝ) * ε := by
    rw [avg_dlineSelfMismatch_eq_source]
    calc
      _ ≤ avgOver (uniformDistribution (PauliSpace P))
          (WinImplications.pauliRejectionAt S.toStrategy
            (WinImplications.pauliLoopEdge (.dline W))) := by
        apply avgOver_mono
        intro z
        refine le_trans ?_
          (WinImplications.loopMismatch_le_rejection S (.dline W) z)
        apply outcome_event_weight_mono
        intro A B hne hAB
        exact hne (congrArg _ hAB)
      _ ≤ (Fintype.card PauliEdge : ℝ) * ε :=
        WinImplications.fixedEdgeRejection_le_error S _
  rw [linePointDist, WinImplications.avgOver_mix]
  linarith

-- The four-level product indices below exceed the default instance-search size.
namespace ProjectiveSetting

variable {P : AdmissibleParams} {ε : ℝ}

/-! ## Placement of differences on the two bipartitions -/

set_option synthInstance.maxSize 400 in
/-- On the `AA' | BA''(B'B'')` bipartition, the difference of an `AA'` and a
`BA''` placement acts on the expanded state as the corresponding difference
of left and right tensor placements. Formalization-only bookkeeping for the
placement pairs of `lem:qld-comm-line-cons`, paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:559-679`. -/
theorem norm_place_AA'_sub_place_BA'' (S : ProjectiveSetting P ε)
    (O₁ : Op (S.toStrategy.ιA × PauliRegister P))
    (O₂ : Op (S.toStrategy.ιB × PauliRegister P)) :
    ‖applyOperatorToState (S.place .AA' O₁ - S.place .BA'' O₂) S.psiHat‖ =
      ‖applyOperatorToState
        (heteroKron O₁ (1 : Op ((S.toStrategy.ιB × PauliRegister P) ×
            (PauliRegister P × PauliRegister P))) -
          heteroKron (1 : Op (S.toStrategy.ιA × PauliRegister P))
            (heteroKron O₂ (1 : Op (PauliRegister P × PauliRegister P))))
        (reindexState (aaBaBipartition P S.toStrategy.ιA S.toStrategy.ιB)
          S.psiHat)‖ := by
  rw [WinImplications.norm_applyOperatorToState_reindexState,
    WinImplications.reindexOp_sub, reindexOp_aaBaBipartition_left,
    reindexOp_aaBaBipartition_right]

set_option synthInstance.maxSize 400 in
/-- On the `AB'' | BB'(A'A'')` bipartition, the difference of an `AB''` and a
`BB'` placement acts on the expanded state as the corresponding difference of
left and right tensor placements. Formalization-only bookkeeping for the
placement pairs of `lem:qld-comm-line-cons`, paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:559-679`. -/
theorem norm_place_AB''_sub_place_BB' (S : ProjectiveSetting P ε)
    (O₁ : Op (S.toStrategy.ιA × PauliRegister P))
    (O₂ : Op (S.toStrategy.ιB × PauliRegister P)) :
    ‖applyOperatorToState (S.place .AB'' O₁ - S.place .BB' O₂) S.psiHat‖ =
      ‖applyOperatorToState
        (heteroKron O₁ (1 : Op ((S.toStrategy.ιB × PauliRegister P) ×
            (PauliRegister P × PauliRegister P))) -
          heteroKron (1 : Op (S.toStrategy.ιA × PauliRegister P))
            (heteroKron O₂ (1 : Op (PauliRegister P × PauliRegister P))))
        (reindexState (abBbBipartition P S.toStrategy.ιA S.toStrategy.ιB)
          S.psiHat)‖ := by
  rw [WinImplications.norm_applyOperatorToState_reindexState,
    WinImplications.reindexOp_sub, reindexOp_abBbBipartition_left,
    reindexOp_abBbBipartition_right]

set_option synthInstance.maxSize 400 in
/-- The expanded state is a unit vector on either bipartition. -/
theorem norm_reindexState_psiHat (S : ProjectiveSetting P ε)
    (e : SixReg P S.toStrategy.ιA S.toStrategy.ιB ≃
      (S.toStrategy.ιA × PauliRegister P) ×
        ((S.toStrategy.ιB × PauliRegister P) ×
          (PauliRegister P × PauliRegister P))) :
    ‖reindexState e S.psiHat‖ = 1 := by
  rw [norm_reindexState, psiHat_norm]

/-! ## Fine-product consistency on the two bipartitions -/

set_option synthInstance.maxSize 400 in
/-- Tensoring the strategy line measurements with the perfectly correlated
Pauli line measurement does not change their consistency defect on the
`AA' | BA''(B'B'')` bipartition. This is the product step in item 1 of
`lem:qld-comm-line-cons`, paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:559-568`. -/
theorem lineTauConsistency_aaBa_eq (S : ProjectiveSetting P ε) (W : PauliKind) :
    consistencyDefect (linePointDist P.toLdParams)
        (fun sample p => heteroKron ((S.lineTauMeas .alice W sample.1).effect p)
          (1 : Op ((S.toStrategy.ιB × PauliRegister P) ×
            (PauliRegister P × PauliRegister P))))
        (fun sample p => heteroKron (1 : Op (S.toStrategy.ιA × PauliRegister P))
          (heteroKron ((S.lineTauMeas .bob W sample.1).effect p)
            (1 : Op (PauliRegister P × PauliRegister P))))
        (reindexState (aaBaBipartition P S.toStrategy.ιA S.toStrategy.ιB)
          S.psiHat) =
      consistencyDefect (linePointDist P.toLdParams)
        (fun sample f => heteroKron ((S.lineMeas .alice W sample.1).effect f) 1)
        (fun sample f => heteroKron 1 ((S.lineMeas .bob W sample.1).effect f))
        S.toStrategy.ψ := by
  let X := LineDesc P.toLdParams × (Fin P.m → PauliScalar P)
  let R := PauliRegister P
  let D := DegPoly P.toLdParams (P.m * P.d)
  let μ := linePointDist P.toLdParams
  let e := aaBaBipartition P S.toStrategy.ιA S.toStrategy.ιB
  let fineA : X → Measurement (D × D) (S.toStrategy.ιA × R) := fun sample =>
    S.lineTauMeas .alice W sample.1
  let fineB : X → Measurement (D × D) ((S.toStrategy.ιB × R) × (R × R)) :=
    fun sample => DistanceCalculus.leftPlacedMeasurement (ιB := R × R)
      (S.lineTauMeas .bob W sample.1)
  let A : X → Measurement (D × D)
      ((S.toStrategy.ιA × R) × ((S.toStrategy.ιB × R) × (R × R))) :=
    fun sample => DistanceCalculus.leftPlacedMeasurement (fineA sample)
  let B : X → Measurement (D × D)
      ((S.toStrategy.ιA × R) × ((S.toStrategy.ιB × R) × (R × R))) :=
    fun sample => DistanceCalculus.rightPlacedMeasurement (fineB sample)
  let lineA : X → Measurement D (S.toStrategy.ιA × S.toStrategy.ιB) :=
    fun sample => DistanceCalculus.leftPlacedMeasurement
      (S.lineMeas .alice W sample.1)
  let lineB : X → Measurement D (S.toStrategy.ιA × S.toStrategy.ιB) :=
    fun sample => DistanceCalculus.rightPlacedMeasurement
      (S.lineMeas .bob W sample.1)
  have hμ : μ.IsProbability := linePointDist_isProbability P.toLdParams
  have hgroup : ‖reindexState e S.psiHat‖ = 1 := norm_reindexState_psiHat S e
  have hfine :
      consistencyDefect μ (fun sample p => (A sample).effect p)
          (fun sample p => (B sample).effect p) (reindexState e S.psiHat) =
        1 - avgOver μ (fun sample => ∑ p,
          DistanceCalculus.stateQForm (reindexState e S.psiHat)
            ((A sample).effect p * (B sample).effect p)) :=
    DistanceCalculus.consistencyDefect_eq_one_sub_overlap μ A B _ hμ hgroup
  have hline :
      consistencyDefect μ (fun sample f => (lineA sample).effect f)
          (fun sample f => (lineB sample).effect f) S.toStrategy.ψ =
        1 - avgOver μ (fun sample => ∑ f,
          DistanceCalculus.stateQForm S.toStrategy.ψ
            ((lineA sample).effect f * (lineB sample).effect f)) :=
    DistanceCalculus.consistencyDefect_eq_one_sub_overlap μ lineA lineB _ hμ
      S.toStrategy.ψ_norm
  change consistencyDefect μ (fun sample p => (A sample).effect p)
      (fun sample p => (B sample).effect p) (reindexState e S.psiHat) =
    consistencyDefect μ (fun sample f => (lineA sample).effect f)
      (fun sample f => (lineB sample).effect f) S.toStrategy.ψ
  rw [hfine, hline]
  congr 1
  apply avgOver_congr
  intro sample
  have hterm (p : D × D) :
      DistanceCalculus.stateQForm (reindexState e S.psiHat)
          ((A sample).effect p * (B sample).effect p) =
        DistanceCalculus.stateQForm S.toStrategy.ψ
            (heteroKron ((S.lineMeas .alice W sample.1).effect p.1)
              ((S.lineMeas .bob W sample.1).effect p.1)) *
          DistanceCalculus.stateQForm (eprState (PauliRegister P))
            (heteroKron (tauLineProj P W sample.1 p.2)
              (tauLineProj P W sample.1 p.2)) := by
    let OA : Op (S.toStrategy.ιA × R) :=
      (S.lineTauMeas .alice W sample.1).effect p
    let OB : Op (S.toStrategy.ιB × R) :=
      (S.lineTauMeas .bob W sample.1).effect p
    have hop :
        reindexOp e (heteroKron OA
          (heteroKron OB (1 : Op (R × R)))) =
        S.place .AA' OA * S.place .BA'' OB := by
      rw [show heteroKron OA (heteroKron OB (1 : Op (R × R))) =
          heteroKron OA 1 *
            heteroKron 1 (heteroKron OB (1 : Op (R × R))) by
        rw [heteroKron_mul, Matrix.mul_one, Matrix.one_mul]]
      rw [WinImplications.reindexOp_mul,
        reindexOp_aaBaBipartition_left, reindexOp_aaBaBipartition_right]
    simp only [A, B, fineA, fineB, DistanceCalculus.leftPlacedMeasurement,
      DistanceCalculus.rightPlacedMeasurement, Measurement.ofSumEqOne]
    rw [DistanceCalculus.placed_product_stateQForm_eq,
      WinImplications.stateQForm_reindexState]
    change DistanceCalculus.stateQForm S.psiHat
        (reindexOp e (heteroKron OA (heteroKron OB (1 : Op (R × R))))) = _
    rw [hop]
    convert stateQForm_place_AA'_mul_BA'' S
        ((S.lineMeas .alice W sample.1).effect p.1)
        ((S.lineMeas .bob W sample.1).effect p.1) (tauLineProj P W sample.1 p.2)
      (Matrix.nonneg_iff_posSemidef.mp
        ((S.lineMeas .alice W sample.1).pos p.1)).isHermitian
      (Matrix.nonneg_iff_posSemidef.mp
        ((S.lineMeas .bob W sample.1).pos p.1)).isHermitian
      (Matrix.nonneg_iff_posSemidef.mp
        ((tauLineMeas P W sample.1).pos p.2)).isHermitian using 1
    all_goals simp [OA, OB]
    all_goals rfl
  simp_rw [hterm]
  rw [Fintype.sum_prod_type]
  calc
    (∑ x : D, ∑ y : D,
        DistanceCalculus.stateQForm S.toStrategy.ψ
            (heteroKron ((S.lineMeas .alice W sample.1).effect x)
              ((S.lineMeas .bob W sample.1).effect x)) *
          DistanceCalculus.stateQForm (eprState R)
            (heteroKron (tauLineProj P W sample.1 y)
              (tauLineProj P W sample.1 y))) =
      (∑ x : D,
        DistanceCalculus.stateQForm S.toStrategy.ψ
          (heteroKron ((S.lineMeas .alice W sample.1).effect x)
            ((S.lineMeas .bob W sample.1).effect x))) *
        ∑ y : D, DistanceCalculus.stateQForm (eprState R)
          (heteroKron (tauLineProj P W sample.1 y)
            (tauLineProj P W sample.1 y)) := by
      rw [Finset.sum_mul]
      simp_rw [Finset.mul_sum]
    _ = ∑ f : D,
        DistanceCalculus.stateQForm S.toStrategy.ψ
          ((lineA sample).effect f * (lineB sample).effect f) := by
      rw [sum_tauLineProj_pair_stateQForm_eprState, mul_one]
      simp only [lineA, lineB, DistanceCalculus.leftPlacedMeasurement,
        DistanceCalculus.rightPlacedMeasurement, Measurement.ofSumEqOne]
      simp_rw [DistanceCalculus.placed_product_stateQForm_eq]

set_option synthInstance.maxSize 400 in
/-- Tensoring the strategy line measurements with the perfectly correlated
Pauli line measurement does not change their consistency defect on the
`AB'' | BB'(A'A'')` bipartition. This is the second explicit product placement
in item 1 of `lem:qld-comm-line-cons`, paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:559-568`. -/
theorem lineTauConsistency_abBb_eq (S : ProjectiveSetting P ε) (W : PauliKind) :
    consistencyDefect (linePointDist P.toLdParams)
        (fun sample p => heteroKron ((S.lineTauMeas .alice W sample.1).effect p)
          (1 : Op ((S.toStrategy.ιB × PauliRegister P) ×
            (PauliRegister P × PauliRegister P))))
        (fun sample p => heteroKron (1 : Op (S.toStrategy.ιA × PauliRegister P))
          (heteroKron ((S.lineTauMeas .bob W sample.1).effect p)
            (1 : Op (PauliRegister P × PauliRegister P))))
        (reindexState (abBbBipartition P S.toStrategy.ιA S.toStrategy.ιB)
          S.psiHat) =
      consistencyDefect (linePointDist P.toLdParams)
        (fun sample f => heteroKron ((S.lineMeas .alice W sample.1).effect f) 1)
        (fun sample f => heteroKron 1 ((S.lineMeas .bob W sample.1).effect f))
        S.toStrategy.ψ := by
  let X := LineDesc P.toLdParams × (Fin P.m → PauliScalar P)
  let R := PauliRegister P
  let D := DegPoly P.toLdParams (P.m * P.d)
  let μ := linePointDist P.toLdParams
  let e := abBbBipartition P S.toStrategy.ιA S.toStrategy.ιB
  let fineA : X → Measurement (D × D) (S.toStrategy.ιA × R) := fun sample =>
    S.lineTauMeas .alice W sample.1
  let fineB : X → Measurement (D × D) ((S.toStrategy.ιB × R) × (R × R)) :=
    fun sample => DistanceCalculus.leftPlacedMeasurement (ιB := R × R)
      (S.lineTauMeas .bob W sample.1)
  let A : X → Measurement (D × D)
      ((S.toStrategy.ιA × R) × ((S.toStrategy.ιB × R) × (R × R))) :=
    fun sample => DistanceCalculus.leftPlacedMeasurement (fineA sample)
  let B : X → Measurement (D × D)
      ((S.toStrategy.ιA × R) × ((S.toStrategy.ιB × R) × (R × R))) :=
    fun sample => DistanceCalculus.rightPlacedMeasurement (fineB sample)
  let lineA : X → Measurement D (S.toStrategy.ιA × S.toStrategy.ιB) :=
    fun sample => DistanceCalculus.leftPlacedMeasurement
      (S.lineMeas .alice W sample.1)
  let lineB : X → Measurement D (S.toStrategy.ιA × S.toStrategy.ιB) :=
    fun sample => DistanceCalculus.rightPlacedMeasurement
      (S.lineMeas .bob W sample.1)
  have hμ : μ.IsProbability := linePointDist_isProbability P.toLdParams
  have hgroup : ‖reindexState e S.psiHat‖ = 1 := norm_reindexState_psiHat S e
  have hfine :
      consistencyDefect μ (fun sample p => (A sample).effect p)
          (fun sample p => (B sample).effect p) (reindexState e S.psiHat) =
        1 - avgOver μ (fun sample => ∑ p,
          DistanceCalculus.stateQForm (reindexState e S.psiHat)
            ((A sample).effect p * (B sample).effect p)) :=
    DistanceCalculus.consistencyDefect_eq_one_sub_overlap μ A B _ hμ hgroup
  have hline :
      consistencyDefect μ (fun sample f => (lineA sample).effect f)
          (fun sample f => (lineB sample).effect f) S.toStrategy.ψ =
        1 - avgOver μ (fun sample => ∑ f,
          DistanceCalculus.stateQForm S.toStrategy.ψ
            ((lineA sample).effect f * (lineB sample).effect f)) :=
    DistanceCalculus.consistencyDefect_eq_one_sub_overlap μ lineA lineB _ hμ
      S.toStrategy.ψ_norm
  change consistencyDefect μ (fun sample p => (A sample).effect p)
      (fun sample p => (B sample).effect p) (reindexState e S.psiHat) =
    consistencyDefect μ (fun sample f => (lineA sample).effect f)
      (fun sample f => (lineB sample).effect f) S.toStrategy.ψ
  rw [hfine, hline]
  congr 1
  apply avgOver_congr
  intro sample
  have hterm (p : D × D) :
      DistanceCalculus.stateQForm (reindexState e S.psiHat)
          ((A sample).effect p * (B sample).effect p) =
        DistanceCalculus.stateQForm S.toStrategy.ψ
            (heteroKron ((S.lineMeas .alice W sample.1).effect p.1)
              ((S.lineMeas .bob W sample.1).effect p.1)) *
          DistanceCalculus.stateQForm (eprState (PauliRegister P))
            (heteroKron (tauLineProj P W sample.1 p.2)
              (tauLineProj P W sample.1 p.2)) := by
    let OA : Op (S.toStrategy.ιA × R) :=
      (S.lineTauMeas .alice W sample.1).effect p
    let OB : Op (S.toStrategy.ιB × R) :=
      (S.lineTauMeas .bob W sample.1).effect p
    have hop :
        reindexOp e (heteroKron OA
          (heteroKron OB (1 : Op (R × R)))) =
        S.place .AB'' OA * S.place .BB' OB := by
      rw [show heteroKron OA (heteroKron OB (1 : Op (R × R))) =
          heteroKron OA 1 *
            heteroKron 1 (heteroKron OB (1 : Op (R × R))) by
        rw [heteroKron_mul, Matrix.mul_one, Matrix.one_mul]]
      rw [WinImplications.reindexOp_mul,
        reindexOp_abBbBipartition_left, reindexOp_abBbBipartition_right]
    simp only [A, B, fineA, fineB, DistanceCalculus.leftPlacedMeasurement,
      DistanceCalculus.rightPlacedMeasurement, Measurement.ofSumEqOne]
    rw [DistanceCalculus.placed_product_stateQForm_eq,
      WinImplications.stateQForm_reindexState]
    change DistanceCalculus.stateQForm S.psiHat
        (reindexOp e (heteroKron OA (heteroKron OB (1 : Op (R × R))))) = _
    rw [hop]
    convert stateQForm_place_AB''_mul_BB' S
        ((S.lineMeas .alice W sample.1).effect p.1)
        ((S.lineMeas .bob W sample.1).effect p.1) (tauLineProj P W sample.1 p.2)
      (Matrix.nonneg_iff_posSemidef.mp
        ((S.lineMeas .alice W sample.1).pos p.1)).isHermitian
      (Matrix.nonneg_iff_posSemidef.mp
        ((S.lineMeas .bob W sample.1).pos p.1)).isHermitian
      (Matrix.nonneg_iff_posSemidef.mp
        ((tauLineMeas P W sample.1).pos p.2)).isHermitian using 1
    all_goals simp [OA, OB]
    all_goals rfl
  simp_rw [hterm]
  rw [Fintype.sum_prod_type]
  calc
    (∑ x : D, ∑ y : D,
        DistanceCalculus.stateQForm S.toStrategy.ψ
            (heteroKron ((S.lineMeas .alice W sample.1).effect x)
              ((S.lineMeas .bob W sample.1).effect x)) *
          DistanceCalculus.stateQForm (eprState R)
            (heteroKron (tauLineProj P W sample.1 y)
              (tauLineProj P W sample.1 y))) =
      (∑ x : D,
        DistanceCalculus.stateQForm S.toStrategy.ψ
          (heteroKron ((S.lineMeas .alice W sample.1).effect x)
            ((S.lineMeas .bob W sample.1).effect x))) *
        ∑ y : D, DistanceCalculus.stateQForm (eprState R)
          (heteroKron (tauLineProj P W sample.1 y)
            (tauLineProj P W sample.1 y)) := by
      rw [Finset.sum_mul]
      simp_rw [Finset.mul_sum]
    _ = ∑ f : D,
        DistanceCalculus.stateQForm S.toStrategy.ψ
          ((lineA sample).effect f * (lineB sample).effect f) := by
      rw [sum_tauLineProj_pair_stateQForm_eprState, mul_one]
      simp only [lineA, lineB, DistanceCalculus.leftPlacedMeasurement,
        DistanceCalculus.rightPlacedMeasurement, Measurement.ofSumEqOne]
      simp_rw [DistanceCalculus.placed_product_stateQForm_eq]

/-! ## Data processing and transport back to the six registers -/

set_option synthInstance.maxSize 400 in
/-- The expanded line distance on the `AA'`--`BA''` placement pair equals the
distance of the left- and right-placed expanded line measurements on the
`AA' | BA''(B'B'')` bipartition. Formalization-only transport for item 1 of
`lem:qld-comm-line-cons`, paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:559-568`. -/
theorem expLineDist_aaBa_eq (S : ProjectiveSetting P ε) (W : PauliKind) :
    opFamilyDistSq (linePointDist P.toLdParams)
        (fun sample f => S.place .AA' ((S.lineMeasExp .alice W sample.1).effect f))
        (fun sample f => S.place .BA'' ((S.lineMeasExp .bob W sample.1).effect f))
        S.psiHat =
      opFamilyDistSq (linePointDist P.toLdParams)
        (fun sample f => heteroKron ((S.lineMeasExp .alice W sample.1).effect f)
          (1 : Op ((S.toStrategy.ιB × PauliRegister P) ×
            (PauliRegister P × PauliRegister P))))
        (fun sample f => heteroKron (1 : Op (S.toStrategy.ιA × PauliRegister P))
          ((DistanceCalculus.leftPlacedMeasurement
            (ιB := PauliRegister P × PauliRegister P)
            (S.lineMeasExp .bob W sample.1)).effect f))
        (reindexState (aaBaBipartition P S.toStrategy.ιA S.toStrategy.ιB)
          S.psiHat) := by
  unfold opFamilyDistSq
  apply avgOver_congr
  intro sample
  apply Finset.sum_congr rfl
  intro f _
  rw [norm_place_AA'_sub_place_BA'']
  rfl

set_option synthInstance.maxSize 400 in
/-- The expanded line distance on the `AB''`--`BB'` placement pair equals the
distance of the left- and right-placed expanded line measurements on the
`AB'' | BB'(A'A'')` bipartition. Formalization-only transport for item 1 of
`lem:qld-comm-line-cons`, paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:559-568`. -/
theorem expLineDist_abBb_eq (S : ProjectiveSetting P ε) (W : PauliKind) :
    opFamilyDistSq (linePointDist P.toLdParams)
        (fun sample f => S.place .AB'' ((S.lineMeasExp .alice W sample.1).effect f))
        (fun sample f => S.place .BB' ((S.lineMeasExp .bob W sample.1).effect f))
        S.psiHat =
      opFamilyDistSq (linePointDist P.toLdParams)
        (fun sample f => heteroKron ((S.lineMeasExp .alice W sample.1).effect f)
          (1 : Op ((S.toStrategy.ιB × PauliRegister P) ×
            (PauliRegister P × PauliRegister P))))
        (fun sample f => heteroKron (1 : Op (S.toStrategy.ιA × PauliRegister P))
          ((DistanceCalculus.leftPlacedMeasurement
            (ιB := PauliRegister P × PauliRegister P)
            (S.lineMeasExp .bob W sample.1)).effect f))
        (reindexState (abBbBipartition P S.toStrategy.ιA S.toStrategy.ιB)
          S.psiHat) := by
  unfold opFamilyDistSq
  apply avgOver_congr
  intro sample
  apply Finset.sum_congr rfl
  intro f _
  rw [norm_place_AB''_sub_place_BB']
  rfl

set_option synthInstance.maxSize 400 in
/-- Expanded line consistency for the directed `AA'`--`BA''` placement pair,
with the linear error of the strategy self-consistency. This is the explicit
data-processing estimate for item 1 of `lem:qld-comm-line-cons`, paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:559-568`,
blueprint `ch14_qpbt_observables.tex:1082-1102`. -/
theorem expLineDist_aaBa_le (S : ProjectiveSetting P ε) (W : PauliKind) :
    opFamilyDistSq (linePointDist P.toLdParams)
        (fun sample f => S.place .AA' ((S.lineMeasExp .alice W sample.1).effect f))
        (fun sample f => S.place .BA'' ((S.lineMeasExp .bob W sample.1).effect f))
        S.psiHat ≤ 2 * ((Fintype.card PauliEdge : ℝ) * ε) := by
  let X := LineDesc P.toLdParams × (Fin P.m → PauliScalar P)
  let R := PauliRegister P
  let D := DegPoly P.toLdParams (P.m * P.d)
  let μ := linePointDist P.toLdParams
  let e := aaBaBipartition P S.toStrategy.ιA S.toStrategy.ιB
  let add : D × D → D := fun p => p.1 + p.2
  let fineA : X → Measurement (D × D) (S.toStrategy.ιA × R) := fun sample =>
    S.lineTauMeas .alice W sample.1
  let fineB : X → Measurement (D × D) ((S.toStrategy.ιB × R) × (R × R)) :=
    fun sample => DistanceCalculus.leftPlacedMeasurement (ιB := R × R)
      (S.lineTauMeas .bob W sample.1)
  let coarseA : X → Measurement D (S.toStrategy.ιA × R) := fun sample =>
    S.lineMeasExp .alice W sample.1
  let coarseB : X → Measurement D ((S.toStrategy.ιB × R) × (R × R)) :=
    fun sample => DistanceCalculus.leftPlacedMeasurement (ιB := R × R)
      (S.lineMeasExp .bob W sample.1)
  have hfine :
      consistencyDefect μ
          (fun sample p => heteroKron ((fineA sample).effect p)
            (1 : Op ((S.toStrategy.ιB × R) × (R × R))))
          (fun sample p => heteroKron (1 : Op (S.toStrategy.ιA × R))
            ((fineB sample).effect p))
          (reindexState e S.psiHat) ≤ (Fintype.card PauliEdge : ℝ) * ε := by
    calc
      _ = consistencyDefect μ
          (fun sample f => heteroKron ((S.lineMeas .alice W sample.1).effect f) 1)
          (fun sample f => heteroKron 1 ((S.lineMeas .bob W sample.1).effect f))
          S.toStrategy.ψ := by
        convert lineTauConsistency_aaBa_eq S W using 1
        all_goals rfl
      _ ≤ (Fintype.card PauliEdge : ℝ) * ε := line_self_consistency_le S W
  have hcoarse :
      consistencyDefect μ
          (fun sample f => heteroKron (((fineA sample).postprocess add).effect f)
            (1 : Op ((S.toStrategy.ιB × R) × (R × R))))
          (fun sample f => heteroKron (1 : Op (S.toStrategy.ιA × R))
            (((fineB sample).postprocess add).effect f))
          (reindexState e S.psiHat) ≤ (Fintype.card PauliEdge : ℝ) * ε :=
    le_trans (consistencyDefect_postprocess_le μ fineA fineB
      (reindexState e S.psiHat) add) hfine
  have hAeff (sample : X) (f : D) :
      ((fineA sample).postprocess add).effect f = (coarseA sample).effect f := by
    convert
      (S.lineMeasExp_effect_eq_lineTauMeas_postprocess .alice W sample.1 f).symm
        using 1 <;> rfl
  have hBeff (sample : X) (f : D) :
      ((fineB sample).postprocess add).effect f = (coarseB sample).effect f := by
    calc
      _ = heteroKron
          (((S.lineTauMeas .bob W sample.1).postprocess add).effect f)
          (1 : Op (R × R)) := by
        convert leftPlacedMeasurement_postprocess_effect
          (S.lineTauMeas .bob W sample.1) add f using 1 <;> rfl
      _ = _ := by
        rw [← S.lineMeasExp_effect_eq_lineTauMeas_postprocess .bob W sample.1 f]
        rfl
  have hcoarse' :
      consistencyDefect μ
          (fun sample f => heteroKron ((coarseA sample).effect f)
            (1 : Op ((S.toStrategy.ιB × R) × (R × R))))
          (fun sample f => heteroKron (1 : Op (S.toStrategy.ιA × R))
            ((coarseB sample).effect f))
          (reindexState e S.psiHat) ≤ (Fintype.card PauliEdge : ℝ) * ε := by
    refine le_of_eq_of_le
      (WinImplications.consistencyDefect_congr _ _ _ _ _ _ ?_ ?_) hcoarse
    · intro sample f
      rw [hAeff]
    · intro sample f
      rw [hBeff]
  have hdist := WinImplications.opFamilyDistSq_placed_le_of_consistencyDefect_le
    μ coarseA coarseB (reindexState e S.psiHat) hcoarse'
  rw [expLineDist_aaBa_eq]
  exact hdist

set_option synthInstance.maxSize 400 in
/-- Expanded line consistency for the directed `AB''`--`BB'` placement pair,
with the linear error of the strategy self-consistency. This is the second
bipartition of item 1 and does not assume strategy symmetry; paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:559-568`,
blueprint `ch14_qpbt_observables.tex:1082-1102`. -/
theorem expLineDist_abBb_le (S : ProjectiveSetting P ε) (W : PauliKind) :
    opFamilyDistSq (linePointDist P.toLdParams)
        (fun sample f => S.place .AB'' ((S.lineMeasExp .alice W sample.1).effect f))
        (fun sample f => S.place .BB' ((S.lineMeasExp .bob W sample.1).effect f))
        S.psiHat ≤ 2 * ((Fintype.card PauliEdge : ℝ) * ε) := by
  let X := LineDesc P.toLdParams × (Fin P.m → PauliScalar P)
  let R := PauliRegister P
  let D := DegPoly P.toLdParams (P.m * P.d)
  let μ := linePointDist P.toLdParams
  let e := abBbBipartition P S.toStrategy.ιA S.toStrategy.ιB
  let add : D × D → D := fun p => p.1 + p.2
  let fineA : X → Measurement (D × D) (S.toStrategy.ιA × R) := fun sample =>
    S.lineTauMeas .alice W sample.1
  let fineB : X → Measurement (D × D) ((S.toStrategy.ιB × R) × (R × R)) :=
    fun sample => DistanceCalculus.leftPlacedMeasurement (ιB := R × R)
      (S.lineTauMeas .bob W sample.1)
  let coarseA : X → Measurement D (S.toStrategy.ιA × R) := fun sample =>
    S.lineMeasExp .alice W sample.1
  let coarseB : X → Measurement D ((S.toStrategy.ιB × R) × (R × R)) :=
    fun sample => DistanceCalculus.leftPlacedMeasurement (ιB := R × R)
      (S.lineMeasExp .bob W sample.1)
  have hfine :
      consistencyDefect μ
          (fun sample p => heteroKron ((fineA sample).effect p)
            (1 : Op ((S.toStrategy.ιB × R) × (R × R))))
          (fun sample p => heteroKron (1 : Op (S.toStrategy.ιA × R))
            ((fineB sample).effect p))
          (reindexState e S.psiHat) ≤ (Fintype.card PauliEdge : ℝ) * ε := by
    calc
      _ = consistencyDefect μ
          (fun sample f => heteroKron ((S.lineMeas .alice W sample.1).effect f) 1)
          (fun sample f => heteroKron 1 ((S.lineMeas .bob W sample.1).effect f))
          S.toStrategy.ψ := by
        convert lineTauConsistency_abBb_eq S W using 1
        all_goals rfl
      _ ≤ (Fintype.card PauliEdge : ℝ) * ε := line_self_consistency_le S W
  have hcoarse :
      consistencyDefect μ
          (fun sample f => heteroKron (((fineA sample).postprocess add).effect f)
            (1 : Op ((S.toStrategy.ιB × R) × (R × R))))
          (fun sample f => heteroKron (1 : Op (S.toStrategy.ιA × R))
            (((fineB sample).postprocess add).effect f))
          (reindexState e S.psiHat) ≤ (Fintype.card PauliEdge : ℝ) * ε :=
    le_trans (consistencyDefect_postprocess_le μ fineA fineB
      (reindexState e S.psiHat) add) hfine
  have hAeff (sample : X) (f : D) :
      ((fineA sample).postprocess add).effect f = (coarseA sample).effect f := by
    convert
      (S.lineMeasExp_effect_eq_lineTauMeas_postprocess .alice W sample.1 f).symm
        using 1 <;> rfl
  have hBeff (sample : X) (f : D) :
      ((fineB sample).postprocess add).effect f = (coarseB sample).effect f := by
    calc
      _ = heteroKron
          (((S.lineTauMeas .bob W sample.1).postprocess add).effect f)
          (1 : Op (R × R)) := by
        convert leftPlacedMeasurement_postprocess_effect
          (S.lineTauMeas .bob W sample.1) add f using 1 <;> rfl
      _ = _ := by
        rw [← S.lineMeasExp_effect_eq_lineTauMeas_postprocess .bob W sample.1 f]
        rfl
  have hcoarse' :
      consistencyDefect μ
          (fun sample f => heteroKron ((coarseA sample).effect f)
            (1 : Op ((S.toStrategy.ιB × R) × (R × R))))
          (fun sample f => heteroKron (1 : Op (S.toStrategy.ιA × R))
            ((coarseB sample).effect f))
          (reindexState e S.psiHat) ≤ (Fintype.card PauliEdge : ℝ) * ε := by
    refine le_of_eq_of_le
      (WinImplications.consistencyDefect_congr _ _ _ _ _ _ ?_ ?_) hcoarse
    · intro sample f
      rw [hAeff]
    · intro sample f
      rw [hBeff]
  have hdist := WinImplications.opFamilyDistSq_placed_le_of_consistencyDefect_le
    μ coarseA coarseB (reindexState e S.psiHat) hcoarse'
  rw [expLineDist_abBb_eq]
  exact hdist

set_option synthInstance.maxSize 400 in
/-- The expanded line distance on the `AA'`--`BA''` placement pair is at most
four. This trivial bound supplies the large-`ε` case of the common
square-root error in item 1 of `lem:qld-comm-line-cons`, paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:559-568`. -/
theorem expLineDist_aaBa_le_four (S : ProjectiveSetting P ε) (W : PauliKind) :
    opFamilyDistSq (linePointDist P.toLdParams)
        (fun sample f => S.place .AA' ((S.lineMeasExp .alice W sample.1).effect f))
        (fun sample f => S.place .BA'' ((S.lineMeasExp .bob W sample.1).effect f))
        S.psiHat ≤ 4 := by
  rw [expLineDist_aaBa_eq]
  exact DistanceCalculus.opFamilyDistSq_placed_le_four _
    (linePointDist_isProbability P.toLdParams) _ _ _
    (norm_reindexState_psiHat S _)

set_option synthInstance.maxSize 400 in
/-- The expanded line distance on the `AB''`--`BB'` placement pair is at most
four. This trivial bound supplies the large-`ε` case of the common
square-root error in item 1 of `lem:qld-comm-line-cons`, paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:559-568`. -/
theorem expLineDist_abBb_le_four (S : ProjectiveSetting P ε) (W : PauliKind) :
    opFamilyDistSq (linePointDist P.toLdParams)
        (fun sample f => S.place .AB'' ((S.lineMeasExp .alice W sample.1).effect f))
        (fun sample f => S.place .BB' ((S.lineMeasExp .bob W sample.1).effect f))
        S.psiHat ≤ 4 := by
  rw [expLineDist_abBb_eq]
  exact DistanceCalculus.opFamilyDistSq_placed_le_four _
    (linePointDist_isProbability P.toLdParams) _ _ _
    (norm_reindexState_psiHat S _)

/-- The error parameter of a projective setting is nonnegative: the expanded
line distance is nonnegative and bounded by a positive multiple of `ε`.
Formalization-only auxiliary supplying the sign hypothesis of the winning
implications used in items 2 and 3 of `lem:qld-comm-line-cons`. -/
theorem eps_nonneg (S : ProjectiveSetting P ε) : 0 ≤ ε := by
  have h := expLineDist_aaBa_le S .X
  have h0 := DistanceCalculus.opFamilyDistSq_nonneg (linePointDist P.toLdParams)
    (fun sample f => S.place .AA' ((S.lineMeasExp .alice .X sample.1).effect f))
    (fun sample f => S.place .BA'' ((S.lineMeasExp .bob .X sample.1).effect f))
    S.psiHat
  have hcard : (0 : ℝ) < Fintype.card PauliEdge := by
    exact_mod_cast (Fintype.card_pos : 0 < Fintype.card PauliEdge)
  have hprod : 0 ≤ (Fintype.card PauliEdge : ℝ) * ε := by linarith
  exact (mul_nonneg_iff_of_pos_left hcard).mp hprod

end ProjectiveSetting

end

end MIPStarRE.QPBT
