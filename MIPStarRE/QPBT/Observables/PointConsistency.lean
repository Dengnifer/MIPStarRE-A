import MIPStarRE.QPBT.Games.ErrorFunctions
import MIPStarRE.QPBT.Observables.Anticommuting
import MIPStarRE.QPBT.Observables.ExpandedCommutation

/-!
# Expanded point consistency and commutation

This module records the quantitative conclusions for the expanded point
measurements on each of the four register placements. No symmetry-transfer
principle is assumed: the four placements occur explicitly in the statements.

## References

The declarations formalize `lem:qld-comm-cons` in
`blueprint/src/chapter/ch14_qpbt_observables.tex:932-1032`, whose paper source
is `references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:452-505`.
-/

open scoped BigOperators Matrix MatrixOrder ComplexOrder

namespace MIPStarRE.QPBT

open MIPStarRE.LDT hiding Measurement
open MIPStarRE.Quantum

noncomputable section

local instance pauliEdgeNonemptyPointConsistency : Nonempty PauliEdge :=
  pauliEdge_nonempty

/-! ## Consistency of the unexpanded point measurements -/

/-- Full point-measurement inconsistency is the probability that the two
postprocessed point answers differ. This is the point self-loop specialization
used in item 1 of `lem:qld-comm-cons`, paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:455-465`. -/
theorem pointConsistency_eq_mismatch {P : AdmissibleParams} {ε : ℝ}
    (S : ProjectiveSetting P ε) (W : PauliKind) :
    consistencyDefect (uniformDistribution (Fin P.m → PauliScalar P))
        (fun u a => heteroKron ((S.pointMeas .alice W u).effect a) 1)
        (fun u a => heteroKron 1 ((S.pointMeas .bob W u).effect a))
        S.toStrategy.ψ =
      avgOver (uniformDistribution (Fin P.m → PauliScalar P)) (fun u =>
        outcomeEventWeight S.toStrategy
          (ProjectiveSetting.pointQuestion P W u)
          (ProjectiveSetting.pointQuestion P W u)
          (fun A B => ProjectiveSetting.pointAnswerOrZero A ≠
            ProjectiveSetting.pointAnswerOrZero B)) := by
  let X := Fin P.m → PauliScalar P
  let q : X → PauliQuestion P := fun u => ProjectiveSetting.pointQuestion P W u
  let f : X → PauliAnswer P → PauliScalar P := fun _ =>
    ProjectiveSetting.pointAnswerOrZero
  have h := WinImplications.consistencyDefect_postprocess_eq_mismatch
    (X := X) (uniformDistribution X) S.toStrategy q q f f
  have hA : ∀ (u : X) c,
      heteroKron ((S.pointMeas .alice W u).effect c)
          (1 : Op S.toStrategy.ιB) =
        heteroKron (((S.toStrategy.A (q u)).postprocess (f u)).effect c)
          (1 : Op S.toStrategy.ιB) := by
    intro u c
    rfl
  have hB : ∀ (u : X) c,
      heteroKron (1 : Op S.toStrategy.ιA)
          ((S.pointMeas .bob W u).effect c) =
        heteroKron (1 : Op S.toStrategy.ιA)
          (((S.toStrategy.B (q u)).postprocess (f u)).effect c) := by
    intro u c
    rfl
  calc
    _ = consistencyDefect (uniformDistribution X)
        (fun u c => heteroKron
          (((S.toStrategy.A (q u)).postprocess (f u)).effect c) 1)
        (fun u c => heteroKron 1
          (((S.toStrategy.B (q u)).postprocess (f u)).effect c))
        S.toStrategy.ψ :=
          WinImplications.consistencyDefect_congr _ _ _ _ _ _ hA hB
    _ = avgOver (uniformDistribution X) (fun u =>
        outcomeEventWeight S.toStrategy (q u) (q u)
          (fun A B => f u A ≠ f u B)) := h
    _ = _ := by rfl

/-- The two strategy point measurements are self-consistent on average over
the point, with the rejection bound of the point self-loop. This is the input
used at paper `14_analysis_of_the_pauli_basis_test.tex:455-465`. -/
theorem point_self_consistency_le {P : AdmissibleParams} {ε : ℝ}
    (S : ProjectiveSetting P ε) (W : PauliKind) :
    consistencyDefect (uniformDistribution (Fin P.m → PauliScalar P))
        (fun u a => heteroKron ((S.pointMeas .alice W u).effect a) 1)
        (fun u a => heteroKron 1 ((S.pointMeas .bob W u).effect a))
        S.toStrategy.ψ ≤ (Fintype.card PauliEdge : ℝ) * ε := by
  rw [pointConsistency_eq_mismatch]
  have hsource :
      avgOver (uniformDistribution (Fin P.m → PauliScalar P)) (fun u =>
          outcomeEventWeight S.toStrategy
            (ProjectiveSetting.pointQuestion P W u)
            (ProjectiveSetting.pointQuestion P W u)
            (fun A B => ProjectiveSetting.pointAnswerOrZero A ≠
              ProjectiveSetting.pointAnswerOrZero B)) =
        avgOver (uniformDistribution (PauliSpace P)) (fun z =>
          outcomeEventWeight S.toStrategy
            (ProjectiveSetting.pointQuestion P W (pauliToLd P W z).point)
            (ProjectiveSetting.pointQuestion P W (pauliToLd P W z).point)
            (fun A B => ProjectiveSetting.pointAnswerOrZero A ≠
              ProjectiveSetting.pointAnswerOrZero B)) := by
    let g : (Fin P.m → PauliScalar P) → ℝ := fun u =>
      outcomeEventWeight S.toStrategy
        (ProjectiveSetting.pointQuestion P W u)
        (ProjectiveSetting.pointQuestion P W u)
        (fun A B => ProjectiveSetting.pointAnswerOrZero A ≠
          ProjectiveSetting.pointAnswerOrZero B)
    have hld := WinImplications.avgOver_pauliToLd_uniform P W (fun z => g z.point)
    have hpoint := WinImplications.avgOver_ldPoint_uniform P.toLdParams g
    exact (hld.trans hpoint).symm
  rw [hsource]
  calc
    _ ≤ avgOver (uniformDistribution (PauliSpace P))
        (WinImplications.pauliRejectionAt S.toStrategy
          (WinImplications.pauliLoopEdge (.point W))) := by
      apply avgOver_mono
      intro z
      refine le_trans ?_
        (WinImplications.loopMismatch_le_rejection S (.point W) z)
      apply outcome_event_weight_mono
      intro A B hne hAB
      exact hne (congrArg ProjectiveSetting.pointAnswerOrZero hAB)
    _ ≤ (Fintype.card PauliEdge : ℝ) * ε :=
      WinImplications.fixedEdgeRejection_le_error S _

/-- Postprocessing a measurement after adjoining an identity register agrees
effectwise with adjoining that register after postprocessing. -/
theorem leftPlacedMeasurement_postprocess_effect
    {α β ι κ : Type*} [Fintype α] [DecidableEq α] [Fintype β]
    [DecidableEq β] [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (M : Measurement α ι) (f : α → β) (b : β) :
    ((DistanceCalculus.leftPlacedMeasurement (ιB := κ) M).postprocess f).effect b =
      heteroKron ((M.postprocess f).effect b) (1 : Op κ) := by
  rw [Measurement.postprocess_effect, Measurement.postprocess_effect]
  change (∑ a ∈ Finset.univ.filter (fun a => f a = b),
      leftTensor (ι₂ := κ) (M.effect a)) =
    leftTensor (ι₂ := κ)
      (∑ a ∈ Finset.univ.filter (fun a => f a = b), M.effect a)
  exact leftTensor_finset_sum _ _

-- The four-level product indices below exceed the default instance-search size.
namespace ProjectiveSetting

/-! ## Fine-product consistency on the two bipartitions -/

set_option synthInstance.maxSize 400 in
/-- Tensoring the strategy point measurements with the perfectly correlated
Pauli point measurement does not change their consistency defect on the
`AA' | BA''(B'B'')` bipartition. This is the product step in item 1 of
`lem:qld-comm-cons`, paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:455-465`. -/
theorem pointTauConsistency_aaBa_eq {P : AdmissibleParams} {ε : ℝ}
    (S : ProjectiveSetting P ε) (W : PauliKind) :
    consistencyDefect (uniformDistribution (Fin P.m → PauliScalar P))
        (fun u p => heteroKron ((S.pointTauMeas .alice W u).effect p)
          (1 : Op ((S.toStrategy.ιB × PauliRegister P) ×
            (PauliRegister P × PauliRegister P))))
        (fun u p => heteroKron (1 : Op (S.toStrategy.ιA × PauliRegister P))
          (heteroKron ((S.pointTauMeas .bob W u).effect p)
            (1 : Op (PauliRegister P × PauliRegister P))))
        (reindexState (aaBaBipartition P S.toStrategy.ιA S.toStrategy.ιB)
          S.psiHat) =
      consistencyDefect (uniformDistribution (Fin P.m → PauliScalar P))
        (fun u a => heteroKron ((S.pointMeas .alice W u).effect a) 1)
        (fun u a => heteroKron 1 ((S.pointMeas .bob W u).effect a))
        S.toStrategy.ψ := by
  let X := Fin P.m → PauliScalar P
  let R := PauliRegister P
  let μ := uniformDistribution X
  let e := aaBaBipartition P S.toStrategy.ιA S.toStrategy.ιB
  let fineA : X → Measurement (PauliScalar P × PauliScalar P)
      (S.toStrategy.ιA × R) := fun u => S.pointTauMeas .alice W u
  let fineB : X → Measurement (PauliScalar P × PauliScalar P)
      ((S.toStrategy.ιB × R) × (R × R)) := fun u =>
    DistanceCalculus.leftPlacedMeasurement (ιB := R × R)
      (S.pointTauMeas .bob W u)
  let A : X → Measurement (PauliScalar P × PauliScalar P)
      ((S.toStrategy.ιA × R) × ((S.toStrategy.ιB × R) × (R × R))) :=
    fun u => DistanceCalculus.leftPlacedMeasurement (fineA u)
  let B : X → Measurement (PauliScalar P × PauliScalar P)
      ((S.toStrategy.ιA × R) × ((S.toStrategy.ιB × R) × (R × R))) :=
    fun u => DistanceCalculus.rightPlacedMeasurement (fineB u)
  let pointA : X → Measurement (PauliScalar P)
      (S.toStrategy.ιA × S.toStrategy.ιB) := fun u =>
    DistanceCalculus.leftPlacedMeasurement (S.pointMeas .alice W u)
  let pointB : X → Measurement (PauliScalar P)
      (S.toStrategy.ιA × S.toStrategy.ιB) := fun u =>
    DistanceCalculus.rightPlacedMeasurement (S.pointMeas .bob W u)
  have hμ : μ.IsProbability := uniformDistribution_isProbability X
  have hgroup : ‖reindexState e S.psiHat‖ = 1 := by
    rw [norm_reindexState, psiHat_norm]
  have hfine :
      consistencyDefect μ (fun u p => (A u).effect p)
          (fun u p => (B u).effect p) (reindexState e S.psiHat) =
        1 - avgOver μ (fun u => ∑ p,
          DistanceCalculus.stateQForm (reindexState e S.psiHat)
            ((A u).effect p * (B u).effect p)) :=
    DistanceCalculus.consistencyDefect_eq_one_sub_overlap μ A B _ hμ hgroup
  have hpoint :
      consistencyDefect μ (fun u a => (pointA u).effect a)
          (fun u a => (pointB u).effect a) S.toStrategy.ψ =
        1 - avgOver μ (fun u => ∑ a,
          DistanceCalculus.stateQForm S.toStrategy.ψ
            ((pointA u).effect a * (pointB u).effect a)) :=
    DistanceCalculus.consistencyDefect_eq_one_sub_overlap μ pointA pointB _ hμ
      S.toStrategy.ψ_norm
  change consistencyDefect μ (fun u p => (A u).effect p)
      (fun u p => (B u).effect p) (reindexState e S.psiHat) =
    consistencyDefect μ (fun u a => (pointA u).effect a)
      (fun u a => (pointB u).effect a) S.toStrategy.ψ
  rw [hfine, hpoint]
  congr 1
  apply avgOver_congr
  intro u
  have hterm (p : PauliScalar P × PauliScalar P) :
      DistanceCalculus.stateQForm (reindexState e S.psiHat)
          ((A u).effect p * (B u).effect p) =
        DistanceCalculus.stateQForm S.toStrategy.ψ
            (heteroKron ((S.pointMeas .alice W u).effect p.1)
              ((S.pointMeas .bob W u).effect p.1)) *
          DistanceCalculus.stateQForm (eprState (PauliRegister P))
            (heteroKron (tauPointProj W u p.2) (tauPointProj W u p.2)) := by
    let OA : Op (S.toStrategy.ιA × R) :=
      (S.pointTauMeas .alice W u).effect p
    let OB : Op (S.toStrategy.ιB × R) :=
      (S.pointTauMeas .bob W u).effect p
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
        ((S.pointMeas .alice W u).effect p.1)
        ((S.pointMeas .bob W u).effect p.1) (tauPointProj W u p.2)
      (Matrix.nonneg_iff_posSemidef.mp
        ((S.pointMeas .alice W u).pos p.1)).isHermitian
      (Matrix.nonneg_iff_posSemidef.mp
        ((S.pointMeas .bob W u).pos p.1)).isHermitian
      (Matrix.nonneg_iff_posSemidef.mp
        ((tauPointMeas W u).pos p.2)).isHermitian using 1
    all_goals simp [OA, OB]
    all_goals rfl
  simp_rw [hterm]
  rw [Fintype.sum_prod_type]
  calc
    (∑ x : PauliScalar P, ∑ y : PauliScalar P,
        DistanceCalculus.stateQForm S.toStrategy.ψ
            (heteroKron ((S.pointMeas .alice W u).effect x)
              ((S.pointMeas .bob W u).effect x)) *
          DistanceCalculus.stateQForm (eprState R)
            (heteroKron (tauPointProj W u y) (tauPointProj W u y))) =
      (∑ x : PauliScalar P,
        DistanceCalculus.stateQForm S.toStrategy.ψ
          (heteroKron ((S.pointMeas .alice W u).effect x)
            ((S.pointMeas .bob W u).effect x))) *
        ∑ y : PauliScalar P, DistanceCalculus.stateQForm (eprState R)
          (heteroKron (tauPointProj W u y) (tauPointProj W u y)) := by
      rw [Finset.sum_mul]
      simp_rw [Finset.mul_sum]
    _ = ∑ a : PauliScalar P,
        DistanceCalculus.stateQForm S.toStrategy.ψ
          ((pointA u).effect a * (pointB u).effect a) := by
      rw [sum_tauPointProj_pair_stateQForm_eprState, mul_one]
      simp only [pointA, pointB, DistanceCalculus.leftPlacedMeasurement,
        DistanceCalculus.rightPlacedMeasurement, Measurement.ofSumEqOne]
      simp_rw [DistanceCalculus.placed_product_stateQForm_eq]

set_option synthInstance.maxSize 400 in
/-- Tensoring the strategy point measurements with the perfectly correlated
Pauli point measurement does not change their consistency defect on the
`AB'' | BB'(A'A'')` bipartition. This is the second explicit product placement
in item 1 of `lem:qld-comm-cons`, paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:455-465`. -/
theorem pointTauConsistency_abBb_eq {P : AdmissibleParams} {ε : ℝ}
    (S : ProjectiveSetting P ε) (W : PauliKind) :
    consistencyDefect (uniformDistribution (Fin P.m → PauliScalar P))
        (fun u p => heteroKron ((S.pointTauMeas .alice W u).effect p)
          (1 : Op ((S.toStrategy.ιB × PauliRegister P) ×
            (PauliRegister P × PauliRegister P))))
        (fun u p => heteroKron (1 : Op (S.toStrategy.ιA × PauliRegister P))
          (heteroKron ((S.pointTauMeas .bob W u).effect p)
            (1 : Op (PauliRegister P × PauliRegister P))))
        (reindexState (abBbBipartition P S.toStrategy.ιA S.toStrategy.ιB)
          S.psiHat) =
      consistencyDefect (uniformDistribution (Fin P.m → PauliScalar P))
        (fun u a => heteroKron ((S.pointMeas .alice W u).effect a) 1)
        (fun u a => heteroKron 1 ((S.pointMeas .bob W u).effect a))
        S.toStrategy.ψ := by
  let X := Fin P.m → PauliScalar P
  let R := PauliRegister P
  let μ := uniformDistribution X
  let e := abBbBipartition P S.toStrategy.ιA S.toStrategy.ιB
  let fineA : X → Measurement (PauliScalar P × PauliScalar P)
      (S.toStrategy.ιA × R) := fun u => S.pointTauMeas .alice W u
  let fineB : X → Measurement (PauliScalar P × PauliScalar P)
      ((S.toStrategy.ιB × R) × (R × R)) := fun u =>
    DistanceCalculus.leftPlacedMeasurement (ιB := R × R)
      (S.pointTauMeas .bob W u)
  let A : X → Measurement (PauliScalar P × PauliScalar P)
      ((S.toStrategy.ιA × R) × ((S.toStrategy.ιB × R) × (R × R))) :=
    fun u => DistanceCalculus.leftPlacedMeasurement (fineA u)
  let B : X → Measurement (PauliScalar P × PauliScalar P)
      ((S.toStrategy.ιA × R) × ((S.toStrategy.ιB × R) × (R × R))) :=
    fun u => DistanceCalculus.rightPlacedMeasurement (fineB u)
  let pointA : X → Measurement (PauliScalar P)
      (S.toStrategy.ιA × S.toStrategy.ιB) := fun u =>
    DistanceCalculus.leftPlacedMeasurement (S.pointMeas .alice W u)
  let pointB : X → Measurement (PauliScalar P)
      (S.toStrategy.ιA × S.toStrategy.ιB) := fun u =>
    DistanceCalculus.rightPlacedMeasurement (S.pointMeas .bob W u)
  have hμ : μ.IsProbability := uniformDistribution_isProbability X
  have hgroup : ‖reindexState e S.psiHat‖ = 1 := by
    rw [norm_reindexState, psiHat_norm]
  have hfine :
      consistencyDefect μ (fun u p => (A u).effect p)
          (fun u p => (B u).effect p) (reindexState e S.psiHat) =
        1 - avgOver μ (fun u => ∑ p,
          DistanceCalculus.stateQForm (reindexState e S.psiHat)
            ((A u).effect p * (B u).effect p)) :=
    DistanceCalculus.consistencyDefect_eq_one_sub_overlap μ A B _ hμ hgroup
  have hpoint :
      consistencyDefect μ (fun u a => (pointA u).effect a)
          (fun u a => (pointB u).effect a) S.toStrategy.ψ =
        1 - avgOver μ (fun u => ∑ a,
          DistanceCalculus.stateQForm S.toStrategy.ψ
            ((pointA u).effect a * (pointB u).effect a)) :=
    DistanceCalculus.consistencyDefect_eq_one_sub_overlap μ pointA pointB _ hμ
      S.toStrategy.ψ_norm
  change consistencyDefect μ (fun u p => (A u).effect p)
      (fun u p => (B u).effect p) (reindexState e S.psiHat) =
    consistencyDefect μ (fun u a => (pointA u).effect a)
      (fun u a => (pointB u).effect a) S.toStrategy.ψ
  rw [hfine, hpoint]
  congr 1
  apply avgOver_congr
  intro u
  have hterm (p : PauliScalar P × PauliScalar P) :
      DistanceCalculus.stateQForm (reindexState e S.psiHat)
          ((A u).effect p * (B u).effect p) =
        DistanceCalculus.stateQForm S.toStrategy.ψ
            (heteroKron ((S.pointMeas .alice W u).effect p.1)
              ((S.pointMeas .bob W u).effect p.1)) *
          DistanceCalculus.stateQForm (eprState (PauliRegister P))
            (heteroKron (tauPointProj W u p.2) (tauPointProj W u p.2)) := by
    let OA : Op (S.toStrategy.ιA × R) :=
      (S.pointTauMeas .alice W u).effect p
    let OB : Op (S.toStrategy.ιB × R) :=
      (S.pointTauMeas .bob W u).effect p
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
        ((S.pointMeas .alice W u).effect p.1)
        ((S.pointMeas .bob W u).effect p.1) (tauPointProj W u p.2)
      (Matrix.nonneg_iff_posSemidef.mp
        ((S.pointMeas .alice W u).pos p.1)).isHermitian
      (Matrix.nonneg_iff_posSemidef.mp
        ((S.pointMeas .bob W u).pos p.1)).isHermitian
      (Matrix.nonneg_iff_posSemidef.mp
        ((tauPointMeas W u).pos p.2)).isHermitian using 1
    all_goals simp [OA, OB]
    all_goals rfl
  simp_rw [hterm]
  rw [Fintype.sum_prod_type]
  calc
    (∑ x : PauliScalar P, ∑ y : PauliScalar P,
        DistanceCalculus.stateQForm S.toStrategy.ψ
            (heteroKron ((S.pointMeas .alice W u).effect x)
              ((S.pointMeas .bob W u).effect x)) *
          DistanceCalculus.stateQForm (eprState R)
            (heteroKron (tauPointProj W u y) (tauPointProj W u y))) =
      (∑ x : PauliScalar P,
        DistanceCalculus.stateQForm S.toStrategy.ψ
          (heteroKron ((S.pointMeas .alice W u).effect x)
            ((S.pointMeas .bob W u).effect x))) *
        ∑ y : PauliScalar P, DistanceCalculus.stateQForm (eprState R)
          (heteroKron (tauPointProj W u y) (tauPointProj W u y)) := by
      rw [Finset.sum_mul]
      simp_rw [Finset.mul_sum]
    _ = ∑ a : PauliScalar P,
        DistanceCalculus.stateQForm S.toStrategy.ψ
          ((pointA u).effect a * (pointB u).effect a) := by
      rw [sum_tauPointProj_pair_stateQForm_eprState, mul_one]
      simp only [pointA, pointB, DistanceCalculus.leftPlacedMeasurement,
        DistanceCalculus.rightPlacedMeasurement, Measurement.ofSumEqOne]
      simp_rw [DistanceCalculus.placed_product_stateQForm_eq]

/-! ## Data processing and transport back to the six registers -/

set_option synthInstance.maxSize 400 in
/-- Expanded point consistency for the directed `AA'`--`BA''` placement pair.
This is the explicit data-processing estimate for item 1 of
`lem:qld-comm-cons`, paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:468-489`,
blueprint `ch14_qpbt_observables.tex:1148-1182`. -/
theorem expPointDist_aaBa_le {P : AdmissibleParams} {ε : ℝ}
    (S : ProjectiveSetting P ε) (W : PauliKind) :
    opFamilyDistSq (uniformDistribution (Fin P.m → PauliScalar P))
        (fun u a => S.place .AA' ((S.pointMeasExp .alice W u).effect a))
        (fun u a => S.place .BA'' ((S.pointMeasExp .bob W u).effect a))
        S.psiHat ≤ 2 * ((Fintype.card PauliEdge : ℝ) * ε) := by
  let X := Fin P.m → PauliScalar P
  let R := PauliRegister P
  let μ := uniformDistribution X
  let e := aaBaBipartition P S.toStrategy.ιA S.toStrategy.ιB
  let add : PauliScalar P × PauliScalar P → PauliScalar P :=
    fun p => p.1 + p.2
  let fineA : X → Measurement (PauliScalar P × PauliScalar P)
      (S.toStrategy.ιA × R) := fun u => S.pointTauMeas .alice W u
  let fineB : X → Measurement (PauliScalar P × PauliScalar P)
      ((S.toStrategy.ιB × R) × (R × R)) := fun u =>
    DistanceCalculus.leftPlacedMeasurement (ιB := R × R)
      (S.pointTauMeas .bob W u)
  have hfine :
      consistencyDefect μ
          (fun u p => heteroKron ((fineA u).effect p)
            (1 : Op ((S.toStrategy.ιB × R) × (R × R))))
          (fun u p => heteroKron (1 : Op (S.toStrategy.ιA × R))
            ((fineB u).effect p))
          (reindexState e S.psiHat) ≤ (Fintype.card PauliEdge : ℝ) * ε := by
    calc
      _ = consistencyDefect (uniformDistribution X)
          (fun u a => heteroKron ((S.pointMeas .alice W u).effect a) 1)
          (fun u a => heteroKron 1 ((S.pointMeas .bob W u).effect a))
          S.toStrategy.ψ := by
        convert pointTauConsistency_aaBa_eq S W using 1
        all_goals rfl
      _ ≤ (Fintype.card PauliEdge : ℝ) * ε := point_self_consistency_le S W
  have hcoarse :
      consistencyDefect μ
          (fun u a => heteroKron (((fineA u).postprocess add).effect a)
            (1 : Op ((S.toStrategy.ιB × R) × (R × R))))
          (fun u a => heteroKron (1 : Op (S.toStrategy.ιA × R))
            (((fineB u).postprocess add).effect a))
          (reindexState e S.psiHat) ≤ (Fintype.card PauliEdge : ℝ) * ε :=
    le_trans (consistencyDefect_postprocess_le μ fineA fineB
      (reindexState e S.psiHat) add) hfine
  have hdist := WinImplications.opFamilyDistSq_placed_le_of_consistencyDefect_le
    μ (fun u => (fineA u).postprocess add)
      (fun u => (fineB u).postprocess add) (reindexState e S.psiHat) hcoarse
  have hAeff (u : X) (a : PauliScalar P) :
      ((fineA u).postprocess add).effect a =
        (S.pointMeasExp .alice W u).effect a := by
    convert
      (S.pointMeasExp_effect_eq_pointTauMeas_postprocess .alice W u a).symm
        using 1 <;> rfl
  have hBeff (u : X) (a : PauliScalar P) :
      ((fineB u).postprocess add).effect a =
        heteroKron ((S.pointMeasExp .bob W u).effect a) (1 : Op (R × R)) := by
    calc
      _ = heteroKron
          (((S.pointTauMeas .bob W u).postprocess add).effect a)
          (1 : Op (R × R)) := by
        convert leftPlacedMeasurement_postprocess_effect
          (S.pointTauMeas .bob W u) add a using 1 <;> rfl
      _ = _ := by
        rw [← S.pointMeasExp_effect_eq_pointTauMeas_postprocess .bob W u a]
  have hnorm (u : X) (a : PauliScalar P) :
      ‖applyOperatorToState
          (S.place .AA' ((S.pointMeasExp .alice W u).effect a) -
            S.place .BA'' ((S.pointMeasExp .bob W u).effect a)) S.psiHat‖ =
        ‖applyOperatorToState
          (heteroKron (((fineA u).postprocess add).effect a) 1 -
            heteroKron 1 (((fineB u).postprocess add).effect a))
          (reindexState e S.psiHat)‖ := by
    let OA : Op (S.toStrategy.ιA × R) :=
      (S.pointMeasExp .alice W u).effect a
    let OB : Op (S.toStrategy.ιB × R) :=
      (S.pointMeasExp .bob W u).effect a
    have hop :
        reindexOp e
            (heteroKron OA
                (1 : Op ((S.toStrategy.ιB × R) × (R × R))) -
              heteroKron (1 : Op (S.toStrategy.ιA × R))
                (heteroKron OB (1 : Op (R × R)))) =
          S.place .AA' OA - S.place .BA'' OB := by
      rw [WinImplications.reindexOp_sub,
        reindexOp_aaBaBipartition_left, reindexOp_aaBaBipartition_right]
    rw [hAeff, hBeff, WinImplications.norm_applyOperatorToState_reindexState]
    change ‖applyOperatorToState (S.place .AA' OA - S.place .BA'' OB)
        S.psiHat‖ =
      ‖applyOperatorToState
        (reindexOp e
          (heteroKron OA (1 : Op ((S.toStrategy.ιB × R) × (R × R))) -
            heteroKron (1 : Op (S.toStrategy.ιA × R))
              (heteroKron OB (1 : Op (R × R))))) S.psiHat‖
    rw [hop]
  change opFamilyDistSq μ
      (fun u a => S.place .AA' ((S.pointMeasExp .alice W u).effect a))
      (fun u a => S.place .BA'' ((S.pointMeasExp .bob W u).effect a))
      S.psiHat ≤ _
  calc
    _ = opFamilyDistSq μ
        (fun u a => heteroKron (((fineA u).postprocess add).effect a) 1)
        (fun u a => heteroKron 1 (((fineB u).postprocess add).effect a))
        (reindexState e S.psiHat) := by
      unfold opFamilyDistSq
      apply avgOver_congr
      intro u
      apply Finset.sum_congr rfl
      intro a _
      rw [hnorm]
    _ ≤ 2 * ((Fintype.card PauliEdge : ℝ) * ε) := hdist

set_option synthInstance.maxSize 400 in
/-- Expanded point consistency for the directed `AB''`--`BB'` placement pair.
This is the second bipartition of item 1 and does not assume strategy symmetry;
paper `references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:468-489`,
blueprint `ch14_qpbt_observables.tex:1148-1182`. -/
theorem expPointDist_abBb_le {P : AdmissibleParams} {ε : ℝ}
    (S : ProjectiveSetting P ε) (W : PauliKind) :
    opFamilyDistSq (uniformDistribution (Fin P.m → PauliScalar P))
        (fun u a => S.place .AB'' ((S.pointMeasExp .alice W u).effect a))
        (fun u a => S.place .BB' ((S.pointMeasExp .bob W u).effect a))
        S.psiHat ≤ 2 * ((Fintype.card PauliEdge : ℝ) * ε) := by
  let X := Fin P.m → PauliScalar P
  let R := PauliRegister P
  let μ := uniformDistribution X
  let e := abBbBipartition P S.toStrategy.ιA S.toStrategy.ιB
  let add : PauliScalar P × PauliScalar P → PauliScalar P :=
    fun p => p.1 + p.2
  let fineA : X → Measurement (PauliScalar P × PauliScalar P)
      (S.toStrategy.ιA × R) := fun u => S.pointTauMeas .alice W u
  let fineB : X → Measurement (PauliScalar P × PauliScalar P)
      ((S.toStrategy.ιB × R) × (R × R)) := fun u =>
    DistanceCalculus.leftPlacedMeasurement (ιB := R × R)
      (S.pointTauMeas .bob W u)
  have hfine :
      consistencyDefect μ
          (fun u p => heteroKron ((fineA u).effect p)
            (1 : Op ((S.toStrategy.ιB × R) × (R × R))))
          (fun u p => heteroKron (1 : Op (S.toStrategy.ιA × R))
            ((fineB u).effect p))
          (reindexState e S.psiHat) ≤ (Fintype.card PauliEdge : ℝ) * ε := by
    calc
      _ = consistencyDefect (uniformDistribution X)
          (fun u a => heteroKron ((S.pointMeas .alice W u).effect a) 1)
          (fun u a => heteroKron 1 ((S.pointMeas .bob W u).effect a))
          S.toStrategy.ψ := by
        convert pointTauConsistency_abBb_eq S W using 1
        all_goals rfl
      _ ≤ (Fintype.card PauliEdge : ℝ) * ε := point_self_consistency_le S W
  have hcoarse :
      consistencyDefect μ
          (fun u a => heteroKron (((fineA u).postprocess add).effect a)
            (1 : Op ((S.toStrategy.ιB × R) × (R × R))))
          (fun u a => heteroKron (1 : Op (S.toStrategy.ιA × R))
            (((fineB u).postprocess add).effect a))
          (reindexState e S.psiHat) ≤ (Fintype.card PauliEdge : ℝ) * ε :=
    le_trans (consistencyDefect_postprocess_le μ fineA fineB
      (reindexState e S.psiHat) add) hfine
  have hdist := WinImplications.opFamilyDistSq_placed_le_of_consistencyDefect_le
    μ (fun u => (fineA u).postprocess add)
      (fun u => (fineB u).postprocess add) (reindexState e S.psiHat) hcoarse
  have hAeff (u : X) (a : PauliScalar P) :
      ((fineA u).postprocess add).effect a =
        (S.pointMeasExp .alice W u).effect a := by
    convert
      (S.pointMeasExp_effect_eq_pointTauMeas_postprocess .alice W u a).symm
        using 1 <;> rfl
  have hBeff (u : X) (a : PauliScalar P) :
      ((fineB u).postprocess add).effect a =
        heteroKron ((S.pointMeasExp .bob W u).effect a) (1 : Op (R × R)) := by
    calc
      _ = heteroKron
          (((S.pointTauMeas .bob W u).postprocess add).effect a)
          (1 : Op (R × R)) := by
        convert leftPlacedMeasurement_postprocess_effect
          (S.pointTauMeas .bob W u) add a using 1 <;> rfl
      _ = _ := by
        rw [← S.pointMeasExp_effect_eq_pointTauMeas_postprocess .bob W u a]
  have hnorm (u : X) (a : PauliScalar P) :
      ‖applyOperatorToState
          (S.place .AB'' ((S.pointMeasExp .alice W u).effect a) -
            S.place .BB' ((S.pointMeasExp .bob W u).effect a)) S.psiHat‖ =
        ‖applyOperatorToState
          (heteroKron (((fineA u).postprocess add).effect a) 1 -
            heteroKron 1 (((fineB u).postprocess add).effect a))
          (reindexState e S.psiHat)‖ := by
    let OA : Op (S.toStrategy.ιA × R) :=
      (S.pointMeasExp .alice W u).effect a
    let OB : Op (S.toStrategy.ιB × R) :=
      (S.pointMeasExp .bob W u).effect a
    have hop :
        reindexOp e
            (heteroKron OA
                (1 : Op ((S.toStrategy.ιB × R) × (R × R))) -
              heteroKron (1 : Op (S.toStrategy.ιA × R))
                (heteroKron OB (1 : Op (R × R)))) =
          S.place .AB'' OA - S.place .BB' OB := by
      rw [WinImplications.reindexOp_sub,
        reindexOp_abBbBipartition_left, reindexOp_abBbBipartition_right]
    rw [hAeff, hBeff, WinImplications.norm_applyOperatorToState_reindexState]
    change ‖applyOperatorToState (S.place .AB'' OA - S.place .BB' OB)
        S.psiHat‖ =
      ‖applyOperatorToState
        (reindexOp e
          (heteroKron OA (1 : Op ((S.toStrategy.ιB × R) × (R × R))) -
            heteroKron (1 : Op (S.toStrategy.ιA × R))
              (heteroKron OB (1 : Op (R × R))))) S.psiHat‖
    rw [hop]
  change opFamilyDistSq μ
      (fun u a => S.place .AB'' ((S.pointMeasExp .alice W u).effect a))
      (fun u a => S.place .BB' ((S.pointMeasExp .bob W u).effect a))
      S.psiHat ≤ _
  calc
    _ = opFamilyDistSq μ
        (fun u a => heteroKron (((fineA u).postprocess add).effect a) 1)
        (fun u a => heteroKron 1 (((fineB u).postprocess add).effect a))
        (reindexState e S.psiHat) := by
      unfold opFamilyDistSq
      apply avgOver_congr
      intro u
      apply Finset.sum_congr rfl
      intro a _
      rw [hnorm]
    _ ≤ 2 * ((Fintype.card PauliEdge : ℝ) * ε) := hdist

end ProjectiveSetting

/-- The four directed cross-party placement pairs asserted by the source's
“symmetric equivalents” clause. The relation lists the two orientations of
each of the `AA'`--`BA''` and `BB'`--`AB''` pairs; paper
`14_analysis_of_the_pauli_basis_test.tex:420-450`, blueprint
`ch14_qpbt_observables.tex:876-922`. -/
def Placement.IsOpposite : Placement → Placement → Prop
  | .AA', .BA'' => True
  | .BA'', .AA' => True
  | .BB', .AB'' => True
  | .AB'', .BB' => True
  | _, _ => False

/-- The square-root error obtained by the expanded-observable commutation
argument in `lem:qld-comm-cons`, paper
`14_analysis_of_the_pauli_basis_test.tex:475-505`, blueprint
`ch14_qpbt_observables.tex:932-1032`. -/
noncomputable def deltaAnticom (ε : ℝ) : ℝ :=
  Real.sqrt ε

/-- The concrete square-root error is polynomially small in the sense used by
chapters 14 and 15. This discharges the error-function part of
`lem:qld-comm-cons`, blueprint `ch14_qpbt_observables.tex:932-1032`, from the
explicit value proved at paper `14_analysis_of_the_pauli_basis_test.tex:503-505`. -/
theorem deltaAnticom_isPolyErr : IsPolyErr deltaAnticom := by
  refine ⟨1, (2 : ℝ)⁻¹, le_rfl, by positivity, ?_⟩
  intro x hx
  constructor
  · exact Real.sqrt_nonneg x
  · rw [deltaAnticom, Real.sqrt_eq_rpow]
    simp

/-- All expanded-point conclusions at an abstract error function. The first
conjunct lists the four directed cross-party placements; the second lists all
four same-placement commutation conclusions. This proposition collects the
expanded-point conclusions of `lem:qld-comm-cons`, blueprint
`ch14_qpbt_observables.tex:932-1032`, paper
`14_analysis_of_the_pauli_basis_test.tex:452-505`. -/
def ExpandedPointConclusions (δ : ℝ → ℝ) : Prop :=
  (∃ C : ℝ, 1 ≤ C ∧
    ∀ (P : AdmissibleParams) (ε : ℝ) (S : ProjectiveSetting P ε)
      (p₁ p₂ : Placement), p₁.IsOpposite p₂ →
      ∀ W : PauliKind,
        opFamilyDistSq (uniformDistribution (Fin P.m → PauliScalar P))
          (fun u a => S.place p₁
            ((S.pointMeasExp p₁.side W u).effect a))
          (fun u a => S.place p₂
            ((S.pointMeasExp p₂.side W u).effect a))
          S.psiHat ≤ C * ε) ∧
  (∃ C : ℝ, 1 ≤ C ∧
    ∀ (P : AdmissibleParams) (ε : ℝ) (S : ProjectiveSetting P ε)
      (p : Placement),
      opFamilyDistSq (uniformDistribution (PauliTuple P))
        (fun ω (bits : ZMod 2 × ZMod 2) => S.place p
          ((S.expPointTrace p.side .X ω.1 ω.2.2.1).effect bits.1 *
            (S.expPointTrace p.side .Z ω.2.1 ω.2.2.2).effect bits.2))
        (fun ω (bits : ZMod 2 × ZMod 2) => S.place p
          ((S.expPointTrace p.side .Z ω.2.1 ω.2.2.2).effect bits.2 *
            (S.expPointTrace p.side .X ω.1 ω.2.2.1).effect bits.1))
        S.psiHat ≤ C * δ ε)

/-- Expanded point measurements are self-consistent for each of the four
directed opposite-placement pairs. The universal constant precedes all test
parameters and strategies. This is item 1 of `lem:qld-comm-cons`, paper
`14_analysis_of_the_pauli_basis_test.tex:455-465`, blueprint
`ch14_qpbt_observables.tex:942-959`. -/
theorem expPoint_self_cons :
    ∃ C : ℝ, 1 ≤ C ∧
      ∀ (P : AdmissibleParams) (ε : ℝ) (S : ProjectiveSetting P ε)
        (p₁ p₂ : Placement), p₁.IsOpposite p₂ →
        ∀ W : PauliKind,
          opFamilyDistSq (uniformDistribution (Fin P.m → PauliScalar P))
            (fun u a => S.place p₁
              ((S.pointMeasExp p₁.side W u).effect a))
            (fun u a => S.place p₂
              ((S.pointMeasExp p₂.side W u).effect a))
            S.psiHat ≤ C * ε := by
  refine ⟨2 * (Fintype.card PauliEdge : ℝ), ?_, ?_⟩
  · have hcard : (1 : ℝ) ≤ Fintype.card PauliEdge := by
      exact_mod_cast (Fintype.card_pos : 0 < Fintype.card PauliEdge)
    linarith
  intro P ε S p₁ p₂ hopp W
  cases p₁ <;> cases p₂ <;> simp only [Placement.IsOpposite] at hopp
  · simpa only [Placement.side, mul_assoc] using
      ProjectiveSetting.expPointDist_aaBa_le S W
  · rw [DistanceCalculus.opFamilyDistSq_symm]
    simpa only [Placement.side, mul_assoc] using
      ProjectiveSetting.expPointDist_aaBa_le S W
  · rw [DistanceCalculus.opFamilyDistSq_symm]
    simpa only [Placement.side, mul_assoc] using
      ProjectiveSetting.expPointDist_abBb_le S W
  · simpa only [Placement.side, mul_assoc] using
      ProjectiveSetting.expPointDist_abBb_le S W

/-- Trace-coarse-grained expanded point projections approximately commute on
each of `AA'`, `BA''`, `BB'`, and `AB''`. The universal constant precedes all
test parameters and strategies. This is item 2 of `lem:qld-comm-cons`, paper
`14_analysis_of_the_pauli_basis_test.tex:466-505`, blueprint
`ch14_qpbt_observables.tex:960-1032`. -/
theorem expPointTrace_comm :
    ∃ C : ℝ, 1 ≤ C ∧
      ∀ (P : AdmissibleParams) (ε : ℝ) (S : ProjectiveSetting P ε)
        (p : Placement),
        opFamilyDistSq (uniformDistribution (PauliTuple P))
          (fun ω (bits : ZMod 2 × ZMod 2) => S.place p
            ((S.expPointTrace p.side .X ω.1 ω.2.2.1).effect bits.1 *
              (S.expPointTrace p.side .Z ω.2.1 ω.2.2.2).effect bits.2))
          (fun ω (bits : ZMod 2 × ZMod 2) => S.place p
            ((S.expPointTrace p.side .Z ω.2.1 ω.2.2.2).effect bits.2 *
              (S.expPointTrace p.side .X ω.1 ω.2.2.1).effect bits.1))
          S.psiHat ≤ C * deltaAnticom ε :=
  ProjectiveSetting.expPointTrace_comm_proof

/-- The source's existential polynomial-error formulation, derived from the
concrete square-root bounds rather than postulated independently. This is
`lem:qld-comm-cons`, paper `14_analysis_of_the_pauli_basis_test.tex:452-505`,
blueprint `ch14_qpbt_observables.tex:932-1032`. -/
theorem exists_deltaAnticom :
    ∃ δ : ℝ → ℝ, IsPolyErr δ ∧ ExpandedPointConclusions δ := by
  refine ⟨deltaAnticom, deltaAnticom_isPolyErr, ?_⟩
  exact ⟨expPoint_self_cons, expPointTrace_comm⟩

end


end MIPStarRE.QPBT
