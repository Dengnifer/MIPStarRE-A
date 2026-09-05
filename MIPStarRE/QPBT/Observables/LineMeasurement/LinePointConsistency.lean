import MIPStarRE.QPBT.Observables.LineMeasurement.EvalClassConsistency

/-!
# Consistency of expanded line effects with selected expanded point effects

This module proves item 2 of the expanded-line consistency lemma on the four
directed opposite-placement pairs: an expanded line effect is close to itself
followed by the expanded point effect selected by its value at the sampled
point. Because the expanded line effects are orthogonal projectors refining
the evaluation classes, this distance is dominated by the evaluation-class
distance of item 3.

## References

Item 2 of `lem:qld-comm-line-cons`, paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:569-620`,
blueprint `blueprint/src/chapter/ch14_qpbt_observables.tex:1103-1119`.
-/

open scoped BigOperators Matrix MatrixOrder ComplexOrder

namespace MIPStarRE.QPBT

open MIPStarRE.LDT hiding Measurement
open MIPStarRE.Quantum

noncomputable section

namespace ProjectiveSetting

variable {P : AdmissibleParams} {ε : ℝ}

/-! ## Item 2: line effects versus selected point effects -/

set_option synthInstance.maxSize 400 in
/-- On the directed `AA'`--`BA''` pair, the distance of item 2 is dominated by
the distance of item 3: the expanded line effects are orthogonal projectors
refining the evaluation classes. This is the projective refinement
`eq:qld-mhat-line-1` of `lem:qld-comm-line-cons`, paper
`14_analysis_of_the_pauli_basis_test.tex:569-620`. -/
theorem linePointDist_aaBa_le (S : ProjectiveSetting P ε) (W : PauliKind) :
    opFamilyDistSq (linePointDist P.toLdParams)
        (fun sample f => S.place .AA'
          ((S.lineMeasExp .alice W sample.1).effect f))
        (fun sample f =>
          S.place .AA' ((S.lineMeasExp .alice W sample.1).effect f) *
            S.place .BA'' (S.expPointEffectAtLineAnswer .bob W
              sample.1 sample.2 f))
        S.psiHat ≤
      opFamilyDistSq (linePointDist P.toLdParams)
        (fun sample a => S.place .AA'
          ((S.lineEvalMeasExp .alice W sample.1 sample.2).effect a))
        (fun sample a => S.place .BA''
          ((S.pointMeasExpOption .bob W sample.2).effect a))
        S.psiHat := by
  let X := LineDesc P.toLdParams × (Fin P.m → PauliScalar P)
  let R := PauliRegister P
  let μ := linePointDist P.toLdParams
  let e := aaBaBipartition P S.toStrategy.ιA S.toStrategy.ιB
  let M : X → Measurement (DegPoly P.toLdParams (P.m * P.d))
      (S.ExpandedLocalSpace .alice) := fun sample => S.lineMeasExp .alice W sample.1
  let B : X → Measurement (Option (PauliScalar P))
      (S.ExpandedLocalSpace .bob × (R × R)) := fun sample =>
    DistanceCalculus.leftPlacedMeasurement (ιB := R × R)
      (S.pointMeasExpOption .bob W sample.2)
  have hstep :
      opFamilyDistSq μ
          (fun sample f => S.place .AA'
          ((S.lineMeasExp .alice W sample.1).effect f))
          (fun sample f =>
            S.place .AA' ((S.lineMeasExp .alice W sample.1).effect f) *
            S.place .BA'' (S.expPointEffectAtLineAnswer .bob W
              sample.1 sample.2 f))
          S.psiHat =
        opFamilyDistSq μ (fun sample f => S.place .AA' ((M sample).effect f))
          (fun sample f =>
            S.place .AA' ((M sample).effect f) *
            S.place .BA'' ((S.pointMeasExpOption .bob W sample.2).effect
              (evalOpt sample.1 sample.2 f)))
          S.psiHat :=
    DistanceCalculus.opFamilyDistSq_congr μ _ _ _ _ S.psiHat (fun _ _ => rfl)
      (fun sample f => congrArg
        (fun Z => S.place .AA' ((M sample).effect f) * S.place .BA'' Z)
        (S.pointMeasExpOption_effect_evalOpt .bob W sample.1 sample.2 f).symm)
  have hleft :
      opFamilyDistSq μ (fun sample f => S.place .AA' ((M sample).effect f))
          (fun sample f =>
            S.place .AA' ((M sample).effect f) *
            S.place .BA'' ((S.pointMeasExpOption .bob W sample.2).effect
              (evalOpt sample.1 sample.2 f)))
          S.psiHat =
        opFamilyDistSq μ (fun sample f => heteroKron ((M sample).effect f) 1)
          (fun sample f => heteroKron ((M sample).effect f) 1 *
            heteroKron 1 ((B sample).effect (evalOpt sample.1 sample.2 f)))
          (reindexState e S.psiHat) := by
    unfold opFamilyDistSq
    apply avgOver_congr
    intro sample
    apply Finset.sum_congr rfl
    intro f _
    rw [norm_place_AA'_sub_mul_place_BA'']
    rfl
  have hright :
      opFamilyDistSq μ
          (fun sample a => S.place .AA'
            ((S.lineEvalMeasExp .alice W sample.1 sample.2).effect a))
          (fun sample a => S.place .BA''
            ((S.pointMeasExpOption .bob W sample.2).effect a))
          S.psiHat =
        opFamilyDistSq μ
          (fun sample a => heteroKron
            (((M sample).postprocess (evalOpt sample.1 sample.2)).effect a) 1)
          (fun sample a => heteroKron 1 ((B sample).effect a))
          (reindexState e S.psiHat) := by
    unfold opFamilyDistSq
    apply avgOver_congr
    intro sample
    apply Finset.sum_congr rfl
    intro a _
    rw [norm_place_AA'_sub_place_BA'']
    rfl
  rw [hstep, hleft, hright]
  exact DistanceCalculus.opFamilyDistSq_left_refine_le μ M
    (fun sample => S.lineMeasExp_isProjective .alice W sample.1)
    (fun sample f => evalOpt sample.1 sample.2 f) B (reindexState e S.psiHat)

set_option synthInstance.maxSize 400 in
/-- On the directed `BA''`--`AA'` pair, the distance of item 2 is dominated by
the distance of item 3. Paper `14_analysis_of_the_pauli_basis_test.tex:569-620`. -/
theorem linePointDist_baAa_le (S : ProjectiveSetting P ε) (W : PauliKind) :
    opFamilyDistSq (linePointDist P.toLdParams)
        (fun sample f => S.place .BA''
          ((S.lineMeasExp .bob W sample.1).effect f))
        (fun sample f =>
          S.place .BA'' ((S.lineMeasExp .bob W sample.1).effect f) *
            S.place .AA' (S.expPointEffectAtLineAnswer .alice W
              sample.1 sample.2 f))
        S.psiHat ≤
      opFamilyDistSq (linePointDist P.toLdParams)
        (fun sample a => S.place .BA''
          ((S.lineEvalMeasExp .bob W sample.1 sample.2).effect a))
        (fun sample a => S.place .AA'
          ((S.pointMeasExpOption .alice W sample.2).effect a))
        S.psiHat := by
  let X := LineDesc P.toLdParams × (Fin P.m → PauliScalar P)
  let R := PauliRegister P
  let μ := linePointDist P.toLdParams
  let e := aaBaBipartition P S.toStrategy.ιA S.toStrategy.ιB
  let M : X → Measurement (DegPoly P.toLdParams (P.m * P.d))
      (S.ExpandedLocalSpace .bob × (R × R)) := fun sample =>
    DistanceCalculus.leftPlacedMeasurement (ιB := R × R)
      (S.lineMeasExp .bob W sample.1)
  let B : X → Measurement (Option (PauliScalar P))
      (S.ExpandedLocalSpace .alice) := fun sample =>
    S.pointMeasExpOption .alice W sample.2
  have hM : ∀ sample, MIPStarRE.QPBT.Measurement.IsProjective (M sample) := by
    intro sample f
    have h := S.lineMeasExp_isProjective .bob W sample.1 f
    refine ⟨?_, ?_⟩
    · change heteroKron ((S.lineMeasExp .bob W sample.1).effect f) (1 : Op (R × R)) *
        heteroKron ((S.lineMeasExp .bob W sample.1).effect f) (1 : Op (R × R)) =
          heteroKron ((S.lineMeasExp .bob W sample.1).effect f) (1 : Op (R × R))
      rw [heteroKron_mul, Matrix.mul_one, h.isIdempotentElem.eq]
    · change star (heteroKron ((S.lineMeasExp .bob W sample.1).effect f)
        (1 : Op (R × R))) =
          heteroKron ((S.lineMeasExp .bob W sample.1).effect f) (1 : Op (R × R))
      rw [Matrix.star_eq_conjTranspose, WinImplications.heteroKron_conjTranspose,
        Matrix.conjTranspose_one]
      congr 1
      exact (Matrix.nonneg_iff_posSemidef.mp
        ((S.lineMeasExp .bob W sample.1).pos f)).isHermitian.eq
  have hstep :
      opFamilyDistSq μ
          (fun sample f => S.place .BA''
          ((S.lineMeasExp .bob W sample.1).effect f))
          (fun sample f =>
            S.place .BA'' ((S.lineMeasExp .bob W sample.1).effect f) *
            S.place .AA' (S.expPointEffectAtLineAnswer .alice W
              sample.1 sample.2 f))
          S.psiHat =
        opFamilyDistSq μ (fun sample f => S.place .BA'' ((S.lineMeasExp .bob W sample.1).effect f))
          (fun sample f =>
            S.place .BA'' ((S.lineMeasExp .bob W sample.1).effect f) *
            S.place .AA' ((S.pointMeasExpOption .alice W sample.2).effect
              (evalOpt sample.1 sample.2 f)))
          S.psiHat :=
    DistanceCalculus.opFamilyDistSq_congr μ _ _ _ _ S.psiHat (fun _ _ => rfl)
      (fun sample f => congrArg
        (fun Z => S.place .BA'' ((S.lineMeasExp .bob W sample.1).effect f) *
          S.place .AA' Z)
        (S.pointMeasExpOption_effect_evalOpt .alice W sample.1 sample.2 f).symm)
  have hleft :
      opFamilyDistSq μ (fun sample f => S.place .BA'' ((S.lineMeasExp .bob W sample.1).effect f))
          (fun sample f =>
            S.place .BA'' ((S.lineMeasExp .bob W sample.1).effect f) *
            S.place .AA' ((S.pointMeasExpOption .alice W sample.2).effect
              (evalOpt sample.1 sample.2 f)))
          S.psiHat =
        opFamilyDistSq μ (fun sample f => heteroKron 1 ((M sample).effect f))
          (fun sample f => heteroKron 1 ((M sample).effect f) *
            heteroKron ((B sample).effect (evalOpt sample.1 sample.2 f)) 1)
          (reindexState e S.psiHat) := by
    unfold opFamilyDistSq
    apply avgOver_congr
    intro sample
    apply Finset.sum_congr rfl
    intro f _
    rw [norm_place_BA''_sub_mul_place_AA']
    rfl
  have hright :
      opFamilyDistSq μ
          (fun sample a => S.place .BA''
            ((S.lineEvalMeasExp .bob W sample.1 sample.2).effect a))
          (fun sample a => S.place .AA'
            ((S.pointMeasExpOption .alice W sample.2).effect a))
          S.psiHat =
        opFamilyDistSq μ
          (fun sample a => heteroKron ((B sample).effect a) 1)
          (fun sample a => heteroKron 1
            (((M sample).postprocess (evalOpt sample.1 sample.2)).effect a))
          (reindexState e S.psiHat) := by
    rw [DistanceCalculus.opFamilyDistSq_symm]
    unfold opFamilyDistSq
    apply avgOver_congr
    intro sample
    apply Finset.sum_congr rfl
    intro a _
    rw [norm_place_AA'_sub_place_BA'']
    simp only [M, B]
    rw [leftPlacedMeasurement_postprocess_effect]
    rfl
  rw [hstep, hleft, hright]
  exact DistanceCalculus.opFamilyDistSq_right_refine_le μ M hM
    (fun sample f => evalOpt sample.1 sample.2 f) B (reindexState e S.psiHat)

set_option synthInstance.maxSize 400 in
/-- On the directed `AB''`--`BB'` pair, the distance of item 2 is dominated by
the distance of item 3. Paper `14_analysis_of_the_pauli_basis_test.tex:569-620`. -/
theorem linePointDist_abBb_le (S : ProjectiveSetting P ε) (W : PauliKind) :
    opFamilyDistSq (linePointDist P.toLdParams)
        (fun sample f => S.place .AB''
          ((S.lineMeasExp .alice W sample.1).effect f))
        (fun sample f =>
          S.place .AB'' ((S.lineMeasExp .alice W sample.1).effect f) *
            S.place .BB' (S.expPointEffectAtLineAnswer .bob W
              sample.1 sample.2 f))
        S.psiHat ≤
      opFamilyDistSq (linePointDist P.toLdParams)
        (fun sample a => S.place .AB''
          ((S.lineEvalMeasExp .alice W sample.1 sample.2).effect a))
        (fun sample a => S.place .BB'
          ((S.pointMeasExpOption .bob W sample.2).effect a))
        S.psiHat := by
  let X := LineDesc P.toLdParams × (Fin P.m → PauliScalar P)
  let R := PauliRegister P
  let μ := linePointDist P.toLdParams
  let e := abBbBipartition P S.toStrategy.ιA S.toStrategy.ιB
  let M : X → Measurement (DegPoly P.toLdParams (P.m * P.d))
      (S.ExpandedLocalSpace .alice) := fun sample => S.lineMeasExp .alice W sample.1
  let B : X → Measurement (Option (PauliScalar P))
      (S.ExpandedLocalSpace .bob × (R × R)) := fun sample =>
    DistanceCalculus.leftPlacedMeasurement (ιB := R × R)
      (S.pointMeasExpOption .bob W sample.2)
  have hstep :
      opFamilyDistSq μ
          (fun sample f => S.place .AB''
          ((S.lineMeasExp .alice W sample.1).effect f))
          (fun sample f =>
            S.place .AB'' ((S.lineMeasExp .alice W sample.1).effect f) *
            S.place .BB' (S.expPointEffectAtLineAnswer .bob W
              sample.1 sample.2 f))
          S.psiHat =
        opFamilyDistSq μ (fun sample f => S.place .AB'' ((M sample).effect f))
          (fun sample f =>
            S.place .AB'' ((M sample).effect f) *
            S.place .BB' ((S.pointMeasExpOption .bob W sample.2).effect
              (evalOpt sample.1 sample.2 f)))
          S.psiHat :=
    DistanceCalculus.opFamilyDistSq_congr μ _ _ _ _ S.psiHat (fun _ _ => rfl)
      (fun sample f => congrArg
        (fun Z => S.place .AB'' ((M sample).effect f) * S.place .BB' Z)
        (S.pointMeasExpOption_effect_evalOpt .bob W sample.1 sample.2 f).symm)
  have hleft :
      opFamilyDistSq μ (fun sample f => S.place .AB'' ((M sample).effect f))
          (fun sample f =>
            S.place .AB'' ((M sample).effect f) *
            S.place .BB' ((S.pointMeasExpOption .bob W sample.2).effect
              (evalOpt sample.1 sample.2 f)))
          S.psiHat =
        opFamilyDistSq μ (fun sample f => heteroKron ((M sample).effect f) 1)
          (fun sample f => heteroKron ((M sample).effect f) 1 *
            heteroKron 1 ((B sample).effect (evalOpt sample.1 sample.2 f)))
          (reindexState e S.psiHat) := by
    unfold opFamilyDistSq
    apply avgOver_congr
    intro sample
    apply Finset.sum_congr rfl
    intro f _
    rw [norm_place_AB''_sub_mul_place_BB']
    rfl
  have hright :
      opFamilyDistSq μ
          (fun sample a => S.place .AB''
            ((S.lineEvalMeasExp .alice W sample.1 sample.2).effect a))
          (fun sample a => S.place .BB'
            ((S.pointMeasExpOption .bob W sample.2).effect a))
          S.psiHat =
        opFamilyDistSq μ
          (fun sample a => heteroKron
            (((M sample).postprocess (evalOpt sample.1 sample.2)).effect a) 1)
          (fun sample a => heteroKron 1 ((B sample).effect a))
          (reindexState e S.psiHat) := by
    unfold opFamilyDistSq
    apply avgOver_congr
    intro sample
    apply Finset.sum_congr rfl
    intro a _
    rw [norm_place_AB''_sub_place_BB']
    rfl
  rw [hstep, hleft, hright]
  exact DistanceCalculus.opFamilyDistSq_left_refine_le μ M
    (fun sample => S.lineMeasExp_isProjective .alice W sample.1)
    (fun sample f => evalOpt sample.1 sample.2 f) B (reindexState e S.psiHat)

set_option synthInstance.maxSize 400 in
/-- On the directed `BB'`--`AB''` pair, the distance of item 2 is dominated by
the distance of item 3. Paper `14_analysis_of_the_pauli_basis_test.tex:569-620`. -/
theorem linePointDist_bbAb_le (S : ProjectiveSetting P ε) (W : PauliKind) :
    opFamilyDistSq (linePointDist P.toLdParams)
        (fun sample f => S.place .BB'
          ((S.lineMeasExp .bob W sample.1).effect f))
        (fun sample f =>
          S.place .BB' ((S.lineMeasExp .bob W sample.1).effect f) *
            S.place .AB'' (S.expPointEffectAtLineAnswer .alice W
              sample.1 sample.2 f))
        S.psiHat ≤
      opFamilyDistSq (linePointDist P.toLdParams)
        (fun sample a => S.place .BB'
          ((S.lineEvalMeasExp .bob W sample.1 sample.2).effect a))
        (fun sample a => S.place .AB''
          ((S.pointMeasExpOption .alice W sample.2).effect a))
        S.psiHat := by
  let X := LineDesc P.toLdParams × (Fin P.m → PauliScalar P)
  let R := PauliRegister P
  let μ := linePointDist P.toLdParams
  let e := abBbBipartition P S.toStrategy.ιA S.toStrategy.ιB
  let M : X → Measurement (DegPoly P.toLdParams (P.m * P.d))
      (S.ExpandedLocalSpace .bob × (R × R)) := fun sample =>
    DistanceCalculus.leftPlacedMeasurement (ιB := R × R)
      (S.lineMeasExp .bob W sample.1)
  let B : X → Measurement (Option (PauliScalar P))
      (S.ExpandedLocalSpace .alice) := fun sample =>
    S.pointMeasExpOption .alice W sample.2
  have hM : ∀ sample, MIPStarRE.QPBT.Measurement.IsProjective (M sample) := by
    intro sample f
    have h := S.lineMeasExp_isProjective .bob W sample.1 f
    refine ⟨?_, ?_⟩
    · change heteroKron ((S.lineMeasExp .bob W sample.1).effect f) (1 : Op (R × R)) *
        heteroKron ((S.lineMeasExp .bob W sample.1).effect f) (1 : Op (R × R)) =
          heteroKron ((S.lineMeasExp .bob W sample.1).effect f) (1 : Op (R × R))
      rw [heteroKron_mul, Matrix.mul_one, h.isIdempotentElem.eq]
    · change star (heteroKron ((S.lineMeasExp .bob W sample.1).effect f)
        (1 : Op (R × R))) =
          heteroKron ((S.lineMeasExp .bob W sample.1).effect f) (1 : Op (R × R))
      rw [Matrix.star_eq_conjTranspose, WinImplications.heteroKron_conjTranspose,
        Matrix.conjTranspose_one]
      congr 1
      exact (Matrix.nonneg_iff_posSemidef.mp
        ((S.lineMeasExp .bob W sample.1).pos f)).isHermitian.eq
  have hstep :
      opFamilyDistSq μ
          (fun sample f => S.place .BB'
          ((S.lineMeasExp .bob W sample.1).effect f))
          (fun sample f =>
            S.place .BB' ((S.lineMeasExp .bob W sample.1).effect f) *
            S.place .AB'' (S.expPointEffectAtLineAnswer .alice W
              sample.1 sample.2 f))
          S.psiHat =
        opFamilyDistSq μ (fun sample f => S.place .BB' ((S.lineMeasExp .bob W sample.1).effect f))
          (fun sample f =>
            S.place .BB' ((S.lineMeasExp .bob W sample.1).effect f) *
            S.place .AB'' ((S.pointMeasExpOption .alice W sample.2).effect
              (evalOpt sample.1 sample.2 f)))
          S.psiHat :=
    DistanceCalculus.opFamilyDistSq_congr μ _ _ _ _ S.psiHat (fun _ _ => rfl)
      (fun sample f => congrArg
        (fun Z => S.place .BB' ((S.lineMeasExp .bob W sample.1).effect f) *
          S.place .AB'' Z)
        (S.pointMeasExpOption_effect_evalOpt .alice W sample.1 sample.2 f).symm)
  have hleft :
      opFamilyDistSq μ (fun sample f => S.place .BB' ((S.lineMeasExp .bob W sample.1).effect f))
          (fun sample f =>
            S.place .BB' ((S.lineMeasExp .bob W sample.1).effect f) *
            S.place .AB'' ((S.pointMeasExpOption .alice W sample.2).effect
              (evalOpt sample.1 sample.2 f)))
          S.psiHat =
        opFamilyDistSq μ (fun sample f => heteroKron 1 ((M sample).effect f))
          (fun sample f => heteroKron 1 ((M sample).effect f) *
            heteroKron ((B sample).effect (evalOpt sample.1 sample.2 f)) 1)
          (reindexState e S.psiHat) := by
    unfold opFamilyDistSq
    apply avgOver_congr
    intro sample
    apply Finset.sum_congr rfl
    intro f _
    rw [norm_place_BB'_sub_mul_place_AB'']
    rfl
  have hright :
      opFamilyDistSq μ
          (fun sample a => S.place .BB'
            ((S.lineEvalMeasExp .bob W sample.1 sample.2).effect a))
          (fun sample a => S.place .AB''
            ((S.pointMeasExpOption .alice W sample.2).effect a))
          S.psiHat =
        opFamilyDistSq μ
          (fun sample a => heteroKron ((B sample).effect a) 1)
          (fun sample a => heteroKron 1
            (((M sample).postprocess (evalOpt sample.1 sample.2)).effect a))
          (reindexState e S.psiHat) := by
    rw [DistanceCalculus.opFamilyDistSq_symm]
    unfold opFamilyDistSq
    apply avgOver_congr
    intro sample
    apply Finset.sum_congr rfl
    intro a _
    rw [norm_place_AB''_sub_place_BB']
    simp only [M, B]
    rw [leftPlacedMeasurement_postprocess_effect]
    rfl
  rw [hstep, hleft, hright]
  exact DistanceCalculus.opFamilyDistSq_right_refine_le μ M hM
    (fun sample f => evalOpt sample.1 sample.2 f) B (reindexState e S.psiHat)

end ProjectiveSetting

end

end MIPStarRE.QPBT
