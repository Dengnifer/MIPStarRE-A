import MIPStarRE.QPBT.Combining.ExtendedLineGame.StateTransport

/-!
# Line/point rejection for the extended direct game

This module identifies the axis-line/point, diagonal-line/point, and reversed
point/axis-line branch rejections of the strategy constructed from an
`ExtendedLinesWitness` with the corresponding completed line-point defects.
These are finite postprocessing and state-transport steps in the first
paragraph of the proof of `lem:qld-4-7`; they do not establish a passing-value
bound or construct the supplied witness.

## References

- `references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1279-1288`
- Blueprint `lem:qld-4-7`.
- Issues #302, #305, #307, and #309.
-/

open scoped BigOperators MatrixOrder ComplexOrder

-- The six-register products use the same instance-search budget as StateTransport.
set_option synthInstance.maxSize 400

namespace MIPStarRE.QPBT

open MIPStarRE.LDT hiding Measurement
open MIPStarRE.Quantum

noncomputable section

namespace ExtendedLineGame

variable {P : AdmissibleParams} {epsilon deltaQ deltaL : ℝ}
variable {setting : ProjectiveSetting P epsilon}
variable {points : CombinedPointsWitness setting deltaQ}

private def onlyCoordinate : Fin P.extendedDirectLd.k :=
  ⟨0, by change 0 < 1; decide⟩

private def axisGameRead
    (sample : DirectLdSpace P.extendedDirectLd) :
    DirectLdAnswer P.extendedDirectLd → Option (PauliScalar P)
  | .alinePolys coeffs =>
      (directEvalOpt (directALineDescOf P.extendedDirectLd sample) sample.point
        (coeffs onlyCoordinate)).map (extendedDirectScalarEquiv P)
  | _ => none

private def pointGameRead :
    DirectLdAnswer P.extendedDirectLd → Option (PauliScalar P)
  | .pointVals values => some (extendedDirectScalarEquiv P (values onlyCoordinate))
  | _ => none

private theorem axis_point_win_iff_read_eq
    (sample : DirectLdSpace P.extendedDirectLd)
    (coeffs : Fin P.extendedDirectLd.k →
      Fin (P.extendedDirectLd.d + 1) → DirectScalarQ P.extendedDirectLd)
    (values : Fin P.extendedDirectLd.k → DirectScalarQ P.extendedDirectLd) :
    directLdWinPredicate P.extendedDirectLd
        (.aline, directLdMap P.extendedDirectLd .aline sample)
        (.point, directLdMap P.extendedDirectLd .point sample)
        (.alinePolys coeffs) (.pointVals values) = true ↔
      axisGameRead sample (.alinePolys coeffs) = pointGameRead (.pointVals values) := by
  let line := directALineDescOf P.extendedDirectLd sample
  have hmem : sample.point ∈ line.pointSet := by
    simpa [line, DirectLineDesc.pointSet, directALineDescOf,
      DirectLineDesc.base, DirectLineDesc.direction] using
      (mem_linePoints_lineRepMap (coordinateDirection sample.index) sample.point)
  constructor
  · intro hwin
    have heval : DirectEvaluatesTo line (coeffs onlyCoordinate) sample.point
        (values onlyCoordinate) := by
      refine ⟨hmem, ?_⟩
      intro parameter hparameter
      have hcondition : directAlinePointCondition P.extendedDirectLd
          (directLdMap P.extendedDirectLd .aline sample)
          (directLdMap P.extendedDirectLd .point sample) coeffs values := by
        simpa [directLdWinPredicate, validDirectLdAnswer] using hwin
      exact hcondition parameter (by
        simpa [line, directALineDescOf, directLdMap, DirectLineDesc.base,
          DirectLineDesc.direction] using hparameter) onlyCoordinate
    have hopt : directEvalOpt line sample.point (coeffs onlyCoordinate) =
        some (values onlyCoordinate) :=
      (directEvalOpt_eq_some_iff line sample.point (coeffs onlyCoordinate)
        (values onlyCoordinate)).2 heval
    simp [axisGameRead, pointGameRead, line, hopt]
  · intro hread
    have hopt : directEvalOpt line sample.point (coeffs onlyCoordinate) =
        some (values onlyCoordinate) := by
      cases h : directEvalOpt line sample.point (coeffs onlyCoordinate) with
      | none => simp [axisGameRead, pointGameRead, line, h] at hread
      | some value =>
          have hvalue : value = values onlyCoordinate := by
            apply (extendedDirectScalarEquiv P).injective
            simpa [axisGameRead, pointGameRead, line, h] using hread
          subst value
          rfl
    have heval := (directEvalOpt_eq_some_iff line sample.point
      (coeffs onlyCoordinate) (values onlyCoordinate)).1 hopt
    simp only [directLdWinPredicate, validDirectLdAnswer, Bool.and_self,
      ↓reduceIte, decide_eq_true_eq]
    intro parameter hparameter index
    have hindex : index = onlyCoordinate := by
      have hlt : index.val < 1 := by
        exact index.isLt
      have hzero : (onlyCoordinate (P := P)).val = 0 := rfl
      apply Fin.ext
      rw [hzero]
      omega
    subst index
    exact heval.2 parameter (by
      simpa [line, directALineDescOf, directLdMap, DirectLineDesc.base,
        DirectLineDesc.direction] using hparameter)

private theorem axisGameRead_axisAnswer_eq_of_effect_ne_zero
    (lines : ExtendedLinesWitness setting points deltaL)
    (sample : DirectLdSpace P.extendedDirectLd)
    (coeffs : DirectDegPoly P.extendedDirectLd (P.m * P.d + 1))
    (heffect : (lines.Qline .alice
      (directALineDescOf P.extendedDirectLd sample)).effect coeffs ≠ 0) :
    axisGameRead sample (axisAnswer P coeffs) =
      (directEvalOpt (directALineDescOf P.extendedDirectLd sample) sample.point coeffs).map
        (extendedDirectScalarEquiv P) := by
  change (directEvalOpt (directALineDescOf P.extendedDirectLd sample) sample.point
      (axisRead P coeffs)).map (extendedDirectScalarEquiv P) = _
  have heval (parameter : DirectScalarQ P.extendedDirectLd) :
      evalCoefficient (axisRead P coeffs) parameter = evalCoefficient coeffs parameter :=
    axisRead_eval_of_effect_ne_zero lines .alice _ rfl coeffs heffect parameter
  apply congrArg (Option.map (extendedDirectScalarEquiv P))
  cases hfull : directEvalOpt (directALineDescOf P.extendedDirectLd sample)
      sample.point coeffs with
  | none =>
      cases haxis : directEvalOpt (directALineDescOf P.extendedDirectLd sample)
          sample.point (axisRead P coeffs) with
      | none => rfl
      | some answer =>
          have hspec := (directEvalOpt_eq_some_iff _ _ _ _).1 haxis
          have hfull' : directEvalOpt (directALineDescOf P.extendedDirectLd sample)
              sample.point coeffs = some answer := by
            apply (directEvalOpt_eq_some_iff _ _ _ _).2
            exact ⟨hspec.1, fun parameter hparameter =>
              (heval parameter).symm.trans (hspec.2 parameter hparameter)⟩
          rw [hfull] at hfull'
          contradiction
  | some answer =>
      have hspec := (directEvalOpt_eq_some_iff _ _ _ _).1 hfull
      have haxis : directEvalOpt (directALineDescOf P.extendedDirectLd sample)
          sample.point (axisRead P coeffs) = some answer := by
        apply (directEvalOpt_eq_some_iff _ _ _ _).2
        exact ⟨hspec.1, fun parameter hparameter =>
          (heval parameter).trans (hspec.2 parameter hparameter)⟩
      rw [haxis]

private theorem axis_read_effect
    (lines : ExtendedLinesWitness setting points deltaL)
    (sample : DirectLdSpace P.extendedDirectLd) (answer : Option (PauliScalar P)) :
    ((((answerMeasurement lines .alice
        (.aline, directLdMap P.extendedDirectLd .aline sample)).postprocess
      (axisGameRead sample)).effect answer)) =
      (((lines.Qline .alice (directALineDescOf P.extendedDirectLd sample)).postprocess
        (fun coeffs => (directEvalOpt
          (directALineDescOf P.extendedDirectLd sample) sample.point coeffs).map
            (extendedDirectScalarEquiv P))).effect answer) := by
  classical
  unfold answerMeasurement
  rw [axis_description_canonical, MIPStarRE.Quantum.Measurement.postprocess_comp]
  simp only [MIPStarRE.Quantum.Measurement.postprocess_effect, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro coeffs _
  by_cases heffect : (lines.Qline .alice
      (directALineDescOf P.extendedDirectLd sample)).effect coeffs = 0
  · simp [heffect]
  · rw [axisGameRead_axisAnswer_eq_of_effect_ne_zero lines sample coeffs heffect]

private theorem point_read_effect
    (lines : ExtendedLinesWitness setting points deltaL)
    (sample : DirectLdSpace P.extendedDirectLd) (answer : Option (PauliScalar P)) :
    ((((answerMeasurement lines .bob
        (.point, directLdMap P.extendedDirectLd .point sample)).postprocess
      pointGameRead).effect answer)) =
      (((points.Q .bob
        (projX (directPointToPauli P sample.point))
        (projZ (directPointToPauli P sample.point))).postprocess fun values =>
          some (directPointToPauli P sample.point (alphaVar P.m) * values.1 +
            directPointToPauli P sample.point (betaVar P.m) * values.2)).effect answer) := by
  classical
  unfold answerMeasurement CombinedPointsWitness.extendedQ
  rw [MIPStarRE.Quantum.Measurement.postprocess_comp,
    MIPStarRE.Quantum.Measurement.postprocess_comp]
  rfl

private theorem rejectedTerm_eq_read_mismatch
    (lines : ExtendedLinesWitness setting points deltaL)
    (sample : DirectLdSpace P.extendedDirectLd)
    (answerA answerB : DirectLdAnswer P.extendedDirectLd) :
    (if directLdWinPredicate P.extendedDirectLd
        (.aline, directLdMap P.extendedDirectLd .aline sample)
        (.point, directLdMap P.extendedDirectLd .point sample) answerA answerB then
      0
    else outcomeWeight (strategy lines)
      (.aline, directLdMap P.extendedDirectLd .aline sample)
      (.point, directLdMap P.extendedDirectLd .point sample) answerA answerB) =
      if axisGameRead sample answerA = pointGameRead answerB then 0
      else outcomeWeight (strategy lines)
        (.aline, directLdMap P.extendedDirectLd .aline sample)
        (.point, directLdMap P.extendedDirectLd .point sample) answerA answerB := by
  classical
  cases answerA with
  | pointVals valuesA =>
      cases answerB with
      | pointVals valuesB =>
          rw [outcomeWeight_eq_zero_of_invalid lines _ _ _ _ (Or.inl rfl)]
          simp
      | alinePolys coeffsB =>
          rw [outcomeWeight_eq_zero_of_invalid lines _ _ _ _ (Or.inl rfl)]
          simp
      | dlinePolys coeffsB =>
          rw [outcomeWeight_eq_zero_of_invalid lines _ _ _ _ (Or.inl rfl)]
          simp
  | alinePolys coeffs =>
      cases answerB with
      | pointVals values =>
          by_cases hwin : directLdWinPredicate P.extendedDirectLd
              (.aline, directLdMap P.extendedDirectLd .aline sample)
              (.point, directLdMap P.extendedDirectLd .point sample)
              (.alinePolys coeffs) (.pointVals values) = true
          · have hread := (axis_point_win_iff_read_eq sample coeffs values).1 hwin
            simp [hwin, hread]
          · have hread : axisGameRead sample (.alinePolys coeffs) ≠
                pointGameRead (.pointVals values) :=
              fun h => hwin ((axis_point_win_iff_read_eq sample coeffs values).2 h)
            simp [hwin, hread]
      | alinePolys coeffsB =>
          rw [outcomeWeight_eq_zero_of_invalid lines _ _ _ _ (Or.inr rfl)]
          simp
      | dlinePolys coeffsB =>
          rw [outcomeWeight_eq_zero_of_invalid lines _ _ _ _ (Or.inr rfl)]
          simp
  | dlinePolys coeffsA =>
      cases answerB with
      | pointVals valuesB =>
          rw [outcomeWeight_eq_zero_of_invalid lines _ _ _ _ (Or.inl rfl)]
          simp
      | alinePolys coeffsB =>
          rw [outcomeWeight_eq_zero_of_invalid lines _ _ _ _ (Or.inl rfl)]
          simp
      | dlinePolys coeffsB =>
          rw [outcomeWeight_eq_zero_of_invalid lines _ _ _ _ (Or.inl rfl)]
          simp

private theorem rejectedMass_eq_read_mismatch
    (lines : ExtendedLinesWitness setting points deltaL)
    (sample : DirectLdSpace P.extendedDirectLd) :
    directRejectedMass P.extendedDirectLd (strategy lines)
        (.aline, directLdMap P.extendedDirectLd .aline sample)
        (.point, directLdMap P.extendedDirectLd .point sample) =
      outcomeEventWeight (strategy lines)
        (.aline, directLdMap P.extendedDirectLd .aline sample)
        (.point, directLdMap P.extendedDirectLd .point sample)
        (fun answerA answerB => axisGameRead sample answerA ≠ pointGameRead answerB) := by
  classical
  unfold directRejectedMass outcomeEventWeight
  apply Finset.sum_congr rfl
  intro answerA _
  apply Finset.sum_congr rfl
  intro answerB _
  have hterm := rejectedTerm_eq_read_mismatch lines sample answerA answerB
  by_cases hread : axisGameRead sample answerA = pointGameRead answerB
  · simpa [hread] using hterm
  · simpa [hread] using hterm

private theorem completed_defect_eq_read_defect
    (lines : ExtendedLinesWitness setting points deltaL) :
    completedLinePointDefect lines .AA' .BA''
        (directALinePointDist P.extendedDirectLd) =
      consistencyDefect (uniformDistribution (DirectLdSpace P.extendedDirectLd))
        (fun sample answer => heteroKron
          (((answerMeasurement lines .alice
            (.aline, directLdMap P.extendedDirectLd .aline sample)).postprocess
              (axisGameRead sample)).effect answer) 1)
        (fun sample answer => heteroKron 1
          (((answerMeasurement lines .bob
            (.point, directLdMap P.extendedDirectLd .point sample)).postprocess
              pointGameRead).effect answer))
        (pairState setting) := by
  unfold completedLinePointDefect consistencyDefect
  rw [directALinePointDist, Distribution.avgOver_map]
  apply avgOver_congr
  intro sample
  apply Finset.sum_congr rfl
  intro answerA _
  apply Finset.sum_congr rfl
  intro answerB _
  by_cases hab : answerA = answerB
  · simp [hab]
  · simp only [hab, if_false, DistanceCalculus.consistency_term_eq_stateQForm]
    rw [axis_read_effect lines sample answerA, point_read_effect lines sample answerB,
      DistanceCalculus.placed_product_stateQForm_eq]
    symm
    apply stateQForm_pairState_eq_AA'_BA''
    · exact (Matrix.nonneg_iff_posSemidef.mp
        (((lines.Qline .alice
          (directALineDescOf P.extendedDirectLd sample)).postprocess
            (fun coeffs => (directEvalOpt
              (directALineDescOf P.extendedDirectLd sample) sample.point coeffs).map
                (extendedDirectScalarEquiv P))).pos answerA)).isHermitian
    · exact (Matrix.nonneg_iff_posSemidef.mp
        (((points.Q .bob
          (projX (directPointToPauli P sample.point))
          (projZ (directPointToPauli P sample.point))).postprocess fun values =>
            some (directPointToPauli P sample.point (alphaVar P.m) * values.1 +
              directPointToPauli P sample.point (betaVar P.m) * values.2)).pos answerB)).isHermitian

/-- The axis-line/point branch rejection of the supplied strategy is exactly
the `AA'`--`BA''` completed line-point defect.  This uses only the supplied
measurement witness, its degree support, finite postprocessing, and the
state-correlation identity from issue #302. -/
theorem aline_point_rejection_eq_completedLinePointDefect
    (lines : ExtendedLinesWitness setting points deltaL) :
    directLdBranchRejectionProbability P.extendedDirectLd (strategy lines)
        (.aline, .point) =
      completedLinePointDefect lines .AA' .BA''
        (directALinePointDist P.extendedDirectLd) := by
  rw [directLdBranchRejectionProbability_eq_avgOver]
  calc
    avgOver (uniformDistribution (DirectLdSpace P.extendedDirectLd))
        (fun sample => directRejectedMass P.extendedDirectLd (strategy lines)
          (.aline, directLdMap P.extendedDirectLd .aline sample)
          (.point, directLdMap P.extendedDirectLd .point sample)) =
        avgOver (uniformDistribution (DirectLdSpace P.extendedDirectLd))
          (fun sample => outcomeEventWeight (strategy lines)
            (.aline, directLdMap P.extendedDirectLd .aline sample)
            (.point, directLdMap P.extendedDirectLd .point sample)
            (fun answerA answerB =>
              axisGameRead sample answerA ≠ pointGameRead answerB)) := by
      apply avgOver_congr
      exact rejectedMass_eq_read_mismatch lines
    _ = consistencyDefect (uniformDistribution (DirectLdSpace P.extendedDirectLd))
        (fun sample answer => heteroKron
          (((answerMeasurement lines .alice
            (.aline, directLdMap P.extendedDirectLd .aline sample)).postprocess
              (axisGameRead sample)).effect answer) 1)
        (fun sample answer => heteroKron 1
          (((answerMeasurement lines .bob
            (.point, directLdMap P.extendedDirectLd .point sample)).postprocess
              pointGameRead).effect answer))
        (pairState setting) :=
      by
        exact (WinImplications.consistencyDefect_postprocess_eq_mismatch
          (uniformDistribution (DirectLdSpace P.extendedDirectLd)) (strategy lines)
          (fun sample => (.aline, directLdMap P.extendedDirectLd .aline sample))
          (fun sample => (.point, directLdMap P.extendedDirectLd .point sample))
          axisGameRead (fun _ => pointGameRead)).symm
    _ = completedLinePointDefect lines .AA' .BA''
        (directALinePointDist P.extendedDirectLd) :=
      (completed_defect_eq_read_defect lines).symm

private def diagonalGameRead
    (sample : DirectLdSpace P.extendedDirectLd) :
    DirectLdAnswer P.extendedDirectLd → Option (PauliScalar P)
  | .dlinePolys coeffs =>
      (directEvalOpt (directDLineDescOf P.extendedDirectLd sample) sample.point
        (coeffs onlyCoordinate)).map (extendedDirectScalarEquiv P)
  | _ => none

private theorem diagonal_point_win_iff_read_eq
    (sample : DirectLdSpace P.extendedDirectLd)
    (coeffs : Fin P.extendedDirectLd.k →
      Fin (P.extendedDirectLd.m * P.extendedDirectLd.d + 1) →
        DirectScalarQ P.extendedDirectLd)
    (values : Fin P.extendedDirectLd.k → DirectScalarQ P.extendedDirectLd) :
    directLdWinPredicate P.extendedDirectLd
        (.dline, directLdMap P.extendedDirectLd .dline sample)
        (.point, directLdMap P.extendedDirectLd .point sample)
        (.dlinePolys coeffs) (.pointVals values) = true ↔
      diagonalGameRead sample (.dlinePolys coeffs) = pointGameRead (.pointVals values) := by
  let line := directDLineDescOf P.extendedDirectLd sample
  have hmem : sample.point ∈ line.pointSet := by
    simpa [line, DirectLineDesc.pointSet, directDLineDescOf,
      DirectLineDesc.base, DirectLineDesc.direction] using
      (mem_linePoints_lineRepMap
        (directPrefixProjection sample.index sample.direction) sample.point)
  constructor
  · intro hwin
    have heval : DirectEvaluatesTo line (coeffs onlyCoordinate) sample.point
        (values onlyCoordinate) := by
      refine ⟨hmem, ?_⟩
      intro parameter hparameter
      have hcondition : directDlinePointCondition P.extendedDirectLd
          (directLdMap P.extendedDirectLd .dline sample)
          (directLdMap P.extendedDirectLd .point sample) coeffs values := by
        simpa [directLdWinPredicate, validDirectLdAnswer] using hwin
      exact hcondition parameter (by
        simpa [line, directDLineDescOf, directLdMap, DirectLineDesc.base,
          DirectLineDesc.direction] using hparameter) onlyCoordinate
    have hopt : directEvalOpt line sample.point (coeffs onlyCoordinate) =
        some (values onlyCoordinate) :=
      (directEvalOpt_eq_some_iff line sample.point (coeffs onlyCoordinate)
        (values onlyCoordinate)).2 heval
    simp [diagonalGameRead, pointGameRead, line, hopt]
  · intro hread
    have hopt : directEvalOpt line sample.point (coeffs onlyCoordinate) =
        some (values onlyCoordinate) := by
      cases h : directEvalOpt line sample.point (coeffs onlyCoordinate) with
      | none => simp [diagonalGameRead, pointGameRead, line, h] at hread
      | some value =>
          have hvalue : value = values onlyCoordinate := by
            apply (extendedDirectScalarEquiv P).injective
            simpa [diagonalGameRead, pointGameRead, line, h] using hread
          subst value
          rfl
    have heval := (directEvalOpt_eq_some_iff line sample.point
      (coeffs onlyCoordinate) (values onlyCoordinate)).1 hopt
    simp only [directLdWinPredicate, validDirectLdAnswer, Bool.and_self,
      ↓reduceIte, decide_eq_true_eq]
    intro parameter hparameter index
    have hindex : index = onlyCoordinate := by
      have hlt : index.val < 1 := index.isLt
      have hzero : (onlyCoordinate (P := P)).val = 0 := rfl
      apply Fin.ext
      rw [hzero]
      omega
    subst index
    exact heval.2 parameter (by
      simpa [line, directDLineDescOf, directLdMap, DirectLineDesc.base,
        DirectLineDesc.direction] using hparameter)

private theorem diagonalGameRead_diagonalAnswer_eq
    (sample : DirectLdSpace P.extendedDirectLd)
    (coeffs : DirectDegPoly P.extendedDirectLd (P.m * P.d + 1)) :
    diagonalGameRead sample (diagonalAnswer P coeffs) =
      (directEvalOpt (directDLineDescOf P.extendedDirectLd sample) sample.point coeffs).map
        (extendedDirectScalarEquiv P) := by
  change (directEvalOpt (directDLineDescOf P.extendedDirectLd sample) sample.point
      (diagonalRead P coeffs)).map (extendedDirectScalarEquiv P) = _
  have heval (parameter : DirectScalarQ P.extendedDirectLd) :
      evalCoefficient (diagonalRead P coeffs) parameter = evalCoefficient coeffs parameter :=
    diagonalRead_eval P coeffs parameter
  apply congrArg (Option.map (extendedDirectScalarEquiv P))
  cases hfull : directEvalOpt (directDLineDescOf P.extendedDirectLd sample)
      sample.point coeffs with
  | none =>
      cases hdiagonal : directEvalOpt (directDLineDescOf P.extendedDirectLd sample)
          sample.point (diagonalRead P coeffs) with
      | none => rfl
      | some answer =>
          have hspec := (directEvalOpt_eq_some_iff _ _ _ _).1 hdiagonal
          have hfull' : directEvalOpt (directDLineDescOf P.extendedDirectLd sample)
              sample.point coeffs = some answer := by
            apply (directEvalOpt_eq_some_iff _ _ _ _).2
            exact ⟨hspec.1, fun parameter hparameter =>
              (heval parameter).symm.trans (hspec.2 parameter hparameter)⟩
          rw [hfull] at hfull'
          contradiction
  | some answer =>
      have hspec := (directEvalOpt_eq_some_iff _ _ _ _).1 hfull
      have hdiagonal : directEvalOpt (directDLineDescOf P.extendedDirectLd sample)
          sample.point (diagonalRead P coeffs) = some answer := by
        apply (directEvalOpt_eq_some_iff _ _ _ _).2
        exact ⟨hspec.1, fun parameter hparameter =>
          (heval parameter).trans (hspec.2 parameter hparameter)⟩
      rw [hdiagonal]

private theorem diagonal_read_effect
    (lines : ExtendedLinesWitness setting points deltaL)
    (sample : DirectLdSpace P.extendedDirectLd) (answer : Option (PauliScalar P)) :
    ((((answerMeasurement lines .alice
        (.dline, directLdMap P.extendedDirectLd .dline sample)).postprocess
      (diagonalGameRead sample)).effect answer)) =
      (((lines.Qline .alice (directDLineDescOf P.extendedDirectLd sample)).postprocess
        (fun coeffs => (directEvalOpt
          (directDLineDescOf P.extendedDirectLd sample) sample.point coeffs).map
            (extendedDirectScalarEquiv P))).effect answer) := by
  classical
  unfold answerMeasurement
  rw [diagonal_description_canonical, MIPStarRE.Quantum.Measurement.postprocess_comp]
  simp only [MIPStarRE.Quantum.Measurement.postprocess_effect, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro coeffs _
  rw [diagonalGameRead_diagonalAnswer_eq]

private theorem diagonal_rejectedTerm_eq_read_mismatch
    (lines : ExtendedLinesWitness setting points deltaL)
    (sample : DirectLdSpace P.extendedDirectLd)
    (answerA answerB : DirectLdAnswer P.extendedDirectLd) :
    (if directLdWinPredicate P.extendedDirectLd
        (.dline, directLdMap P.extendedDirectLd .dline sample)
        (.point, directLdMap P.extendedDirectLd .point sample) answerA answerB then
      0
    else outcomeWeight (strategy lines)
      (.dline, directLdMap P.extendedDirectLd .dline sample)
      (.point, directLdMap P.extendedDirectLd .point sample) answerA answerB) =
      if diagonalGameRead sample answerA = pointGameRead answerB then 0
      else outcomeWeight (strategy lines)
        (.dline, directLdMap P.extendedDirectLd .dline sample)
        (.point, directLdMap P.extendedDirectLd .point sample) answerA answerB := by
  classical
  cases answerA with
  | pointVals valuesA =>
      cases answerB with
      | pointVals valuesB =>
          rw [outcomeWeight_eq_zero_of_invalid lines _ _ _ _ (Or.inl rfl)]
          simp
      | alinePolys coeffsB =>
          rw [outcomeWeight_eq_zero_of_invalid lines _ _ _ _ (Or.inl rfl)]
          simp
      | dlinePolys coeffsB =>
          rw [outcomeWeight_eq_zero_of_invalid lines _ _ _ _ (Or.inl rfl)]
          simp
  | alinePolys coeffsA =>
      cases answerB with
      | pointVals valuesB =>
          rw [outcomeWeight_eq_zero_of_invalid lines _ _ _ _ (Or.inl rfl)]
          simp
      | alinePolys coeffsB =>
          rw [outcomeWeight_eq_zero_of_invalid lines _ _ _ _ (Or.inl rfl)]
          simp
      | dlinePolys coeffsB =>
          rw [outcomeWeight_eq_zero_of_invalid lines _ _ _ _ (Or.inl rfl)]
          simp
  | dlinePolys coeffs =>
      cases answerB with
      | pointVals values =>
          by_cases hwin : directLdWinPredicate P.extendedDirectLd
              (.dline, directLdMap P.extendedDirectLd .dline sample)
              (.point, directLdMap P.extendedDirectLd .point sample)
              (.dlinePolys coeffs) (.pointVals values) = true
          · have hread := (diagonal_point_win_iff_read_eq sample coeffs values).1 hwin
            simp [hwin, hread]
          · have hread : diagonalGameRead sample (.dlinePolys coeffs) ≠
                pointGameRead (.pointVals values) :=
              fun h => hwin ((diagonal_point_win_iff_read_eq sample coeffs values).2 h)
            simp [hwin, hread]
      | alinePolys coeffsB =>
          rw [outcomeWeight_eq_zero_of_invalid lines _ _ _ _ (Or.inr rfl)]
          simp
      | dlinePolys coeffsB =>
          rw [outcomeWeight_eq_zero_of_invalid lines _ _ _ _ (Or.inr rfl)]
          simp

private theorem diagonal_rejectedMass_eq_read_mismatch
    (lines : ExtendedLinesWitness setting points deltaL)
    (sample : DirectLdSpace P.extendedDirectLd) :
    directRejectedMass P.extendedDirectLd (strategy lines)
        (.dline, directLdMap P.extendedDirectLd .dline sample)
        (.point, directLdMap P.extendedDirectLd .point sample) =
      outcomeEventWeight (strategy lines)
        (.dline, directLdMap P.extendedDirectLd .dline sample)
        (.point, directLdMap P.extendedDirectLd .point sample)
        (fun answerA answerB => diagonalGameRead sample answerA ≠ pointGameRead answerB) := by
  classical
  unfold directRejectedMass outcomeEventWeight
  apply Finset.sum_congr rfl
  intro answerA _
  apply Finset.sum_congr rfl
  intro answerB _
  have hterm := diagonal_rejectedTerm_eq_read_mismatch lines sample answerA answerB
  by_cases hread : diagonalGameRead sample answerA = pointGameRead answerB
  · simpa [hread] using hterm
  · simpa [hread] using hterm

private theorem diagonal_completed_defect_eq_read_defect
    (lines : ExtendedLinesWitness setting points deltaL) :
    completedLinePointDefect lines .AA' .BA''
        (directDLinePointDist P.extendedDirectLd) =
      consistencyDefect (uniformDistribution (DirectLdSpace P.extendedDirectLd))
        (fun sample answer => heteroKron
          (((answerMeasurement lines .alice
            (.dline, directLdMap P.extendedDirectLd .dline sample)).postprocess
              (diagonalGameRead sample)).effect answer) 1)
        (fun sample answer => heteroKron 1
          (((answerMeasurement lines .bob
            (.point, directLdMap P.extendedDirectLd .point sample)).postprocess
              pointGameRead).effect answer))
        (pairState setting) := by
  unfold completedLinePointDefect consistencyDefect
  rw [directDLinePointDist, Distribution.avgOver_map]
  apply avgOver_congr
  intro sample
  apply Finset.sum_congr rfl
  intro answerA _
  apply Finset.sum_congr rfl
  intro answerB _
  by_cases hab : answerA = answerB
  · simp [hab]
  · simp only [hab, if_false, DistanceCalculus.consistency_term_eq_stateQForm]
    rw [diagonal_read_effect lines sample answerA, point_read_effect lines sample answerB,
      DistanceCalculus.placed_product_stateQForm_eq]
    symm
    apply stateQForm_pairState_eq_AA'_BA''
    · exact (Matrix.nonneg_iff_posSemidef.mp
        (((lines.Qline .alice
          (directDLineDescOf P.extendedDirectLd sample)).postprocess
            (fun coeffs => (directEvalOpt
              (directDLineDescOf P.extendedDirectLd sample) sample.point coeffs).map
                (extendedDirectScalarEquiv P))).pos answerA)).isHermitian
    · exact (Matrix.nonneg_iff_posSemidef.mp
        (((points.Q .bob
          (projX (directPointToPauli P sample.point))
          (projZ (directPointToPauli P sample.point))).postprocess fun values =>
            some (directPointToPauli P sample.point (alphaVar P.m) * values.1 +
              directPointToPauli P sample.point (betaVar P.m) * values.2)).pos answerB)).isHermitian

/-- The diagonal-line/point branch rejection of the supplied strategy is exactly
the `AA'`--`BA''` completed line-point defect. This includes zero diagonal
directions: failed completed evaluation remains the `none` outcome and
contributes to rejection rather than being replaced by a scalar value. -/
theorem dline_point_rejection_eq_completedLinePointDefect
    (lines : ExtendedLinesWitness setting points deltaL) :
    directLdBranchRejectionProbability P.extendedDirectLd (strategy lines)
        (.dline, .point) =
      completedLinePointDefect lines .AA' .BA''
        (directDLinePointDist P.extendedDirectLd) := by
  rw [directLdBranchRejectionProbability_eq_avgOver]
  calc
    avgOver (uniformDistribution (DirectLdSpace P.extendedDirectLd))
        (fun sample => directRejectedMass P.extendedDirectLd (strategy lines)
          (.dline, directLdMap P.extendedDirectLd .dline sample)
          (.point, directLdMap P.extendedDirectLd .point sample)) =
        avgOver (uniformDistribution (DirectLdSpace P.extendedDirectLd))
          (fun sample => outcomeEventWeight (strategy lines)
            (.dline, directLdMap P.extendedDirectLd .dline sample)
            (.point, directLdMap P.extendedDirectLd .point sample)
            (fun answerA answerB =>
              diagonalGameRead sample answerA ≠ pointGameRead answerB)) := by
      apply avgOver_congr
      exact diagonal_rejectedMass_eq_read_mismatch lines
    _ = consistencyDefect (uniformDistribution (DirectLdSpace P.extendedDirectLd))
        (fun sample answer => heteroKron
          (((answerMeasurement lines .alice
            (.dline, directLdMap P.extendedDirectLd .dline sample)).postprocess
              (diagonalGameRead sample)).effect answer) 1)
        (fun sample answer => heteroKron 1
          (((answerMeasurement lines .bob
            (.point, directLdMap P.extendedDirectLd .point sample)).postprocess
              pointGameRead).effect answer))
        (pairState setting) := by
      exact (WinImplications.consistencyDefect_postprocess_eq_mismatch
        (uniformDistribution (DirectLdSpace P.extendedDirectLd)) (strategy lines)
        (fun sample => (.dline, directLdMap P.extendedDirectLd .dline sample))
        (fun sample => (.point, directLdMap P.extendedDirectLd .point sample))
        diagonalGameRead (fun _ => pointGameRead)).symm
    _ = completedLinePointDefect lines .AA' .BA''
        (directDLinePointDist P.extendedDirectLd) :=
      (diagonal_completed_defect_eq_read_defect lines).symm

private theorem point_axis_win_iff_read_eq
    (sample : DirectLdSpace P.extendedDirectLd)
    (values : Fin P.extendedDirectLd.k → DirectScalarQ P.extendedDirectLd)
    (coeffs : Fin P.extendedDirectLd.k →
      Fin (P.extendedDirectLd.d + 1) → DirectScalarQ P.extendedDirectLd) :
    directLdWinPredicate P.extendedDirectLd
        (.point, directLdMap P.extendedDirectLd .point sample)
        (.aline, directLdMap P.extendedDirectLd .aline sample)
        (.pointVals values) (.alinePolys coeffs) = true ↔
      pointGameRead (.pointVals values) = axisGameRead sample (.alinePolys coeffs) := by
  have hpredicate :
      directLdWinPredicate P.extendedDirectLd
          (.point, directLdMap P.extendedDirectLd .point sample)
          (.aline, directLdMap P.extendedDirectLd .aline sample)
          (.pointVals values) (.alinePolys coeffs) =
        directLdWinPredicate P.extendedDirectLd
          (.aline, directLdMap P.extendedDirectLd .aline sample)
          (.point, directLdMap P.extendedDirectLd .point sample)
          (.alinePolys coeffs) (.pointVals values) := by
    rfl
  rw [hpredicate]
  constructor
  · exact fun h => ((axis_point_win_iff_read_eq (P := P) sample coeffs values).1 h).symm
  · exact fun h =>
      (axis_point_win_iff_read_eq (P := P) sample coeffs values).2 h.symm

private theorem axisGameRead_axisAnswer_eq_of_effect_ne_zero_bob
    (lines : ExtendedLinesWitness setting points deltaL)
    (sample : DirectLdSpace P.extendedDirectLd)
    (coeffs : DirectDegPoly P.extendedDirectLd (P.m * P.d + 1))
    (heffect : (lines.Qline .bob
      (directALineDescOf P.extendedDirectLd sample)).effect coeffs ≠ 0) :
    axisGameRead sample (axisAnswer P coeffs) =
      (directEvalOpt (directALineDescOf P.extendedDirectLd sample) sample.point coeffs).map
        (extendedDirectScalarEquiv P) := by
  change (directEvalOpt (directALineDescOf P.extendedDirectLd sample) sample.point
      (axisRead P coeffs)).map (extendedDirectScalarEquiv P) = _
  have heval (parameter : DirectScalarQ P.extendedDirectLd) :
      evalCoefficient (axisRead P coeffs) parameter = evalCoefficient coeffs parameter :=
    axisRead_eval_of_effect_ne_zero lines .bob _ rfl coeffs heffect parameter
  apply congrArg (Option.map (extendedDirectScalarEquiv P))
  cases hfull : directEvalOpt (directALineDescOf P.extendedDirectLd sample)
      sample.point coeffs with
  | none =>
      cases haxis : directEvalOpt (directALineDescOf P.extendedDirectLd sample)
          sample.point (axisRead P coeffs) with
      | none => rfl
      | some answer =>
          have hspec := (directEvalOpt_eq_some_iff _ _ _ _).1 haxis
          have hfull' : directEvalOpt (directALineDescOf P.extendedDirectLd sample)
              sample.point coeffs = some answer := by
            apply (directEvalOpt_eq_some_iff _ _ _ _).2
            exact ⟨hspec.1, fun parameter hparameter =>
              (heval parameter).symm.trans (hspec.2 parameter hparameter)⟩
          rw [hfull] at hfull'
          contradiction
  | some answer =>
      have hspec := (directEvalOpt_eq_some_iff _ _ _ _).1 hfull
      have haxis : directEvalOpt (directALineDescOf P.extendedDirectLd sample)
          sample.point (axisRead P coeffs) = some answer := by
        apply (directEvalOpt_eq_some_iff _ _ _ _).2
        exact ⟨hspec.1, fun parameter hparameter =>
          (heval parameter).trans (hspec.2 parameter hparameter)⟩
      rw [haxis]

private theorem axis_read_effect_bob
    (lines : ExtendedLinesWitness setting points deltaL)
    (sample : DirectLdSpace P.extendedDirectLd) (answer : Option (PauliScalar P)) :
    ((((answerMeasurement lines .bob
        (.aline, directLdMap P.extendedDirectLd .aline sample)).postprocess
      (axisGameRead sample)).effect answer)) =
      (((lines.Qline .bob (directALineDescOf P.extendedDirectLd sample)).postprocess
        (fun coeffs => (directEvalOpt
          (directALineDescOf P.extendedDirectLd sample) sample.point coeffs).map
            (extendedDirectScalarEquiv P))).effect answer) := by
  classical
  unfold answerMeasurement
  rw [axis_description_canonical, MIPStarRE.Quantum.Measurement.postprocess_comp]
  simp only [MIPStarRE.Quantum.Measurement.postprocess_effect, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro coeffs _
  by_cases heffect : (lines.Qline .bob
      (directALineDescOf P.extendedDirectLd sample)).effect coeffs = 0
  · simp [heffect]
  · rw [axisGameRead_axisAnswer_eq_of_effect_ne_zero_bob lines sample coeffs heffect]

private theorem point_read_effect_alice
    (lines : ExtendedLinesWitness setting points deltaL)
    (sample : DirectLdSpace P.extendedDirectLd) (answer : Option (PauliScalar P)) :
    ((((answerMeasurement lines .alice
        (.point, directLdMap P.extendedDirectLd .point sample)).postprocess
      pointGameRead).effect answer)) =
      (((points.Q .alice
        (projX (directPointToPauli P sample.point))
        (projZ (directPointToPauli P sample.point))).postprocess fun values =>
          some (directPointToPauli P sample.point (alphaVar P.m) * values.1 +
            directPointToPauli P sample.point (betaVar P.m) * values.2)).effect answer) := by
  classical
  unfold answerMeasurement CombinedPointsWitness.extendedQ
  rw [MIPStarRE.Quantum.Measurement.postprocess_comp,
    MIPStarRE.Quantum.Measurement.postprocess_comp]
  rfl

private theorem point_axis_rejectedTerm_eq_read_mismatch
    (lines : ExtendedLinesWitness setting points deltaL)
    (sample : DirectLdSpace P.extendedDirectLd)
    (answerA answerB : DirectLdAnswer P.extendedDirectLd) :
    (if directLdWinPredicate P.extendedDirectLd
        (.point, directLdMap P.extendedDirectLd .point sample)
        (.aline, directLdMap P.extendedDirectLd .aline sample) answerA answerB then
      0
    else outcomeWeight (strategy lines)
      (.point, directLdMap P.extendedDirectLd .point sample)
      (.aline, directLdMap P.extendedDirectLd .aline sample) answerA answerB) =
      if pointGameRead answerA = axisGameRead sample answerB then 0
      else outcomeWeight (strategy lines)
        (.point, directLdMap P.extendedDirectLd .point sample)
        (.aline, directLdMap P.extendedDirectLd .aline sample) answerA answerB := by
  classical
  cases answerA with
  | pointVals values =>
      cases answerB with
      | pointVals valuesB =>
          rw [outcomeWeight_eq_zero_of_invalid lines _ _ _ _ (Or.inr rfl)]
          simp
      | alinePolys coeffs =>
          by_cases hwin : directLdWinPredicate P.extendedDirectLd
              (.point, directLdMap P.extendedDirectLd .point sample)
              (.aline, directLdMap P.extendedDirectLd .aline sample)
              (.pointVals values) (.alinePolys coeffs) = true
          · have hread := (point_axis_win_iff_read_eq sample values coeffs).1 hwin
            simp [hwin, hread]
          · have hread : pointGameRead (.pointVals values) ≠
                axisGameRead sample (.alinePolys coeffs) :=
              fun h => hwin ((point_axis_win_iff_read_eq sample values coeffs).2 h)
            simp [hwin, hread]
      | dlinePolys coeffsB =>
          rw [outcomeWeight_eq_zero_of_invalid lines _ _ _ _ (Or.inr rfl)]
          simp
  | alinePolys coeffsA =>
      cases answerB with
      | pointVals valuesB =>
          rw [outcomeWeight_eq_zero_of_invalid lines _ _ _ _ (Or.inl rfl)]
          simp
      | alinePolys coeffsB =>
          rw [outcomeWeight_eq_zero_of_invalid lines _ _ _ _ (Or.inl rfl)]
          simp
      | dlinePolys coeffsB =>
          rw [outcomeWeight_eq_zero_of_invalid lines _ _ _ _ (Or.inl rfl)]
          simp
  | dlinePolys coeffsA =>
      cases answerB with
      | pointVals valuesB =>
          rw [outcomeWeight_eq_zero_of_invalid lines _ _ _ _ (Or.inl rfl)]
          simp
      | alinePolys coeffsB =>
          rw [outcomeWeight_eq_zero_of_invalid lines _ _ _ _ (Or.inl rfl)]
          simp
      | dlinePolys coeffsB =>
          rw [outcomeWeight_eq_zero_of_invalid lines _ _ _ _ (Or.inl rfl)]
          simp

private theorem point_axis_rejectedMass_eq_read_mismatch
    (lines : ExtendedLinesWitness setting points deltaL)
    (sample : DirectLdSpace P.extendedDirectLd) :
    directRejectedMass P.extendedDirectLd (strategy lines)
        (.point, directLdMap P.extendedDirectLd .point sample)
        (.aline, directLdMap P.extendedDirectLd .aline sample) =
      outcomeEventWeight (strategy lines)
        (.point, directLdMap P.extendedDirectLd .point sample)
        (.aline, directLdMap P.extendedDirectLd .aline sample)
        (fun answerA answerB => pointGameRead answerA ≠ axisGameRead sample answerB) := by
  classical
  unfold directRejectedMass outcomeEventWeight
  apply Finset.sum_congr rfl
  intro answerA _
  apply Finset.sum_congr rfl
  intro answerB _
  have hterm := point_axis_rejectedTerm_eq_read_mismatch lines sample answerA answerB
  by_cases hread : pointGameRead answerA = axisGameRead sample answerB
  · simpa [hread] using hterm
  · simpa [hread] using hterm

private theorem place_BB'_mul_AB''_comm
    (A : Op (setting.ExpandedLocalSpace .alice))
    (B : Op (setting.ExpandedLocalSpace .bob)) :
    setting.place .BB' B * setting.place .AB'' A =
      setting.place .AB'' A * setting.place .BB' B := by
  change Op (setting.toStrategy.ιA × PauliRegister P) at A
  change Op (setting.toStrategy.ιB × PauliRegister P) at B
  let e := ProjectiveSetting.abBbBipartition P
    setting.toStrategy.ιA setting.toStrategy.ιB
  let I_A : Op (setting.toStrategy.ιA × PauliRegister P) := 1
  let I_R : Op ((setting.toStrategy.ιB × PauliRegister P) ×
      (PauliRegister P × PauliRegister P)) := 1
  let C := heteroKron B (1 : Op (PauliRegister P × PauliRegister P))
  let L := heteroKron A I_R
  let R := heteroKron I_A C
  have hleft : reindexOp e L = setting.place .AB'' A := by
    simpa [e, L, I_R] using
      (ProjectiveSetting.reindexOp_abBbBipartition_left setting A)
  have hright : reindexOp e R = setting.place .BB' B := by
    simpa [e, R, I_A, C] using
      (ProjectiveSetting.reindexOp_abBbBipartition_right setting B)
  have hcomm : R * L = L * R := by
    simpa [R, L, I_A, I_R] using
      (WinImplications.heteroKron_left_right_comm A C).symm
  calc
    setting.place .BB' B * setting.place .AB'' A =
        reindexOp e R * reindexOp e L :=
      congrArg₂ (fun X Y => X * Y) hright.symm hleft.symm
    _ = reindexOp e (R * L) :=
      (WinImplications.reindexOp_mul e _ _).symm
    _ = reindexOp e (L * R) := congrArg (reindexOp e) hcomm
    _ = reindexOp e L * reindexOp e R :=
      WinImplications.reindexOp_mul e _ _
    _ = setting.place .AB'' A * setting.place .BB' B :=
      congrArg₂ (fun X Y => X * Y) hleft hright

private theorem reversed_axis_completed_defect_eq_read_defect
    (lines : ExtendedLinesWitness setting points deltaL) :
    completedLinePointDefect lines .BB' .AB''
        (directALinePointDist P.extendedDirectLd) =
      consistencyDefect (uniformDistribution (DirectLdSpace P.extendedDirectLd))
        (fun sample answer => heteroKron
          (((answerMeasurement lines .alice
            (.point, directLdMap P.extendedDirectLd .point sample)).postprocess
              pointGameRead).effect answer) 1)
        (fun sample answer => heteroKron 1
          (((answerMeasurement lines .bob
            (.aline, directLdMap P.extendedDirectLd .aline sample)).postprocess
              (axisGameRead sample)).effect answer))
        (pairState setting) := by
  unfold completedLinePointDefect consistencyDefect
  rw [directALinePointDist, Distribution.avgOver_map]
  apply avgOver_congr
  intro sample
  conv_lhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro answerA _
  apply Finset.sum_congr rfl
  intro answerB _
  by_cases hab : answerA = answerB
  · simp [hab]
  · have hba : answerB ≠ answerA := Ne.symm hab
    simp only [hab, hba, if_false, DistanceCalculus.consistency_term_eq_stateQForm]
    let A : Op (setting.ExpandedLocalSpace .alice) :=
      ((points.Q .alice
        (projX (directPointToPauli P sample.point))
        (projZ (directPointToPauli P sample.point))).postprocess fun values =>
          some (directPointToPauli P sample.point (alphaVar P.m) * values.1 +
            directPointToPauli P sample.point (betaVar P.m) * values.2)).effect answerA
    let B : Op (setting.ExpandedLocalSpace .bob) :=
      ((lines.Qline .bob
        (directALineDescOf P.extendedDirectLd sample)).postprocess fun coeffs =>
          (directEvalOpt
            (directALineDescOf P.extendedDirectLd sample) sample.point coeffs).map
              (extendedDirectScalarEquiv P)).effect answerB
    have hA : A.IsHermitian := by
      exact (Matrix.nonneg_iff_posSemidef.mp
        (((points.Q .alice
          (projX (directPointToPauli P sample.point))
          (projZ (directPointToPauli P sample.point))).postprocess fun values =>
            some (directPointToPauli P sample.point (alphaVar P.m) * values.1 +
              directPointToPauli P sample.point (betaVar P.m) * values.2)).pos answerA)).isHermitian
    have hB : B.IsHermitian := by
      exact (Matrix.nonneg_iff_posSemidef.mp
        (((lines.Qline .bob
          (directALineDescOf P.extendedDirectLd sample)).postprocess
            (fun coeffs => (directEvalOpt
              (directALineDescOf P.extendedDirectLd sample) sample.point coeffs).map
                (extendedDirectScalarEquiv P))).pos answerB)).isHermitian
    rw [point_read_effect_alice lines sample answerA, axis_read_effect_bob lines sample answerB,
      DistanceCalculus.placed_product_stateQForm_eq]
    change DistanceCalculus.stateQForm setting.psiHat
        (setting.place .BB' B * setting.place .AB'' A) =
      DistanceCalculus.stateQForm (pairState setting) (heteroKron A B)
    rw [place_BB'_mul_AB''_comm]
    exact (stateQForm_pairState_eq_AB''_BB' setting A B hA hB).symm

/-- The point/axis-line branch rejection of the supplied strategy is exactly
the `BB'`--`AB''` completed line-point defect. The proof uses the second
expanded-state correlation and does not identify the two player spaces or
assume a symmetry of the strategy. -/
theorem point_aline_rejection_eq_completedLinePointDefect
    (lines : ExtendedLinesWitness setting points deltaL) :
    directLdBranchRejectionProbability P.extendedDirectLd (strategy lines)
        (.point, .aline) =
      completedLinePointDefect lines .BB' .AB''
        (directALinePointDist P.extendedDirectLd) := by
  rw [directLdBranchRejectionProbability_eq_avgOver]
  calc
    avgOver (uniformDistribution (DirectLdSpace P.extendedDirectLd))
        (fun sample => directRejectedMass P.extendedDirectLd (strategy lines)
          (.point, directLdMap P.extendedDirectLd .point sample)
          (.aline, directLdMap P.extendedDirectLd .aline sample)) =
        avgOver (uniformDistribution (DirectLdSpace P.extendedDirectLd))
          (fun sample => outcomeEventWeight (strategy lines)
            (.point, directLdMap P.extendedDirectLd .point sample)
            (.aline, directLdMap P.extendedDirectLd .aline sample)
            (fun answerA answerB =>
              pointGameRead answerA ≠ axisGameRead sample answerB)) := by
      apply avgOver_congr
      exact point_axis_rejectedMass_eq_read_mismatch lines
    _ = consistencyDefect (uniformDistribution (DirectLdSpace P.extendedDirectLd))
        (fun sample answer => heteroKron
          (((answerMeasurement lines .alice
            (.point, directLdMap P.extendedDirectLd .point sample)).postprocess
              pointGameRead).effect answer) 1)
        (fun sample answer => heteroKron 1
          (((answerMeasurement lines .bob
            (.aline, directLdMap P.extendedDirectLd .aline sample)).postprocess
              (axisGameRead sample)).effect answer))
        (pairState setting) := by
      exact (WinImplications.consistencyDefect_postprocess_eq_mismatch
        (uniformDistribution (DirectLdSpace P.extendedDirectLd)) (strategy lines)
        (fun sample => (.point, directLdMap P.extendedDirectLd .point sample))
        (fun sample => (.aline, directLdMap P.extendedDirectLd .aline sample))
        (fun _ => pointGameRead) axisGameRead).symm
    _ = completedLinePointDefect lines .BB' .AB''
        (directALinePointDist P.extendedDirectLd) :=
      (reversed_axis_completed_defect_eq_read_defect lines).symm

end ExtendedLineGame

end

end MIPStarRE.QPBT
