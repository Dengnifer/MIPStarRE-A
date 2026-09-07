import MIPStarRE.QPBT.Combining.ExtendedLineGame.StateTransport

/-!
# Axis-line/point rejection for the extended direct game

This module identifies the axis-line/point branch rejection of the strategy
constructed from an `ExtendedLinesWitness` with the corresponding completed
line-point defect.  It is a finite postprocessing and state-transport step in
the first paragraph of the proof of `lem:qld-4-7`; it does not establish a
passing-value bound or construct the supplied witness.

## References

- `references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1279-1288`
- Blueprint `lem:qld-4-7`.
- Issues #302 and #305.
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

/-- The unique coordinate of the one-coordinate extended direct low-degree game. -/
private def onlyCoordinate : Fin P.extendedDirectLd.k :=
  ⟨0, by change 0 < 1; decide⟩

/-- Evaluate an axis-line answer at the sampled point, returning `none` for
invalid answer formats or evaluations. -/
private def axisGameRead
    (sample : DirectLdSpace P.extendedDirectLd) :
    DirectLdAnswer P.extendedDirectLd → Option (PauliScalar P)
  | .alinePolys coeffs =>
      (directEvalOpt (directALineDescOf P.extendedDirectLd sample) sample.point
        (coeffs onlyCoordinate)).map (extendedDirectScalarEquiv P)
  | _ => none

/-- Read the unique coordinate of a point-format answer, returning `none` for
other answer formats. -/
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

end ExtendedLineGame

end

end MIPStarRE.QPBT
