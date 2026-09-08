import MIPStarRE.QPBT.Combining.ExtendedLineGame.LinePointRejection

/-!
# Mixed line/point rejection bounds for the extended direct game

This module identifies the remaining reversed point/diagonal-line branch with
its completed line-point defect and bounds the sum of all four mixed
line/point rejection probabilities. These are exact supplied-witness
consequences used before the soundness step in the proof of `lem:qld-4-7`;
they do not establish a complete passing-value bound or construct a witness.

## References

- `references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1279-1288`
- Blueprint `lem:qld-4-7`.
- Issues #302, #305, #307, #309, and #311.
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

private theorem point_diagonal_win_iff_read_eq
    (sample : DirectLdSpace P.extendedDirectLd)
    (values : Fin P.extendedDirectLd.k → DirectScalarQ P.extendedDirectLd)
    (coeffs : Fin P.extendedDirectLd.k →
      Fin (P.extendedDirectLd.m * P.extendedDirectLd.d + 1) →
        DirectScalarQ P.extendedDirectLd) :
    directLdWinPredicate P.extendedDirectLd
        (.point, directLdMap P.extendedDirectLd .point sample)
        (.dline, directLdMap P.extendedDirectLd .dline sample)
        (.pointVals values) (.dlinePolys coeffs) = true ↔
      pointGameRead (.pointVals values) =
        diagonalGameRead sample (.dlinePolys coeffs) := by
  have hpredicate :
      directLdWinPredicate P.extendedDirectLd
          (.point, directLdMap P.extendedDirectLd .point sample)
          (.dline, directLdMap P.extendedDirectLd .dline sample)
          (.pointVals values) (.dlinePolys coeffs) =
        directLdWinPredicate P.extendedDirectLd
          (.dline, directLdMap P.extendedDirectLd .dline sample)
          (.point, directLdMap P.extendedDirectLd .point sample)
          (.dlinePolys coeffs) (.pointVals values) := by
    rfl
  rw [hpredicate]
  constructor
  · exact fun h => (diagonal_point_win_iff_read_eq sample coeffs values).mp h |>.symm
  · exact fun h => (diagonal_point_win_iff_read_eq sample coeffs values).mpr h.symm

private theorem diagonal_read_effect_bob
    (lines : ExtendedLinesWitness setting points deltaL)
    (sample : DirectLdSpace P.extendedDirectLd) (answer : Option (PauliScalar P)) :
    ((((answerMeasurement lines .bob
        (.dline, directLdMap P.extendedDirectLd .dline sample)).postprocess
      (diagonalGameRead sample)).effect answer)) =
      (((lines.Qline .bob (directDLineDescOf P.extendedDirectLd sample)).postprocess
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

private theorem point_diagonal_rejectedTerm_eq_read_mismatch
    (lines : ExtendedLinesWitness setting points deltaL)
    (sample : DirectLdSpace P.extendedDirectLd)
    (answerA answerB : DirectLdAnswer P.extendedDirectLd) :
    (if directLdWinPredicate P.extendedDirectLd
        (.point, directLdMap P.extendedDirectLd .point sample)
        (.dline, directLdMap P.extendedDirectLd .dline sample) answerA answerB then
      0
    else outcomeWeight (strategy lines)
      (.point, directLdMap P.extendedDirectLd .point sample)
      (.dline, directLdMap P.extendedDirectLd .dline sample) answerA answerB) =
      if pointGameRead answerA = diagonalGameRead sample answerB then 0
      else outcomeWeight (strategy lines)
        (.point, directLdMap P.extendedDirectLd .point sample)
        (.dline, directLdMap P.extendedDirectLd .dline sample) answerA answerB := by
  classical
  cases answerA with
  | pointVals values =>
      cases answerB with
      | pointVals valuesB =>
          rw [outcomeWeight_eq_zero_of_invalid lines _ _ _ _ (Or.inr rfl)]
          simp
      | alinePolys coeffsB =>
          rw [outcomeWeight_eq_zero_of_invalid lines _ _ _ _ (Or.inr rfl)]
          simp
      | dlinePolys coeffs =>
          by_cases hwin : directLdWinPredicate P.extendedDirectLd
              (.point, directLdMap P.extendedDirectLd .point sample)
              (.dline, directLdMap P.extendedDirectLd .dline sample)
              (.pointVals values) (.dlinePolys coeffs) = true
          · have hread := (point_diagonal_win_iff_read_eq sample values coeffs).mp hwin
            simp [hwin, hread]
          · have hread : pointGameRead (.pointVals values) ≠
                diagonalGameRead sample (.dlinePolys coeffs) :=
              fun h => hwin ((point_diagonal_win_iff_read_eq sample values coeffs).mpr h)
            simp [hwin, hread]
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

private theorem point_diagonal_rejectedMass_eq_read_mismatch
    (lines : ExtendedLinesWitness setting points deltaL)
    (sample : DirectLdSpace P.extendedDirectLd) :
    directRejectedMass P.extendedDirectLd (strategy lines)
        (.point, directLdMap P.extendedDirectLd .point sample)
        (.dline, directLdMap P.extendedDirectLd .dline sample) =
      outcomeEventWeight (strategy lines)
        (.point, directLdMap P.extendedDirectLd .point sample)
        (.dline, directLdMap P.extendedDirectLd .dline sample)
        (fun answerA answerB =>
          pointGameRead answerA ≠ diagonalGameRead sample answerB) := by
  classical
  unfold directRejectedMass outcomeEventWeight
  apply Finset.sum_congr rfl
  intro answerA _
  apply Finset.sum_congr rfl
  intro answerB _
  have hterm := point_diagonal_rejectedTerm_eq_read_mismatch lines sample answerA answerB
  by_cases hread : pointGameRead answerA = diagonalGameRead sample answerB
  · simpa [hread] using hterm
  · simpa [hread] using hterm

/-- The `BB'`--`AB''` completed diagonal-line/point defect is the consistency
defect of the reversed completed direct-game readouts on `pairState`. -/
theorem reversed_diagonal_completed_defect_eq_read_defect
    (lines : ExtendedLinesWitness setting points deltaL) :
    completedLinePointDefect lines .BB' .AB''
        (directDLinePointDist P.extendedDirectLd) =
      consistencyDefect (uniformDistribution (DirectLdSpace P.extendedDirectLd))
        (fun sample answer => heteroKron
          (((answerMeasurement lines .alice
            (.point, directLdMap P.extendedDirectLd .point sample)).postprocess
              pointGameRead).effect answer) 1)
        (fun sample answer => heteroKron 1
          (((answerMeasurement lines .bob
            (.dline, directLdMap P.extendedDirectLd .dline sample)).postprocess
              (diagonalGameRead sample)).effect answer))
        (pairState setting) := by
  unfold completedLinePointDefect consistencyDefect
  rw [directDLinePointDist, Distribution.avgOver_map]
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
        (directDLineDescOf P.extendedDirectLd sample)).postprocess fun coeffs =>
          (directEvalOpt
            (directDLineDescOf P.extendedDirectLd sample) sample.point coeffs).map
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
          (directDLineDescOf P.extendedDirectLd sample)).postprocess
            (fun coeffs => (directEvalOpt
              (directDLineDescOf P.extendedDirectLd sample) sample.point coeffs).map
                (extendedDirectScalarEquiv P))).pos answerB)).isHermitian
    rw [point_read_effect_alice lines sample answerA,
      diagonal_read_effect_bob lines sample answerB,
      DistanceCalculus.placed_product_stateQForm_eq]
    change DistanceCalculus.stateQForm setting.psiHat
        (setting.place .BB' B * setting.place .AB'' A) =
      DistanceCalculus.stateQForm (pairState setting) (heteroKron A B)
    rw [place_BB'_mul_AB''_comm]
    exact (stateQForm_pairState_eq_AB''_BB' setting A B hA hB).symm

/-- The point/diagonal-line branch rejection is exactly the `BB'`--`AB''`
completed diagonal-line/point defect. Zero directions and failed completed
evaluation retain their `none` outcome. Paper
`14_analysis_of_the_pauli_basis_test.tex:1279-1288`; blueprint `lem:qld-4-7`. -/
theorem point_dline_rejection_eq_completedLinePointDefect
    (lines : ExtendedLinesWitness setting points deltaL) :
    directLdBranchRejectionProbability P.extendedDirectLd (strategy lines)
        (.point, .dline) =
      completedLinePointDefect lines .BB' .AB''
        (directDLinePointDist P.extendedDirectLd) := by
  rw [directLdBranchRejectionProbability_eq_avgOver]
  calc
    avgOver (uniformDistribution (DirectLdSpace P.extendedDirectLd))
        (fun sample => directRejectedMass P.extendedDirectLd (strategy lines)
          (.point, directLdMap P.extendedDirectLd .point sample)
          (.dline, directLdMap P.extendedDirectLd .dline sample)) =
        avgOver (uniformDistribution (DirectLdSpace P.extendedDirectLd))
          (fun sample => outcomeEventWeight (strategy lines)
            (.point, directLdMap P.extendedDirectLd .point sample)
            (.dline, directLdMap P.extendedDirectLd .dline sample)
            (fun answerA answerB =>
              pointGameRead answerA ≠ diagonalGameRead sample answerB)) := by
      apply avgOver_congr
      exact point_diagonal_rejectedMass_eq_read_mismatch lines
    _ = consistencyDefect (uniformDistribution (DirectLdSpace P.extendedDirectLd))
        (fun sample answer => heteroKron
          (((answerMeasurement lines .alice
            (.point, directLdMap P.extendedDirectLd .point sample)).postprocess
              pointGameRead).effect answer) 1)
        (fun sample answer => heteroKron 1
          (((answerMeasurement lines .bob
            (.dline, directLdMap P.extendedDirectLd .dline sample)).postprocess
              (diagonalGameRead sample)).effect answer))
        (pairState setting) := by
      exact (WinImplications.consistencyDefect_postprocess_eq_mismatch
        (uniformDistribution (DirectLdSpace P.extendedDirectLd)) (strategy lines)
        (fun sample => (.point, directLdMap P.extendedDirectLd .point sample))
        (fun sample => (.dline, directLdMap P.extendedDirectLd .dline sample))
        (fun _ => pointGameRead) diagonalGameRead).symm
    _ = completedLinePointDefect lines .BB' .AB''
        (directDLinePointDist P.extendedDirectLd) :=
      (reversed_diagonal_completed_defect_eq_read_defect lines).symm

/-- The sum of the four mixed point/line rejection probabilities is at most
`4 * deltaL`. This combines only the exact branch identities with the two
oriented completed-defect bounds supplied by `lines`. Paper
`14_analysis_of_the_pauli_basis_test.tex:1279-1288`; blueprint `lem:qld-4-7`. -/
theorem mixed_line_point_rejections_le_four_mul
    (lines : ExtendedLinesWitness setting points deltaL) :
    directLdBranchRejectionProbability P.extendedDirectLd (strategy lines)
          (.aline, .point) +
        directLdBranchRejectionProbability P.extendedDirectLd (strategy lines)
          (.dline, .point) +
        directLdBranchRejectionProbability P.extendedDirectLd (strategy lines)
          (.point, .aline) +
        directLdBranchRejectionProbability P.extendedDirectLd (strategy lines)
          (.point, .dline) ≤ 4 * deltaL := by
  rw [aline_point_rejection_eq_completedLinePointDefect lines,
    dline_point_rejection_eq_completedLinePointDefect lines,
    point_aline_rejection_eq_completedLinePointDefect lines,
    point_dline_rejection_eq_completedLinePointDefect lines]
  have hbounds := completedLinePointDefect_sums_le lines
  linarith [hbounds.1, hbounds.2]

end ExtendedLineGame

end

end MIPStarRE.QPBT
