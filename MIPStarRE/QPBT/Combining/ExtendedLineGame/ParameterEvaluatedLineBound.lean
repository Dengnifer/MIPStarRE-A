import MIPStarRE.QPBT.Combining.DirectLowDegree.Transport.LineResampling
import MIPStarRE.QPBT.Combining.ExtendedLineGame.LineNoneMass
import MIPStarRE.QPBT.Combining.ExtendedLineGame.ParameterCompletion

/-!
# Bounds for independently parameter-evaluated line answers

This module specializes the parameter/completed-read comparison to the axis
and diagonal measurements supplied by an `ExtendedLinesWitness`. The affine
parameter is sampled independently of the line. Affine resampling then
recovers the original joint line-point law, including zero directions.
The numerical estimates are formalization-only consequences of the supplied
point and line witnesses supporting the classical-game construction in the
proof of `lem:qld-4-7`.

## References

- `references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1020-1034`
- `references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1279-1288`
- `references/qpbt-paper/06_nonlocal_games_and_mipstar.tex:295-311`
- Blueprint `lem:qld-4-7`.
- Issue #341.
-/

open scoped BigOperators MatrixOrder ComplexOrder

namespace MIPStarRE.QPBT

open MIPStarRE.LDT hiding Measurement
open MIPStarRE.Quantum

noncomputable section

namespace ExtendedLineGame

variable {P : AdmissibleParams} {epsilon deltaQ deltaL : ℝ}
variable {setting : ProjectiveSetting P epsilon}
variable {points : CombinedPointsWitness setting deltaQ}

/-- The unique coordinate in the extended direct game. -/
private def lineCoordinate : Fin P.extendedDirectLd.k :=
  ⟨0, by change 0 < 1; decide⟩

private theorem coordinate_eq_lineCoordinate (i : Fin P.extendedDirectLd.k) :
    i = lineCoordinate (P := P) := by
  apply Fin.ext
  have hi := i.isLt
  change i.val < 1 at hi
  change i.val = 0
  omega

/-- Read the axis coefficient vector from a direct-game answer. Wrong answer
formats receive an arbitrary zero value; their Born weight is zero. -/
private def axisCoefficients
    (answer : DirectLdAnswer P.extendedDirectLd) :
    DirectDegPoly P.extendedDirectLd P.d :=
  match answer with
  | .alinePolys coefficients => coefficients lineCoordinate
  | _ => 0

/-- Read the diagonal coefficient vector from a direct-game answer. Wrong
answer formats receive an arbitrary zero value; their Born weight is zero. -/
private def diagonalCoefficients
    (answer : DirectLdAnswer P.extendedDirectLd) :
    DirectDegPoly P.extendedDirectLd
      (P.extendedDirectLd.m * P.extendedDirectLd.d) :=
  match answer with
  | .dlinePolys coefficients => coefficients lineCoordinate
  | _ => 0

/-- The canonical direct-game axis question represented by an axis line. -/
private def axisQuestion (line : DirectLineDesc P.extendedDirectLd) :
    DirectLdQuestion P.extendedDirectLd :=
  (.aline, ⟨line.base, line.index, 0⟩)

/-- The canonical direct-game diagonal question represented by a diagonal line. -/
private def diagonalQuestion (line : DirectLineDesc P.extendedDirectLd) :
    DirectLdQuestion P.extendedDirectLd :=
  (.dline, ⟨line.base, line.index, line.direction⟩)

/-- The axis parameter-evaluation defect under the actual axis-line marginal
and an independent uniform affine parameter. -/
noncomputable def axisParameterEvaluationDefect
    (lines : ExtendedLinesWitness setting points deltaL) : ℝ :=
  avgOver (directALinePointDist P.extendedDirectLd) fun sample =>
    avgOver (uniformDistribution (DirectScalarQ P.extendedDirectLd)) fun parameter =>
      parameterEvalDefect (strategy lines) (axisQuestion sample.1)
        (axisQuestion sample.1) axisCoefficients axisCoefficients parameter

/-- The diagonal parameter-evaluation defect under the actual diagonal-line
marginal and an independent uniform affine parameter, including zero directions. -/
noncomputable def diagonalParameterEvaluationDefect
    (lines : ExtendedLinesWitness setting points deltaL) : ℝ :=
  avgOver (directDLinePointDist P.extendedDirectLd) fun sample =>
    avgOver (uniformDistribution (DirectScalarQ P.extendedDirectLd)) fun parameter =>
      parameterEvalDefect (strategy lines) (diagonalQuestion sample.1)
        (diagonalQuestion sample.1) diagonalCoefficients diagonalCoefficients parameter

private theorem axisQuestion_directALineDescOf
    (sample : DirectLdSpace P.extendedDirectLd) :
    axisQuestion (directALineDescOf P.extendedDirectLd sample) =
      (.aline, directLdMap P.extendedDirectLd .aline sample) := by
  rfl

private theorem diagonalQuestion_directDLineDescOf
    (sample : DirectLdSpace P.extendedDirectLd) :
    diagonalQuestion (directDLineDescOf P.extendedDirectLd sample) =
      (.dline, directLdMap P.extendedDirectLd .dline sample) := by
  rfl

private theorem axis_completed_mismatch_eq
    (lines : ExtendedLinesWitness setting points deltaL)
    (sample : DirectLdSpace P.extendedDirectLd) :
    outcomeEventWeight (strategy lines)
        (.aline, directLdMap P.extendedDirectLd .aline sample)
        (.aline, directLdMap P.extendedDirectLd .aline sample)
        (fun answerA answerB =>
          directEvalOpt (directALineDescOf P.extendedDirectLd sample) sample.point
              (axisCoefficients answerA) ≠
            directEvalOpt (directALineDescOf P.extendedDirectLd sample) sample.point
              (axisCoefficients answerB)) =
      outcomeEventWeight (strategy lines)
        (.aline, directLdMap P.extendedDirectLd .aline sample)
        (.aline, directLdMap P.extendedDirectLd .aline sample)
        (fun answerA answerB => axisGameRead sample answerA ≠ axisGameRead sample answerB) := by
  classical
  unfold outcomeEventWeight
  apply Finset.sum_congr rfl
  intro answerA _
  apply Finset.sum_congr rfl
  intro answerB _
  by_cases hinvalid : validDirectLdAnswer (D := P.extendedDirectLd) .aline answerA = false ∨
      validDirectLdAnswer (D := P.extendedDirectLd) .aline answerB = false
  · rw [outcomeWeight_eq_zero_of_invalid lines _ _ answerA answerB hinvalid]
    simp
  · cases answerA <;> cases answerB <;> simp [validDirectLdAnswer] at hinvalid
    have hmap : Function.Injective (Option.map (extendedDirectScalarEquiv P)) :=
      Option.map_injective (extendedDirectScalarEquiv P).injective
    simp only [axisCoefficients, axisGameRead, coordinate_eq_lineCoordinate,
      ne_eq, hmap.eq_iff]
    rfl

private theorem diagonal_completed_mismatch_eq
    (lines : ExtendedLinesWitness setting points deltaL)
    (sample : DirectLdSpace P.extendedDirectLd) :
    outcomeEventWeight (strategy lines)
        (.dline, directLdMap P.extendedDirectLd .dline sample)
        (.dline, directLdMap P.extendedDirectLd .dline sample)
        (fun answerA answerB =>
          directEvalOpt (directDLineDescOf P.extendedDirectLd sample) sample.point
              (diagonalCoefficients answerA) ≠
            directEvalOpt (directDLineDescOf P.extendedDirectLd sample) sample.point
              (diagonalCoefficients answerB)) =
      outcomeEventWeight (strategy lines)
        (.dline, directLdMap P.extendedDirectLd .dline sample)
        (.dline, directLdMap P.extendedDirectLd .dline sample)
        (fun answerA answerB =>
          diagonalGameRead sample answerA ≠ diagonalGameRead sample answerB) := by
  classical
  unfold outcomeEventWeight
  apply Finset.sum_congr rfl
  intro answerA _
  apply Finset.sum_congr rfl
  intro answerB _
  by_cases hinvalid : validDirectLdAnswer (D := P.extendedDirectLd) .dline answerA = false ∨
      validDirectLdAnswer (D := P.extendedDirectLd) .dline answerB = false
  · rw [outcomeWeight_eq_zero_of_invalid lines _ _ answerA answerB hinvalid]
    simp
  · cases answerA <;> cases answerB <;> simp [validDirectLdAnswer] at hinvalid
    have hmap : Function.Injective (Option.map (extendedDirectScalarEquiv P)) :=
      Option.map_injective (extendedDirectScalarEquiv P).injective
    simp only [diagonalCoefficients, diagonalGameRead, coordinate_eq_lineCoordinate,
      ne_eq, hmap.eq_iff]
    rfl

private theorem axis_none_mass_eq
    (lines : ExtendedLinesWitness setting points deltaL)
    (side : PlayerSide) (sample : DirectLdSpace P.extendedDirectLd) :
    (match side with
      | .alice => aliceEventWeight (strategy lines)
          (.aline, directLdMap P.extendedDirectLd .aline sample)
          (fun answer => directEvalOpt (directALineDescOf P.extendedDirectLd sample)
            sample.point (axisCoefficients answer) = none)
      | .bob => bobEventWeight (strategy lines)
          (.aline, directLdMap P.extendedDirectLd .aline sample)
          (fun answer => directEvalOpt (directALineDescOf P.extendedDirectLd sample)
            sample.point (axisCoefficients answer) = none)) =
    (match side with
      | .alice => aliceEventWeight (strategy lines)
          (.aline, directLdMap P.extendedDirectLd .aline sample)
          (fun answer => axisGameRead sample answer = none)
      | .bob => bobEventWeight (strategy lines)
          (.aline, directLdMap P.extendedDirectLd .aline sample)
          (fun answer => axisGameRead sample answer = none)) := by
  cases side <;> dsimp only
  all_goals first
  | rw [← outcome_event_weight_left_eq (strategy lines)
      (.aline, directLdMap P.extendedDirectLd .aline sample)
      (.aline, directLdMap P.extendedDirectLd .aline sample),
      ← outcome_event_weight_left_eq (strategy lines)
        (.aline, directLdMap P.extendedDirectLd .aline sample)
        (.aline, directLdMap P.extendedDirectLd .aline sample)]
  | rw [← outcome_event_weight_right_eq (strategy lines)
      (.aline, directLdMap P.extendedDirectLd .aline sample)
      (.aline, directLdMap P.extendedDirectLd .aline sample),
      ← outcome_event_weight_right_eq (strategy lines)
        (.aline, directLdMap P.extendedDirectLd .aline sample)
        (.aline, directLdMap P.extendedDirectLd .aline sample)]
  all_goals
    unfold outcomeEventWeight
    apply Finset.sum_congr rfl
    intro answerA _
    apply Finset.sum_congr rfl
    intro answerB _
  · by_cases hinvalid : validDirectLdAnswer (D := P.extendedDirectLd) .aline answerA = false
    · rw [outcomeWeight_eq_zero_of_invalid lines _ _ answerA answerB (Or.inl hinvalid)]
      simp
    · cases answerA <;> simp [validDirectLdAnswer] at hinvalid
      simp [axisCoefficients, axisGameRead, coordinate_eq_lineCoordinate]
      rfl
  · by_cases hinvalid : validDirectLdAnswer (D := P.extendedDirectLd) .aline answerB = false
    · rw [outcomeWeight_eq_zero_of_invalid lines _ _ answerA answerB (Or.inr hinvalid)]
      simp
    · cases answerB <;> simp [validDirectLdAnswer] at hinvalid
      simp [axisCoefficients, axisGameRead, coordinate_eq_lineCoordinate]
      rfl

private theorem diagonal_none_mass_eq
    (lines : ExtendedLinesWitness setting points deltaL)
    (side : PlayerSide) (sample : DirectLdSpace P.extendedDirectLd) :
    (match side with
      | .alice => aliceEventWeight (strategy lines)
          (.dline, directLdMap P.extendedDirectLd .dline sample)
          (fun answer => directEvalOpt (directDLineDescOf P.extendedDirectLd sample)
            sample.point (diagonalCoefficients answer) = none)
      | .bob => bobEventWeight (strategy lines)
          (.dline, directLdMap P.extendedDirectLd .dline sample)
          (fun answer => directEvalOpt (directDLineDescOf P.extendedDirectLd sample)
            sample.point (diagonalCoefficients answer) = none)) =
    (match side with
      | .alice => aliceEventWeight (strategy lines)
          (.dline, directLdMap P.extendedDirectLd .dline sample)
          (fun answer => diagonalGameRead sample answer = none)
      | .bob => bobEventWeight (strategy lines)
          (.dline, directLdMap P.extendedDirectLd .dline sample)
          (fun answer => diagonalGameRead sample answer = none)) := by
  cases side <;> dsimp only
  all_goals first
  | rw [← outcome_event_weight_left_eq (strategy lines)
      (.dline, directLdMap P.extendedDirectLd .dline sample)
      (.dline, directLdMap P.extendedDirectLd .dline sample),
      ← outcome_event_weight_left_eq (strategy lines)
        (.dline, directLdMap P.extendedDirectLd .dline sample)
        (.dline, directLdMap P.extendedDirectLd .dline sample)]
  | rw [← outcome_event_weight_right_eq (strategy lines)
      (.dline, directLdMap P.extendedDirectLd .dline sample)
      (.dline, directLdMap P.extendedDirectLd .dline sample),
      ← outcome_event_weight_right_eq (strategy lines)
        (.dline, directLdMap P.extendedDirectLd .dline sample)
        (.dline, directLdMap P.extendedDirectLd .dline sample)]
  all_goals
    unfold outcomeEventWeight
    apply Finset.sum_congr rfl
    intro answerA _
    apply Finset.sum_congr rfl
    intro answerB _
  · by_cases hinvalid : validDirectLdAnswer (D := P.extendedDirectLd) .dline answerA = false
    · rw [outcomeWeight_eq_zero_of_invalid lines _ _ answerA answerB (Or.inl hinvalid)]
      simp
    · cases answerA <;> simp [validDirectLdAnswer] at hinvalid
      simp [diagonalCoefficients, diagonalGameRead, coordinate_eq_lineCoordinate]
  · by_cases hinvalid : validDirectLdAnswer (D := P.extendedDirectLd) .dline answerB = false
    · rw [outcomeWeight_eq_zero_of_invalid lines _ _ answerA answerB (Or.inr hinvalid)]
      simp
    · cases answerB <;> simp [validDirectLdAnswer] at hinvalid
      simp [diagonalCoefficients, diagonalGameRead, coordinate_eq_lineCoordinate]

/-- Averaging the parameter/completed-read comparison over the actual axis law. -/
private theorem axis_parameter_evaluation_defect_le_completed
    (lines : ExtendedLinesWitness setting points deltaL) :
    axisParameterEvaluationDefect lines ≤
      axisSameLineEvaluationDefect lines + axisAliceNoneMass lines + axisBobNoneMass lines := by
  let F : DirectLineDesc P.extendedDirectLd ×
      (Fin P.extendedDirectLd.m → DirectScalarQ P.extendedDirectLd) → ℝ := fun sample =>
    outcomeEventWeight (strategy lines) (axisQuestion sample.1) (axisQuestion sample.1)
        (fun answerA answerB => directEvalOpt sample.1 sample.2 (axisCoefficients answerA) ≠
          directEvalOpt sample.1 sample.2 (axisCoefficients answerB)) +
      aliceEventWeight (strategy lines) (axisQuestion sample.1)
        (fun answer => directEvalOpt sample.1 sample.2 (axisCoefficients answer) = none) +
      bobEventWeight (strategy lines) (axisQuestion sample.1)
        (fun answer => directEvalOpt sample.1 sample.2 (axisCoefficients answer) = none)
  have havg : axisParameterEvaluationDefect lines ≤
      avgOver (directALinePointDist P.extendedDirectLd) F := by
    rw [← avgOver_directALinePointDist_resample P.extendedDirectLd F,
      Distribution.avgOver_map]
    unfold axisParameterEvaluationDefect
    apply avgOver_mono
    intro sample
    apply avgOver_mono
    intro parameter
    exact parameterEvalDefect_le_completed_add_none
      (strategy lines) (axisQuestion sample.1) (axisQuestion sample.1)
      axisCoefficients axisCoefficients sample.1 parameter
  calc
    axisParameterEvaluationDefect lines ≤
        avgOver (directALinePointDist P.extendedDirectLd) F := havg
    _ = axisSameLineEvaluationDefect lines + axisAliceNoneMass lines +
        axisBobNoneMass lines := by
      simp only [F, directALinePointDist, Distribution.avgOver_map,
        axisQuestion_directALineDescOf, axis_completed_mismatch_eq,
        axis_none_mass_eq lines .alice, axis_none_mass_eq lines .bob, avgOver_add]
      change _ + axisAliceNoneMass lines + axisBobNoneMass lines =
        axisSameLineEvaluationDefect lines + axisAliceNoneMass lines + axisBobNoneMass lines
      congr 2
      exact (WinImplications.consistencyDefect_postprocess_eq_mismatch
        (uniformDistribution (DirectLdSpace P.extendedDirectLd)) (strategy lines)
        (fun sample => (.aline, directLdMap P.extendedDirectLd .aline sample))
        (fun sample => (.aline, directLdMap P.extendedDirectLd .aline sample))
        axisGameRead axisGameRead).symm

/-- Averaging the parameter/completed-read comparison over the actual diagonal law. -/
private theorem diagonal_parameter_evaluation_defect_le_completed
    (lines : ExtendedLinesWitness setting points deltaL) :
    diagonalParameterEvaluationDefect lines ≤
      diagonalSameLineEvaluationDefect lines + diagonalAliceNoneMass lines +
        diagonalBobNoneMass lines := by
  let F : DirectLineDesc P.extendedDirectLd ×
      (Fin P.extendedDirectLd.m → DirectScalarQ P.extendedDirectLd) → ℝ := fun sample =>
    outcomeEventWeight (strategy lines) (diagonalQuestion sample.1) (diagonalQuestion sample.1)
        (fun answerA answerB => directEvalOpt sample.1 sample.2 (diagonalCoefficients answerA) ≠
          directEvalOpt sample.1 sample.2 (diagonalCoefficients answerB)) +
      aliceEventWeight (strategy lines) (diagonalQuestion sample.1)
        (fun answer => directEvalOpt sample.1 sample.2 (diagonalCoefficients answer) = none) +
      bobEventWeight (strategy lines) (diagonalQuestion sample.1)
        (fun answer => directEvalOpt sample.1 sample.2 (diagonalCoefficients answer) = none)
  have havg : diagonalParameterEvaluationDefect lines ≤
      avgOver (directDLinePointDist P.extendedDirectLd) F := by
    rw [← avgOver_directDLinePointDist_resample P.extendedDirectLd F,
      Distribution.avgOver_map]
    unfold diagonalParameterEvaluationDefect
    apply avgOver_mono
    intro sample
    apply avgOver_mono
    intro parameter
    exact parameterEvalDefect_le_completed_add_none
      (strategy lines) (diagonalQuestion sample.1) (diagonalQuestion sample.1)
      diagonalCoefficients diagonalCoefficients sample.1 parameter
  calc
    diagonalParameterEvaluationDefect lines ≤
        avgOver (directDLinePointDist P.extendedDirectLd) F := havg
    _ = diagonalSameLineEvaluationDefect lines + diagonalAliceNoneMass lines +
        diagonalBobNoneMass lines := by
      simp only [F, directDLinePointDist, Distribution.avgOver_map,
        diagonalQuestion_directDLineDescOf, diagonal_completed_mismatch_eq,
        diagonal_none_mass_eq lines .alice, diagonal_none_mass_eq lines .bob, avgOver_add]
      change _ + diagonalAliceNoneMass lines + diagonalBobNoneMass lines =
        diagonalSameLineEvaluationDefect lines + diagonalAliceNoneMass lines +
          diagonalBobNoneMass lines
      congr 2
      exact (WinImplications.consistencyDefect_postprocess_eq_mismatch
        (uniformDistribution (DirectLdSpace P.extendedDirectLd)) (strategy lines)
        (fun sample => (.dline, directLdMap P.extendedDirectLd .dline sample))
        (fun sample => (.dline, directLdMap P.extendedDirectLd .dline sample))
        diagonalGameRead diagonalGameRead).symm

/-- Independently evaluating the supplied axis-line measurements has defect at
most `6 * deltaL + 2 * sqrt (deltaQ + 2 * deltaL)`. This is a formalization-only
estimate supporting `lem:qld-4-7`, paper lines 1279--1288. -/
theorem axis_parameter_evaluation_defect_le
    (lines : ExtendedLinesWitness setting points deltaL) :
    axisParameterEvaluationDefect lines ≤
      6 * deltaL + 2 * Real.sqrt (deltaQ + 2 * deltaL) := by
  have hforward := (completedLinePointDefect_sums_le lines).1
  rw [← aline_point_rejection_eq_completedLinePointDefect lines,
    ← dline_point_rejection_eq_completedLinePointDefect lines] at hforward
  have hreverse := (completedLinePointDefect_sums_le lines).2
  rw [← point_aline_rejection_eq_completedLinePointDefect lines,
    ← point_dline_rejection_eq_completedLinePointDefect lines] at hreverse
  have hforwardNonneg := directLdBranchRejectionProbability_nonneg
    P.extendedDirectLd (strategy lines) (.dline, .point)
  have hreverseNonneg := directLdBranchRejectionProbability_nonneg
    P.extendedDirectLd (strategy lines) (.point, .dline)
  have hcomparison := axis_same_line_evaluation_defect_le lines
  have hnoneA := axis_alice_none_mass_le_rejection lines
  have hnoneB := axis_bob_none_mass_le_rejection lines
  have hparameter := axis_parameter_evaluation_defect_le_completed lines
  linarith

/-- Independently evaluating the supplied diagonal-line measurements has
defect at most `6 * deltaL + 2 * sqrt (deltaQ + 2 * deltaL)`, including zero
directions. This is a formalization-only estimate supporting `lem:qld-4-7`,
paper lines 1279--1288. -/
theorem diagonal_parameter_evaluation_defect_le
    (lines : ExtendedLinesWitness setting points deltaL) :
    diagonalParameterEvaluationDefect lines ≤
      6 * deltaL + 2 * Real.sqrt (deltaQ + 2 * deltaL) := by
  have hforward := (completedLinePointDefect_sums_le lines).1
  rw [← aline_point_rejection_eq_completedLinePointDefect lines,
    ← dline_point_rejection_eq_completedLinePointDefect lines] at hforward
  have hreverse := (completedLinePointDefect_sums_le lines).2
  rw [← point_aline_rejection_eq_completedLinePointDefect lines,
    ← point_dline_rejection_eq_completedLinePointDefect lines] at hreverse
  have hforwardNonneg := directLdBranchRejectionProbability_nonneg
    P.extendedDirectLd (strategy lines) (.aline, .point)
  have hreverseNonneg := directLdBranchRejectionProbability_nonneg
    P.extendedDirectLd (strategy lines) (.point, .aline)
  have hcomparison := diagonal_same_line_evaluation_defect_le lines
  have hnoneA := diagonal_alice_none_mass_le_rejection lines
  have hnoneB := diagonal_bob_none_mass_le_rejection lines
  have hparameter := diagonal_parameter_evaluation_defect_le_completed lines
  linarith

end ExtendedLineGame

end

end MIPStarRE.QPBT
