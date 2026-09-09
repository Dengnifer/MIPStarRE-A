import MIPStarRE.QPBT.Combining.ExtendedLineGame.PointPointRejection

/-!
# Completed same-line evaluation comparison

This module compares Alice's and Bob's completed axis-line or diagonal-line
readouts through the corresponding point readouts. The comparison uses the
consistency triangle on the common direct-game sample and then applies the
already proved mixed and point/point branch bounds.

The readouts take values in `Option (PauliScalar P)`. Agreement on `none`, in
particular for zero directions, is not an equality of parameter evaluations;
no coefficient-collision conclusion is asserted here.

## References

- `references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1279-1288`
- `references/qpbt-paper/06_nonlocal_games_and_mipstar.tex:389-401`
- Blueprint `lem:qld-4-7`.
- Issue #321.
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

/-- Decompose a direct sample with its point first, retaining the jointly
uniform index and direction as the second coordinate. -/
private def directSamplePointEquiv (D : DirectLdParams) :
    DirectLdSpace D ≃
      (Fin D.m → DirectScalarQ D) ×
        (Fin D.m × (Fin D.m → DirectScalarQ D)) where
  toFun sample := (sample.point, sample.index, sample.direction)
  invFun sample := ⟨sample.1, sample.2.1, sample.2.2⟩
  left_inv sample := by cases sample; rfl
  right_inv sample := by cases sample; rfl

/-- A uniform consistency defect whose integrand uses only the first
coordinate of a product equivalence has the corresponding uniform marginal. -/
private theorem consistencyDefect_uniform_equiv_fst
    {Gamma X Y Alpha I : Type*}
    [Fintype Gamma] [DecidableEq Gamma] [Nonempty Gamma]
    [Fintype X] [DecidableEq X] [Nonempty X]
    [Finite Y] [Nonempty Y]
    [Fintype Alpha] [DecidableEq Alpha]
    [Fintype I] [DecidableEq I]
    (e : Gamma ≃ X × Y) (A B : X → Alpha → Op I)
    (psi : EuclideanSpace ℂ I) :
    consistencyDefect (uniformDistribution Gamma)
        (fun sample answer => A (e sample).1 answer)
        (fun sample answer => B (e sample).1 answer) psi =
      consistencyDefect (uniformDistribution X) A B psi := by
  unfold consistencyDefect
  let f : X → ℝ := fun x =>
    ∑ a : Alpha, ∑ b : Alpha,
      if a = b then 0 else
        (inner ℂ psi ((EuclideanSpace.equiv I ℂ).symm
          ((A x a * B x b).mulVec psi))).re
  change avgOver (uniformDistribution Gamma) (fun sample => f (e sample).1) =
    avgOver (uniformDistribution X) f
  exact avgOver_uniform_equiv_fst e f

/-- The consistency defect of Alice's and Bob's completed axis-line readouts
on the common direct-game sample. Failed evaluation remains `none`. -/
noncomputable def axisSameLineEvaluationDefect
    (lines : ExtendedLinesWitness setting points deltaL) : ℝ :=
  consistencyDefect (uniformDistribution (DirectLdSpace P.extendedDirectLd))
    (fun sample answer =>
      (DistanceCalculus.leftPlacedMeasurement
        (ιB := setting.ExpandedLocalSpace .bob)
        ((answerMeasurement lines .alice
          (.aline, directLdMap P.extendedDirectLd .aline sample)).postprocess
            (axisGameRead sample))).effect answer)
    (fun sample answer =>
      (DistanceCalculus.rightPlacedMeasurement
        (ιA := setting.ExpandedLocalSpace .alice)
        ((answerMeasurement lines .bob
          (.aline, directLdMap P.extendedDirectLd .aline sample)).postprocess
            (axisGameRead sample))).effect answer)
    (pairState setting)

/-- The consistency defect of Alice's and Bob's completed diagonal-line
readouts on the common direct-game sample. Failed evaluation remains `none`. -/
noncomputable def diagonalSameLineEvaluationDefect
    (lines : ExtendedLinesWitness setting points deltaL) : ℝ :=
  consistencyDefect (uniformDistribution (DirectLdSpace P.extendedDirectLd))
    (fun sample answer =>
      (DistanceCalculus.leftPlacedMeasurement
        (ιB := setting.ExpandedLocalSpace .bob)
        ((answerMeasurement lines .alice
          (.dline, directLdMap P.extendedDirectLd .dline sample)).postprocess
            (diagonalGameRead sample))).effect answer)
    (fun sample answer =>
      (DistanceCalculus.rightPlacedMeasurement
        (ιA := setting.ExpandedLocalSpace .alice)
        ((answerMeasurement lines .bob
          (.dline, directLdMap P.extendedDirectLd .dline sample)).postprocess
            (diagonalGameRead sample))).effect answer)
    (pairState setting)

/-- The point/point read defect is unchanged when the jointly uniform direct
sample's unused index and direction are retained. -/
private theorem point_read_defect_on_direct_samples_eq_rejection
    (lines : ExtendedLinesWitness setting points deltaL) :
    consistencyDefect (uniformDistribution (DirectLdSpace P.extendedDirectLd))
        (fun sample answer => heteroKron
          (((answerMeasurement lines .alice
            (.point, directLdMap P.extendedDirectLd .point sample)).postprocess
              pointGameRead).effect answer) 1)
        (fun sample answer => heteroKron 1
          (((answerMeasurement lines .bob
            (.point, directLdMap P.extendedDirectLd .point sample)).postprocess
              pointGameRead).effect answer))
        (pairState setting) =
      directLdBranchRejectionProbability P.extendedDirectLd (strategy lines)
        (.point, .point) := by
  rw [point_branch_rejection_eq_consistencyDefect lines]
  calc
    _ = consistencyDefect (uniformDistribution (DirectLdSpace P.extendedDirectLd))
        (fun sample answer => heteroKron
          (((points.Q .alice
            (projX (directPointToPauli P sample.point))
            (projZ (directPointToPauli P sample.point))).postprocess fun values =>
              some (directPointToPauli P sample.point (alphaVar P.m) * values.1 +
                directPointToPauli P sample.point (betaVar P.m) * values.2)).effect answer) 1)
        (fun sample answer => heteroKron 1
          (((points.Q .bob
            (projX (directPointToPauli P sample.point))
            (projZ (directPointToPauli P sample.point))).postprocess fun values =>
              some (directPointToPauli P sample.point (alphaVar P.m) * values.1 +
                directPointToPauli P sample.point (betaVar P.m) * values.2)).effect answer))
        (pairState setting) := by
      apply consistencyDefect_congr <;> intro sample answer
      · rw [point_read_effect lines .alice]
      · rw [point_read_effect lines .bob]
    _ = consistencyDefect (uniformDistribution
          (Fin P.extendedDirectLd.m → DirectScalarQ P.extendedDirectLd))
        (fun point answer => heteroKron
          (((points.Q .alice
            (projX (directPointToPauli P point))
            (projZ (directPointToPauli P point))).postprocess fun values =>
              some (directPointToPauli P point (alphaVar P.m) * values.1 +
                directPointToPauli P point (betaVar P.m) * values.2)).effect answer) 1)
        (fun point answer => heteroKron 1
          (((points.Q .bob
            (projX (directPointToPauli P point))
            (projZ (directPointToPauli P point))).postprocess fun values =>
              some (directPointToPauli P point (alphaVar P.m) * values.1 +
                directPointToPauli P point (betaVar P.m) * values.2)).effect answer))
        (pairState setting) := by
      exact consistencyDefect_uniform_equiv_fst
        (Gamma := DirectLdSpace P.extendedDirectLd)
        (X := Fin P.extendedDirectLd.m → DirectScalarQ P.extendedDirectLd)
        (Y := Fin P.extendedDirectLd.m ×
          (Fin P.extendedDirectLd.m → DirectScalarQ P.extendedDirectLd))
        (Alpha := Option (PauliScalar P))
        (I := setting.ExpandedLocalSpace .alice × setting.ExpandedLocalSpace .bob)
        (directSamplePointEquiv P.extendedDirectLd)
        (fun point answer => heteroKron
          (((points.Q .alice
            (projX (directPointToPauli P point))
            (projZ (directPointToPauli P point))).postprocess fun values =>
              some (directPointToPauli P point (alphaVar P.m) * values.1 +
                directPointToPauli P point (betaVar P.m) * values.2)).effect answer) 1)
        (fun point answer => heteroKron 1
          (((points.Q .bob
            (projX (directPointToPauli P point))
            (projZ (directPointToPauli P point))).postprocess fun values =>
              some (directPointToPauli P point (alphaVar P.m) * values.1 +
                directPointToPauli P point (betaVar P.m) * values.2)).effect answer))
        (pairState setting)

/-- Completed axis-line readouts compare through the two point readouts. This
uses the consistency triangle and does not assume projectivity of `Qline`. -/
theorem axis_same_line_evaluation_defect_le_branch_chain
    (lines : ExtendedLinesWitness setting points deltaL) :
    axisSameLineEvaluationDefect lines ≤
      directLdBranchRejectionProbability P.extendedDirectLd (strategy lines)
          (.aline, .point) +
        2 * Real.sqrt
          (directLdBranchRejectionProbability P.extendedDirectLd (strategy lines)
              (.point, .point) +
            directLdBranchRejectionProbability P.extendedDirectLd (strategy lines)
              (.point, .aline)) := by
  let μ := uniformDistribution (DirectLdSpace P.extendedDirectLd)
  let A : DirectLdSpace P.extendedDirectLd →
      Measurement (Option (PauliScalar P))
        (setting.ExpandedLocalSpace .alice × setting.ExpandedLocalSpace .bob) :=
    fun sample => DistanceCalculus.leftPlacedMeasurement
      (ιB := setting.ExpandedLocalSpace .bob)
      ((answerMeasurement lines .alice
        (.aline, directLdMap P.extendedDirectLd .aline sample)).postprocess
          (axisGameRead sample))
  let B : DirectLdSpace P.extendedDirectLd →
      Measurement (Option (PauliScalar P))
        (setting.ExpandedLocalSpace .alice × setting.ExpandedLocalSpace .bob) :=
    fun sample => DistanceCalculus.rightPlacedMeasurement
      (ιA := setting.ExpandedLocalSpace .alice)
      ((answerMeasurement lines .bob
        (.point, directLdMap P.extendedDirectLd .point sample)).postprocess pointGameRead)
  let C : DirectLdSpace P.extendedDirectLd →
      Measurement (Option (PauliScalar P))
        (setting.ExpandedLocalSpace .alice × setting.ExpandedLocalSpace .bob) :=
    fun sample => DistanceCalculus.leftPlacedMeasurement
      (ιB := setting.ExpandedLocalSpace .bob)
      ((answerMeasurement lines .alice
        (.point, directLdMap P.extendedDirectLd .point sample)).postprocess pointGameRead)
  let D : DirectLdSpace P.extendedDirectLd →
      Measurement (Option (PauliScalar P))
        (setting.ExpandedLocalSpace .alice × setting.ExpandedLocalSpace .bob) :=
    fun sample => DistanceCalculus.rightPlacedMeasurement
      (ιA := setting.ExpandedLocalSpace .alice)
      ((answerMeasurement lines .bob
        (.aline, directLdMap P.extendedDirectLd .aline sample)).postprocess
          (axisGameRead sample))
  have hAB : consistencyDefect μ (fun sample answer => (A sample).effect answer)
      (fun sample answer => (B sample).effect answer) (pairState setting) ≤
      directLdBranchRejectionProbability P.extendedDirectLd (strategy lines)
        (.aline, .point) := by
    change consistencyDefect μ
      (fun sample answer => heteroKron
        (((answerMeasurement lines .alice
          (.aline, directLdMap P.extendedDirectLd .aline sample)).postprocess
            (axisGameRead sample)).effect answer) 1)
      (fun sample answer => heteroKron 1
        (((answerMeasurement lines .bob
          (.point, directLdMap P.extendedDirectLd .point sample)).postprocess
            pointGameRead).effect answer)) (pairState setting) ≤ _
    rw [← completed_defect_eq_read_defect lines,
      ← aline_point_rejection_eq_completedLinePointDefect lines]
  have hCB : consistencyDefect μ (fun sample answer => (C sample).effect answer)
      (fun sample answer => (B sample).effect answer) (pairState setting) ≤
      directLdBranchRejectionProbability P.extendedDirectLd (strategy lines)
        (.point, .point) := by
    change consistencyDefect μ
      (fun sample answer => heteroKron
        (((answerMeasurement lines .alice
          (.point, directLdMap P.extendedDirectLd .point sample)).postprocess
            pointGameRead).effect answer) 1)
      (fun sample answer => heteroKron 1
        (((answerMeasurement lines .bob
          (.point, directLdMap P.extendedDirectLd .point sample)).postprocess
            pointGameRead).effect answer)) (pairState setting) ≤ _
    exact le_of_eq (point_read_defect_on_direct_samples_eq_rejection lines)
  have hCD : consistencyDefect μ (fun sample answer => (C sample).effect answer)
      (fun sample answer => (D sample).effect answer) (pairState setting) ≤
      directLdBranchRejectionProbability P.extendedDirectLd (strategy lines)
        (.point, .aline) := by
    change consistencyDefect μ
      (fun sample answer => heteroKron
        (((answerMeasurement lines .alice
          (.point, directLdMap P.extendedDirectLd .point sample)).postprocess
            pointGameRead).effect answer) 1)
      (fun sample answer => heteroKron 1
        (((answerMeasurement lines .bob
          (.aline, directLdMap P.extendedDirectLd .aline sample)).postprocess
            (axisGameRead sample)).effect answer)) (pairState setting) ≤ _
    rw [← reversed_axis_completed_defect_eq_read_defect lines,
      ← point_aline_rejection_eq_completedLinePointDefect lines]
  change consistencyDefect μ (fun sample answer => (A sample).effect answer)
    (fun sample answer => (D sample).effect answer) (pairState setting) ≤ _
  exact consistencyDefect_trans_le μ A B C D (pairState setting) _ _ _
    (uniformDistribution_isProbability _) (pairState_norm setting) hAB hCB hCD

/-- Completed diagonal-line readouts compare through the two point readouts.
This uses the consistency triangle and does not assume projectivity of `Qline`. -/
theorem diagonal_same_line_evaluation_defect_le_branch_chain
    (lines : ExtendedLinesWitness setting points deltaL) :
    diagonalSameLineEvaluationDefect lines ≤
      directLdBranchRejectionProbability P.extendedDirectLd (strategy lines)
          (.dline, .point) +
        2 * Real.sqrt
          (directLdBranchRejectionProbability P.extendedDirectLd (strategy lines)
              (.point, .point) +
            directLdBranchRejectionProbability P.extendedDirectLd (strategy lines)
              (.point, .dline)) := by
  let μ := uniformDistribution (DirectLdSpace P.extendedDirectLd)
  let A : DirectLdSpace P.extendedDirectLd →
      Measurement (Option (PauliScalar P))
        (setting.ExpandedLocalSpace .alice × setting.ExpandedLocalSpace .bob) :=
    fun sample => DistanceCalculus.leftPlacedMeasurement
      (ιB := setting.ExpandedLocalSpace .bob)
      ((answerMeasurement lines .alice
        (.dline, directLdMap P.extendedDirectLd .dline sample)).postprocess
          (diagonalGameRead sample))
  let B : DirectLdSpace P.extendedDirectLd →
      Measurement (Option (PauliScalar P))
        (setting.ExpandedLocalSpace .alice × setting.ExpandedLocalSpace .bob) :=
    fun sample => DistanceCalculus.rightPlacedMeasurement
      (ιA := setting.ExpandedLocalSpace .alice)
      ((answerMeasurement lines .bob
        (.point, directLdMap P.extendedDirectLd .point sample)).postprocess pointGameRead)
  let C : DirectLdSpace P.extendedDirectLd →
      Measurement (Option (PauliScalar P))
        (setting.ExpandedLocalSpace .alice × setting.ExpandedLocalSpace .bob) :=
    fun sample => DistanceCalculus.leftPlacedMeasurement
      (ιB := setting.ExpandedLocalSpace .bob)
      ((answerMeasurement lines .alice
        (.point, directLdMap P.extendedDirectLd .point sample)).postprocess pointGameRead)
  let D : DirectLdSpace P.extendedDirectLd →
      Measurement (Option (PauliScalar P))
        (setting.ExpandedLocalSpace .alice × setting.ExpandedLocalSpace .bob) :=
    fun sample => DistanceCalculus.rightPlacedMeasurement
      (ιA := setting.ExpandedLocalSpace .alice)
      ((answerMeasurement lines .bob
        (.dline, directLdMap P.extendedDirectLd .dline sample)).postprocess
          (diagonalGameRead sample))
  have hAB : consistencyDefect μ (fun sample answer => (A sample).effect answer)
      (fun sample answer => (B sample).effect answer) (pairState setting) ≤
      directLdBranchRejectionProbability P.extendedDirectLd (strategy lines)
        (.dline, .point) := by
    change consistencyDefect μ
      (fun sample answer => heteroKron
        (((answerMeasurement lines .alice
          (.dline, directLdMap P.extendedDirectLd .dline sample)).postprocess
            (diagonalGameRead sample)).effect answer) 1)
      (fun sample answer => heteroKron 1
        (((answerMeasurement lines .bob
          (.point, directLdMap P.extendedDirectLd .point sample)).postprocess
            pointGameRead).effect answer)) (pairState setting) ≤ _
    rw [← diagonal_completed_defect_eq_read_defect lines,
      ← dline_point_rejection_eq_completedLinePointDefect lines]
  have hCB : consistencyDefect μ (fun sample answer => (C sample).effect answer)
      (fun sample answer => (B sample).effect answer) (pairState setting) ≤
      directLdBranchRejectionProbability P.extendedDirectLd (strategy lines)
        (.point, .point) := by
    change consistencyDefect μ
      (fun sample answer => heteroKron
        (((answerMeasurement lines .alice
          (.point, directLdMap P.extendedDirectLd .point sample)).postprocess
            pointGameRead).effect answer) 1)
      (fun sample answer => heteroKron 1
        (((answerMeasurement lines .bob
          (.point, directLdMap P.extendedDirectLd .point sample)).postprocess
            pointGameRead).effect answer)) (pairState setting) ≤ _
    exact le_of_eq (point_read_defect_on_direct_samples_eq_rejection lines)
  have hCD : consistencyDefect μ (fun sample answer => (C sample).effect answer)
      (fun sample answer => (D sample).effect answer) (pairState setting) ≤
      directLdBranchRejectionProbability P.extendedDirectLd (strategy lines)
        (.point, .dline) := by
    change consistencyDefect μ
      (fun sample answer => heteroKron
        (((answerMeasurement lines .alice
          (.point, directLdMap P.extendedDirectLd .point sample)).postprocess
            pointGameRead).effect answer) 1)
      (fun sample answer => heteroKron 1
        (((answerMeasurement lines .bob
          (.dline, directLdMap P.extendedDirectLd .dline sample)).postprocess
            (diagonalGameRead sample)).effect answer)) (pairState setting) ≤ _
    rw [← reversed_diagonal_completed_defect_eq_read_defect lines,
      ← point_dline_rejection_eq_completedLinePointDefect lines]
  change consistencyDefect μ (fun sample answer => (A sample).effect answer)
    (fun sample answer => (D sample).effect answer) (pairState setting) ≤ _
  exact consistencyDefect_trans_le μ A B C D (pairState setting) _ _ _
    (uniformDistribution_isProbability _) (pairState_norm setting) hAB hCB hCD

/-- The completed axis-line comparison obtained from the supplied line and
point witnesses. This remains an `Option`-readout statement. -/
theorem axis_same_line_evaluation_defect_le
    (lines : ExtendedLinesWitness setting points deltaL) :
    axisSameLineEvaluationDefect lines ≤
      2 * deltaL + 2 * Real.sqrt (deltaQ + 2 * deltaL) := by
  have hforward := (completedLinePointDefect_sums_le lines).1
  rw [← aline_point_rejection_eq_completedLinePointDefect lines,
    ← dline_point_rejection_eq_completedLinePointDefect lines] at hforward
  have hforwardNonneg := directLdBranchRejectionProbability_nonneg
    P.extendedDirectLd (strategy lines) (.dline, .point)
  have hforwardAxis :
      directLdBranchRejectionProbability P.extendedDirectLd (strategy lines)
          (.aline, .point) ≤ 2 * deltaL := by
    linarith
  have hreverse := (completedLinePointDefect_sums_le lines).2
  rw [← point_aline_rejection_eq_completedLinePointDefect lines,
    ← point_dline_rejection_eq_completedLinePointDefect lines] at hreverse
  have hreverseNonneg := directLdBranchRejectionProbability_nonneg
    P.extendedDirectLd (strategy lines) (.point, .dline)
  have hreverseAxis :
      directLdBranchRejectionProbability P.extendedDirectLd (strategy lines)
          (.point, .aline) ≤ 2 * deltaL := by
    linarith
  have hpoint := point_point_rejection_le lines
  calc
    axisSameLineEvaluationDefect lines ≤
        directLdBranchRejectionProbability P.extendedDirectLd (strategy lines)
            (.aline, .point) +
          2 * Real.sqrt
            (directLdBranchRejectionProbability P.extendedDirectLd (strategy lines)
                (.point, .point) +
              directLdBranchRejectionProbability P.extendedDirectLd (strategy lines)
                (.point, .aline)) :=
      axis_same_line_evaluation_defect_le_branch_chain lines
    _ ≤ 2 * deltaL +
        2 * Real.sqrt
          (directLdBranchRejectionProbability P.extendedDirectLd (strategy lines)
              (.point, .point) +
            directLdBranchRejectionProbability P.extendedDirectLd (strategy lines)
              (.point, .aline)) := by
      exact add_le_add hforwardAxis le_rfl
    _ ≤ 2 * deltaL + 2 * Real.sqrt (deltaQ + 2 * deltaL) := by
      gcongr

/-- The completed diagonal-line comparison obtained from the supplied line
and point witnesses. This remains an `Option`-readout statement. -/
theorem diagonal_same_line_evaluation_defect_le
    (lines : ExtendedLinesWitness setting points deltaL) :
    diagonalSameLineEvaluationDefect lines ≤
      2 * deltaL + 2 * Real.sqrt (deltaQ + 2 * deltaL) := by
  have hforward := (completedLinePointDefect_sums_le lines).1
  rw [← aline_point_rejection_eq_completedLinePointDefect lines,
    ← dline_point_rejection_eq_completedLinePointDefect lines] at hforward
  have hforwardNonneg := directLdBranchRejectionProbability_nonneg
    P.extendedDirectLd (strategy lines) (.aline, .point)
  have hforwardDiagonal :
      directLdBranchRejectionProbability P.extendedDirectLd (strategy lines)
          (.dline, .point) ≤ 2 * deltaL := by
    linarith
  have hreverse := (completedLinePointDefect_sums_le lines).2
  rw [← point_aline_rejection_eq_completedLinePointDefect lines,
    ← point_dline_rejection_eq_completedLinePointDefect lines] at hreverse
  have hreverseNonneg := directLdBranchRejectionProbability_nonneg
    P.extendedDirectLd (strategy lines) (.point, .aline)
  have hreverseDiagonal :
      directLdBranchRejectionProbability P.extendedDirectLd (strategy lines)
          (.point, .dline) ≤ 2 * deltaL := by
    linarith
  have hpoint := point_point_rejection_le lines
  calc
    diagonalSameLineEvaluationDefect lines ≤
        directLdBranchRejectionProbability P.extendedDirectLd (strategy lines)
            (.dline, .point) +
          2 * Real.sqrt
            (directLdBranchRejectionProbability P.extendedDirectLd (strategy lines)
                (.point, .point) +
              directLdBranchRejectionProbability P.extendedDirectLd (strategy lines)
                (.point, .dline)) :=
      diagonal_same_line_evaluation_defect_le_branch_chain lines
    _ ≤ 2 * deltaL +
        2 * Real.sqrt
          (directLdBranchRejectionProbability P.extendedDirectLd (strategy lines)
              (.point, .point) +
            directLdBranchRejectionProbability P.extendedDirectLd (strategy lines)
              (.point, .dline)) := by
      exact add_le_add hforwardDiagonal le_rfl
    _ ≤ 2 * deltaL + 2 * Real.sqrt (deltaQ + 2 * deltaL) := by
      gcongr

end ExtendedLineGame

end

end MIPStarRE.QPBT
