import MIPStarRE.QPBT.Combining.PassingError
import MIPStarRE.QPBT.Combining.DirectLowDegree.ExtendedCoefficientLoss
import MIPStarRE.QPBT.Combining.DirectLowDegree.RejectionBounds
import MIPStarRE.QPBT.Combining.ExtendedLineGame.AxisParameterDefectTransport
import MIPStarRE.QPBT.Combining.ExtendedLineGame.DiagonalParameterDefectTransport
import MIPStarRE.QPBT.Combining.ExtendedLineGame.ParameterEvaluatedLineBound
import MIPStarRE.QPBT.Combining.ExtendedLineGame.SameLineCoefficientBound
import MIPStarRE.QPBT.Combining.WitnessErrorNonneg

/-!
# Passing value of the supplied extended-line strategy

This module assembles the seven potentially rejecting branches of the directly
indexed low-degree strategy constructed from an `ExtendedLinesWitness`.  It
then transports the resulting lower bound through the explicit Naimark
dilation.  These are formalization-only supplied-witness consequences; they do
not construct the witness or establish source theorem `lem:qld-4-7`.

## References

- `references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1020-1034`
- `references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1279-1288`
- Blueprint `lem:qld-4-7`
- Issue #348
-/

namespace MIPStarRE.QPBT

open MIPStarRE.LDT hiding Measurement

noncomputable section

namespace ExtendedLineGame

variable {P : AdmissibleParams} {epsilon deltaQ deltaL : Real}
variable {setting : ProjectiveSetting P epsilon}
variable {points : CombinedPointsWitness setting deltaQ}

/-- The sum of the seven potentially rejecting branches of the supplied
strategy is bounded by the scalar expression used by the direct passing-error
envelope. -/
theorem seven_branch_rejections_le
    (lines : ExtendedLinesWitness setting points deltaL) :
    directLdBranchRejectionProbability P.extendedDirectLd (strategy lines)
          (.point, .point) +
        directLdBranchRejectionProbability P.extendedDirectLd (strategy lines)
          (.point, .aline) +
        directLdBranchRejectionProbability P.extendedDirectLd (strategy lines)
          (.point, .dline) +
        directLdBranchRejectionProbability P.extendedDirectLd (strategy lines)
          (.aline, .point) +
        directLdBranchRejectionProbability P.extendedDirectLd (strategy lines)
          (.aline, .aline) +
        directLdBranchRejectionProbability P.extendedDirectLd (strategy lines)
          (.dline, .point) +
        directLdBranchRejectionProbability P.extendedDirectLd (strategy lines)
          (.dline, .dline) ≤
      deltaQ + 16 * deltaL + 4 * Real.sqrt (deltaQ + 2 * deltaL) +
        5 * ((P.m * P.d : Real) / (P.q : Real)) := by
  have hpoint := point_point_rejection_le lines
  have hmixed := mixed_line_point_rejections_le_four_mul lines
  have haxis :=
    aline_aline_rejection_le_axisParameterEvaluatedCoefficientDefect_add lines
  have hdiagonal :=
    dline_dline_rejection_le_diagonalParameterEvaluatedCoefficientDefect_add lines
  rw [axis_parameter_evaluated_coefficient_defect_eq] at haxis
  rw [diagonal_parameter_evaluated_coefficient_defect_eq] at hdiagonal
  have haxisEval := axis_parameter_evaluation_defect_le lines
  have hdiagonalEval := diagonal_parameter_evaluation_defect_le lines
  have hcollision :
      (P.d : Real) / (P.extendedDirectLd.q : Real) +
          (P.extendedDirectLd.m * P.extendedDirectLd.d : Real) /
            (P.extendedDirectLd.q : Real) ≤
        5 * ((P.m * P.d : Real) / (P.q : Real)) := by
    calc
      _ = ((P.extendedDirectLd.d : Real) +
            (P.extendedDirectLd.m * P.extendedDirectLd.d : Real)) /
          (P.extendedDirectLd.q : Real) := by
        change
          (P.extendedDirectLd.d : Real) / (P.extendedDirectLd.q : Real) +
              (P.extendedDirectLd.m * P.extendedDirectLd.d : Real) /
                (P.extendedDirectLd.q : Real) = _
        ring
      _ ≤ _ := extendedDirectLd_coefficientCollisionLoss_le_five_mul P
  linarith

/-- The supplied directly indexed strategy passes with error bounded by the
concrete polynomial envelope in `deltaQ + deltaL` and `m*d/q`. -/
theorem strategy_value_ge_directPassingErrorEnvelope
    (lines : ExtendedLinesWitness setting points deltaL) :
    1 - directPassingErrorEnvelope (deltaQ + deltaL)
        ((P.m * P.d : Real) / (P.q : Real)) ≤
      (strategy lines).value := by
  let rejection :=
    directLdBranchRejectionProbability P.extendedDirectLd (strategy lines)
          (.point, .point) +
        directLdBranchRejectionProbability P.extendedDirectLd (strategy lines)
          (.point, .aline) +
        directLdBranchRejectionProbability P.extendedDirectLd (strategy lines)
          (.point, .dline) +
        directLdBranchRejectionProbability P.extendedDirectLd (strategy lines)
          (.aline, .point) +
        directLdBranchRejectionProbability P.extendedDirectLd (strategy lines)
          (.aline, .aline) +
        directLdBranchRejectionProbability P.extendedDirectLd (strategy lines)
          (.dline, .point) +
        directLdBranchRejectionProbability P.extendedDirectLd (strategy lines)
          (.dline, .dline)
  have hsum : rejection ≤
      deltaQ + 16 * deltaL + 4 * Real.sqrt (deltaQ + 2 * deltaL) +
        5 * ((P.m * P.d : Real) / (P.q : Real)) := by
    exact seven_branch_rejections_le lines
  have hcap : rejection / 9 ≤ 1 := by
    have h := directLdRejectionProbability_le_one P.extendedDirectLd (strategy lines)
    rw [directLdRejectionProbability_eq_one_sub_value, strategy_value_eq lines] at h
    change rejection / 9 ≤ 1
    linarith
  have hraw : rejection / 9 ≤
      (deltaQ + 16 * deltaL + 4 * Real.sqrt (deltaQ + 2 * deltaL) +
        5 * ((P.m * P.d : Real) / (P.q : Real))) / 9 := by
    linarith
  have henvelope := seven_branch_capped_error_le_directPassingErrorEnvelope
    deltaQ deltaL ((P.m * P.d : Real) / (P.q : Real))
    points.delta_nonneg lines.delta_nonneg (by positivity)
  have hrejection : rejection / 9 ≤
      directPassingErrorEnvelope (deltaQ + deltaL)
        ((P.m * P.d : Real) / (P.q : Real)) :=
    (le_min hcap hraw).trans henvelope
  rw [strategy_value_eq lines]
  change 1 - _ ≤ 1 - rejection / 9
  linarith

/-- The Naimark-projectivized supplied strategy has the same passing-value
lower bound as the original strategy. -/
theorem projectiveStrategy_value_ge_directPassingErrorEnvelope
    (lines : ExtendedLinesWitness setting points deltaL) :
    1 - directPassingErrorEnvelope (deltaQ + deltaL)
        ((P.m * P.d : Real) / (P.q : Real)) ≤
      (projectiveStrategy lines).value := by
  rw [projectiveStrategy_value]
  exact strategy_value_ge_directPassingErrorEnvelope lines

end ExtendedLineGame

end

end MIPStarRE.QPBT
