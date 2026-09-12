import MIPStarRE.QPBT.Combining.DirectLowDegree.CoefficientConsistency
import MIPStarRE.QPBT.Combining.ExtendedLineGame.SameLineRejection

/-!
# Coefficient bounds for same-line rejection

The exact axis-axis and diagonal-diagonal rejection identities are bounded by
evaluating the corresponding coefficient measurements at an independent
uniform affine parameter. The losses are the direct univariate collision terms
`d / q` and `md / q`.

## References

- `references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1020-1034`
- `references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1279-1288`
- `references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1595-1603`
- Blueprint `lem:qld-4-7`.
- Issue #328.
-/

open scoped BigOperators

namespace MIPStarRE.QPBT

open MIPStarRE.LDT hiding Measurement
open MIPStarRE.Quantum

noncomputable section

namespace ExtendedLineGame

variable {P : AdmissibleParams} {epsilon deltaQ deltaL : Real}
variable {setting : ProjectiveSetting P epsilon}
variable {points : CombinedPointsWitness setting deltaQ}

/-- The consistency defect of the axis coefficient measurements after
evaluation at an independent uniform affine parameter. -/
def axisParameterEvaluatedCoefficientDefect
    (lines : ExtendedLinesWitness setting points deltaL) : Real :=
  consistencyDefect
    (Distribution.prod ((directALinePointDist P.extendedDirectLd).map Prod.fst)
      (uniformDistribution (DirectScalarQ P.extendedDirectLd)))
    (fun sample value => heteroKron
      (((((lines.Qline .alice sample.1).postprocess (axisRead P)).postprocess
        (fun coefficients => evalCoefficient coefficients sample.2)).effect value)) 1)
    (fun sample value => heteroKron 1
      (((((lines.Qline .bob sample.1).postprocess (axisRead P)).postprocess
        (fun coefficients => evalCoefficient coefficients sample.2)).effect value)))
    (pairState setting)

/-- The consistency defect of the diagonal coefficient measurements after
evaluation at an independent uniform affine parameter. -/
def diagonalParameterEvaluatedCoefficientDefect
    (lines : ExtendedLinesWitness setting points deltaL) : Real :=
  consistencyDefect
    (Distribution.prod ((directDLinePointDist P.extendedDirectLd).map Prod.fst)
      (uniformDistribution (DirectScalarQ P.extendedDirectLd)))
    (fun sample value => heteroKron
      (((((lines.Qline .alice sample.1).postprocess (diagonalRead P)).postprocess
        (fun coefficients => evalCoefficient coefficients sample.2)).effect value)) 1)
    (fun sample value => heteroKron 1
      (((((lines.Qline .bob sample.1).postprocess (diagonalRead P)).postprocess
        (fun coefficients => evalCoefficient coefficients sample.2)).effect value)))
    (pairState setting)

private theorem axisCoefficientAnswerDefect_le_raw
    (lines : ExtendedLinesWitness setting points deltaL) :
    @LE.le Real Real.instLE (axisCoefficientAnswerDefect lines)
      (consistencyDefect ((directALinePointDist P.extendedDirectLd).map Prod.fst)
        (fun line coefficients => heteroKron
          (((lines.Qline .alice line).postprocess (axisRead P)).effect coefficients) 1)
        (fun line coefficients => heteroKron 1
          (((lines.Qline .bob line).postprocess (axisRead P)).effect coefficients))
        (pairState setting)) := by
  let A := fun line => (lines.Qline .alice line).postprocess (axisRead P)
  let B := fun line => (lines.Qline .bob line).postprocess (axisRead P)
  let wrap : DirectDegPoly P.extendedDirectLd P.d ->
      DirectLdAnswer P.extendedDirectLd := fun coefficients =>
    @DirectLdAnswer.alinePolys P.extendedDirectLd
      (fun _ index => coefficients
        (Fin.cast (by simp [AdmissibleParams.extendedDirectLd]) index))
  have hwrap : (fun coefficients => wrap (axisRead P coefficients)) = axisAnswer P := by
    funext coefficients
    dsimp [wrap, axisAnswer]
    congr 1
  have h := consistencyDefect_postprocess_le
    ((directALinePointDist P.extendedDirectLd).map Prod.fst)
    A B (pairState setting) wrap
  have hEq : axisCoefficientAnswerDefect lines =
      consistencyDefect ((directALinePointDist P.extendedDirectLd).map Prod.fst)
        (fun line answer => heteroKron (((A line).postprocess wrap).effect answer) 1)
        (fun line answer => heteroKron 1 (((B line).postprocess wrap).effect answer))
        (pairState setting) := by
    unfold axisCoefficientAnswerDefect
    apply consistencyDefect_congr
    · intro line answer
      apply congrArg (fun effect => heteroKron effect 1)
      rw [<- hwrap]
      simpa only [A] using
        (SandwichProduct.postprocess_postprocess_effect
          (lines.Qline .alice line) (axisRead P) wrap answer).symm
    · intro line answer
      apply congrArg (fun effect => heteroKron 1 effect)
      rw [<- hwrap]
      simpa only [B] using
        (SandwichProduct.postprocess_postprocess_effect
          (lines.Qline .bob line) (axisRead P) wrap answer).symm
  rw [hEq]
  exact h

private theorem diagonalCoefficientAnswerDefect_le_raw
    (lines : ExtendedLinesWitness setting points deltaL) :
    @LE.le Real Real.instLE (diagonalCoefficientAnswerDefect lines)
      (consistencyDefect ((directDLinePointDist P.extendedDirectLd).map Prod.fst)
        (fun line coefficients => heteroKron
          (((lines.Qline .alice line).postprocess (diagonalRead P)).effect coefficients) 1)
        (fun line coefficients => heteroKron 1
          (((lines.Qline .bob line).postprocess (diagonalRead P)).effect coefficients))
        (pairState setting)) := by
  let A := fun line => (lines.Qline .alice line).postprocess (diagonalRead P)
  let B := fun line => (lines.Qline .bob line).postprocess (diagonalRead P)
  let wrap : DirectDegPoly P.extendedDirectLd
      (P.extendedDirectLd.m * P.extendedDirectLd.d) ->
      DirectLdAnswer P.extendedDirectLd := fun coefficients =>
    @DirectLdAnswer.dlinePolys P.extendedDirectLd (fun _ => coefficients)
  have hwrap : (fun coefficients => wrap (diagonalRead P coefficients)) =
      diagonalAnswer P := by
    funext coefficients
    rfl
  have h := consistencyDefect_postprocess_le
    ((directDLinePointDist P.extendedDirectLd).map Prod.fst)
    A B (pairState setting) wrap
  have hEq : diagonalCoefficientAnswerDefect lines =
      consistencyDefect ((directDLinePointDist P.extendedDirectLd).map Prod.fst)
        (fun line answer => heteroKron (((A line).postprocess wrap).effect answer) 1)
        (fun line answer => heteroKron 1 (((B line).postprocess wrap).effect answer))
        (pairState setting) := by
    unfold diagonalCoefficientAnswerDefect
    apply consistencyDefect_congr
    · intro line answer
      apply congrArg (fun effect => heteroKron effect 1)
      rw [<- hwrap]
      simpa only [A] using
        (SandwichProduct.postprocess_postprocess_effect
          (lines.Qline .alice line) (diagonalRead P) wrap answer).symm
    · intro line answer
      apply congrArg (fun effect => heteroKron 1 effect)
      rw [<- hwrap]
      simpa only [B] using
        (SandwichProduct.postprocess_postprocess_effect
          (lines.Qline .bob line) (diagonalRead P) wrap answer).symm
  rw [hEq]
  exact h

/-- The axis-axis branch rejection is bounded by the independently evaluated
axis coefficient defect plus `d / q`. -/
theorem aline_aline_rejection_le_axisParameterEvaluatedCoefficientDefect_add
    (lines : ExtendedLinesWitness setting points deltaL) :
    @LE.le Real Real.instLE
      (directLdBranchRejectionProbability P.extendedDirectLd (strategy lines)
        (.aline, .aline))
      (axisParameterEvaluatedCoefficientDefect lines +
        (P.d : Real) / (P.extendedDirectLd.q : Real)) := by
  rw [aline_aline_rejection_eq_axisCoefficientAnswerDefect]
  calc
    axisCoefficientAnswerDefect lines <=
        consistencyDefect ((directALinePointDist P.extendedDirectLd).map Prod.fst)
          (fun line coefficients => heteroKron
            (((lines.Qline .alice line).postprocess (axisRead P)).effect coefficients) 1)
          (fun line coefficients => heteroKron 1
            (((lines.Qline .bob line).postprocess (axisRead P)).effect coefficients))
          (pairState setting) := axisCoefficientAnswerDefect_le_raw lines
    _ <= _ := by
      have hProbability :
          ((directALinePointDist P.extendedDirectLd).map Prod.fst).IsProbability :=
        (directALinePointDist_isProbability P.extendedDirectLd).map _
      simpa [axisParameterEvaluatedCoefficientDefect] using
        (consistencyDefect_directCoefficients_le_evaluated_add
          P.extendedDirectLd P.d
          ((directALinePointDist P.extendedDirectLd).map Prod.fst)
          (fun line => (lines.Qline .alice line).postprocess (axisRead P))
          (fun line => (lines.Qline .bob line).postprocess (axisRead P))
          (pairState setting) hProbability (pairState_norm setting))

/-- The diagonal-diagonal branch rejection is bounded by the independently
evaluated diagonal coefficient defect plus `md / q`. -/
theorem dline_dline_rejection_le_diagonalParameterEvaluatedCoefficientDefect_add
    (lines : ExtendedLinesWitness setting points deltaL) :
    @LE.le Real Real.instLE
      (directLdBranchRejectionProbability P.extendedDirectLd (strategy lines)
        (.dline, .dline))
      (diagonalParameterEvaluatedCoefficientDefect lines +
        (P.extendedDirectLd.m * P.extendedDirectLd.d : Real) /
          (P.extendedDirectLd.q : Real)) := by
  rw [dline_dline_rejection_eq_diagonalCoefficientAnswerDefect]
  calc
    diagonalCoefficientAnswerDefect lines <=
        consistencyDefect ((directDLinePointDist P.extendedDirectLd).map Prod.fst)
          (fun line coefficients => heteroKron
            (((lines.Qline .alice line).postprocess (diagonalRead P)).effect coefficients) 1)
          (fun line coefficients => heteroKron 1
            (((lines.Qline .bob line).postprocess (diagonalRead P)).effect coefficients))
          (pairState setting) := diagonalCoefficientAnswerDefect_le_raw lines
    _ <= _ := by
      have hProbability :
          ((directDLinePointDist P.extendedDirectLd).map Prod.fst).IsProbability :=
        (directDLinePointDist_isProbability P.extendedDirectLd).map _
      simpa [diagonalParameterEvaluatedCoefficientDefect] using
        (consistencyDefect_directCoefficients_le_evaluated_add
          P.extendedDirectLd (P.extendedDirectLd.m * P.extendedDirectLd.d)
          ((directDLinePointDist P.extendedDirectLd).map Prod.fst)
          (fun line => (lines.Qline .alice line).postprocess (diagonalRead P))
          (fun line => (lines.Qline .bob line).postprocess (diagonalRead P))
          (pairState setting) hProbability (pairState_norm setting))

end ExtendedLineGame

end

end MIPStarRE.QPBT
