import MIPStarRE.QPBT.Combining.ExtendedLineGame.StateTransport

/-!
# Nonnegativity of combining-witness errors

This module derives nonnegativity of the error parameters supplied with the
combined point and extended line witnesses.  The point conclusion follows from
nonnegativity of state-dependent squared distance.  The line conclusion uses
the genuine bipartite POVMs underlying the completed line-point defect.

## References

- `references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:689-709`
- `references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1279-1288`
- Blueprint `lem:qld-4-10` and `lem:qld-4-7`.
- Issue #335.
-/

open scoped BigOperators MatrixOrder ComplexOrder

set_option synthInstance.maxSize 400

namespace MIPStarRE.QPBT

open MIPStarRE.LDT hiding Measurement
open MIPStarRE.Quantum

noncomputable section

/-- The error parameter of a supplied combined-point witness is nonnegative. -/
theorem CombinedPointsWitness.delta_nonneg {P : AdmissibleParams} {epsilon deltaQ : ℝ}
    {setting : ProjectiveSetting P epsilon}
    (points : CombinedPointsWitness setting deltaQ) :
    0 ≤ deltaQ := by
  exact le_trans
    (DistanceCalculus.opFamilyDistSq_nonneg
      (uniformDistribution
        ((Fin P.m → PauliScalar P) × (Fin P.m → PauliScalar P)))
      (fun xz ab => setting.place .AA' ((points.Q .alice xz.1 xz.2).effect ab))
      (fun xz ab => setting.place .BA'' ((points.Q .bob xz.1 xz.2).effect ab))
      setting.psiHat)
    (points.self_consistent .AA' .BA'' trivial)

namespace ExtendedLineGame

variable {P : AdmissibleParams} {epsilon deltaQ deltaL : ℝ}
variable {setting : ProjectiveSetting P epsilon}
variable {points : CombinedPointsWitness setting deltaQ}

/-- The completed `AA'`--`BA''` line-point defect is nonnegative because its
correlation terms are those of genuine POVMs on `pairState setting`. -/
theorem completedLinePointDefect_aaBa_nonneg
    (lines : ExtendedLinesWitness setting points deltaL)
    (mu : Distribution
      (DirectLineDesc P.extendedDirectLd ×
        (Fin P.extendedDirectLd.m → DirectScalarQ P.extendedDirectLd))) :
    0 ≤ completedLinePointDefect lines .AA' .BA'' mu := by
  let lineMeasurement :
      (DirectLineDesc P.extendedDirectLd ×
        (Fin P.extendedDirectLd.m → DirectScalarQ P.extendedDirectLd)) →
        Measurement (Option (PauliScalar P)) (setting.ExpandedLocalSpace .alice) :=
    fun sample =>
      (lines.Qline .alice sample.1).postprocess
        (fun coeffs => (directEvalOpt sample.1 sample.2 coeffs).map
          (extendedDirectScalarEquiv P))
  let pointMeasurement :
      (DirectLineDesc P.extendedDirectLd ×
        (Fin P.extendedDirectLd.m → DirectScalarQ P.extendedDirectLd)) →
        Measurement (Option (PauliScalar P)) (setting.ExpandedLocalSpace .bob) :=
    fun sample =>
      (points.Q .bob
        (projX (directPointToPauli P sample.2))
        (projZ (directPointToPauli P sample.2))).postprocess fun values =>
          some (directPointToPauli P sample.2 (alphaVar P.m) * values.1 +
            directPointToPauli P sample.2 (betaVar P.m) * values.2)
  change 0 ≤ consistencyDefect mu
    (fun sample answer => setting.place .AA' ((lineMeasurement sample).effect answer))
    (fun sample answer => setting.place .BA'' ((pointMeasurement sample).effect answer))
    setting.psiHat
  unfold consistencyDefect avgOver
  refine Finset.sum_nonneg fun sample _ =>
    mul_nonneg (mu.nonnegative sample) ?_
  refine Finset.sum_nonneg fun answerA _ => ?_
  refine Finset.sum_nonneg fun answerB _ => ?_
  by_cases hab : answerA = answerB
  · simp [hab]
  · simp only [hab, if_false, DistanceCalculus.consistency_term_eq_stateQForm]
    rw [← stateQForm_pairState_eq_AA'_BA'' setting
      ((lineMeasurement sample).effect answerA)
      ((pointMeasurement sample).effect answerB)
      (Matrix.nonneg_iff_posSemidef.mp
        ((lineMeasurement sample).pos answerA)).isHermitian
      (Matrix.nonneg_iff_posSemidef.mp
        ((pointMeasurement sample).pos answerB)).isHermitian]
    exact DistanceCalculus.stateQForm_nonneg (pairState setting)
      (MIPStarRE.Quantum.kronecker_nonneg
        ((lineMeasurement sample).pos answerA)
        ((pointMeasurement sample).pos answerB))

end ExtendedLineGame

/-- The error parameter of a supplied extended-line witness is nonnegative. -/
theorem ExtendedLinesWitness.delta_nonneg {P : AdmissibleParams}
    {epsilon deltaQ deltaL : ℝ} {setting : ProjectiveSetting P epsilon}
    {points : CombinedPointsWitness setting deltaQ}
    (lines : ExtendedLinesWitness setting points deltaL) :
    0 ≤ deltaL := by
  exact le_trans
    (ExtendedLineGame.completedLinePointDefect_aaBa_nonneg lines
      (directLinePointDist P.extendedDirectLd))
    lines.consistent_alice

end

end MIPStarRE.QPBT
