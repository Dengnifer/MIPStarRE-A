import MIPStarRE.QPBT.Combining.ExtendedLineGame.SuppliedDirectSoundness

/-!
# Native supplied-point interface for direct soundness

This module identifies the scalar point readout in the directly indexed
low-degree strategy with the corresponding coarse-graining of the supplied
joint point measurement, on the original expanded local space.

The result is a Lean-only exact interface for the first paragraph of paper
`lem:qld-4-7`.  It does not construct the supplied witnesses or complete that
source lemma.

## References

- `references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1277-1289`
- Blueprint `lem:qld-4-7`
- Issue #362
-/

namespace MIPStarRE.QPBT

open MIPStarRE.Quantum

noncomputable section

namespace ExtendedLineGame

/-- Reading the unique coordinate of the direct-game point measurement gives
exactly the supplied joint point measurement coarse-grained by
`alpha * a + beta * b`. -/
theorem point_values_measurement_eq_suppliedQ
    {P : AdmissibleParams} {epsilon deltaQ deltaL : ℝ}
    {setting : ProjectiveSetting P epsilon}
    {points : CombinedPointsWitness setting deltaQ}
    (lines : ExtendedLinesWitness setting points deltaL)
    (side : PlayerSide)
    (u : Fin P.extendedDirectLd.m → DirectScalarQ P.extendedDirectLd) :
    ((answerMeasurement lines side
        (directLdPointQuestionOf P.extendedDirectLd u)).postprocess
      (directLdPointValuesOrZero P.extendedDirectLd)).postprocess
        (fun values =>
          extendedDirectScalarEquiv P
            (values ⟨0, by change 0 < 1; decide⟩)) =
      (points.Q side
        (projX (directPointToPauli P u))
        (projZ (directPointToPauli P u))).postprocess
          (fun ab =>
            directPointToPauli P u (alphaVar P.m) * ab.1 +
              directPointToPauli P u (betaVar P.m) * ab.2) := by
  classical
  unfold answerMeasurement directLdPointQuestionOf pointAnswer
    directLdPointValuesOrZero CombinedPointsWitness.extendedQ
  rw [Measurement.postprocess_comp, Measurement.postprocess_comp,
    Measurement.postprocess_comp]
  apply Measurement.ext
  intro outcome
  rw [Measurement.postprocess_effect, Measurement.postprocess_effect]
  apply Finset.sum_congr rfl
  intro answer _
  simp

end ExtendedLineGame

end

end MIPStarRE.QPBT
