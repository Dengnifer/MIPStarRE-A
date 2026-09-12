import MIPStarRE.QPBT.Combining.Lines.CombinedMeasurement

/-!
# Marginal of the combined line measurement

This module records the exact X marginal of the X-Z-X sandwich measurement.

## References

The construction is the paired-line measurement in `lem:qld-xz-lines`, paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:942-963`.
-/

namespace MIPStarRE.QPBT

open MIPStarRE.LDT MIPStarRE.Quantum

noncomputable section

/-- Formalization-only constructor identity: summing out the Z outcome from
the X-outer sandwich recovers the X line effect exactly. This uses completeness
of the Z measurement and projectivity of the outer X effect, as in the POVM
construction at paper `14_analysis_of_the_pauli_basis_test.tex:942-963`. -/
theorem ProjectiveSetting.combinedLineMeasurement_sum_Z
    {P : AdmissibleParams} {ε : ℝ} (S : ProjectiveSetting P ε) (side : PlayerSide)
    (lineX lineZ : LineDesc P.toLdParams)
    (fX : DegPoly P.toLdParams (P.m * P.d)) :
    ∑ fZ, (S.combinedLineMeasurement side lineX lineZ).effect (fX, fZ) =
      (S.lineMeasExp side .X lineX).effect fX := by
  simp only [S.combinedLineMeasurement_effect, ← Finset.sum_mul, ← Finset.mul_sum,
    (S.lineMeasExp side .Z lineZ).sum_eq_one, mul_one]
  exact (S.lineMeasExp_isProjective side .X lineX fX).1

end

end MIPStarRE.QPBT
