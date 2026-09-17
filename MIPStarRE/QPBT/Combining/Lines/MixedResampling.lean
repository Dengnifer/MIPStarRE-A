import MIPStarRE.QPBT.Combining.Lines.AxisLineResampling
import MIPStarRE.QPBT.Combining.Lines.DiagonalResampling

/-!
# Mixed line-point parameter resampling

This module combines the axis and diagonal resampling identities for the equal
mixture defining the line-point distribution.

## References

The resampling supports the Schwartz-Zippel step in `lem:qld-xz-lines`,
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:950-955`. The
mixed line-point law is `def:line-point-dist` in
`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:274-287`.
-/

namespace MIPStarRE.QPBT

open MIPStarRE.LDT

noncomputable section

/-- Resampling a uniform affine parameter on a sampled line preserves the
unconditional mixed line-point law, including zero-direction diagonal fibers.
This formalization-only identity combines the axis and diagonal cases of the
conditional sampling used at paper line 955. It is recorded in blueprint
`cor:line-point-parameter-resampling`. -/
theorem avgOver_linePointDist_resample_parameter (L : LdParams)
    (value : (LineDesc L × (Fin L.m → ScalarQ L)) → ℝ) :
    avgOver (linePointDist L) value =
      avgOver (linePointDist L) (fun sample =>
        avgOver (uniformDistribution (ScalarQ L)) (fun param =>
          value (sample.1, sample.1.base + param • sample.1.direction))) := by
  rw [linePointDist, avgOver_mix, avgOver_mix]
  rw [avgOver_aLinePointDist_resample_parameter L value,
    avgOver_dLinePointDist_resample_parameter L value]

end

end MIPStarRE.QPBT
