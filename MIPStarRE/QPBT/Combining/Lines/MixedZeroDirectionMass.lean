import MIPStarRE.QPBT.Combining.Lines.DiagonalZeroDirectionMass
import MIPStarRE.QPBT.Combining.Lines.RestrictedAverage
import MIPStarRE.QPBT.Combining.Lines.ZeroDirectionMass

/-!
# Zero-direction mass for the line-point mixture

This module combines the axis and diagonal zero-direction estimates for the
equal mixture defining the line-point sampler.

## References

The sampler is `def:line-point-dist`, from
`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:274-287`;
the proof-only conditioning context is
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:943-963`.
-/

namespace MIPStarRE.QPBT

open MIPStarRE.LDT

noncomputable section


/-- The equal mixture of axis and diagonal line-point laws gives zero directions
mass at most `1 / (2q)`. This formalization-only estimate preserves the source
sampler, including its degenerate fibers. -/
theorem linePointDist_zero_direction_mass_le (L : LdParams) :
    avgOver (linePointDist L) (fun sample =>
      if sample.1.direction = 0 then 1 else 0) ≤
      1 / (2 * Fintype.card (ScalarQ L)) := by
  rw [linePointDist, avgOver_mix, aLinePointDist_zero_direction_mass]
  have hdiag := dLinePointDist_zero_direction_mass_le L
  calc
    _ = (1 / 2 : ℝ) * avgOver (dLinePointDist L)
        (fun sample => if sample.1.direction = 0 then 1 else 0) := by ring
    _ ≤ (1 / 2 : ℝ) * (1 / Fintype.card (ScalarQ L)) :=
      mul_le_mul_of_nonneg_left hdiag (by norm_num)
    _ = _ := by rw [one_div_mul_one_div]

end

end MIPStarRE.QPBT
