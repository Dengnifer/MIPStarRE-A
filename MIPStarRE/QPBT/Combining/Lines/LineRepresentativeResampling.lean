import MIPStarRE.QPBT.Combining.Lines.SubLineUniform
import MIPStarRE.QPBT.Combining.Lines.RestrictedAverage

/-!
# Resampling a Uniform Point Along Its Canonical Line

This module records the finite-average form of the canonical line
parameterization. A uniformly random point can be replaced by its canonical
line representative together with a fresh uniform affine parameter, while the
representative remains part of the sampled value.

## References

This formalization-only identity supports the conditional sampling step in
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:950-963`.
-/

namespace MIPStarRE.QPBT

open MIPStarRE.LDT

noncomputable section

/-- A uniform point may be replaced by a uniform affine parameter on its
canonical line, while preserving the canonical representative jointly with the
point. This formalization-only identity includes zero directions and supports
the conditional sampling step at paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:955`. -/
theorem avgOver_lineRepMap_resample_parameter {K : Type*} [Field K]
    [Fintype K] [DecidableEq K] {dimension : ℕ}
    (direction : Fin dimension → K)
    (value : (Fin dimension → K) → (Fin dimension → K) → ℝ) :
    avgOver (uniformDistribution (Fin dimension → K))
      (fun point => value (lineRepMap direction point) point) =
    avgOver (uniformDistribution (Fin dimension → K)) (fun point =>
      avgOver (uniformDistribution K) (fun param =>
        value (lineRepMap direction point)
          (lineRepMap direction point + param • direction))) := by
  have hmap := uniformDistribution_map_lineRepMap_add_smul direction
  have havg := congrArg (fun dist => avgOver dist
    (fun point => value (lineRepMap direction point) point)) hmap
  rw [Distribution.avgOver_map, uniformDistribution_prod, avgOver_prod] at havg
  simpa only [lineRepMap_add_smul, lineRepMap_apply_self] using havg.symm

end

end MIPStarRE.QPBT
