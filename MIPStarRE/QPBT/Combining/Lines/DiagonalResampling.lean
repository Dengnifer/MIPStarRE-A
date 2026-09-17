import MIPStarRE.QPBT.Combining.Lines.RestrictedAverage
import MIPStarRE.QPBT.Combining.Lines.SubLineUniform

/-!
# Diagonal line-point parameter resampling

This module proves that a uniform affine parameter may replace the sampled
point on a diagonal line without changing the joint diagonal line-point law,
including its zero-direction fibers.

## References

The result supports the Schwartz-Zippel step in `lem:qld-xz-lines`,
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:950-955`, for
the diagonal sampler of
`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:274-287`.
-/

namespace MIPStarRE.QPBT

open MIPStarRE.LDT

noncomputable section

/-- Resampling a uniform parameter on the sampled diagonal line preserves the
joint line-point law, including the zero-direction fibers. This
formalization-only identity derives the conditional sampling used at paper
`14_analysis_of_the_pauli_basis_test.tex:955` from `def:line-point-dist`. -/
theorem avgOver_dLinePointDist_resample_parameter (L : LdParams)
    (value : (LineDesc L × (Fin L.m -> ScalarQ L)) -> ℝ) :
    avgOver (dLinePointDist L) value =
      avgOver (dLinePointDist L) (fun sample =>
        avgOver (uniformDistribution (ScalarQ L)) (fun param =>
          value (sample.1, sample.1.base + param • sample.1.direction))) := by
  classical
  unfold dLinePointDist clDistribution
  simp only [Distribution.avgOver_map, dLineDescOf_ldDLineCL]
  have hblock := uniformDistribution_map_equiv (ldSpaceBlockEquiv L).symm
  rw [← hblock]
  simp only [Distribution.avgOver_map]
  rw [uniformDistribution_prod]
  simp only [SandwichProduct.avgOver_distribution_prod]
  rw [avgOver_comm, avgOver_comm (uniformDistribution (Fin L.m -> ScalarQ L))]
  apply congrArg
  funext block
  let direction : Fin L.m -> ScalarQ L :=
    prefixProjection (chiIndex L block.1) block.2
  have hprefix : ∀ index : Fin L.m, index.val < (chiIndex L block.1).val ->
      direction index = 0 := by
    intro index hindex
    simp [direction, prefixProjection, hindex]
  change avgOver (uniformDistribution (Fin L.m -> ScalarQ L)) (fun point =>
      value (LineDesc.diagonal (lineRepMap direction point) block.1 direction
        (lineRepMap_apply_self direction point) hprefix, point)) =
    avgOver (uniformDistribution (Fin L.m -> ScalarQ L)) (fun point =>
      avgOver (uniformDistribution (ScalarQ L)) (fun param =>
        value (LineDesc.diagonal (lineRepMap direction point) block.1 direction
          (lineRepMap_apply_self direction point) hprefix,
          lineRepMap direction point + param • direction)))
  have h := avgOver_uniform_lineRepMap_resample_parameter direction
    (fun base point => value (LineDesc.diagonal
      (lineRepMap direction base) block.1 direction
      (lineRepMap_apply_self direction base) hprefix, point))
  simpa only [lineRepMap_apply_self] using h

end

end MIPStarRE.QPBT
