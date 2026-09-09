import MIPStarRE.QPBT.Combining.Lines.RestrictedAverage
import MIPStarRE.QPBT.Combining.Lines.SubLineUniform

/-!
# Axis line-point parameter resampling

This module records that a uniformly sampled point on an axis-parallel line
may be resampled by an independent uniform affine parameter without changing
the joint line-point expectation.

## References

The resampling is used at
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:955`; the
axis line-point law is `def:line-point-dist` at
`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:274-287`.
-/

namespace MIPStarRE.QPBT

open MIPStarRE.LDT

noncomputable section

/-- Resampling a uniform affine parameter on the sampled axis line preserves
the joint axis line-point law. This is the axis case of the conditional
sampling used at paper line 955. -/
theorem avgOver_aLinePointDist_resample_parameter (L : LdParams)
    (value : (LineDesc L × (Fin L.m → ScalarQ L)) → ℝ) :
    avgOver (aLinePointDist L) value =
    avgOver (aLinePointDist L) (fun sample =>
      avgOver (uniformDistribution (ScalarQ L)) (fun param =>
        value (sample.1, sample.1.base + param • sample.1.direction))) := by
  classical
  unfold aLinePointDist clDistribution
  simp only [Distribution.avgOver_map, aLineDescOf_ldALineCL]
  have hblock := uniformDistribution_map_equiv (ldSpaceBlockEquiv L).symm
  rw [← hblock]
  simp only [Distribution.avgOver_map]
  rw [uniformDistribution_prod]
  simp only [SandwichProduct.avgOver_distribution_prod]
  rw [avgOver_comm, avgOver_comm (uniformDistribution (Fin L.m → ScalarQ L))]
  apply congrArg
  funext block
  have hresample (direction : Fin L.m → ScalarQ L)
      (lineValue : (Fin L.m → ScalarQ L) → (Fin L.m → ScalarQ L) → ℝ) :
      avgOver (uniformDistribution (Fin L.m → ScalarQ L))
          (fun point => lineValue (lineRepMap direction point) point) =
        avgOver (uniformDistribution (Fin L.m → ScalarQ L)) (fun point =>
          avgOver (uniformDistribution (ScalarQ L)) (fun param =>
            lineValue (lineRepMap direction point)
              (lineRepMap direction point + param • direction))) := by
    have hmap := uniformDistribution_map_lineRepMap_add_smul direction
    have havg := congrArg (fun dist => avgOver dist
      (fun point => lineValue (lineRepMap direction point) point)) hmap
    rw [Distribution.avgOver_map, uniformDistribution_prod,
      SandwichProduct.avgOver_distribution_prod] at havg
    simpa only [lineRepMap_add_smul, lineRepMap_apply_self] using havg.symm
  let direction : Fin L.m → ScalarQ L :=
    coordinateDirection (chiIndex L block.1)
  change avgOver (uniformDistribution (Fin L.m → ScalarQ L)) (fun point =>
      value (LineDesc.axis (lineRepMap direction point) block.1
        (lineRepMap_apply_self direction point), point)) =
    avgOver (uniformDistribution (Fin L.m → ScalarQ L)) (fun point =>
      avgOver (uniformDistribution (ScalarQ L)) (fun param =>
        value (LineDesc.axis (lineRepMap direction point) block.1
          (lineRepMap_apply_self direction point),
          lineRepMap direction point + param • direction)))
  have haxis := hresample direction
    (fun base point => value (LineDesc.axis
      (lineRepMap direction base) block.1
      (lineRepMap_apply_self _ _), point))
  simpa only [lineRepMap_apply_self] using haxis

end

end MIPStarRE.QPBT
