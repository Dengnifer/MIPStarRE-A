import MIPStarRE.QPBT.Combining.Lines.DiagonalResampling
import MIPStarRE.QPBT.Combining.Lines.SubLineMixture
import MIPStarRE.QPBT.Combining.Points
import MIPStarRE.QPBT.Combining.Lines.PointwiseDefect
import MIPStarRE.QPBT.Combining.Lines.WeightedCollision
import MIPStarRE.QPBT.Combining.Lines.ZeroDirectionMass
import MIPStarRE.QPBT.Games.RestrictedAverage

/-!
# Sampling for conditioned line pasting

The sampling identities retain the zero-direction mass when restoring the
original line-point law.

## References

Paper `references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:882-963`,
blueprint `lem:qld-xz-lines`. The source and completed-answer distinctions are
documented in `docs/paper-gaps/qpbt_combined-lines-error-term.tex`.
-/

namespace MIPStarRE.QPBT

open MIPStarRE.LDT hiding Measurement
open MIPStarRE.Quantum MIPStarRE.QPBT.DistanceCalculus
open scoped BigOperators Matrix MatrixOrder ComplexOrder

noncomputable section

/-- Under the unchanged diagonal line-point law, zero projected directions have
probability at most the inverse field size: the last sampled direction coordinate must
vanish and is uniform. Source: `def:line-point-dist`, paper
`08_classical_and_quantum_low_degree_tests.tex:274-287`. This formalization-only
auxiliary bound supports the collision restriction used for `lem:qld-xz-lines`. -/
theorem dLinePointDist_zero_direction_mass_le (L : LdParams) :
    avgOver (dLinePointDist L) (fun sample =>
      if sample.1.direction = 0 then 1 else 0) ≤
      1 / Fintype.card (ScalarQ L) := by
  classical
  let last : Fin L.m := ⟨L.m - 1, by have := L.hm; omega⟩
  let coord : LdIndex L := .inr last
  have hmap : (uniformDistribution (LdSpace L)).map (fun raw => raw coord) =
      uniformDistribution (ScalarQ L) := by
    change (uniformDistribution (LdSpace L)).map
      (fun raw => (Equiv.funSplitAt coord (ScalarQ L) raw).1) = _
    rw [← Distribution.map_map, uniformDistribution_map_equiv,
      uniformDistribution_map_fst]
  have hzero : avgOver (uniformDistribution (LdSpace L))
      (fun raw => if raw coord = 0 then (1 : ℝ) else 0) =
      1 / Fintype.card (ScalarQ L) := by
    rw [← Distribution.avgOver_map (uniformDistribution (LdSpace L))
      (fun raw => raw coord) (fun value => if value = 0 then (1 : ℝ) else 0), hmap]
    simp [avgOver, uniformDistribution_weight_apply, mul_ite]
  unfold dLinePointDist clDistribution
  rw [Distribution.avgOver_map, Distribution.avgOver_map]
  refine le_trans (avgOver_mono _ _ _ ?_) hzero.le
  intro raw
  dsimp only
  rw [dLineDescOf_ldDLineCL]
  split_ifs with hdir hcoord hcoord
  · exact le_rfl
  · exfalso
    apply hcoord
    have hlast := congrFun hdir last
    change prefixProjection (chiIndex L (LdSpace.seed raw))
      (LdSpace.direction raw) last = 0 at hlast
    have hindex : ¬ last.val < (chiIndex L (LdSpace.seed raw)).val := by
      have := (chiIndex L (LdSpace.seed raw)).isLt
      dsimp [last]
      omega
    simpa [prefixProjection, hindex, LdSpace.direction, coord] using hlast
  · norm_num
  · exact le_rfl

/-- The equal mixture of axis and diagonal line-point laws gives zero directions
mass at most `1 / (2q)`. This formalization-only auxiliary estimate preserves the
sampler of `def:line-point-dist`, paper
`08_classical_and_quantum_low_degree_tests.tex:274-287`, including its degenerate
fibers. -/
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

/-- A uniform point may be replaced by a uniform affine parameter on its
canonical line, while preserving the canonical representative jointly with the
point. This formalization-only identity, including zero directions, supports the
conditional sampling step at paper `14_analysis_of_the_pauli_basis_test.tex:955`. -/
theorem avgOver_lineRepMap_resample_parameter {K : Type*} [Field K] [Fintype K] [DecidableEq K]
    {dimension : ℕ} (direction : Fin dimension → K)
    (value : (Fin dimension → K) → (Fin dimension → K) → ℝ) :
    avgOver (uniformDistribution (Fin dimension → K))
      (fun point => value (lineRepMap direction point) point) =
    avgOver (uniformDistribution (Fin dimension → K)) (fun point =>
      avgOver (uniformDistribution K) (fun param =>
        value (lineRepMap direction point) (lineRepMap direction point + param • direction))) := by
  have hmap := uniformDistribution_map_lineRepMap_add_smul direction
  have havg := congrArg (fun dist => avgOver dist
    (fun point => value (lineRepMap direction point) point)) hmap
  rw [Distribution.avgOver_map, uniformDistribution_prod, avgOver_prod] at havg
  simpa only [lineRepMap_add_smul, lineRepMap_apply_self] using havg.symm

/-- Nondegenerate line fibers have total mass at least three quarters in the
unchanged line-point law. This follows from the zero-direction mass bound and
the fact that a field has at least two elements. This formalization-only auxiliary
positivity bound supports the conditioning at paper
`14_analysis_of_the_pauli_basis_test.tex:950-963`. -/
theorem linePointDist_nondegenerate_mass_ge (L : LdParams) :
    (3 / 4 : ℝ) ≤ ∑ sample ∈ (linePointDist L).support.filter
      (fun sample => sample.1.direction ≠ 0), (linePointDist L).weight sample := by
  classical
  have hsplit : (∑ sample ∈ (linePointDist L).support.filter
        (fun sample => sample.1.direction ≠ 0), (linePointDist L).weight sample) +
      avgOver (linePointDist L) (fun sample => if sample.1.direction = 0 then 1 else 0) = 1 := by
    simp only [avgOver, mul_ite, mul_one, mul_zero, ← Finset.sum_filter]
    rw [add_comm, Finset.sum_filter_add_sum_filter_not]
    exact (linePointDist_isProbability L).weight_sum_eq_one
  have hmass := linePointDist_zero_direction_mass_le L
  have hcard : (2 : ℝ) ≤ Fintype.card (ScalarQ L) := by
    exact_mod_cast Fintype.one_lt_card (α := ScalarQ L)
  have hquarter : 1 / (2 * (Fintype.card (ScalarQ L) : ℝ)) ≤ 1 / 4 := by
    apply one_div_le_one_div_of_le (by norm_num)
    linarith
  linarith

/-- For two independent line-point samples, excluding only zero X directions
costs at most `1 / (2q)`. Only X requires the collision estimate when the
X-outer sandwich is instantiated with `G2 = X`. This formalization-only auxiliary
bound supports the pasting calculation at paper
`14_analysis_of_the_pauli_basis_test.tex:943-963`. -/
theorem prod_linePointDist_zero_X_direction_mass_le (L : LdParams) :
    avgOver (Distribution.prod (linePointDist L) (linePointDist L))
      (fun samples => if samples.1.1.direction = 0 then 1 else 0) ≤
      1 / (2 * Fintype.card (ScalarQ L)) := by
  rw [avgOver_prod]
  change avgOver (linePointDist L) (fun sample => avgOver (linePointDist L)
    (fun _ => if sample.1.direction = 0 then 1 else 0)) ≤ _
  simp_rw [avgOver_const_of_isProbability _ (linePointDist_isProbability L)]
  exact linePointDist_zero_direction_mass_le L


end

end MIPStarRE.QPBT
