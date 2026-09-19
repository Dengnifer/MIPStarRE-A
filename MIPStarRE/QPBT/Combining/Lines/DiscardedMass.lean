import MIPStarRE.QPBT.Combining.Lines.ZeroDirectionMass
import MIPStarRE.QPBT.Combining.Lines.DiagonalResampling

/-! # Discarded zero-direction mass

## References

Paper `lem:qld-xz-lines`, lines 950--963.
-/

namespace MIPStarRE.QPBT
open MIPStarRE.LDT
noncomputable section

/-- Under the unchanged diagonal line-point law, zero projected directions have
probability at most the inverse field size: the final unprojected direction coordinate must
vanish and is uniform. Source: `def:line-point-dist`, paper
`08_classical_and_quantum_low_degree_tests.tex:274-287`. This formalization-only bound
supports the collision restriction used in the paired-line construction. -/
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
mass at most `1 / (2q)`. This formalization-only estimate preserves the source sampler of
`def:line-point-dist`, paper `08_classical_and_quantum_low_degree_tests.tex:274-287`,
including its degenerate fibers. -/
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

/-- Nonzero directions have mass at least three quarters under the unchanged
line-point law. This formalization-only consequence of the discarded-mass bound
supports the conditioning in paper `lem:qld-xz-lines`,
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:950-963`.
Blueprint `lem:qld-nondegenerate-line-mass`. The original public statement from
`Lines/Sampling.lean` is preserved here; see the 2026-09-15 supplement to
`audits/2026-09-12_issue512-saved-proof-recovery.md`. -/
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
X-outer sandwich is instantiated with `G2 = X`. This is a formalization-only bound for
paper `14_analysis_of_the_pauli_basis_test.tex:943-963`. -/
theorem prod_linePointDist_zero_X_direction_mass_le (L : LdParams) :
    avgOver (Distribution.prod (linePointDist L) (linePointDist L))
      (fun samples => if samples.1.1.direction = 0 then 1 else 0) ≤
      1 / (2 * Fintype.card (ScalarQ L)) := by
  rw [SandwichProduct.avgOver_distribution_prod]
  change avgOver (linePointDist L) (fun sample => avgOver (linePointDist L)
    (fun _ => if sample.1.direction = 0 then 1 else 0)) ≤ _
  simp_rw [avgOver_const_of_isProbability _ (linePointDist_isProbability L)]
  exact linePointDist_zero_direction_mass_le L


end
end MIPStarRE.QPBT
