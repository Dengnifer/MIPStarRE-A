import MIPStarRE.QPBT.Games.DistributionAux

/-!
# Averages over restricted finite distributions

This module records a generic comparison between a nonnegative average and
the corresponding average after conditioning on a positive-mass event.

## References

The estimate supports the proof-only conditioning step in `lem:qld-xz-lines`,
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:950-963`.
-/

open scoped BigOperators

namespace MIPStarRE.QPBT

open MIPStarRE.LDT

/-- Conditioning a nonnegative finite average inflates its bound by at most
the inverse retained mass. This is a formalization-only finite probability
estimate used in the conditioning step of `lem:qld-xz-lines`, paper
`14_analysis_of_the_pauli_basis_test.tex:950-963`. -/
theorem avgOver_restrict_le_div_mass {Sample : Type*} [DecidableEq Sample]
    (dist : Distribution Sample) (good : Sample -> Prop) [DecidablePred good]
    (hpos : 0 < ∑ sample ∈ dist.support.filter good, dist.weight sample)
    (value : Sample -> ℝ) (hnonneg : ∀ sample, 0 ≤ value sample) :
    avgOver (Distribution.restrict dist good hpos) value ≤
      avgOver dist value /
        (∑ sample ∈ dist.support.filter good, dist.weight sample) := by
  have hmul :
      (∑ sample ∈ dist.support.filter good, dist.weight sample) *
          avgOver (Distribution.restrict dist good hpos) value =
        ∑ sample ∈ dist.support.filter good,
          dist.weight sample * value sample := by
    unfold avgOver Distribution.restrict
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro sample hsample
    simp only [if_pos (Finset.mem_filter.mp hsample).2]
    field_simp
  apply (le_div_iff₀ hpos).mpr
  rw [mul_comm, hmul]
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
    (fun sample _ _ => mul_nonneg (dist.nonnegative sample) (hnonneg sample))

end MIPStarRE.QPBT
