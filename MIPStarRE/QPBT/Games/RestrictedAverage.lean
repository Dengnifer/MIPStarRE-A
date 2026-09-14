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

/-- Multiplying a normalized restricted average by its retained mass gives the
unnormalized restricted sum. This formalization-only identity supports
proof-only conditioning in `lem:qld-xz-lines`, paper
`14_analysis_of_the_pauli_basis_test.tex:950-963`; it changes no game distribution. -/
theorem avgOver_restrict_mul_mass {Sample : Type*} [DecidableEq Sample]
    (dist : Distribution Sample) (good : Sample -> Prop) [DecidablePred good]
    (hpos : 0 < ∑ sample ∈ dist.support.filter good, dist.weight sample)
    (value : Sample -> ℝ) :
    (∑ sample ∈ dist.support.filter good, dist.weight sample) *
      avgOver (Distribution.restrict dist good hpos) value =
      ∑ sample ∈ dist.support.filter good, dist.weight sample * value sample := by
  unfold avgOver Distribution.restrict
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro sample hsample
  simp only [if_pos (Finset.mem_filter.mp hsample).2]
  field_simp

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
  apply (le_div_iff₀ hpos).mpr
  rw [mul_comm, avgOver_restrict_mul_mass]
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
    (fun sample _ _ => mul_nonneg (dist.nonnegative sample) (hnonneg sample))

/-- An average of a function bounded above by one is at most the retained mass
times its conditional average, plus the discarded probability mass. This
formalization-only estimate restores the original distribution after proof-only
conditioning in `lem:qld-xz-lines`, paper
`14_analysis_of_the_pauli_basis_test.tex:950-963`. No discarded mass is omitted. -/
theorem avgOver_le_restrict_add_discarded_mass {Sample : Type*} [DecidableEq Sample]
    (dist : Distribution Sample) (good : Sample -> Prop) [DecidablePred good]
    (hpos : 0 < ∑ sample ∈ dist.support.filter good, dist.weight sample)
    (value : Sample -> ℝ) (hunit : ∀ sample, value sample ≤ 1) :
    avgOver dist value ≤
      (∑ sample ∈ dist.support.filter good, dist.weight sample) *
        avgOver (Distribution.restrict dist good hpos) value +
      ∑ sample ∈ dist.support.filter (fun sample => ¬ good sample), dist.weight sample := by
  classical
  rw [avgOver_restrict_mul_mass]
  unfold avgOver
  rw [← Finset.sum_filter_add_sum_filter_not dist.support good
    (fun sample => dist.weight sample * value sample)]
  exact add_le_add_right (Finset.sum_le_sum fun sample _ =>
    mul_le_of_le_one_right (dist.nonnegative sample) (hunit sample)) _

end MIPStarRE.QPBT
