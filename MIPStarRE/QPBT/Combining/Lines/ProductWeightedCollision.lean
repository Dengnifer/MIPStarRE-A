import MIPStarRE.QPBT.Combining.Lines.RestrictedAverage
import MIPStarRE.QPBT.Combining.Lines.WeightedCollision

/-!
# Product-distribution weighted collision bounds

This module lifts the nondegenerate weighted collision estimate for one
line-point sample to two independent samples. The nonnegative weight may
depend on the complete second sample and on the first sampled line.

## References

This is formalization-only conditioning support for `lem:qld-xz-lines`, paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:950-955`, using
the collision hypothesis of `lem:pasting` at
`references/qpbt-paper/06_nonlocal_games_and_mipstar.tex:504-525`.
-/

namespace MIPStarRE.QPBT

open MIPStarRE.LDT

noncomputable section

/-- Independent sampling of a second line-point pair preserves the weighted
collision estimate on nonzero first directions. The weight may depend on the
complete second sample, but on the first sample only through its line. No
condition is imposed on the second direction. -/
theorem prod_linePointDist_nondegenerate_weighted_collision_le
    {L : LdParams} {bound : ℕ}
    (weight : LineDesc L → (LineDesc L × (Fin L.m → ScalarQ L)) → ℝ)
    (hweight : ∀ line sample, 0 ≤ weight line sample)
    (first second : DegPoly L bound) (hne : first ≠ second) :
    avgOver (Distribution.prod (linePointDist L) (linePointDist L)) (fun samples =>
      if samples.1.1.direction ≠ 0 then weight samples.1.1 samples.2 *
        (if evalOpt samples.1.1 samples.1.2 first =
          evalOpt samples.1.1 samples.1.2 second then 1 else 0) else 0) ≤
    (bound : ℝ) / Fintype.card (ScalarQ L) *
      avgOver (Distribution.prod (linePointDist L) (linePointDist L)) (fun samples =>
        if samples.1.1.direction ≠ 0 then weight samples.1.1 samples.2 else 0) := by
  classical
  simp only [avgOver_prod]
  rw [avgOver_comm, avgOver_comm (linePointDist L) (linePointDist L)
    (fun firstSample secondSample =>
      if firstSample.1.direction ≠ 0 then weight firstSample.1 secondSample else 0)]
  rw [← avgOver_const_mul]
  apply avgOver_mono
  intro sample
  exact linePointDist_nondegenerate_weighted_collision_le
    (fun line => weight line sample) (fun line => hweight line sample)
    first second hne

end

end MIPStarRE.QPBT
