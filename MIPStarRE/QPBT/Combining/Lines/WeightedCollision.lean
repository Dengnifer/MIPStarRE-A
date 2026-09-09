import MIPStarRE.QPBT.Combining.Lines.MixedResampling
import MIPStarRE.QPBT.Combining.Lines.UniformAffineCollision

/-!
# Weighted collision bounds for sampled lines

This module lifts the uniform affine-parameter collision estimate to the mixed
line-point distribution with an arbitrary nonnegative weight depending only on
the sampled line.

## References

The estimate is the Schwartz--Zippel step in `lem:qld-xz-lines`,
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:950-955`.
-/

namespace MIPStarRE.QPBT

open MIPStarRE.LDT

noncomputable section

/-- The collision bound remains valid with any nonnegative weight depending
only on the line, after restricting to nonzero directions. This proof-only
estimate is the conditional form of the root argument in `lem:qld-xz-lines`,
paper lines 950--955; it does not assert the false unrestricted collision bound
on zero-direction coefficient presentations. -/
theorem linePointDist_nondegenerate_weighted_collision_le {L : LdParams}
    {bound : ℕ} (weight : LineDesc L → ℝ)
    (hweight : ∀ line, 0 ≤ weight line) (first second : DegPoly L bound)
    (hne : first ≠ second) :
    avgOver (linePointDist L) (fun sample =>
      if sample.1.direction ≠ 0 then weight sample.1 *
        (if evalOpt sample.1 sample.2 first = evalOpt sample.1 sample.2 second
          then 1 else 0) else 0) ≤
      (bound : ℝ) / Fintype.card (ScalarQ L) *
        avgOver (linePointDist L) (fun sample =>
          if sample.1.direction ≠ 0 then weight sample.1 else 0) := by
  classical
  rw [avgOver_linePointDist_resample_parameter]
  rw [← avgOver_const_mul]
  apply avgOver_mono
  intro sample
  by_cases hdir : sample.1.direction ≠ 0
  · simp only [if_pos hdir]
    rw [avgOver_const_mul]
    exact (mul_le_mul_of_nonneg_left
      (evalOpt_uniform_parameter_collision_le sample.1 hdir first second hne)
      (hweight sample.1)).trans_eq
      (mul_comm _ _)
  · simp [hdir, avgOver]

end

end MIPStarRE.QPBT
