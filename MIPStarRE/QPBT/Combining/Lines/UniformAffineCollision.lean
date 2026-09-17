import MIPStarRE.QPBT.Algebra.Coefficients
import MIPStarRE.QPBT.Combining.Lines.AffineEvaluation

/-!
# Uniform collision bounds on nondegenerate affine lines

This module combines uniqueness of affine evaluation with the univariate
root-count bound to control collisions under a uniform line parameter.

## References

The result is the Schwartz--Zippel step in `lem:qld-xz-lines`,
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:950-955`.
-/

namespace MIPStarRE.QPBT

open MIPStarRE.LDT MIPStarRE.Quantum

noncomputable section

/-- On a nondegenerate line, completed evaluations of distinct degree-bounded
polynomials collide with probability at most the degree bound divided by the
field size under a uniform affine parameter. -/
theorem evalOpt_uniform_parameter_collision_le {L : LdParams} {bound : ℕ}
    (line : LineDesc L) (hdir : line.direction ≠ 0)
    (first second : DegPoly L bound) (hne : first ≠ second) :
    avgOver (uniformDistribution (ScalarQ L)) (fun param =>
      if evalOpt line (line.base + param • line.direction) first =
        evalOpt line (line.base + param • line.direction) second then 1 else 0) ≤
      (bound : ℝ) / Fintype.card (ScalarQ L) := by
  classical
  simp_rw [evalOpt_affine_parameter_of_direction_ne_zero line hdir,
    Option.some.injEq]
  have hcard := evalCoefficient_collision_card_le first second hne
  unfold avgOver
  simp only [uniformDistribution_support, uniformDistribution_weight_apply,
    mul_ite, mul_one, mul_zero, ← Finset.sum_filter]
  rw [Finset.sum_const, nsmul_eq_mul, mul_one_div]
  exact div_le_div_of_nonneg_right (by exact_mod_cast hcard) (by positivity)

end

end MIPStarRE.QPBT
