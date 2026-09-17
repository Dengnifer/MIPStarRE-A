import MIPStarRE.QPBT.Observables.WinImplications.LowDegree

/-!
# Evaluation on a nondegenerate affine line

This module identifies completed line-polynomial evaluation with evaluation at
the unique affine parameter of a point on a line with nonzero direction.

## References

The result is the geometric step in the collision argument at
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:950-955`.
-/

namespace MIPStarRE.QPBT

open MIPStarRE.LDT MIPStarRE.Quantum

noncomputable section

/-- On a nonzero direction, completed evaluation agrees with polynomial
evaluation at the unique affine parameter. -/
theorem evalOpt_affine_parameter_of_direction_ne_zero {L : LdParams}
    {bound : ℕ} (line : LineDesc L) (hdir : line.direction ≠ 0)
    (poly : DegPoly L bound) (param : ScalarQ L) :
    evalOpt line (line.base + param • line.direction) poly =
      some (evalCoefficient poly param) := by
  apply WinImplications.evalOpt_eq_some_of_evaluatesTo
  refine ⟨⟨param, rfl⟩, ?_⟩
  intro other heq
  have hsmul : param • line.direction = other • line.direction :=
    add_left_cancel heq
  have hsub : (param - other) • line.direction = 0 := by
    rw [sub_smul, hsmul, sub_self]
  have hparam : param = other :=
    sub_eq_zero.mp ((smul_eq_zero.mp hsub).resolve_right hdir)
  rw [hparam]

end

end MIPStarRE.QPBT
