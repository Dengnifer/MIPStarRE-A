import MIPStarRE.QPBT.Observables.LineDefs
import MIPStarRE.QPBT.Algebra.Coefficients

/-!
# Collision bounds for coefficient polynomials

This module retains the line-collision import path and the coefficient-list
evaluation identity. The root-count bound `evalCoefficient_collision_card_le`
is supplied by the shared coefficient-polynomial module.

## References

The lemmas support the Schwartz-Zippel step in `lem:qld-xz-lines`,
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:950-955`.
-/

namespace MIPStarRE.QPBT

/-- The Mathlib polynomial associated to a coefficient tuple has the specified
evaluation. This formalization-only identity connects the coefficient
convention to the root bound used at paper
`14_analysis_of_the_pauli_basis_test.tex:955`. -/
theorem polynomial_ofFn_eval_eq_evalCoefficient {K : Type*} [CommSemiring K]
    [DecidableEq K] {size : ℕ} (coeffs : Fin size -> K) (param : K) :
    (Polynomial.ofFn size coeffs).eval param = evalCoefficient coeffs param := by
  simp [Polynomial.ofFn_eq_sum_monomial, Polynomial.eval_finsetSum,
    Polynomial.eval_monomial, evalCoefficient]

end MIPStarRE.QPBT
