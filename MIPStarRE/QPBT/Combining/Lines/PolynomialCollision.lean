import MIPStarRE.QPBT.Observables.LineDefs
import Mathlib.Algebra.Polynomial.OfFn
import Mathlib.Algebra.Polynomial.Roots

/-!
# Collision bounds for coefficient polynomials

This module identifies coefficient-list evaluation with Mathlib polynomial
evaluation. The root-count bound `evalCoefficient_collision_card_le` is
imported from `Algebra.Coefficients`, where it is stated for finite integral
domains and therefore applies to the scalar field of every line descriptor.

## References

The lemmas support the Schwartz-Zippel step in `lem:qld-xz-lines`,
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:950-955`.
-/

namespace MIPStarRE.QPBT

open MIPStarRE.LDT

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
