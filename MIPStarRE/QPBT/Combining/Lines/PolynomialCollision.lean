import MIPStarRE.QPBT.Observables.LineDefs
import Mathlib.Algebra.Polynomial.OfFn
import Mathlib.Algebra.Polynomial.Roots

/-!
# Collision bounds for coefficient polynomials

This module identifies coefficient-list evaluation with Mathlib polynomial
evaluation and derives the finite root-count bound for distinct line
polynomials.

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

/-- Distinct coefficient polynomials of degree at most `bound` agree at no
more than `bound` field elements. This is the univariate root bound underlying
the Schwartz-Zippel step at paper
`14_analysis_of_the_pauli_basis_test.tex:955`. No restriction of the degree
relative to the field size is required. -/
theorem evalCoefficient_collision_card_le {L : LdParams} {bound : ℕ}
    (first second : DegPoly L bound) (hne : first ≠ second) :
    (Finset.univ.filter fun param => evalCoefficient first param =
      evalCoefficient second param).card ≤ bound := by
  classical
  by_contra hcard
  have hdeg (poly : DegPoly L bound) :
      (Polynomial.ofFn (bound + 1) poly).natDegree ≤ bound :=
    Nat.lt_succ_iff.mp (Polynomial.ofFn_natDegree_lt (by omega) poly)
  have heq := Polynomial.eq_of_natDegree_lt_card_of_eval_eq
    (Polynomial.ofFn (bound + 1) first)
    (Polynomial.ofFn (bound + 1) second)
    (f := fun param : {param : ScalarQ L // evalCoefficient first param =
      evalCoefficient second param} => param.val)
    Subtype.val_injective
    (fun param => by
      simpa only [polynomial_ofFn_eval_eq_evalCoefficient] using param.property)
    (by
      simpa only [Fintype.card_subtype] using
        lt_of_le_of_lt (max_le (hdeg first) (hdeg second))
          (Nat.lt_of_not_ge hcard))
  exact hne (Polynomial.injective_ofFn _ heq)

end MIPStarRE.QPBT
