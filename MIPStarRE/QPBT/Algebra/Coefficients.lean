import Mathlib.Algebra.Polynomial.OfFn
import Mathlib.Algebra.Polynomial.Roots

/-!
# Coefficient polynomials and finite-field collision bounds

This module supplies the coefficient evaluation and polynomial representation
shared by the low-degree games and the combining argument. Distinct bounded
coefficient vectors agree at no more parameters than their degree bound.

## References

- Blueprint `def:ld-win-predicate` and `lem:coefficient-polynomial-agreement`.
- `references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:331-344`.
- `references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:950-955`.
-/

open scoped BigOperators

namespace MIPStarRE.QPBT

/-- Evaluation of a coefficient tuple at a field element. This is the
representative convention used by the line answers in blueprint
`def:ld-win-predicate`, paper origin
`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:31-391`.
-/
def evalCoefficient {K : Type*} [Semiring K] {n : ℕ}
    (c : Fin n → K) (t : K) : K :=
  ∑ i : Fin n, c i * t ^ i.val

/-- Interpret a bounded coefficient list as an ordinary univariate
polynomial. This helper makes the line-combination definition use Mathlib's
actual polynomial composition operation. -/
noncomputable def linePolynomialOfCoefficients {K : Type*} [Semiring K]
    {c : ℕ} (f : Fin (c + 1) → K) : Polynomial K :=
  ∑ i : Fin (c + 1), Polynomial.C (f i) * Polynomial.X ^ i.val

/-- Evaluating the polynomial represented by a coefficient list agrees with
`evalCoefficient`. -/
theorem linePolynomialOfCoefficients_eval {K : Type*} [Semiring K]
    {c : ℕ} (f : Fin (c + 1) → K) (t : K) :
    (linePolynomialOfCoefficients f).eval t = evalCoefficient f t := by
  change Polynomial.eval t
      (∑ i ∈ Finset.univ, Polynomial.C (f i) * Polynomial.X ^ i.val) =
    ∑ i ∈ Finset.univ, f i * t ^ i.val
  rw [Polynomial.eval_finsetSum]
  simp

/-- The coefficient polynomial agrees with Mathlib's coefficient-vector
construction. -/
theorem linePolynomialOfCoefficients_eq_ofFn {K : Type*} [Semiring K]
    [DecidableEq K] {c : ℕ} (f : Fin (c + 1) → K) :
    linePolynomialOfCoefficients f = Polynomial.ofFn (c + 1) f := by
  simp only [linePolynomialOfCoefficients, Polynomial.ofFn_eq_sum_monomial,
    Polynomial.C_mul_X_pow_eq_monomial]

/-- Distinct bounded coefficient vectors represent distinct polynomials. -/
theorem linePolynomialOfCoefficients_injective {K : Type*} [Semiring K] (c : ℕ) :
    Function.Injective (linePolynomialOfCoefficients (K := K) (c := c)) := by
  classical
  intro first second heq
  exact Polynomial.injective_ofFn (c + 1)
    (by simpa only [linePolynomialOfCoefficients_eq_ofFn] using heq)

/-- The polynomial of a bounded coefficient vector has degree at most `n`. -/
theorem linePolynomialOfCoefficients_natDegree_le {K : Type*} [Semiring K] {n : ℕ}
    (f : Fin (n + 1) → K) :
    (linePolynomialOfCoefficients f).natDegree ≤ n := by
  classical
  rw [linePolynomialOfCoefficients_eq_ofFn]
  exact Nat.lt_succ_iff.mp (Polynomial.ofFn_natDegree_lt (Nat.succ_pos n) f)

/-- Distinct coefficient polynomials of degree at most `bound` agree at no
more than `bound` elements of a finite integral domain. This is the univariate
root bound underlying the Schwartz-Zippel step in `lem:qld-xz-lines`, paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:955`.
No restriction of the degree relative to the field size is required. -/
theorem evalCoefficient_collision_card_le {K : Type*} [CommRing K] [IsDomain K]
    [Fintype K] [DecidableEq K] {bound : ℕ}
    (first second : Fin (bound + 1) → K) (hne : first ≠ second) :
    (Finset.univ.filter fun param => evalCoefficient first param =
      evalCoefficient second param).card ≤ bound := by
  classical
  by_contra hcard
  have heq := Polynomial.eq_of_natDegree_lt_card_of_eval_eq'
    (linePolynomialOfCoefficients first) (linePolynomialOfCoefficients second)
    (Finset.univ.filter fun param => evalCoefficient first param =
      evalCoefficient second param)
    (fun param hparam => by
      simpa only [linePolynomialOfCoefficients_eval] using (Finset.mem_filter.mp hparam).2)
    (lt_of_le_of_lt (max_le (linePolynomialOfCoefficients_natDegree_le first)
      (linePolynomialOfCoefficients_natDegree_le second)) (Nat.lt_of_not_ge hcard))
  exact hne (linePolynomialOfCoefficients_injective bound heq)

end MIPStarRE.QPBT
