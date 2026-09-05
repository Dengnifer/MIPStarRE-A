import MIPStarRE.QPBT.Combining.Defs
import MIPStarRE.QPBT.Combining.DirectLowDegree.Transport.Combining.Parameters

/-!
# Answer polynomials of the combined strategy

The combined strategy of `def:ld-combined-strategy` answers every question of
the directly indexed low-degree game at the combined parameters by measuring a
single question of the original game and relabelling its outcome.  Four of its
five cases produce a line answer, that is a bounded coefficient vector, from a
line answer or from a point answer of the original game.  This module collects
the univariate polynomials underlying those relabellings, with their degree
bounds and their evaluation identities.

Line answers of both games are bounded coefficient vectors evaluated by
`evalCoefficient`.  The polynomials below are therefore built from
`linePolynomialOfCoefficients` and converted back to coefficient vectors by
`coefficientsOfPolynomial`; the degree bounds are what makes that round trip
faithful.

The parameter `s` in the two line cases is the affine shift relating the two
canonical parametrizations of the line.

## Main definitions

* `coefficientsOfPolynomial` — the bounded coefficient vector of a polynomial.
* `shiftedLinePolynomial` — the affine reparametrization of a line answer.
* `combinedAxisPolynomial` — case 2 of `def:ld-combined-strategy`.
* `combinedDiagonalPolynomial` — case 4 of `def:ld-combined-strategy`.
* `fiberLinePolynomial` — cases 3 and 5 of `def:ld-combined-strategy`, the two
  cases whose line lies in a fiber of the projection to the point coordinates.

## References

* `references/neexp-paper/05_quantum_preliminaries.tex:1409-1503`
* `references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:413-458`
* `blueprint/src/chapter/ch13_qpbt_test.tex:420-472`
-/

open scoped BigOperators

namespace MIPStarRE.QPBT

open MIPStarRE.LDT
open MIPStarRE.LDT.Preliminaries

noncomputable section

/-! ## Coefficient vectors and univariate polynomials -/

/-- The bounded coefficient vector of a univariate polynomial.  It is a left
inverse of `linePolynomialOfCoefficients` on polynomials of degree at most
`n`, which is the content of `evalCoefficient_coefficientsOfPolynomial`. -/
def coefficientsOfPolynomial {K : Type*} [Semiring K] (n : ℕ)
    (p : Polynomial K) : Fin (n + 1) → K :=
  fun i => p.coeff i.val

/-- A polynomial of degree at most `n` is evaluated by its bounded coefficient
vector of length `n + 1`. -/
theorem evalCoefficient_coefficientsOfPolynomial {K : Type*} [Semiring K] {n : ℕ}
    {p : Polynomial K} (hp : p.natDegree ≤ n) (t : K) :
    evalCoefficient (coefficientsOfPolynomial n p) t = p.eval t := by
  rw [Polynomial.eval_eq_sum_range' (Nat.lt_succ_of_le hp) t,
    ← Fin.sum_univ_eq_sum_range (fun i => p.coeff i * t ^ i) (n + 1)]
  rfl

/-- The polynomial of a bounded coefficient vector has degree at most `n`. -/
theorem linePolynomialOfCoefficients_natDegree_le {K : Type*} [Semiring K] {n : ℕ}
    (f : Fin (n + 1) → K) :
    (linePolynomialOfCoefficients f).natDegree ≤ n := by
  refine Polynomial.natDegree_sum_le_of_forall_le _ _ fun i _ => ?_
  refine le_trans (Polynomial.natDegree_C_mul_le _ _) ?_
  calc (Polynomial.X ^ i.val : Polynomial K).natDegree
      ≤ i.val * (Polynomial.X : Polynomial K).natDegree :=
        Polynomial.natDegree_pow_le
    _ ≤ i.val * 1 := Nat.mul_le_mul_left _ Polynomial.natDegree_X_le
    _ = i.val := mul_one _
    _ ≤ n := Nat.lt_succ_iff.mp i.isLt

/-- The affine reparametrization `t ↦ evalCoefficient f (t + s)` of a bounded
coefficient vector, as a univariate polynomial. -/
def shiftedLinePolynomial {K : Type*} [CommSemiring K] {n : ℕ}
    (f : Fin (n + 1) → K) (s : K) : Polynomial K :=
  (linePolynomialOfCoefficients f).comp (Polynomial.X + Polynomial.C s)

theorem shiftedLinePolynomial_eval {K : Type*} [CommSemiring K] {n : ℕ}
    (f : Fin (n + 1) → K) (s t : K) :
    (shiftedLinePolynomial f s).eval t = evalCoefficient f (t + s) := by
  rw [shiftedLinePolynomial, Polynomial.eval_comp]
  simpa using linePolynomialOfCoefficients_eval f (t + s)

/-- Reparametrizing does not raise the degree of a line answer. -/
theorem shiftedLinePolynomial_natDegree_le {K : Type*} [CommSemiring K] {n : ℕ}
    (f : Fin (n + 1) → K) (s : K) :
    (shiftedLinePolynomial f s).natDegree ≤ n := by
  refine le_trans Polynomial.natDegree_comp_le ?_
  have hshift : (Polynomial.X + Polynomial.C s : Polynomial K).natDegree ≤ 1 := by
    refine le_trans (Polynomial.natDegree_add_le _ _) ?_
    simp [Polynomial.natDegree_X_le]
  calc (linePolynomialOfCoefficients f).natDegree *
        (Polynomial.X + Polynomial.C s : Polynomial K).natDegree
      ≤ n * 1 := Nat.mul_le_mul (linePolynomialOfCoefficients_natDegree_le f) hshift
    _ = n := mul_one n

/-! ## The answer polynomials of the combined strategy -/

/-- The combined answer on an axis-parallel line of the combined space whose
stored index is a point coordinate: the combining part `α` of the canonical
base is constant along such a line, so the answer is the fixed combination
`∑ r, α r * f r` of the measured line answers, reparametrized by `s`.  This is
case 2 of `def:ld-combined-strategy`. -/
def combinedAxisPolynomial {K : Type*} [CommSemiring K] {k n : ℕ}
    (α : Fin k → K) (s : K) (f : Fin k → Fin (n + 1) → K) : Polynomial K :=
  ∑ r : Fin k, Polynomial.C (α r) * shiftedLinePolynomial (f r) s

theorem combinedAxisPolynomial_natDegree_le {K : Type*} [CommSemiring K] {k n : ℕ}
    (α : Fin k → K) (s : K) (f : Fin k → Fin (n + 1) → K) :
    (combinedAxisPolynomial α s f).natDegree ≤ n := by
  refine Polynomial.natDegree_sum_le_of_forall_le _ _ fun r _ => ?_
  exact le_trans (Polynomial.natDegree_C_mul_le _ _)
    (shiftedLinePolynomial_natDegree_le (f r) s)

theorem combinedAxisPolynomial_eval {K : Type*} [CommSemiring K] {k n : ℕ}
    (α : Fin k → K) (s : K) (f : Fin k → Fin (n + 1) → K) (t : K) :
    (combinedAxisPolynomial α s f).eval t =
      ∑ r : Fin k, α r * evalCoefficient (f r) (t + s) := by
  rw [combinedAxisPolynomial, Polynomial.eval_finsetSum]
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [Polynomial.eval_mul, Polynomial.eval_C, shiftedLinePolynomial_eval]

/-- The combined answer on a diagonal line of the combined space whose stored
index is a point coordinate: the combining part of the point at parameter `t`
is `α + t • w`, so the answer is `∑ r, (α r + t * w r) * f r (t + s)`.  This is
case 4 of `def:ld-combined-strategy`. -/
def combinedDiagonalPolynomial {K : Type*} [CommSemiring K] {k n : ℕ}
    (α w : Fin k → K) (s : K) (f : Fin k → Fin (n + 1) → K) : Polynomial K :=
  ∑ r : Fin k, (Polynomial.C (α r) + Polynomial.C (w r) * Polynomial.X) *
    shiftedLinePolynomial (f r) s

theorem combinedDiagonalPolynomial_natDegree_le {K : Type*} [CommSemiring K]
    {k n : ℕ} (α w : Fin k → K) (s : K) (f : Fin k → Fin (n + 1) → K) :
    (combinedDiagonalPolynomial α w s f).natDegree ≤ n + 1 := by
  refine Polynomial.natDegree_sum_le_of_forall_le _ _ fun r _ => ?_
  refine le_trans (Polynomial.natDegree_mul_le) ?_
  have haffine :
      (Polynomial.C (α r) + Polynomial.C (w r) * Polynomial.X :
        Polynomial K).natDegree ≤ 1 := by
    refine le_trans (Polynomial.natDegree_add_le _ _) (max_le ?_ ?_)
    · exact le_trans (le_of_eq (Polynomial.natDegree_C _)) (Nat.zero_le 1)
    · exact le_trans (Polynomial.natDegree_C_mul_le _ _) Polynomial.natDegree_X_le
  have := shiftedLinePolynomial_natDegree_le (f r) s
  omega

theorem combinedDiagonalPolynomial_eval {K : Type*} [CommSemiring K] {k n : ℕ}
    (α w : Fin k → K) (s : K) (f : Fin k → Fin (n + 1) → K) (t : K) :
    (combinedDiagonalPolynomial α w s f).eval t =
      ∑ r : Fin k, (α r + t * w r) * evalCoefficient (f r) (t + s) := by
  rw [combinedDiagonalPolynomial, Polynomial.eval_finsetSum]
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [Polynomial.eval_mul, Polynomial.eval_add, Polynomial.eval_mul,
    Polynomial.eval_C, Polynomial.eval_C, Polynomial.eval_X,
    shiftedLinePolynomial_eval]
  ring

/-- The combined answer on a line of the combined space contained in a fiber of
the projection to the point coordinates: the point part is constant along the
line, the combined value at parameter `t` is `∑ r, (α r + t * w r) * b r`, and
the measured outcome is the point answer `b`.  This is cases 3 and 5 of
`def:ld-combined-strategy`; case 3 is the axis-parallel case, where `w` is the
standard basis vector of the varying combining coordinate. -/
def fiberLinePolynomial {K : Type*} [CommSemiring K] {k : ℕ}
    (α w b : Fin k → K) : Polynomial K :=
  Polynomial.C (∑ r : Fin k, α r * b r) +
    Polynomial.C (∑ r : Fin k, w r * b r) * Polynomial.X

theorem fiberLinePolynomial_natDegree_le {K : Type*} [CommSemiring K] {k : ℕ}
    (α w b : Fin k → K) : (fiberLinePolynomial α w b).natDegree ≤ 1 := by
  refine le_trans (Polynomial.natDegree_add_le _ _) (max_le ?_ ?_)
  · exact le_trans (le_of_eq (Polynomial.natDegree_C _)) (Nat.zero_le 1)
  · exact le_trans (Polynomial.natDegree_C_mul_le _ _) Polynomial.natDegree_X_le

theorem fiberLinePolynomial_eval {K : Type*} [CommSemiring K] {k : ℕ}
    (α w b : Fin k → K) (t : K) :
    (fiberLinePolynomial α w b).eval t =
      ∑ r : Fin k, (α r + t * w r) * b r := by
  rw [fiberLinePolynomial]
  simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
    Polynomial.eval_X]
  rw [Finset.sum_mul, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun r _ => by ring

end

end MIPStarRE.QPBT
