import MIPStarRE.QPBT.Combining.DirectLowDegree.Transport.Combining.Answers

/-!
# Collision bounds for direct line coefficients

This module bounds the probability that two distinct coefficient vectors give
the same value at a uniformly sampled affine parameter.  It uses the existing
coefficient-polynomial representation and Mathlib's univariate root count.

## References

- `references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:331-344`
- `references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1595-1603`
-/

open scoped BigOperators

namespace MIPStarRE.QPBT

open MIPStarRE.LDT
open MIPStarRE.LDT.Preliminaries

noncomputable section

/-- Two distinct direct coefficient vectors of degree at most `degree` agree
at a uniformly sampled parameter with probability at most `degree / q`.

This is a Lean-only auxiliary. The cited paper passages describe the coefficient
answer format and apply Schwartz-Zippel to a later multivariate collision term;
they do not state this exact univariate averaging bound.

The estimate has no hypothesis `degree < q`; when the displayed bound exceeds
one it remains a valid, deliberately nontruncated root-count bound. -/
theorem directCoefficientCollision_avg_le (D : DirectLdParams) (degree : ℕ)
    (a b : DirectDegPoly D degree) (hne : a ≠ b) :
    avgOver (uniformDistribution (DirectScalarQ D))
        (fun t => if evalCoefficient a t = evalCoefficient b t then
          (1 : ℝ) else 0) ≤
      (degree : ℝ) / (D.q : ℝ) := by
  classical
  let collisionSet : Finset (DirectScalarQ D) :=
    Finset.univ.filter fun t => evalCoefficient a t = evalCoefficient b t
  have hcollision_card : collisionSet.card ≤ degree :=
    evalCoefficient_collision_card_le a b hne
  calc
    avgOver (uniformDistribution (DirectScalarQ D))
        (fun t => if evalCoefficient a t = evalCoefficient b t then
          (1 : ℝ) else 0) =
        (collisionSet.card : ℝ) /
          Fintype.card (DirectScalarQ D) := by
      calc
        avgOver (uniformDistribution (DirectScalarQ D))
            (fun t => if evalCoefficient a t = evalCoefficient b t then
              (1 : ℝ) else 0) =
            ∑ t : DirectScalarQ D,
              if evalCoefficient a t = evalCoefficient b t then
                (1 / Fintype.card (DirectScalarQ D) : ℝ) else 0 := by
          simp [avgOver, uniformDistribution]
        _ = ∑ _t ∈ collisionSet,
              (1 / Fintype.card (DirectScalarQ D) : ℝ) := by
          rw [← Finset.sum_filter]
        _ = (collisionSet.card : ℝ) /
              Fintype.card (DirectScalarQ D) := by
          simp [div_eq_mul_inv]
    _ ≤ (degree : ℝ) / Fintype.card (DirectScalarQ D) := by
      exact div_le_div_of_nonneg_right (by exact_mod_cast hcollision_card) (by positivity)
    _ = (degree : ℝ) / (D.q : ℝ) := by
      rw [card_directScalarQ]

end

end MIPStarRE.QPBT
