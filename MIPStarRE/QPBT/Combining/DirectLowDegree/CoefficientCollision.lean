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

private theorem linePolynomialOfCoefficients_injective_at_degree
    {K : Type*} [Field K] (degree : ℕ) :
    Function.Injective
      (linePolynomialOfCoefficients (K := K) (c := degree)) := by
  classical
  intro a b hab
  funext i
  have hcoeff := congrArg (fun p : Polynomial K => p.coeff i.val) hab
  simp only [linePolynomialOfCoefficients, Polynomial.finsetSum_coeff,
    Polynomial.coeff_C_mul_X_pow] at hcoeff
  have ha : (∑ j, if i.val = j.val then a j else 0) = a i := by
    simpa only [Fin.ext_iff] using Fintype.sum_ite_eq i a
  have hb : (∑ j, if i.val = j.val then b j else 0) = b i := by
    simpa only [Fin.ext_iff] using Fintype.sum_ite_eq i b
  rw [ha, hb] at hcoeff
  exact hcoeff

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
  let p := linePolynomialOfCoefficients a
  let p' := linePolynomialOfCoefficients b
  have hpoly_ne : p ≠ p' := by
    intro hpoly
    exact hne (linePolynomialOfCoefficients_injective_at_degree degree hpoly)
  let collisionSet : Finset (DirectScalarQ D) :=
    Finset.univ.filter fun t => evalCoefficient a t = evalCoefficient b t
  have hcollision_card : collisionSet.card ≤ degree := by
    have hsub_ne : p - p' ≠ 0 := sub_ne_zero.mpr hpoly_ne
    have hsubset : collisionSet.val ⊆ (p - p').roots := by
      intro t ht
      have heval : p.eval t = p'.eval t := by
        simpa [collisionSet, p, p', linePolynomialOfCoefficients_eval] using ht
      apply (Polynomial.mem_roots hsub_ne).2
      rw [Polynomial.IsRoot.def, Polynomial.eval_sub, sub_eq_zero]
      exact heval
    have hroot_card := Polynomial.card_le_degree_of_subset_roots
      (p := p - p') (Z := collisionSet) hsubset
    have hdegree : (p - p').natDegree ≤ max p.natDegree p'.natDegree := by
      simpa [sub_eq_add_neg, Polynomial.natDegree_neg] using
        (Polynomial.natDegree_add_le p (-p'))
    exact hroot_card.trans <| hdegree.trans <| max_le
      (linePolynomialOfCoefficients_natDegree_le a)
      (linePolynomialOfCoefficients_natDegree_le b)
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
