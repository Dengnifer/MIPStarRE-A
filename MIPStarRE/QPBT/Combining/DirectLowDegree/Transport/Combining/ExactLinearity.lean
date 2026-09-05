import MIPStarRE.QPBT.Combining.DirectLowDegree.Transport.Combining.Coefficients

/-!
# Exact linearity in the combining variables

The recovery step of the combining reduction needs to know that a polynomial in
the combined variables which is not the combined polynomial of any tuple only
rarely restricts to a linear form in the combining variables: writing
`p = ∑_μ c_μ α^μ` with coefficients `c_μ` in the point variables, the
polynomial `p` is combined exactly when `c_μ` vanishes for every exponent vector
`μ` outside the `k` standard basis vectors, and the restriction `p(u, ·)` is a
linear form exactly when `c_μ(u)` vanishes for every such `μ`.  Fixing one such
`μ` with `c_μ ≠ 0`, whose total degree is at most `m d`, the Schwartz--Zippel
lemma bounds the probability of `c_μ(u) = 0` by `m d / q`.

## Main statements

* `exists_eq_combiningLinearForm_iff` — a polynomial in the combining variables
  is a linear form exactly when its coefficients vanish off the standard basis
  vectors.
* `combinedRestrict_combiningLinearForm_avg_le` — `lem:ld-combining-exact-linearity`.
* `directCombinedExactLinearity_avg_le` — the same bound in the parameters of
  the directly indexed low-degree game.

## References

* `references/neexp-paper/05_quantum_preliminaries.tex:1440-1477`
* `references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:413-458`
* `blueprint/src/chapter/ch13_qpbt_test.tex:575-600`
-/

open scoped BigOperators

namespace MIPStarRE.QPBT

open MIPStarRE.LDT
open MIPStarRE.LDT.Preliminaries

noncomputable section

/-! ## Linear forms in terms of their coefficients -/

/-- A linear form is the sum of its monomials at the standard basis vectors. -/
theorem combiningLinearForm_eq_sum_monomial {K : Type*} [CommSemiring K] {k : ℕ}
    (c : Fin k → K) :
    combiningLinearForm c =
      ∑ r : Fin k, MvPolynomial.monomial (Finsupp.single r 1) (c r) := by
  simp only [combiningLinearForm]
  exact Finset.sum_congr rfl fun r _ => MvPolynomial.C_mul_X_eq_monomial

/-- The coefficients of a linear form vanish outside the standard basis
vectors. -/
theorem coeff_combiningLinearForm_eq_zero {K : Type*} [CommSemiring K] {k : ℕ}
    (c : Fin k → K) {μ : Fin k →₀ ℕ} (hμ : ∀ r : Fin k, μ ≠ Finsupp.single r 1) :
    MvPolynomial.coeff μ (combiningLinearForm c) = 0 := by
  classical
  rw [combiningLinearForm_eq_sum_monomial, MvPolynomial.coeff_sum]
  refine Finset.sum_eq_zero fun r _ => ?_
  rw [MvPolynomial.coeff_monomial, if_neg]
  exact fun hEq => hμ r hEq.symm

/-- A polynomial in the combining variables is a linear form exactly when its
coefficients vanish outside the `k` standard basis vectors. -/
theorem exists_eq_combiningLinearForm_iff {K : Type*} [CommSemiring K] {k : ℕ}
    (P : MvPolynomial (Fin k) K) :
    (∃ c : Fin k → K, P = combiningLinearForm c) ↔
      ∀ μ : Fin k →₀ ℕ, (∀ r : Fin k, μ ≠ Finsupp.single r 1) →
        MvPolynomial.coeff μ P = 0 := by
  classical
  constructor
  · rintro ⟨c, rfl⟩ μ hμ
    exact coeff_combiningLinearForm_eq_zero c hμ
  · intro h
    refine ⟨fun r => MvPolynomial.coeff (Finsupp.single r 1) P, ?_⟩
    rw [combiningLinearForm_eq_sum_monomial]
    exact eq_sum_monomial_single P h

/-- The restriction of `p` at `u` is a linear form exactly when the values at
`u` of the coefficients off the standard basis vectors all vanish. -/
theorem exists_eq_combiningLinearForm_combinedRestrict_iff {K : Type*} [CommSemiring K]
    {m k : ℕ} (p : MvPolynomial (Fin (m + k)) K) (u : Fin m → K) :
    (∃ c : Fin k → K, combinedRestrict p u = combiningLinearForm c) ↔
      ∀ μ : Fin k →₀ ℕ, (∀ r : Fin k, μ ≠ Finsupp.single r 1) →
        MvPolynomial.eval u (combinedCoef p μ) = 0 := by
  rw [exists_eq_combiningLinearForm_iff]
  simp only [eval_combinedCoef]

/-! ## The exact-linearity estimate -/

open scoped Classical in
/-- `lem:ld-combining-exact-linearity`.  A polynomial of individual degree at
most `d` in the combined variables which is not the combined polynomial of any
tuple restricts, at a uniformly sampled point of the original space, to a linear
form in the combining variables with probability at most `m d / q`. -/
theorem combinedRestrict_combiningLinearForm_avg_le {K : Type*} [Field K] [Fintype K]
    [DecidableEq K] {m k d : ℕ} {p : MvPolynomial (Fin (m + k)) K}
    (hp : p ∈ polyFunc (m + k) K d)
    (hnc : ∀ g : Fin k → MvPolynomial (Fin m) K, p ≠ combinePolyTuple g) :
    avgOver (uniformDistribution (Fin m → K))
        (fun u => if ∃ c : Fin k → K, combinedRestrict p u = combiningLinearForm c then
          (1 : Error) else 0) ≤
      ((((m * d : ℕ) : ℚ≥0) / Fintype.card K : ℚ≥0) : Error) := by
  classical
  obtain ⟨μ, hμ, hne⟩ : ∃ μ : Fin k →₀ ℕ, (∀ r : Fin k, μ ≠ Finsupp.single r 1) ∧
      combinedCoef p μ ≠ 0 := by
    by_contra hcon
    push Not at hcon
    obtain ⟨g, hg⟩ := (combinePolyTuple_combinedCoef_iff p).mpr hcon
    exact hnc g hg
  calc
    avgOver (uniformDistribution (Fin m → K))
        (fun u => if ∃ c : Fin k → K, combinedRestrict p u = combiningLinearForm c then
          (1 : Error) else 0)
      ≤ avgOver (uniformDistribution (Fin m → K))
          (fun u => if MvPolynomial.eval u (combinedCoef p μ) =
            MvPolynomial.eval u (0 : MvPolynomial (Fin m) K) then (1 : Error) else 0) := by
        refine avgOver_mono _ _ _ fun u => ?_
        by_cases hu : ∃ c : Fin k → K, combinedRestrict p u = combiningLinearForm c
        · have h0 : MvPolynomial.eval u (combinedCoef p μ) =
              MvPolynomial.eval u (0 : MvPolynomial (Fin m) K) := by
            rw [map_zero]
            exact (exists_eq_combiningLinearForm_combinedRestrict_iff p u).mp hu μ hμ
          rw [if_pos hu, if_pos h0]
        · rw [if_neg hu]
          split_ifs <;> norm_num
    _ = (polynomialAgreementProbability m K (combinedCoef p μ) 0 : Error) :=
        polynomialAgreement_avg_eq_agreementProbability _ _
    _ ≤ ((((m * d : ℕ) : ℚ≥0) / Fintype.card K : ℚ≥0) : Error) := by
        have hdeg : (combinedCoef p μ).totalDegree ≤ m * d :=
          totalDegree_combinedCoef_le hp μ
        have hzero : (0 : MvPolynomial (Fin m) K).totalDegree ≤ m * d := by
          simp
        exact_mod_cast schwartzZippel_totalDegree hne hdeg hzero

open scoped Classical in
/-- `lem:ld-combining-exact-linearity` in the parameters of the directly indexed
low-degree game: an outcome of the combined game which is not combined restricts
to a linear form in the combining variables with probability at most `m d / q`
over a uniformly sampled point of the original space. -/
theorem directCombinedExactLinearity_avg_le (D : DirectLdParams)
    (p : PolyIndex D.combined.m (DirectScalarQ D) D.d) (hnc : ¬ IsDirectCombined D p) :
    avgOver (uniformDistribution (Fin D.m → DirectScalarQ D))
        (fun u => if ∃ c : Fin D.k → DirectScalarQ D,
          combinedRestrict p.1 u = combiningLinearForm c then (1 : Error) else 0) ≤
      ((D.m * D.d : ℕ) : Error) / D.q := by
  classical
  have hnc' : ∀ g : Fin D.k → MvPolynomial (Fin D.m) (DirectScalarQ D),
      p.1 ≠ combinePolyTuple g := by
    intro g hg
    refine hnc ⟨fun r => ⟨g r, mem_polyFunc_of_combinePolyTuple p.2 hg r⟩, ?_⟩
    exact Subtype.ext hg.symm
  have hbound := combinedRestrict_combiningLinearForm_avg_le (d := D.d) p.2 hnc'
  calc
    avgOver (uniformDistribution (Fin D.m → DirectScalarQ D))
        (fun u => if ∃ c : Fin D.k → DirectScalarQ D,
          combinedRestrict p.1 u = combiningLinearForm c then (1 : Error) else 0)
      ≤ ((((D.m * D.d : ℕ) : ℚ≥0) /
          Fintype.card (DirectScalarQ D) : ℚ≥0) : Error) := hbound
    _ = ((D.m * D.d : ℕ) : Error) / D.q := by
        rw [card_directScalarQ]
        push_cast
        ring

end

end MIPStarRE.QPBT
