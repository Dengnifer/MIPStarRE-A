import MIPStarRE.QPBT.Combining.DirectLowDegree.Transport.Combining.Parameters

/-!
# The linear form in the combining variables and its collision estimate

At a fixed point `u` of the original space, the combined polynomial of a tuple
`g` restricts, as a function of the combining variables `α`, to the linear form
`α ↦ ∑_{r < k} g_r(u) α_r`.  The recovery step of the reduction compares two
such linear forms: if the tuple of values `(g_0(u), …, g_{k-1}(u))` differs from
a tuple `b` of answers, then the two linear forms are distinct polynomials of
total degree at most one, so by the Schwartz--Zippel lemma they agree at a
uniformly sampled `α` with probability at most `1/q`.

This module proves that estimate.  It is the quantitative content of the last
paragraph of the source proof, where the same bound is obtained for the
combining map of the surface game.

## Main statements

* `combiningLinearForm_injective` — a linear form determines its coefficients.
* `combiningLinearForm_agreementProbability_le` — the Schwartz--Zippel bound.
* `directCombiningCollision_avg_le` — the bound in the averaged form used by the
  consistency calculus of the directly indexed game.

## References

* `references/neexp-paper/05_quantum_preliminaries.tex:1484-1503`
* `references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:413-458`
* `blueprint/src/chapter/ch13_qpbt_test.tex:240-250`
-/

open scoped BigOperators

namespace MIPStarRE.QPBT

open MIPStarRE.LDT
open MIPStarRE.LDT.Preliminaries

noncomputable section

/-! ## The linear form of a tuple of scalars -/

/-- The linear form `α ↦ ∑_{r < k} c_r α_r` in the combining variables. -/
def combiningLinearForm {K : Type*} [CommSemiring K] {k : ℕ} (c : Fin k → K) :
    MvPolynomial (Fin k) K :=
  ∑ r : Fin k, MvPolynomial.C (c r) * MvPolynomial.X r

@[simp] theorem combiningLinearForm_eval {K : Type*} [CommSemiring K] {k : ℕ}
    (c α : Fin k → K) :
    MvPolynomial.eval α (combiningLinearForm c) = ∑ r : Fin k, c r * α r := by
  simp [combiningLinearForm]

/-- A linear form has total degree at most one. -/
theorem combiningLinearForm_totalDegree_le_one {K : Type*} [CommSemiring K]
    [Nontrivial K] {k : ℕ} (c : Fin k → K) :
    (combiningLinearForm c).totalDegree ≤ 1 := by
  refine le_trans (MvPolynomial.totalDegree_finsetSum _ _) (Finset.sup_le fun r _ => ?_)
  refine le_trans (MvPolynomial.totalDegree_mul _ _) ?_
  simp [MvPolynomial.totalDegree_C, MvPolynomial.totalDegree_X]

/-- The coefficient of the variable `α_r` in a linear form is `c r`. -/
theorem combiningLinearForm_coeff {K : Type*} [CommSemiring K] {k : ℕ}
    (c : Fin k → K) (r : Fin k) :
    MvPolynomial.coeff (Finsupp.single r 1) (combiningLinearForm c) = c r := by
  classical
  rw [combiningLinearForm, MvPolynomial.coeff_sum, Finset.sum_eq_single r]
  · simp [MvPolynomial.coeff_C_mul, MvPolynomial.coeff_X]
  · intro s _ hs
    rw [MvPolynomial.coeff_C_mul, MvPolynomial.coeff_X, if_neg, mul_zero]
    intro hEq
    exact hs (Finsupp.single_left_injective one_ne_zero hEq)
  · intro h
    exact absurd (Finset.mem_univ r) h

/-- A linear form determines its coefficients. -/
theorem combiningLinearForm_injective {K : Type*} [CommSemiring K] {k : ℕ} :
    Function.Injective (combiningLinearForm (K := K) (k := k)) := by
  intro c c' h
  funext r
  rw [← combiningLinearForm_coeff c r, h, combiningLinearForm_coeff]

/-- Two linear forms with distinct coefficient tuples agree at a uniformly
sampled point with probability at most `1/q`.  This is the Schwartz--Zippel
bound at total degree one. -/
theorem combiningLinearForm_agreementProbability_le {K : Type*} [Field K] [Fintype K]
    [DecidableEq K] {k : ℕ} (c b : Fin k → K) (hne : c ≠ b) :
    polynomialAgreementProbability k K (combiningLinearForm c) (combiningLinearForm b) ≤
      1 / Fintype.card K := by
  have hpoly : combiningLinearForm c ≠ combiningLinearForm b := fun h =>
    hne (combiningLinearForm_injective h)
  simpa using schwartzZippel_totalDegree (d := 1) hpoly
    (combiningLinearForm_totalDegree_le_one c) (combiningLinearForm_totalDegree_le_one b)

/-! ## The averaged form -/

/-- The uniform agreement probability of two polynomials, written as the average
of the agreement indicator over a uniformly sampled point.

This is the general form of the computation carried out inline in the proof of
`polynomialAgreement_avg_le_mdq`, which is stated for the point space of the
low individual degree test; the combining variables of the reduction are not a
point space of that test, so the general form is needed here. -/
theorem polynomialAgreement_avg_eq_agreementProbability {m : ℕ} {K : Type*} [Field K]
    [Fintype K] [DecidableEq K] (g h : MvPolynomial (Fin m) K) :
    avgOver (uniformDistribution (Fin m → K))
        (fun u => if MvPolynomial.eval u g = MvPolynomial.eval u h then (1 : Error) else 0) =
      (polynomialAgreementProbability m K g h : Error) := by
  classical
  calc
    avgOver (uniformDistribution (Fin m → K))
        (fun u => if MvPolynomial.eval u g = MvPolynomial.eval u h then (1 : Error) else 0)
      = ∑ u : Fin m → K,
          if MvPolynomial.eval u g = MvPolynomial.eval u h then
            (Fintype.card K ^ m : Error)⁻¹ else 0 := by
        simp [avgOver, uniformDistribution]
    _ = ∑ u ∈ Finset.univ.filter (fun u : Fin m → K =>
          MvPolynomial.eval u g = MvPolynomial.eval u h),
          (Fintype.card K ^ m : Error)⁻¹ := by
        rw [← Finset.sum_filter]
    _ = (((Finset.univ.filter fun u : Fin m → K =>
          MvPolynomial.eval u g = MvPolynomial.eval u h).card : ℕ) : Error) *
          (Fintype.card K ^ m : Error)⁻¹ := by
        simp
    _ = (polynomialAgreementProbability m K g h : Error) := by
        simp [polynomialAgreementProbability, div_eq_mul_inv]

/-- The collision estimate of the recovery step, in the averaged form used by
the consistency calculus of the directly indexed game: if the tuple of values
`c` differs from the tuple of answers `b`, then the two combinations agree at a
uniformly sampled combining vector with probability at most `1/q`. -/
theorem directCombiningCollision_avg_le (D : DirectLdParams)
    (c b : Fin D.k → DirectScalarQ D) (hne : c ≠ b) :
    avgOver (uniformDistribution (Fin D.k → DirectScalarQ D))
        (fun α => if ∑ r : Fin D.k, c r * α r = ∑ r : Fin D.k, b r * α r then
          (1 : Error) else 0) ≤
      (1 : Error) / D.q := by
  classical
  have hagree := combiningLinearForm_agreementProbability_le c b hne
  calc
    avgOver (uniformDistribution (Fin D.k → DirectScalarQ D))
        (fun α => if ∑ r : Fin D.k, c r * α r = ∑ r : Fin D.k, b r * α r then
          (1 : Error) else 0)
      = avgOver (uniformDistribution (Fin D.k → DirectScalarQ D))
          (fun α => if MvPolynomial.eval α (combiningLinearForm c) =
            MvPolynomial.eval α (combiningLinearForm b) then (1 : Error) else 0) := by
        apply avgOver_congr
        intro α
        rw [combiningLinearForm_eval, combiningLinearForm_eval]
    _ = (polynomialAgreementProbability D.k (DirectScalarQ D)
          (combiningLinearForm c) (combiningLinearForm b) : Error) :=
        polynomialAgreement_avg_eq_agreementProbability _ _
    _ ≤ ((1 / Fintype.card (DirectScalarQ D) : ℚ≥0) : Error) := by
        exact_mod_cast hagree
    _ = (1 : Error) / D.q := by
        rw [card_directScalarQ]
        simp

end

end MIPStarRE.QPBT
