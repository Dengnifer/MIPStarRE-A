import MIPStarRE.QPBT.Combining.DirectLowDegree.Transport.Combining.ExactLinearity

/-!
# Uniform bounds for specialization in a block of variables

Write a polynomial as `p(z, x)`, with `m` parameter variables followed by `k`
variables that are averaged over. If `p` is not a polynomial in `z` alone, a
nonzero coefficient of a nonconstant `x`-monomial defines one exceptional set
of parameters. Outside that set, every answer has probability at most `D / q`,
where `D` bounds the total degree. The exceptional set has the same bound.

This is the scalar specialization argument between `eq:qld-g-2` and
`eq:qld-g-prime-xpt-bound`. Polynomial nonconstancy, rather than nonconstancy
of the induced function, permits the argument for arbitrary degrees, including
`D ≥ q`.

## References

* `references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1344-1363`
* Issue #283.
-/

open scoped BigOperators

namespace MIPStarRE.QPBT

open MIPStarRE.LDT MIPStarRE.LDT.Preliminaries

noncomputable section

private theorem combined_exp_sum_split {m k : ℕ} (s : Fin (m + k) →₀ ℕ) :
    s.sum (fun _ e => e) = (combinedPointExp s).sum (fun _ e => e) +
      (combinedCoefExp s).sum (fun _ e => e) := by
  simp only [Finsupp.sum_fintype _ (fun _ (e : ℕ) => e) (fun _ => rfl)]
  rw [← Fintype.sum_equiv finSumFinEquiv (fun i => s (finSumFinEquiv i)) s
    (fun _ => rfl), Fintype.sum_sum_type]
  rfl

/-- Taking the coefficient of an `x`-monomial does not increase total degree
in the remaining parameter variables. -/
theorem totalDegree_combinedCoef_le_totalDegree {K : Type*} [CommSemiring K]
    {m k : ℕ} (p : MvPolynomial (Fin (m + k)) K) (μ : Fin k →₀ ℕ) :
    (combinedCoef p μ).totalDegree ≤ p.totalDegree := by
  classical
  rw [combinedCoef_eq_sum]
  refine MvPolynomial.totalDegree_finsetSum_le fun s hs => ?_
  split_ifs
  · exact (MvPolynomial.totalDegree_monomial_le _ _).trans
      ((Nat.le_add_right _ _).trans
        ((combined_exp_sum_split s).symm.le.trans (MvPolynomial.le_totalDegree hs)))
  · simp

/-- Substituting values for a block of variables does not increase total degree. -/
theorem totalDegree_combinedRestrict_le_totalDegree {K : Type*} [CommSemiring K]
    {m k : ℕ} (p : MvPolynomial (Fin (m + k)) K) (z : Fin m → K) :
    (combinedRestrict p z).totalDegree ≤ p.totalDegree := by
  classical
  rw [MvPolynomial.totalDegree]
  refine Finset.sup_le fun μ hμ => ?_
  have hne : combinedCoef p μ ≠ 0 := by
    intro hzero
    apply MvPolynomial.mem_support_iff.mp hμ
    rw [← eval_combinedCoef, hzero, map_zero]
  obtain ⟨s, hs, rfl⟩ := exists_mem_support_of_combinedCoef_ne_zero hne
  exact (Nat.le_add_left _ _).trans
    ((combined_exp_sum_split s).symm.le.trans (MvPolynomial.le_totalDegree hs))

/-- Polynomial dependence on the `x` block supplies a nonzero coefficient
polynomial of a positive-degree `x`-monomial. Dependence is expressed by
excluding the image of the polynomial ring in the parameter variables. -/
theorem exists_nonzero_combinedCoef_of_depends_on_block {K : Type*} [CommSemiring K]
    {m k : ℕ} (p : MvPolynomial (Fin (m + k)) K)
    (hdep : ∀ r : MvPolynomial (Fin m) K,
      p ≠ MvPolynomial.rename (combinedPointVar m k) r) :
    ∃ μ : Fin k →₀ ℕ, μ ≠ 0 ∧ combinedCoef p μ ≠ 0 := by
  classical
  by_contra h
  push Not at h
  have heq : combinedCoefAlgHom K m k p = MvPolynomial.C (combinedCoef p 0) := by
    apply MvPolynomial.ext
    intro μ
    by_cases hμ : μ = 0
    · subst μ
      simp [combinedCoef]
    · simpa [combinedCoef, MvPolynomial.coeff_C, hμ, Ne.symm hμ] using h μ hμ
  apply hdep (combinedCoef p 0)
  have hinv := congrArg (combinedCoefInv K m k) heq
  rw [combinedCoefInv_combinedCoefAlgHom] at hinv
  simpa [combinedCoefInv] using hinv

/-- One nonzero coefficient polynomial defines an exceptional set of probability
at most `D / |K|`. Outside this same set, the fiber bound `D / |K|` holds for
every answer `b`. This is the uniform specialization step following `eq:qld-g-2`
in `references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1344-1363`.
No upper bound on `D` relative to the field cardinality is needed. -/
theorem exists_block_specialization_exceptional_coefficient {K : Type*} [Field K]
    [Fintype K] [DecidableEq K] {m k D : ℕ}
    (p : MvPolynomial (Fin (m + k)) K) (hdegree : p.totalDegree ≤ D)
    (hdep : ∀ r : MvPolynomial (Fin m) K,
      p ≠ MvPolynomial.rename (combinedPointVar m k) r) :
    ∃ μ : Fin k →₀ ℕ, μ ≠ 0 ∧ combinedCoef p μ ≠ 0 ∧
      (combinedCoef p μ).totalDegree ≤ D ∧
      avgOver (uniformDistribution (Fin m → K))
        (fun z => if MvPolynomial.eval z (combinedCoef p μ) = 0 then (1 : ℝ) else 0) ≤
          (D : ℝ) / Fintype.card K ∧
      ∀ z : Fin m → K, MvPolynomial.eval z (combinedCoef p μ) ≠ 0 →
        ∀ b : K, avgOver (uniformDistribution (Fin k → K))
          (fun x => if MvPolynomial.eval (combinedPoint z x) p = b then (1 : ℝ) else 0) ≤
            (D : ℝ) / Fintype.card K := by
  classical
  obtain ⟨μ, hμ, hcoef⟩ := exists_nonzero_combinedCoef_of_depends_on_block p hdep
  have hcoef_degree := (totalDegree_combinedCoef_le_totalDegree p μ).trans hdegree
  refine ⟨μ, hμ, hcoef, hcoef_degree, ?_, ?_⟩
  · have hbound := schwartzZippel_totalDegree hcoef hcoef_degree
      (show (0 : MvPolynomial (Fin m) K).totalDegree ≤ D by simp)
    have havg := polynomialAgreement_avg_eq_agreementProbability (combinedCoef p μ) 0
    simp only [map_zero] at havg
    rw [havg]
    have hreal : (polynomialAgreementProbability m K (combinedCoef p μ) 0 : ℝ) ≤
        (((D : ℚ≥0) / Fintype.card K : ℚ≥0) : ℝ) := by exact_mod_cast hbound
    simpa using hreal
  · intro z hz b
    have hnc : combinedRestrict p z ≠ MvPolynomial.C b := by
      intro heq
      apply hz
      rw [eval_combinedCoef, heq]
      simp [MvPolynomial.coeff_C, Ne.symm hμ]
    have hbound := schwartzZippel_totalDegree hnc
      ((totalDegree_combinedRestrict_le_totalDegree p z).trans hdegree)
      (show (MvPolynomial.C b : MvPolynomial (Fin k) K).totalDegree ≤ D by simp)
    have havg := polynomialAgreement_avg_eq_agreementProbability
      (combinedRestrict p z) (MvPolynomial.C b)
    simp only [eval_combinedRestrict, MvPolynomial.eval_C] at havg
    rw [havg]
    have hreal : (polynomialAgreementProbability k K
        (combinedRestrict p z) (MvPolynomial.C b) : ℝ) ≤
          (((D : ℚ≥0) / Fintype.card K : ℚ≥0) : ℝ) := by exact_mod_cast hbound
    simpa using hreal

/-- The scalar weighted specialization estimate following `eq:qld-g-2` in
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1344-1363`.
Nonnegative answer weights may depend arbitrarily on the parameter `z`, provided
their sum is the same mass `M` at every `z`. The weighted average is at most
`(2 D / |K|) M`, with no factor for the number of answers. -/
theorem block_specialization_weighted_avg_le {K : Type*} [Field K] [Fintype K]
    [DecidableEq K] {m k D : ℕ} (p : MvPolynomial (Fin (m + k)) K)
    (hdegree : p.totalDegree ≤ D)
    (hdep : ∀ r : MvPolynomial (Fin m) K,
      p ≠ MvPolynomial.rename (combinedPointVar m k) r)
    (w : (Fin m → K) → K → ℝ) (M : ℝ) (hw : ∀ z b, 0 ≤ w z b)
    (hmass : ∀ z, ∑ b : K, w z b = M) :
    avgOver (uniformDistribution (Fin m → K))
      (fun z => ∑ b : K, avgOver (uniformDistribution (Fin k → K))
        (fun x => if MvPolynomial.eval (combinedPoint z x) p = b then (1 : ℝ) else 0) *
          w z b) ≤ (2 * (D : ℝ) / Fintype.card K) * M := by
  classical
  obtain ⟨μ, _, _, _, hbad, hgood⟩ :=
    exists_block_specialization_exceptional_coefficient p hdegree hdep
  have hM : 0 ≤ M := by
    rw [← hmass (fun _ => 0)]
    exact Finset.sum_nonneg fun b _ => hw _ b
  have hratio : 0 ≤ (D : ℝ) / Fintype.card K := by positivity
  have hfiber (z : Fin m → K) (b : K) :
      avgOver (uniformDistribution (Fin k → K))
        (fun x => if MvPolynomial.eval (combinedPoint z x) p = b then (1 : ℝ) else 0) ≤
      (if MvPolynomial.eval z (combinedCoef p μ) = 0 then 1 else 0) +
        (D : ℝ) / Fintype.card K := by
    by_cases hz : MvPolynomial.eval z (combinedCoef p μ) = 0
    · rw [if_pos hz]
      refine (avgOver_uniform_le_const _ 1 fun x => ?_).trans (le_add_of_nonneg_right hratio)
      split_ifs <;> norm_num
    · simpa [hz] using hgood z hz b
  calc
    _ ≤ avgOver (uniformDistribution (Fin m → K))
        (fun z => ((if MvPolynomial.eval z (combinedCoef p μ) = 0 then 1 else 0) +
          (D : ℝ) / Fintype.card K) * M) := by
      refine avgOver_mono _ _ _ fun z => ?_
      calc
        _ ≤ ∑ b : K,
            ((if MvPolynomial.eval z (combinedCoef p μ) = 0 then 1 else 0) +
              (D : ℝ) / Fintype.card K) * w z b :=
          Finset.sum_le_sum fun b _ => mul_le_mul_of_nonneg_right (hfiber z b) (hw z b)
        _ = _ := by rw [← Finset.mul_sum, hmass]
    _ = (avgOver (uniformDistribution (Fin m → K))
        (fun z => if MvPolynomial.eval z (combinedCoef p μ) = 0 then (1 : ℝ) else 0) +
          (D : ℝ) / Fintype.card K) * M := by
      rw [avgOver_mul_const, avgOver_add, avgOver_uniform_const]
    _ ≤ ((D : ℝ) / Fintype.card K + (D : ℝ) / Fintype.card K) * M :=
      mul_le_mul_of_nonneg_right (add_le_add hbad le_rfl) hM
    _ = _ := by ring

end

end MIPStarRE.QPBT
