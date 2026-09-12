import MIPStarRE.QPBT.Games.DistanceTheorems.TensorSupport

/-! # Consistency under independent additive convolution

Adding the outcomes of an independently perfectly correlated ancillary measurement
pair preserves the consistency defect. The four register types are independent;
`prodShuffle` places the two registers of each player next to one another.

These are formalization-only auxiliary identities. Perfect ancillary correlation
is a hypothesis of the generic result, to be proved for the Pauli measurements
before applying it to the expanded point construction.

## References

- `references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:367-438`,
  the expanded state and the convolution formula for expanded point effects.
- The same paper, `lem:qld-construct-the-paulis`.
- Blueprint `def:expanded-state` and `def:expanded-point-measurement`.
- Issue #266; the ideal-point specialization is the separate issue #267.
-/

open scoped BigOperators Matrix MatrixOrder ComplexOrder

namespace MIPStarRE.QPBT

open MIPStarRE.LDT hiding Measurement
open MIPStarRE.Quantum DistanceCalculus

section Factorization

variable {ιA ιB κA κB : Type*}
  [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB]
  [Fintype κA] [DecidableEq κA] [Fintype κB] [DecidableEq κB]

/-- Joint expectations factor after regrouping an independent pair of bipartite
states by player. The shuffle sends `((i, j), (k, l))` to `((i, k), (j, l))`. -/
theorem inner_prodShuffle_vecTensor_heteroKron
    (ψ : EuclideanSpace ℂ (ιA × ιB)) (φ : EuclideanSpace ℂ (κA × κB))
    (A : Op ιA) (B : Op ιB) (R : Op κA) (T : Op κB) :
    inner ℂ (reindexState prodShuffle (vecTensor ψ φ))
        (applyOperatorToState (heteroKron (heteroKron A R) (heteroKron B T))
          (reindexState prodShuffle (vecTensor ψ φ))) =
      inner ℂ ψ (applyOperatorToState (heteroKron A B) ψ) *
        inner ℂ φ (applyOperatorToState (heteroKron R T) φ) := by
  simp only [applyOperatorToState, Matrix.toEuclideanLin, Matrix.toLpLin_apply,
    EuclideanSpace.inner_eq_star_dotProduct, dotProduct, Matrix.mulVec]
  simp_rw [Finset.sum_mul, Finset.mul_sum]
  rw [← (prodShuffle : (ιA × ιB) × (κA × κB) ≃ _).sum_comp]
  simp_rw [← (prodShuffle : (ιA × ιB) × (κA × κB) ≃ _).sum_comp]
  change (∑ p : (ιA × ιB) × (κA × κB), ∑ q : (ιA × ιB) × (κA × κB),
    ((A p.1.1 q.1.1 * R p.2.1 q.2.1) * (B p.1.2 q.1.2 * T p.2.2 q.2.2) *
      (ψ q.1 * φ q.2)) * star (ψ p.1 * φ p.2)) =
    ∑ i : ιA × ιB, ∑ j : ιA × ιB, ∑ k : κA × κB, ∑ l : κA × κB,
      ((A i.1 j.1 * B i.2 j.2 * ψ j) * star (ψ i)) *
        ((R k.1 l.1 * T k.2 l.2 * φ l) * star (φ k))
  simp only [Fintype.sum_prod_type (α₁ := ιA × ιB) (α₂ := κA × κB), star_mul]
  conv_lhs =>
    arg 2
    ext i
    rw [Finset.sum_comm]
  congr! 4 with i j k l
  ring

/-- For positive ancillary effects, the real joint expectation factors on the
shuffled tensor state. No normalization or positivity of `A` and `B` is needed. -/
theorem stateQForm_prodShuffle_vecTensor_heteroKron
    (ψ : EuclideanSpace ℂ (ιA × ιB)) (φ : EuclideanSpace ℂ (κA × κB))
    (A : Op ιA) (B : Op ιB) {R : Op κA} {T : Op κB}
    (hR : 0 ≤ R) (hT : 0 ≤ T) :
    stateQForm (reindexState prodShuffle (vecTensor ψ φ))
        (heteroKron (heteroKron A R) (heteroKron B T)) =
      stateQForm ψ (heteroKron A B) * stateQForm φ (heteroKron R T) := by
  have hnonneg := (Matrix.nonneg_iff_posSemidef.mp
    (kronecker_nonneg hR hT)).dotProduct_mulVec_nonneg φ.ofLp
  have him : (inner ℂ φ (applyOperatorToState (heteroKron R T) φ)).im = 0 := by
    simpa only [applyOperatorToState, Matrix.toEuclideanLin, Matrix.toLpLin_apply,
      EuclideanSpace.inner_eq_star_dotProduct, dotProduct_comm, heteroKron] using
      (Complex.nonneg_iff.mp hnonneg).2.symm
  simp only [stateQForm, inner_prodShuffle_vecTensor_heteroKron, Complex.mul_re,
    him, mul_zero, sub_zero]

end Factorization

/-- An additive convolution of effect families can be indexed by the ancillary
answer alone. This is the finite-fiber form of the expanded point construction. -/
theorem sum_add_fiber_heteroKron {G ι κ : Type*}
    [Fintype G] [DecidableEq G] [AddCommGroup G]
    (A : G → Op ι) (R : G → Op κ) (z : G) :
    (∑ p ∈ Finset.univ.filter (fun p : G × G => p.1 + p.2 = z),
      heteroKron (A p.1) (R p.2)) =
      ∑ c : G, heteroKron (A (z - c)) (R c) := by
  rw [Finset.sum_filter, Fintype.sum_prod_type, Finset.sum_comm]
  simp only [← eq_sub_iff_add_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true]

/-- Averaging a common additive shift preserves the off-diagonal mass of any
weight function. The ancillary joint weights are supported on the diagonal
and have total diagonal mass one. -/
private theorem sum_convolution_off_diagonal_eq {G : Type*}
    [Fintype G] [DecidableEq G] [AddCommGroup G]
    (p q : G → G → ℝ) (hzero : ∀ c d, c ≠ d → q c d = 0)
    (hdiag : ∑ c : G, q c c = 1) :
    (∑ z : G, ∑ w : G, if z = w then 0 else
      ∑ c : G, ∑ d : G, p (z - c) (w - d) * q c d) =
      ∑ a : G, ∑ b : G, if a = b then 0 else p a b := by
  have hinner (z w c : G) :
      (∑ d : G, p (z - c) (w - d) * q c d) =
        p (z - c) (w - c) * q c c := by
    apply Finset.sum_eq_single c
    · intro d _ hdc
      rw [hzero c d hdc.symm, mul_zero]
    · simp
  have hshift (c : G) :
      (∑ z : G, ∑ w : G, if z = w then 0 else p (z - c) (w - c)) =
        ∑ a : G, ∑ b : G, if a = b then 0 else p a b := by
    refine Fintype.sum_equiv (Equiv.subRight c) _ _ fun z => ?_
    refine Fintype.sum_equiv (Equiv.subRight c) _ _ fun w => ?_
    change (if z = w then 0 else p (z - c) (w - c)) =
      if z - c = w - c then 0 else p (z - c) (w - c)
    simp only [sub_left_inj]
  simp_rw [hinner]
  calc
    (∑ z : G, ∑ w : G, if z = w then 0 else
        ∑ c : G, p (z - c) (w - c) * q c c) =
        ∑ z : G, ∑ w : G, ∑ c : G,
          (if z = w then 0 else p (z - c) (w - c)) * q c c := by
      apply Finset.sum_congr rfl
      intro z _
      apply Finset.sum_congr rfl
      intro w _
      by_cases hzw : z = w <;> simp [hzw]
    _ = ∑ c : G, (∑ z : G, ∑ w : G,
        if z = w then 0 else p (z - c) (w - c)) * q c c := by
      simp_rw [Finset.sum_mul]
      conv_lhs =>
        arg 2
        ext z
        rw [Finset.sum_comm]
      rw [Finset.sum_comm]
    _ = _ := by
      simp_rw [hshift]
      rw [← Finset.mul_sum, hdiag, mul_one]

/-- Independent additive convolution with a normalized, perfectly correlated
ancillary POVM pair preserves the consistency defect exactly. All four register
types may differ, and neither the original state nor the question distribution
needs to be normalized. No measurement is assumed projective.

This is a generic auxiliary for the expanded point construction in paper
`14_analysis_of_the_pauli_basis_test.tex:367-438` and
`lem:qld-construct-the-paulis`, not the latter paper theorem. Its ancillary
perfection hypothesis must be established for the concrete ideal measurements
before specialization; that application is tracked in issue #267. -/
theorem consistencyDefect_convolution_eq_of_perfect
    {X G ιA ιB κA κB : Type*}
    [Fintype X] [DecidableEq X] [Fintype G] [DecidableEq G] [AddCommGroup G]
    [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB]
    [Fintype κA] [DecidableEq κA] [Fintype κB] [DecidableEq κB]
    (μ : Distribution X) (A : X → Measurement G ιA) (B : X → Measurement G ιB)
    (R : X → Measurement G κA) (T : X → Measurement G κB)
    (ψ : EuclideanSpace ℂ (ιA × ιB)) (φ : EuclideanSpace ℂ (κA × κB))
    (hφ : ‖φ‖ = 1)
    (hperfect : ∀ x, (∑ c : G, ∑ d : G, if c = d then 0 else
      stateQForm φ (heteroKron ((R x).effect c) ((T x).effect d))) = 0) :
    consistencyDefect μ
        (fun x z => heteroKron
          (∑ p ∈ Finset.univ.filter (fun p : G × G => p.1 + p.2 = z),
            heteroKron ((A x).effect p.1) ((R x).effect p.2)) 1)
        (fun x z => heteroKron 1
          (∑ p ∈ Finset.univ.filter (fun p : G × G => p.1 + p.2 = z),
            heteroKron ((B x).effect p.1) ((T x).effect p.2)))
        (reindexState prodShuffle (vecTensor ψ φ)) =
      consistencyDefect μ (fun x a => heteroKron ((A x).effect a) 1)
        (fun x b => heteroKron 1 ((B x).effect b)) ψ := by
  unfold consistencyDefect
  simp_rw [consistency_term_eq_stateQForm, placed_product_stateQForm_eq]
  apply avgOver_congr
  intro x
  let q : G → G → ℝ := fun c d =>
    stateQForm φ (heteroKron ((R x).effect c) ((T x).effect d))
  have hnonneg (c d : G) : 0 ≤ q c d :=
    stateQForm_nonneg φ (kronecker_nonneg ((R x).pos c) ((T x).pos d))
  have hoff (c d : G) : 0 ≤ (if c = d then 0 else q c d) := by
    split_ifs
    · exact le_rfl
    · exact hnonneg c d
  have hzero (c d : G) (hcd : c ≠ d) : q c d = 0 := by
    have hrow := (Finset.sum_eq_zero_iff_of_nonneg
      (fun c _ => Finset.sum_nonneg (fun d _ => hoff c d))).mp (hperfect x)
    have hterm := (Finset.sum_eq_zero_iff_of_nonneg
      (fun d _ => hoff c d)).mp (hrow c (Finset.mem_univ c)) d (Finset.mem_univ d)
    simpa only [if_neg hcd] using hterm
  have hdiag : ∑ c : G, q c c = 1 := by
    have h := point_defect_eq (leftPlacedMeasurement (R x))
      (rightPlacedMeasurement (T x)) φ
    simp only [leftPlacedMeasurement, rightPlacedMeasurement, Measurement.ofSumEqOne,
      placed_product_stateQForm_eq, hperfect x, hφ, one_pow] at h
    dsimp only [q]
    linarith
  have hfactor (a b c d : G) := stateQForm_prodShuffle_vecTensor_heteroKron ψ φ
    ((A x).effect a) ((B x).effect b) ((R x).pos c) ((T x).pos d)
  simp_rw [sum_add_fiber_heteroKron, heteroKron_finset_sum_left,
    heteroKron_finset_sum_right, stateQForm_finset_sum, hfactor]
  exact sum_convolution_off_diagonal_eq
    (fun a b => stateQForm ψ (heteroKron ((A x).effect a) ((B x).effect b)))
    q hzero hdiag

end MIPStarRE.QPBT
