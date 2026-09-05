import MIPStarRE.QPBT.Games.Sandwich.Pasting.PinchedReduction

/-! # Moving a second codeword effect across the tensor factors

This module records the estimate of step 5 of the proof of the adopted
statement of `lem:pasting`: in the cross term of the commutator mass of a first
codeword family against a second codeword family, the rightmost second codeword
effect is moved to the opposite tensor factor at the cost of the square root of
the summed cross distance of that family.

## References

`lem:pasting` in `blueprint/src/chapter/ch12_qpbt_games.tex:960-990`, with the
proof of the adopted statement in
`docs/paper-gaps/qpbt_pasting-product-error.tex`.
-/

open scoped BigOperators MatrixOrder Matrix ComplexOrder

namespace MIPStarRE.QPBT

open MIPStarRE.LDT hiding Measurement
open MIPStarRE.Quantum
open DistanceCalculus

/-- The move estimate of `lem:pasting` at a fixed question. The cross term of
the commutator mass of a first codeword family against a second codeword
family, both placed on the second tensor factor, differs from the expectation
of the tensor products of the second codeword effects against their pinchings
of the first family by at most the square root of the summed squared distance
between the two placements of the second family. This is the move of step 5 of
the proof of the adopted statement in
`docs/paper-gaps/qpbt_pasting-product-error.tex`; blueprint
`ch12_qpbt_games.tex:960-990`. -/
theorem abs_cross_move_gap_le_sqrt {R₁ Γ₂ ι : Type*}
    [Fintype R₁] [DecidableEq R₁] [Fintype Γ₂] [DecidableEq Γ₂]
    [Fintype ι] [DecidableEq ι]
    (P : Measurement R₁ ι) (G : Measurement Γ₂ ι)
    (ψ : EuclideanSpace ℂ (ι × ι)) (hψ : ‖ψ‖ = 1) :
    |(∑ a : R₁, ∑ g : Γ₂, stateQForm ψ (heteroKron 1
          (G.effect g * P.effect a * G.effect g * P.effect a))) -
        ∑ g : Γ₂, stateQForm ψ (heteroKron (G.effect g)
          (∑ a : R₁, P.effect a * G.effect g * P.effect a))| ≤
      Real.sqrt (∑ g : Γ₂, ‖applyOperatorToState
        (heteroKron 1 (G.effect g) - heteroKron (G.effect g) 1) ψ‖ ^ 2) := by
  classical
  -- the inlined identities of the distance calculus; see issue #204
  have hqf : ∀ M N : Op (ι × ι), stateQForm ψ (M * N) =
      (inner ℂ (applyOperatorToState Mᴴ ψ) (applyOperatorToState N ψ)).re := by
    intro M N
    have happ : applyOperatorToState (M * N) ψ =
        applyOperatorToState M (applyOperatorToState N ψ) := by
      unfold applyOperatorToState
      simp [Matrix.toEuclideanLin, Matrix.toLpLin_mul_same]
    have hadj : (Matrix.toEuclideanLin M).adjoint = Matrix.toEuclideanLin Mᴴ := by
      rw [← Matrix.toEuclideanLin_conjTranspose_eq_adjoint]
    have h1 : (inner ℂ ((Matrix.toEuclideanLin M).adjoint ψ)
        (applyOperatorToState N ψ) : ℂ) =
        inner ℂ ψ (Matrix.toEuclideanLin M (applyOperatorToState N ψ)) :=
      LinearMap.adjoint_inner_left _ _ _
    rw [stateQForm, happ]
    rw [show applyOperatorToState Mᴴ ψ = (Matrix.toEuclideanLin M).adjoint ψ by
      rw [hadj]; rfl]
    rw [h1]
    rfl
  have hct : ∀ M N : Op ι, (heteroKron M N)ᴴ = heteroKron Mᴴ Nᴴ := by
    intro M N
    unfold heteroKron
    exact Matrix.conjTranspose_kronecker M N
  set u : R₁ × Γ₂ → EuclideanSpace ℂ (ι × ι) := fun p =>
    applyOperatorToState (heteroKron 1 (P.effect p.1) *
      (heteroKron 1 (G.effect p.2) - heteroKron (G.effect p.2) 1)) ψ with hu
  set v : R₁ × Γ₂ → EuclideanSpace ℂ (ι × ι) := fun p =>
    applyOperatorToState (heteroKron 1 (G.effect p.2 * P.effect p.1)) ψ with hv
  -- the pointwise gap is the overlap of the moved vector with the cross vector
  have hpt : ∀ (a : R₁) (g : Γ₂),
      stateQForm ψ (heteroKron 1
          (G.effect g * P.effect a * G.effect g * P.effect a)) -
        stateQForm ψ (heteroKron (G.effect g)
          (P.effect a * G.effect g * P.effect a)) =
        (inner ℂ (u (a, g)) (v (a, g))).re := by
    intro a g
    have e1 : heteroKron (1 : Op ι)
        (G.effect g * P.effect a * G.effect g * P.effect a) =
        heteroKron 1 (G.effect g * P.effect a) *
          heteroKron 1 (G.effect g * P.effect a) := by
      rw [heteroKron_mul]
      congr 1
      · rw [one_mul]
      · simp [mul_assoc]
    have e2 : heteroKron (G.effect g) (P.effect a * G.effect g * P.effect a) =
        heteroKron (G.effect g) (P.effect a) *
          heteroKron 1 (G.effect g * P.effect a) := by
      rw [heteroKron_mul]
      congr 1
      · rw [mul_one]
      · simp [mul_assoc]
    have h1 : (heteroKron (1 : Op ι) (G.effect g * P.effect a))ᴴ =
        heteroKron 1 (P.effect a * G.effect g) := by
      rw [hct]
      simp [Matrix.conjTranspose_mul, measurement_effect_hermitian]
    have h2 : (heteroKron (G.effect g) (P.effect a))ᴴ =
        heteroKron (G.effect g) (P.effect a) := by
      rw [hct, measurement_effect_hermitian, measurement_effect_hermitian]
    have hudiff : applyOperatorToState (heteroKron 1 (P.effect a * G.effect g)) ψ -
        applyOperatorToState (heteroKron (G.effect g) (P.effect a)) ψ = u (a, g) := by
      simp only [hu]
      rw [show heteroKron (1 : Op ι) (P.effect a) *
          (heteroKron 1 (G.effect g) - heteroKron (G.effect g) 1) =
          heteroKron 1 (P.effect a * G.effect g) -
            heteroKron (G.effect g) (P.effect a) by
        simp [mul_sub, heteroKron_mul]]
      simp [applyOperatorToState]
    rw [e1, e2, hqf, hqf, h1, h2, ← Complex.sub_re, ← inner_sub_left, hudiff]
  -- the two mass estimates
  have hCP : ∑ a : R₁, (heteroKron (1 : Op ι) (P.effect a))ᴴ *
      heteroKron 1 (P.effect a) ≤ 1 := by
    simpa using MIPStarRE.QPBT.measurement_sum_adjoint_mul_le_one
      (Measurement.rightPlacement (ιA := ι) P)
  have hCG : ∑ g : Γ₂, (heteroKron (1 : Op ι) (G.effect g))ᴴ *
      heteroKron 1 (G.effect g) ≤ 1 := by
    simpa using MIPStarRE.QPBT.measurement_sum_adjoint_mul_le_one
      (Measurement.rightPlacement (ιA := ι) G)
  have hmassU : (∑ p : R₁ × Γ₂, ‖u p‖ ^ 2) ≤
      ∑ g : Γ₂, ‖applyOperatorToState
        (heteroKron 1 (G.effect g) - heteroKron (G.effect g) 1) ψ‖ ^ 2 := by
    rw [Fintype.sum_prod_type, Finset.sum_comm]
    refine Finset.sum_le_sum fun g _ => ?_
    simpa [hu] using sum_norm_mul_apply_le
      (fun a : R₁ => heteroKron (1 : Op ι) (P.effect a))
      (heteroKron 1 (G.effect g) - heteroKron (G.effect g) 1) ψ hCP
  have hmassV : (∑ p : R₁ × Γ₂, ‖v p‖ ^ 2) ≤ 1 := by
    have hone : applyOperatorToState (1 : Op (ι × ι)) ψ = ψ := by
      simp [applyOperatorToState]
    rw [Fintype.sum_prod_type]
    calc (∑ a : R₁, ∑ g : Γ₂, ‖v (a, g)‖ ^ 2)
        ≤ ∑ a : R₁, ‖applyOperatorToState (heteroKron 1 (P.effect a)) ψ‖ ^ 2 := by
          refine Finset.sum_le_sum fun a _ => ?_
          simpa [hv, heteroKron_mul] using sum_norm_mul_apply_le
            (fun g : Γ₂ => heteroKron (1 : Op ι) (G.effect g))
            (heteroKron 1 (P.effect a)) ψ hCG
      _ ≤ 1 := by
          have h := sum_norm_mul_apply_le
            (fun a : R₁ => heteroKron (1 : Op ι) (P.effect a)) (1 : Op (ι × ι)) ψ hCP
          rw [hone, hψ, one_pow] at h
          simpa using h
  -- the expansion of the gap over the pairs
  have hexpand : (∑ a : R₁, ∑ g : Γ₂, stateQForm ψ (heteroKron 1
        (G.effect g * P.effect a * G.effect g * P.effect a))) -
      (∑ g : Γ₂, stateQForm ψ (heteroKron (G.effect g)
        (∑ a : R₁, P.effect a * G.effect g * P.effect a))) =
      ∑ p : R₁ × Γ₂, (inner ℂ (u p) (v p)).re := by
    have hB : (∑ g : Γ₂, stateQForm ψ (heteroKron (G.effect g)
        (∑ a : R₁, P.effect a * G.effect g * P.effect a))) =
        ∑ a : R₁, ∑ g : Γ₂, stateQForm ψ (heteroKron (G.effect g)
          (P.effect a * G.effect g * P.effect a)) := by
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun g _ => ?_
      rw [heteroKron_finset_sum_right, stateQForm_finset_sum]
    rw [hB, ← Finset.sum_sub_distrib, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun g _ => hpt a g
  rw [hexpand]
  calc |∑ p : R₁ × Γ₂, (inner ℂ (u p) (v p)).re|
      ≤ ∑ p : R₁ × Γ₂, |(inner ℂ (u p) (v p)).re| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ p : R₁ × Γ₂, ‖u p‖ * ‖v p‖ := Finset.sum_le_sum fun p _ =>
        le_trans (Complex.abs_re_le_norm _) (norm_inner_le_norm _ _)
    _ ≤ Real.sqrt (∑ p : R₁ × Γ₂, ‖u p‖ ^ 2) *
          Real.sqrt (∑ p : R₁ × Γ₂, ‖v p‖ ^ 2) := by
        simpa using Real.sum_mul_le_sqrt_mul_sqrt
          (Finset.univ : Finset (R₁ × Γ₂)) (fun p => ‖u p‖) (fun p => ‖v p‖)
    _ ≤ Real.sqrt (∑ g : Γ₂, ‖applyOperatorToState
          (heteroKron 1 (G.effect g) - heteroKron (G.effect g) 1) ψ‖ ^ 2) * 1 := by
        refine mul_le_mul (Real.sqrt_le_sqrt hmassU) ?_ (Real.sqrt_nonneg _)
          (Real.sqrt_nonneg _)
        rw [show (1 : ℝ) = Real.sqrt 1 by rw [Real.sqrt_one]]
        exact Real.sqrt_le_sqrt hmassV
    _ = Real.sqrt (∑ g : Γ₂, ‖applyOperatorToState
          (heteroKron 1 (G.effect g) - heteroKron (G.effect g) 1) ψ‖ ^ 2) := by
        rw [mul_one]

/-- The expansion of the commutator mass of `lem:pasting` at a fixed question.
For a measurement and a projective measurement placed on the second tensor
factor, the summed squared norm of the commutators is the summed squared norm
of the ordered products, plus the expectation of the squares of the effects of
the first family, minus twice the cross term. This is the term-by-term
expansion of step 5 of the proof of the adopted statement in
`docs/paper-gaps/qpbt_pasting-product-error.tex`; blueprint
`ch12_qpbt_games.tex:960-990`. -/
theorem commutator_mass_eq_expansion {R₁ Γ₂ ι : Type*}
    [Fintype R₁] [DecidableEq R₁] [Fintype Γ₂] [DecidableEq Γ₂]
    [Fintype ι] [DecidableEq ι]
    (P : Measurement R₁ ι) (G : Measurement Γ₂ ι)
    (ψ : EuclideanSpace ℂ (ι × ι))
    (hG : MIPStarRE.QPBT.Measurement.IsProjective G) :
    (∑ a : R₁, ∑ g : Γ₂, ‖applyOperatorToState (heteroKron 1
        (P.effect a * G.effect g - G.effect g * P.effect a)) ψ‖ ^ 2) =
      (∑ a : R₁, ∑ g : Γ₂, ‖applyOperatorToState
          (heteroKron 1 (P.effect a * G.effect g)) ψ‖ ^ 2) +
        (∑ a : R₁, stateQForm ψ (heteroKron 1 (P.effect a * P.effect a))) -
        2 * ∑ a : R₁, ∑ g : Γ₂, stateQForm ψ (heteroKron 1
          (G.effect g * P.effect a * G.effect g * P.effect a)) := by
  classical
  -- the inlined identities of the distance calculus; see issue #204
  have hqf : ∀ M N : Op (ι × ι), stateQForm ψ (M * N) =
      (inner ℂ (applyOperatorToState Mᴴ ψ) (applyOperatorToState N ψ)).re := by
    intro M N
    have happ : applyOperatorToState (M * N) ψ =
        applyOperatorToState M (applyOperatorToState N ψ) := by
      unfold applyOperatorToState
      simp [Matrix.toEuclideanLin, Matrix.toLpLin_mul_same]
    have hadj : (Matrix.toEuclideanLin M).adjoint = Matrix.toEuclideanLin Mᴴ := by
      rw [← Matrix.toEuclideanLin_conjTranspose_eq_adjoint]
    have h1 : (inner ℂ ((Matrix.toEuclideanLin M).adjoint ψ)
        (applyOperatorToState N ψ) : ℂ) =
        inner ℂ ψ (Matrix.toEuclideanLin M (applyOperatorToState N ψ)) :=
      LinearMap.adjoint_inner_left _ _ _
    rw [stateQForm, happ]
    rw [show applyOperatorToState Mᴴ ψ = (Matrix.toEuclideanLin M).adjoint ψ by
      rw [hadj]; rfl]
    rw [h1]
    rfl
  have hct : ∀ M N : Op ι, (heteroKron M N)ᴴ = heteroKron Mᴴ Nᴴ := by
    intro M N
    unfold heteroKron
    exact Matrix.conjTranspose_kronecker M N
  have hkr : ∀ B C : Op ι,
      heteroKron (1 : Op ι) (B - C) = heteroKron 1 B - heteroKron 1 C := by
    intro B C
    ext p q
    simp [heteroKron, Matrix.kronecker, mul_sub]
  have hnorm : ∀ M : Op (ι × ι),
      ‖applyOperatorToState M ψ‖ ^ 2 = stateQForm ψ (Mᴴ * M) := by
    intro M
    rw [hqf Mᴴ M, Matrix.conjTranspose_conjTranspose]
    exact (inner_self_eq_norm_sq (𝕜 := ℂ) (applyOperatorToState M ψ)).symm
  have hsub : ∀ M N : Op (ι × ι),
      ‖applyOperatorToState (M - N) ψ‖ ^ 2 =
        ‖applyOperatorToState M ψ‖ ^ 2 + ‖applyOperatorToState N ψ‖ ^ 2 -
          2 * stateQForm ψ (Mᴴ * N) := by
    intro M N
    have hlin : applyOperatorToState (M - N) ψ =
        applyOperatorToState M ψ - applyOperatorToState N ψ := by
      simp [applyOperatorToState]
    rw [hlin, norm_sub_sq (𝕜 := ℂ), hqf Mᴴ N, Matrix.conjTranspose_conjTranspose]
    simp only [RCLike.re_to_complex]
    ring
  -- the pointwise expansion at a pair of an answer and a codeword
  have hpt : ∀ (a : R₁) (g : Γ₂),
      ‖applyOperatorToState (heteroKron 1
          (P.effect a * G.effect g - G.effect g * P.effect a)) ψ‖ ^ 2 =
        ‖applyOperatorToState (heteroKron 1 (P.effect a * G.effect g)) ψ‖ ^ 2 +
          stateQForm ψ (heteroKron 1 (P.effect a * G.effect g * P.effect a)) -
          2 * stateQForm ψ (heteroKron 1
            (G.effect g * P.effect a * G.effect g * P.effect a)) := by
    intro a g
    have hH : (heteroKron (1 : Op ι) (P.effect a * G.effect g))ᴴ =
        heteroKron 1 (G.effect g * P.effect a) := by
      rw [hct]
      simp [Matrix.conjTranspose_mul, measurement_effect_hermitian]
    have hH2 : (heteroKron (1 : Op ι) (G.effect g * P.effect a))ᴴ =
        heteroKron 1 (P.effect a * G.effect g) := by
      rw [hct]
      simp [Matrix.conjTranspose_mul, measurement_effect_hermitian]
    have hNN : (heteroKron (1 : Op ι) (G.effect g * P.effect a))ᴴ *
        heteroKron 1 (G.effect g * P.effect a) =
        heteroKron 1 (P.effect a * G.effect g * P.effect a) := by
      rw [hH2, heteroKron_mul, one_mul]
      congr 1
      rw [mul_assoc, ← mul_assoc (G.effect g), (hG g).isIdempotentElem.eq]
      exact (mul_assoc _ _ _).symm
    have hXN : (heteroKron (1 : Op ι) (P.effect a * G.effect g))ᴴ *
        heteroKron 1 (G.effect g * P.effect a) =
        heteroKron 1 (G.effect g * P.effect a * G.effect g * P.effect a) := by
      rw [hH, heteroKron_mul, one_mul]
      congr 1
      simp [mul_assoc]
    rw [hkr, hsub, hnorm (heteroKron 1 (G.effect g * P.effect a)),
      hNN, hXN]
  -- the row sum at a fixed answer
  have hrow : ∀ a : R₁,
      (∑ g : Γ₂, ‖applyOperatorToState (heteroKron 1
          (P.effect a * G.effect g - G.effect g * P.effect a)) ψ‖ ^ 2) =
        (∑ g : Γ₂, ‖applyOperatorToState
            (heteroKron 1 (P.effect a * G.effect g)) ψ‖ ^ 2) +
          stateQForm ψ (heteroKron 1 (P.effect a * P.effect a)) -
          2 * ∑ g : Γ₂, stateQForm ψ (heteroKron 1
            (G.effect g * P.effect a * G.effect g * P.effect a)) := by
    intro a
    have h2 : (∑ g : Γ₂, stateQForm ψ (heteroKron 1
        (P.effect a * G.effect g * P.effect a))) =
        stateQForm ψ (heteroKron 1 (P.effect a * P.effect a)) := by
      rw [← stateQForm_finset_sum, ← heteroKron_finset_sum_right]
      congr 2
      rw [← Finset.sum_mul, ← Finset.mul_sum, G.sum_eq_one, mul_one]
    calc (∑ g : Γ₂, ‖applyOperatorToState (heteroKron 1
            (P.effect a * G.effect g - G.effect g * P.effect a)) ψ‖ ^ 2)
        = ∑ g : Γ₂, (‖applyOperatorToState
              (heteroKron 1 (P.effect a * G.effect g)) ψ‖ ^ 2 +
            stateQForm ψ (heteroKron 1 (P.effect a * G.effect g * P.effect a)) -
            2 * stateQForm ψ (heteroKron 1
              (G.effect g * P.effect a * G.effect g * P.effect a))) :=
          Finset.sum_congr rfl fun g _ => hpt a g
      _ = (∑ g : Γ₂, ‖applyOperatorToState
              (heteroKron 1 (P.effect a * G.effect g)) ψ‖ ^ 2) +
            (∑ g : Γ₂, stateQForm ψ
              (heteroKron 1 (P.effect a * G.effect g * P.effect a))) -
            2 * ∑ g : Γ₂, stateQForm ψ (heteroKron 1
              (G.effect g * P.effect a * G.effect g * P.effect a)) := by
          rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.mul_sum]
      _ = _ := by rw [h2]
  calc (∑ a : R₁, ∑ g : Γ₂, ‖applyOperatorToState (heteroKron 1
          (P.effect a * G.effect g - G.effect g * P.effect a)) ψ‖ ^ 2)
      = ∑ a : R₁, ((∑ g : Γ₂, ‖applyOperatorToState
            (heteroKron 1 (P.effect a * G.effect g)) ψ‖ ^ 2) +
          stateQForm ψ (heteroKron 1 (P.effect a * P.effect a)) -
          2 * ∑ g : Γ₂, stateQForm ψ (heteroKron 1
            (G.effect g * P.effect a * G.effect g * P.effect a))) :=
        Finset.sum_congr rfl fun a _ => hrow a
    _ = _ := by
        rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.mul_sum]

/-- The total mass of the ordered products of two measurements placed on the
second tensor factor is at most one. This bounds the first fine term of the
expansion of step 5 of the proof of the adopted statement in
`docs/paper-gaps/qpbt_pasting-product-error.tex`; blueprint
`ch12_qpbt_games.tex:960-990`. -/
theorem sum_norm_ordered_product_le_one {R₁ Γ₂ ι : Type*}
    [Fintype R₁] [DecidableEq R₁] [Fintype Γ₂] [DecidableEq Γ₂]
    [Fintype ι] [DecidableEq ι]
    (P : Measurement R₁ ι) (G : Measurement Γ₂ ι)
    (ψ : EuclideanSpace ℂ (ι × ι)) (hψ : ‖ψ‖ = 1) :
    (∑ a : R₁, ∑ g : Γ₂, ‖applyOperatorToState
      (heteroKron 1 (P.effect a * G.effect g)) ψ‖ ^ 2) ≤ 1 := by
  classical
  have hone : applyOperatorToState (1 : Op (ι × ι)) ψ = ψ := by
    simp [applyOperatorToState]
  have hCP : ∑ a : R₁, (heteroKron (1 : Op ι) (P.effect a))ᴴ *
      heteroKron 1 (P.effect a) ≤ 1 := by
    simpa using MIPStarRE.QPBT.measurement_sum_adjoint_mul_le_one
      (Measurement.rightPlacement (ιA := ι) P)
  have hCG : ∑ g : Γ₂, (heteroKron (1 : Op ι) (G.effect g))ᴴ *
      heteroKron 1 (G.effect g) ≤ 1 := by
    simpa using MIPStarRE.QPBT.measurement_sum_adjoint_mul_le_one
      (Measurement.rightPlacement (ιA := ι) G)
  rw [Finset.sum_comm]
  calc (∑ g : Γ₂, ∑ a : R₁, ‖applyOperatorToState
          (heteroKron 1 (P.effect a * G.effect g)) ψ‖ ^ 2)
      ≤ ∑ g : Γ₂, ‖applyOperatorToState (heteroKron 1 (G.effect g)) ψ‖ ^ 2 := by
        refine Finset.sum_le_sum fun g _ => ?_
        simpa [heteroKron_mul] using sum_norm_mul_apply_le
          (fun a : R₁ => heteroKron (1 : Op ι) (P.effect a))
          (heteroKron 1 (G.effect g)) ψ hCP
    _ ≤ 1 := by
        have h := sum_norm_mul_apply_le
          (fun g : Γ₂ => heteroKron (1 : Op ι) (G.effect g)) (1 : Op (ι × ι)) ψ hCG
        rw [hone, hψ, one_pow] at h
        simpa using h

end MIPStarRE.QPBT
