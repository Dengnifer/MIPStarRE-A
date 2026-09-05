import MIPStarRE.QPBT.Combining.Points.Orthonormalization

/-!
# Closeness estimates for the combined point measurements

Given projective measurements `Q^{x,z}` on each player's expanded local space
that are close to the sandwich POVMs on the placements where they were
constructed, this file assembles the three conclusions of `lem:qld-4-10` on
every pair of opposite placements by the triangle inequality along
`Q ≈ R ≈ M^Z M^X ≈ M^X M^Z` and the cross-placement consistency of the
ordered products.  It also records the trivial bound `4` on the state-dependent
distance of two square-summable families, used when the test error exceeds
one, and the elementary estimate collapsing the error terms `ε`, `√ε`, and
`(ε + √ε)^{1/4}` into a single power `ε^{1/8}` when `ε ≤ 1`.

## References

Paper `references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:838-881`
(self-consistency and consistency with `M̂` in the proof of `lem:qld-4-10`),
blueprint `blueprint/src/chapter/ch15_qpbt_combining.tex:803-960`; the route
is explained in `docs/paper-gaps/qpbt_linearity-theorem-quotation.tex`.
-/

open scoped BigOperators Matrix MatrixOrder ComplexOrder

namespace MIPStarRE.QPBT

open MIPStarRE.LDT hiding Measurement
open MIPStarRE.Quantum DistanceCalculus

noncomputable section

/-! ## The trivial bound -/

/-- A square-summable family of operators has total squared norm at most one on
a unit vector. -/
theorem sum_norm_apply_sq_le_one {α ι : Type*} [Fintype α] [Fintype ι]
    [DecidableEq ι] (A : α → Op ι) (ψ : EuclideanSpace ℂ ι) (hψ : ‖ψ‖ = 1)
    (hA : ∑ a, (A a)ᴴ * A a ≤ 1) :
    ∑ a, ‖applyOperatorToState (A a) ψ‖ ^ 2 ≤ 1 := by
  have h := sum_norm_mul_apply_le A 1 ψ hA
  simp only [mul_one, WinImplications.applyOperatorToState_one, hψ] at h
  simpa using h

/-- The state-dependent distance of two square-summable families is at most
`4` on a unit vector, under a uniform distribution. -/
theorem opFamilyDistSq_uniform_le_four {X α ι : Type*} [Fintype X] [DecidableEq X]
    [Nonempty X] [Fintype α] [Fintype ι] [DecidableEq ι]
    (A B : X → α → Op ι) (ψ : EuclideanSpace ℂ ι) (hψ : ‖ψ‖ = 1)
    (hA : ∀ x, ∑ a, (A x a)ᴴ * A x a ≤ 1) (hB : ∀ x, ∑ a, (B x a)ᴴ * B x a ≤ 1) :
    opFamilyDistSq (uniformDistribution X) A B ψ ≤ 4 := by
  unfold opFamilyDistSq
  calc avgOver (uniformDistribution X) (fun x =>
        ∑ a, ‖applyOperatorToState (A x a - B x a) ψ‖ ^ 2)
      ≤ avgOver (uniformDistribution X) (fun _ => (4 : ℝ)) := by
        refine avgOver_mono _ _ _ fun x => ?_
        have hA' := sum_norm_apply_sq_le_one (A x) ψ hψ (hA x)
        have hB' := sum_norm_apply_sq_le_one (B x) ψ hψ (hB x)
        have hpt : ∀ a, ‖applyOperatorToState (A x a - B x a) ψ‖ ^ 2 ≤
            2 * ‖applyOperatorToState (A x a) ψ‖ ^ 2 +
              2 * ‖applyOperatorToState (B x a) ψ‖ ^ 2 := by
          intro a
          have hsub : applyOperatorToState (A x a - B x a) ψ =
              applyOperatorToState (A x a) ψ - applyOperatorToState (B x a) ψ := by
            simp [applyOperatorToState]
          rw [hsub]
          have := norm_sub_le (applyOperatorToState (A x a) ψ)
            (applyOperatorToState (B x a) ψ)
          nlinarith [norm_nonneg (applyOperatorToState (A x a) ψ),
            norm_nonneg (applyOperatorToState (B x a) ψ),
            norm_nonneg (applyOperatorToState (A x a) ψ -
              applyOperatorToState (B x a) ψ),
            sq_nonneg (‖applyOperatorToState (A x a) ψ‖ -
              ‖applyOperatorToState (B x a) ψ‖)]
        calc ∑ a, ‖applyOperatorToState (A x a - B x a) ψ‖ ^ 2
            ≤ ∑ a, (2 * ‖applyOperatorToState (A x a) ψ‖ ^ 2 +
                2 * ‖applyOperatorToState (B x a) ψ‖ ^ 2) :=
              Finset.sum_le_sum fun a _ => hpt a
          _ = 2 * ∑ a, ‖applyOperatorToState (A x a) ψ‖ ^ 2 +
                2 * ∑ a, ‖applyOperatorToState (B x a) ψ‖ ^ 2 := by
              rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]
          _ ≤ 4 := by linarith
    _ = 4 := avgOver_uniform_const _

/-- The effects of a projective measurement, placed on a register pair, are
square-summable to the identity. -/
theorem ProjectiveSetting.sum_place_effect_conjTranspose_mul_self_le_one
    {P : AdmissibleParams} {ε : ℝ} (S : ProjectiveSetting P ε) (p : Placement)
    {α : Type*} [Fintype α] (M : Measurement α (S.ExpandedLocalSpace p.side))
    (hM : MIPStarRE.QPBT.Measurement.IsProjective M) :
    ∑ a, (S.place p (M.effect a))ᴴ * S.place p (M.effect a) ≤ 1 := by
  refine le_of_eq ?_
  calc ∑ a, (S.place p (M.effect a))ᴴ * S.place p (M.effect a)
      = ∑ a, S.place p (M.effect a) := by
        refine Finset.sum_congr rfl fun a _ => ?_
        rw [← S.place_conjTranspose, ← S.place_mul,
          (hM a).isSelfAdjoint.isHermitian.eq, (hM a).isIdempotentElem.eq]
    _ = 1 := by rw [← S.place_finsetSum, M.sum_eq_one, S.place_one]

/-- The products `A_a B_b` of the effects of two projective measurements on a
common space are square-summable to the identity. -/
theorem sum_mul_conjTranspose_mul_self_eq_one {α β ι : Type*} [Fintype α]
    [Fintype β] [Fintype ι] [DecidableEq ι]
    (A : Measurement α ι) (B : Measurement β ι)
    (hA : MIPStarRE.QPBT.Measurement.IsProjective A)
    (hB : MIPStarRE.QPBT.Measurement.IsProjective B) :
    ∑ ab : α × β, (A.effect ab.1 * B.effect ab.2)ᴴ * (A.effect ab.1 * B.effect ab.2) =
      1 := by
  have hpt : ∀ (a : α) (b : β),
      (A.effect a * B.effect b)ᴴ * (A.effect a * B.effect b) =
        B.effect b * A.effect a * B.effect b := by
    intro a b
    rw [Matrix.conjTranspose_mul, (hA a).isSelfAdjoint.isHermitian.eq,
      (hB b).isSelfAdjoint.isHermitian.eq, Matrix.mul_assoc _ _ (A.effect a * B.effect b),
      ← Matrix.mul_assoc (A.effect a) (A.effect a), (hA a).isIdempotentElem.eq,
      ← Matrix.mul_assoc]
  rw [Fintype.sum_prod_type_right]
  calc ∑ b : β, ∑ a : α, (A.effect a * B.effect b)ᴴ * (A.effect a * B.effect b)
      = ∑ b : β, B.effect b * (∑ a : α, A.effect a) * B.effect b := by
        refine Finset.sum_congr rfl fun b _ => ?_
        rw [Finset.mul_sum, Finset.sum_mul]
        exact Finset.sum_congr rfl fun a _ => hpt a b
    _ = 1 := by
        simp_rw [A.sum_eq_one, mul_one]
        rw [Finset.sum_congr rfl fun b _ => (hB b).isIdempotentElem.eq]
        exact B.sum_eq_one

/-- The products `B_b A_a` of the effects of two projective measurements on a
common space, indexed by the pair `(a, b)`, are square-summable to the
identity. -/
theorem sum_mul_conjTranspose_mul_self_eq_one' {α β ι : Type*} [Fintype α]
    [Fintype β] [Fintype ι] [DecidableEq ι]
    (A : Measurement α ι) (B : Measurement β ι)
    (hA : MIPStarRE.QPBT.Measurement.IsProjective A)
    (hB : MIPStarRE.QPBT.Measurement.IsProjective B) :
    ∑ ab : α × β, (B.effect ab.2 * A.effect ab.1)ᴴ * (B.effect ab.2 * A.effect ab.1) =
      1 := by
  have hpt : ∀ (a : α) (b : β),
      (B.effect b * A.effect a)ᴴ * (B.effect b * A.effect a) =
        A.effect a * B.effect b * A.effect a := by
    intro a b
    rw [Matrix.conjTranspose_mul, (hA a).isSelfAdjoint.isHermitian.eq,
      (hB b).isSelfAdjoint.isHermitian.eq, Matrix.mul_assoc _ _ (B.effect b * A.effect a),
      ← Matrix.mul_assoc (B.effect b) (B.effect b), (hB b).isIdempotentElem.eq,
      ← Matrix.mul_assoc]
  rw [Fintype.sum_prod_type]
  calc ∑ a : α, ∑ b : β, (B.effect b * A.effect a)ᴴ * (B.effect b * A.effect a)
      = ∑ a : α, A.effect a * (∑ b : β, B.effect b) * A.effect a := by
        refine Finset.sum_congr rfl fun a _ => ?_
        rw [Finset.mul_sum, Finset.sum_mul]
        exact Finset.sum_congr rfl fun b _ => hpt a b
    _ = 1 := by
        simp_rw [B.sum_eq_one, mul_one]
        rw [Finset.sum_congr rfl fun a _ => (hA a).isIdempotentElem.eq]
        exact A.sum_eq_one

/-! ## The chain of closeness estimates -/

namespace ProjectiveSetting

variable {P : AdmissibleParams} {ε : ℝ}

/-- The three closeness conclusions of `lem:qld-4-10` for a pair of projective
families close to the placed sandwiches: with `η` the closeness of `Q` to `R`
on every placement, `C₁ √ε` the closeness of `R` to the ordered product,
`C₂ √ε` the commutation error, and `C₃ ε` the cross-placement consistency of
the ordered products, the distances from `Q` on one placement to the two
ordered products and to `Q` on the opposite placement are bounded by explicit
combinations.  Paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:838-881`. -/
theorem chain_bounds (S : ProjectiveSetting P ε)
    (Q : (side : PlayerSide) → PointPair P →
      Measurement (PauliScalar P × PauliScalar P) (S.ExpandedLocalSpace side))
    (η C₁ C₂ C₃ : ℝ)
    (hQR : ∀ p : Placement, opFamilyDistSq (uniformDistribution (PointPair P))
      (fun xz (ab : PauliScalar P × PauliScalar P) =>
        S.place p ((Q p.side xz).effect ab))
      (fun xz ab => S.place p ((S.sandwichPoint p.side xz.1 xz.2).effect ab))
      S.psiHat ≤ η)
    (h₁ : ∀ p : Placement, opFamilyDistSq (uniformDistribution (PointPair P))
      (fun xz (ab : PauliScalar P × PauliScalar P) =>
        S.place p ((S.sandwichPoint p.side xz.1 xz.2).effect ab))
      (fun xz ab => S.place p
        ((S.pointMeasExp p.side .Z xz.2).effect ab.2 *
          (S.pointMeasExp p.side .X xz.1).effect ab.1))
      S.psiHat ≤ C₁ * Real.sqrt ε)
    (h₂ : ∀ p : Placement, opFamilyDistSq (uniformDistribution (PointPair P))
      (fun xz (ab : PauliScalar P × PauliScalar P) => S.place p
        ((S.pointMeasExp p.side .X xz.1).effect ab.1 *
          (S.pointMeasExp p.side .Z xz.2).effect ab.2))
      (fun xz ab => S.place p
        ((S.pointMeasExp p.side .Z xz.2).effect ab.2 *
          (S.pointMeasExp p.side .X xz.1).effect ab.1))
      S.psiHat ≤ C₂ * Real.sqrt ε)
    (h₃ : ∀ p₁ p₂ : Placement, p₁.IsOpposite p₂ →
      opFamilyDistSq (uniformDistribution (PointPair P))
        (fun xz (ab : PauliScalar P × PauliScalar P) => S.place p₁
          ((S.pointMeasExp p₁.side .Z xz.2).effect ab.2 *
            (S.pointMeasExp p₁.side .X xz.1).effect ab.1))
        (fun xz ab => S.place p₂
          ((S.pointMeasExp p₂.side .X xz.1).effect ab.1 *
            (S.pointMeasExp p₂.side .Z xz.2).effect ab.2))
        S.psiHat ≤ C₃ * ε)
    (p₁ p₂ : Placement) (hopp : p₁.IsOpposite p₂) :
    opFamilyDistSq (uniformDistribution (PointPair P))
        (fun xz (ab : PauliScalar P × PauliScalar P) =>
          S.place p₁ ((Q p₁.side xz).effect ab))
        (fun xz ab => S.place p₂
          ((S.pointMeasExp p₂.side .X xz.1).effect ab.1 *
            (S.pointMeasExp p₂.side .Z xz.2).effect ab.2))
        S.psiHat ≤ 2 * η + 4 * (C₁ * Real.sqrt ε) + 4 * (C₃ * ε) ∧
      opFamilyDistSq (uniformDistribution (PointPair P))
        (fun xz (ab : PauliScalar P × PauliScalar P) =>
          S.place p₁ ((Q p₁.side xz).effect ab))
        (fun xz ab => S.place p₂
          ((S.pointMeasExp p₂.side .Z xz.2).effect ab.2 *
            (S.pointMeasExp p₂.side .X xz.1).effect ab.1))
        S.psiHat ≤ 4 * η + 8 * (C₁ * Real.sqrt ε) + 8 * (C₃ * ε) +
          2 * (C₂ * Real.sqrt ε) ∧
      opFamilyDistSq (uniformDistribution (PointPair P))
        (fun xz (ab : PauliScalar P × PauliScalar P) =>
          S.place p₁ ((Q p₁.side xz).effect ab))
        (fun xz ab => S.place p₂ ((Q p₂.side xz).effect ab))
        S.psiHat ≤ 12 * η + 20 * (C₁ * Real.sqrt ε) + 16 * (C₃ * ε) +
          4 * (C₂ * Real.sqrt ε) := by
  -- `R_1 ≈ M^X M^Z` on the opposite placement
  have hRXZ := opFamilyDistSq_le_of_le_of_le (uniformDistribution (PointPair P))
    _ _ _ S.psiHat _ _ (h₁ p₁) (h₃ p₁ p₂ hopp)
  -- `Q_1 ≈ M^X M^Z` on the opposite placement
  have hQXZ := opFamilyDistSq_le_of_le_of_le (uniformDistribution (PointPair P))
    _ _ _ S.psiHat _ _ (hQR p₁) hRXZ
  -- `Q_1 ≈ M^Z M^X` on the opposite placement
  have hQZX := opFamilyDistSq_le_of_le_of_le (uniformDistribution (PointPair P))
    _ _ _ S.psiHat _ _ hQXZ (h₂ p₂)
  -- `M^Z M^X ≈ Q_2` on the opposite placement
  have hZXQ : opFamilyDistSq (uniformDistribution (PointPair P))
      (fun xz (ab : PauliScalar P × PauliScalar P) => S.place p₂
        ((S.pointMeasExp p₂.side .Z xz.2).effect ab.2 *
          (S.pointMeasExp p₂.side .X xz.1).effect ab.1))
      (fun xz ab => S.place p₂ ((Q p₂.side xz).effect ab))
      S.psiHat ≤ 2 * η + 2 * (C₁ * Real.sqrt ε) := by
    rw [opFamilyDistSq_symm]
    exact opFamilyDistSq_le_of_le_of_le (uniformDistribution (PointPair P))
      _ _ _ S.psiHat _ _ (hQR p₂) (h₁ p₂)
  have hQQ := opFamilyDistSq_le_of_le_of_le (uniformDistribution (PointPair P))
    _ _ _ S.psiHat _ _ hQZX hZXQ
  refine ⟨by linarith, by linarith, by linarith⟩

end ProjectiveSetting

/-! ## Collapsing the error terms into one power -/

/-- For `0 ≤ ε ≤ 1`, the error terms `ε`, `√ε`, and `(C₀ (ε + √ε))^{1/4}`
with `C₀ ≥ 1` are all bounded by multiples of `ε^{1/8}`. -/
theorem error_terms_le_rpow_eighth {ε C₀ : ℝ} (hε : 0 ≤ ε) (hε1 : ε ≤ 1)
    (hC₀ : 1 ≤ C₀) :
    ε ≤ Real.rpow ε (1 / 8 : ℝ) ∧ Real.sqrt ε ≤ Real.rpow ε (1 / 8 : ℝ) ∧
      Real.rpow (C₀ * (ε + Real.sqrt ε)) (1 / 4 : ℝ) ≤
        2 * C₀ * Real.rpow ε (1 / 8 : ℝ) := by
  rcases eq_or_lt_of_le hε with h0 | hpos
  · subst h0
    have h8 : Real.rpow (0 : ℝ) (1 / 8 : ℝ) = 0 := Real.zero_rpow (by norm_num)
    have h4 : Real.rpow (C₀ * (0 + Real.sqrt 0)) (1 / 4 : ℝ) = 0 := by
      rw [Real.sqrt_zero, add_zero, mul_zero]
      exact Real.zero_rpow (by norm_num)
    rw [h8, h4, Real.sqrt_zero]
    refine ⟨le_rfl, le_rfl, ?_⟩
    positivity
  · have hsqrt : Real.sqrt ε = Real.rpow ε (1 / 2 : ℝ) := Real.sqrt_eq_rpow ε
    have hε1' : Real.rpow ε 1 = ε := Real.rpow_one ε
    have hmono : ∀ y z : ℝ, z ≤ y → Real.rpow ε y ≤ Real.rpow ε z := fun y z hyz =>
      Real.rpow_le_rpow_of_exponent_ge hpos hε1 hyz
    refine ⟨?_, ?_, ?_⟩
    · exact le_of_eq_of_le hε1'.symm (hmono 1 (1 / 8) (by norm_num))
    · rw [hsqrt]
      exact hmono (1 / 2) (1 / 8) (by norm_num)
    · have hsum : ε + Real.sqrt ε ≤ 2 * Real.sqrt ε := by
        have : ε ≤ Real.sqrt ε := by
          rw [hsqrt]
          exact le_of_eq_of_le hε1'.symm (hmono 1 (1 / 2) (by norm_num))
        linarith
      have hC : 0 ≤ 2 * C₀ := by linarith
      calc Real.rpow (C₀ * (ε + Real.sqrt ε)) (1 / 4 : ℝ)
          ≤ Real.rpow (2 * C₀ * Real.sqrt ε) (1 / 4 : ℝ) := by
            apply Real.rpow_le_rpow (by positivity) _ (by norm_num)
            nlinarith [Real.sqrt_nonneg ε]
        _ = Real.rpow (2 * C₀) (1 / 4 : ℝ) * Real.rpow ε (1 / 8 : ℝ) := by
            change (2 * C₀ * Real.sqrt ε) ^ (1 / 4 : ℝ) =
              (2 * C₀) ^ (1 / 4 : ℝ) * ε ^ (1 / 8 : ℝ)
            rw [Real.mul_rpow hC (Real.sqrt_nonneg ε), Real.sqrt_eq_rpow,
              ← Real.rpow_mul hε]
            norm_num
        _ ≤ 2 * C₀ * Real.rpow ε (1 / 8 : ℝ) := by
            refine mul_le_mul_of_nonneg_right ?_ (Real.rpow_nonneg hε _)
            calc Real.rpow (2 * C₀) (1 / 4 : ℝ) ≤ Real.rpow (2 * C₀) 1 :=
                  Real.rpow_le_rpow_of_exponent_le (by linarith) (by norm_num)
              _ = 2 * C₀ := Real.rpow_one _

end

end MIPStarRE.QPBT
