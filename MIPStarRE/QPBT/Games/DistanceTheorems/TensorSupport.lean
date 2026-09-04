import MIPStarRE.QPBT.Games.DistanceTheorems.Support
import MIPStarRE.LDT.Basic.TensorPlacement

/-!
# Tensor support for the state-dependent distance calculus

This module collects tensor-placement, marginal, and finite-fiber identities
used in data processing and the commutator estimate.

## References

- `references/qpbt-paper/06_nonlocal_games_and_mipstar.tex:397-461`
- `blueprint/src/chapter/ch12_qpbt_games.tex:340-388`
-/

open scoped BigOperators Matrix MatrixOrder ComplexOrder

namespace MIPStarRE.QPBT.DistanceCalculus

open MIPStarRE.LDT MIPStarRE.Quantum

/-- The state quadratic form commutes with a finite-set sum. -/
private theorem stateQForm_finset_sum {κ ι : Type*}
    [Fintype ι] [DecidableEq ι]
    (ψ : EuclideanSpace ℂ ι) (s : Finset κ) (M : κ → Op ι) :
    stateQForm ψ (∑ k ∈ s, M k) = ∑ k ∈ s, stateQForm ψ (M k) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [stateQForm, applyOperatorToState]
  | @insert k s hk ih => simp [hk, stateQForm_add, ih]

/-- Lift a QPBT measurement to the left tensor factor. -/
noncomputable def leftPlacedMeasurement {α ιA ιB : Type*}
    [Fintype α] [Fintype ιA] [DecidableEq ιA]
    [Fintype ιB] [DecidableEq ιB]
    (M : MIPStarRE.Quantum.Measurement α ιA) :
    MIPStarRE.Quantum.Measurement α (ιA × ιB) :=
  MIPStarRE.Quantum.Measurement.ofSumEqOne
    (fun a => heteroKron (M.effect a) 1)
    (fun a => MIPStarRE.Quantum.kronecker_nonneg (M.pos a)
      (Matrix.PosSemidef.one.nonneg : 0 ≤ (1 : Op ιB)))
    (by
      change ∑ a : α, leftTensor (ι₂ := ιB) (M.effect a) = 1
      rw [leftTensor_finset_sum, M.sum_eq_one, leftTensor_one])

/-- Lift a QPBT measurement to the right tensor factor. -/
noncomputable def rightPlacedMeasurement {α ιA ιB : Type*}
    [Fintype α] [Fintype ιA] [DecidableEq ιA]
    [Fintype ιB] [DecidableEq ιB]
    (M : MIPStarRE.Quantum.Measurement α ιB) :
    MIPStarRE.Quantum.Measurement α (ιA × ιB) :=
  MIPStarRE.Quantum.Measurement.ofSumEqOne
    (fun a => heteroKron 1 (M.effect a))
    (fun a => MIPStarRE.Quantum.kronecker_nonneg
      (Matrix.PosSemidef.one.nonneg : 0 ≤ (1 : Op ιA)) (M.pos a))
    (by
      change ∑ a : α, rightTensor (ι₁ := ιA) (M.effect a) = 1
      rw [rightTensor_finset_sum, M.sum_eq_one, rightTensor_one])

/-- Products of left and right placements evaluate as a Kronecker product. -/
theorem placed_product_stateQForm_eq {ιA ιB : Type*}
    [Fintype ιA] [DecidableEq ιA]
    [Fintype ιB] [DecidableEq ιB]
    (ψ : EuclideanSpace ℂ (ιA × ιB)) (A : Op ιA) (B : Op ιB) :
    stateQForm ψ (heteroKron A 1 * heteroKron 1 B) =
      stateQForm ψ (heteroKron A B) := by
  congr 1
  exact leftTensor_mul_rightTensor_eq_opTensor A B

/-- The quadratic form of a tensor product of positive operators is nonnegative. -/
private theorem stateQForm_opTensor_nonneg {ιA ιB : Type*}
    [Fintype ιA] [DecidableEq ιA]
    [Fintype ιB] [DecidableEq ιB]
    (ψ : EuclideanSpace ℂ (ιA × ιB)) (A : Op ιA) (B : Op ιB)
    (hA : 0 ≤ A) (hB : 0 ≤ B) :
    0 ≤ stateQForm ψ (heteroKron A B) := by
  have hmono := quadratic_form_mono
    (show (0 : Op (ιA × ιB)) ≤ heteroKron A B by
      exact MIPStarRE.Quantum.kronecker_nonneg hA hB) ψ
  simpa [stateQForm, applyOperatorToState] using hmono

/-- Expand the overlap of two postprocessed effects over their fibers. -/
private theorem post_pair_stateQForm_expand {α β ιA ιB : Type*}
    [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    [Fintype ιA] [DecidableEq ιA]
    [Fintype ιB] [DecidableEq ιB]
    (ψ : EuclideanSpace ℂ (ιA × ιB))
    (A : MIPStarRE.Quantum.Measurement α ιA)
    (B : MIPStarRE.Quantum.Measurement α ιB) (f : α → β) (b c : β) :
    stateQForm ψ
        (heteroKron ((A.postprocess f).effect b) ((B.postprocess f).effect c)) =
      ∑ a ∈ Finset.univ.filter (fun a => f a = b),
        ∑ a' ∈ Finset.univ.filter (fun a' => f a' = c),
          stateQForm ψ (heteroKron (A.effect a) (B.effect a')) := by
  change stateQForm ψ
      (opTensor
        (∑ a ∈ Finset.univ.filter (fun a => f a = b), A.effect a)
        (∑ a' ∈ Finset.univ.filter (fun a' => f a' = c), B.effect a')) = _
  rw [opTensor_sum_left_finset, stateQForm_finset_sum]
  apply Finset.sum_congr rfl
  intro a _
  rw [opTensor_sum_right_finset, stateQForm_finset_sum]
  rfl

/-- Postprocessing can only increase diagonal tensor overlap. -/
theorem diagonal_postprocess_stateQForm_ge {α β ιA ιB : Type*}
    [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    [Fintype ιA] [DecidableEq ιA]
    [Fintype ιB] [DecidableEq ιB]
    (ψ : EuclideanSpace ℂ (ιA × ιB))
    (A : MIPStarRE.Quantum.Measurement α ιA)
    (B : MIPStarRE.Quantum.Measurement α ιB) (f : α → β) :
    (∑ b : β, stateQForm ψ
        (heteroKron ((A.postprocess f).effect b) ((B.postprocess f).effect b))) ≥
      ∑ a : α, stateQForm ψ (heteroKron (A.effect a) (B.effect a)) := by
  let fiber : β → Finset α := fun b =>
    Finset.univ.filter fun a => f a = b
  let diagTerm : α → ℝ := fun a =>
    stateQForm ψ (heteroKron (A.effect a) (B.effect a))
  let pairTerm : α → α → ℝ := fun a a' =>
    stateQForm ψ (heteroKron (A.effect a) (B.effect a'))
  let fiberDiag : β → ℝ := fun b => (fiber b).sum diagTerm
  let fiberPair : β → ℝ := fun b =>
    (fiber b).sum fun a => (fiber b).sum fun a' => pairTerm a a'
  have hdiag_le (b : β) : fiberDiag b ≤ fiberPair b := by
    dsimp [fiberDiag, fiberPair]
    refine Finset.sum_le_sum ?_
    intro a ha
    exact Finset.single_le_sum
      (fun a' _ => stateQForm_opTensor_nonneg ψ
        (A.effect a) (B.effect a') (A.pos a) (B.pos a')) ha
  calc
    ∑ a : α, stateQForm ψ (heteroKron (A.effect a) (B.effect a)) =
        ∑ b : β, fiberDiag b := by
      dsimp [fiberDiag, diagTerm, fiber]
      symm
      exact Finset.sum_fiberwise Finset.univ f
        (fun a => stateQForm ψ (heteroKron (A.effect a) (B.effect a)))
    _ ≤ ∑ b : β, fiberPair b :=
      Finset.sum_le_sum fun b _ => hdiag_le b
    _ = ∑ b : β, stateQForm ψ
        (heteroKron ((A.postprocess f).effect b)
          ((B.postprocess f).effect b)) := by
      apply Finset.sum_congr rfl
      intro b _
      dsimp [fiberPair, pairTerm, fiber]
      exact (post_pair_stateQForm_expand ψ A B f b b).symm

/-- Squared effects in one measurement fiber sum to at most the identity. -/
private theorem measurement_fiber_sum_adjoint_mul_le_one {α β ι : Type*}
    [Fintype α] [Fintype β] [Fintype ι] [DecidableEq ι]
    (M : MIPStarRE.Quantum.Measurement (α × β) ι) (a : α) :
    ∑ b : β, (M.effect (a, b))ᴴ * M.effect (a, b) ≤ 1 := by
  classical
  have hsquare_le (z : α × β) :
      (M.effect z)ᴴ * M.effect z ≤ M.effect z := by
    rw [measurement_effect_hermitian M z]
    exact MIPStarRE.Quantum.sq_le_self (M.pos z) (measurement_effect_le_one M z)
  calc
    ∑ b : β, (M.effect (a, b))ᴴ * M.effect (a, b) ≤
        ∑ b : β, M.effect (a, b) :=
      Finset.sum_le_sum fun b _ => hsquare_le (a, b)
    _ ≤ ∑ a' : α, ∑ b : β, M.effect (a', b) :=
      Finset.single_le_sum
        (fun a' _ => Finset.sum_nonneg fun b _ => M.pos (a', b))
        (Finset.mem_univ a)
    _ = ∑ z : α × β, M.effect z := (Fintype.sum_prod_type _).symm
    _ = 1 := M.sum_eq_one

/-- A left-placed measurement fiber is square-summable. -/
theorem left_fiber_contraction {α β ιA ιB : Type*}
    [Fintype α] [Fintype β]
    [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB]
    (M : MIPStarRE.Quantum.Measurement (α × β) ιA) (a : α) :
    (1 - ∑ b : β, (leftTensor (ι₂ := ιB) (M.effect (a, b)))ᴴ *
      leftTensor (ι₂ := ιB) (M.effect (a, b))).PosSemidef := by
  apply Matrix.nonneg_iff_posSemidef.mp
  rw [sub_nonneg]
  calc
    ∑ b : β, (leftTensor (ι₂ := ιB) (M.effect (a, b)))ᴴ *
          leftTensor (ι₂ := ιB) (M.effect (a, b)) =
        ∑ b : β, leftTensor (ι₂ := ιB)
          ((M.effect (a, b))ᴴ * M.effect (a, b)) := by
      apply Finset.sum_congr rfl
      intro b _
      rw [leftTensor_conjTranspose, leftTensor_mul_leftTensor]
    _ = leftTensor (ι₂ := ιB)
        (∑ b : β, (M.effect (a, b))ᴴ * M.effect (a, b)) :=
      leftTensor_finset_sum Finset.univ _
    _ ≤ leftTensor (ι₂ := ιB) (1 : Op ιA) :=
      leftTensor_mono (measurement_fiber_sum_adjoint_mul_le_one M a)
    _ = 1 := leftTensor_one

/-- A right-placed measurement fiber is square-summable. -/
theorem right_fiber_contraction {α β ιA ιB : Type*}
    [Fintype α] [Fintype β]
    [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB]
    (M : MIPStarRE.Quantum.Measurement (α × β) ιB) (a : α) :
    (1 - ∑ b : β, (rightTensor (ι₁ := ιA) (M.effect (a, b)))ᴴ *
      rightTensor (ι₁ := ιA) (M.effect (a, b))).PosSemidef := by
  apply Matrix.nonneg_iff_posSemidef.mp
  rw [sub_nonneg]
  calc
    ∑ b : β, (rightTensor (ι₁ := ιA) (M.effect (a, b)))ᴴ *
          rightTensor (ι₁ := ιA) (M.effect (a, b)) =
        ∑ b : β, rightTensor (ι₁ := ιA)
          ((M.effect (a, b))ᴴ * M.effect (a, b)) := by
      apply Finset.sum_congr rfl
      intro b _
      rw [rightTensor_conjTranspose, rightTensor_mul_rightTensor]
    _ = rightTensor (ι₁ := ιA)
        (∑ b : β, (M.effect (a, b))ᴴ * M.effect (a, b)) :=
      rightTensor_finset_sum Finset.univ _
    _ ≤ rightTensor (ι₁ := ιA) (1 : Op ιB) :=
      rightTensor_mono (measurement_fiber_sum_adjoint_mul_le_one M a)
    _ = 1 := rightTensor_one

/-- A projective effect survives exactly in its postprocessing fiber. -/
private theorem postprocess_effect_mul_effect {ζ α ι : Type*}
    [Fintype ζ] [DecidableEq ζ] [Fintype α] [DecidableEq α]
    [Fintype ι] [DecidableEq ι]
    (M : MIPStarRE.Quantum.Measurement ζ ι)
    (hM : MIPStarRE.QPBT.Measurement.IsProjective M)
    (f : ζ → α) (b : α) (z : ζ) :
    (M.postprocess f).effect b * M.effect z =
      if f z = b then M.effect z else 0 := by
  classical
  rw [MIPStarRE.Quantum.Measurement.postprocess_effect, Finset.sum_mul]
  calc
    ∑ y ∈ Finset.univ.filter (fun y => f y = b), M.effect y * M.effect z =
        ∑ y ∈ Finset.univ.filter (fun y => f y = b),
          if y = z then M.effect z else 0 := by
      apply Finset.sum_congr rfl
      intro y _
      by_cases hyz : y = z
      · subst y
        rw [if_pos rfl]
        exact (hM z).isIdempotentElem.eq
      · rw [if_neg hyz]
        exact projective_effect_mul_effect_eq_zero M hM hyz
    _ = if f z = b then M.effect z else 0 := by simp

/-- Compatible marginals of a projective joint measurement multiply to the joint effect. -/
theorem joint_marginal_product {α β γ ι : Type*}
    [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    [Fintype γ] [DecidableEq γ] [Fintype ι] [DecidableEq ι]
    (M : MIPStarRE.Quantum.Measurement ((α × β) × γ) ι)
    (hM : MIPStarRE.QPBT.Measurement.IsProjective M)
    (a : α) (b : β) (c : γ) :
    ((M.postprocess (fun abc => abc.1)).effect (a, b)) *
        ((M.postprocess (fun abc => (abc.1.1, abc.2))).effect (a, c)) =
      M.effect ((a, b), c) := by
  classical
  simp only [MIPStarRE.Quantum.Measurement.postprocess_effect]
  rw [Finset.mul_sum]
  calc
    ∑ z ∈ Finset.univ.filter (fun z : (α × β) × γ =>
        (z.1.1, z.2) = (a, c)),
        ((M.postprocess (fun abc => abc.1)).effect (a, b)) * M.effect z =
      ∑ z ∈ Finset.univ.filter (fun z : (α × β) × γ =>
        (z.1.1, z.2) = (a, c)), if z.1 = (a, b) then M.effect z else 0 := by
      apply Finset.sum_congr rfl
      intro z _
      exact postprocess_effect_mul_effect M hM (fun abc => abc.1) (a, b) z
    _ = M.effect ((a, b), c) := by
      rw [Finset.sum_eq_single ((a, b), c)]
      · simp
      · intro z hz hne
        have hzfiber := (Finset.mem_filter.mp hz).2
        rw [if_neg]
        intro hzfirst
        apply hne
        exact Prod.ext hzfirst (congrArg (fun p : α × γ => p.2) hzfiber)
      · simp

/-- Compatible projective marginals multiply to the joint effect in reverse order. -/
theorem joint_marginal_product_rev {α β γ ι : Type*}
    [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    [Fintype γ] [DecidableEq γ] [Fintype ι] [DecidableEq ι]
    (M : MIPStarRE.Quantum.Measurement ((α × β) × γ) ι)
    (hM : MIPStarRE.QPBT.Measurement.IsProjective M)
    (a : α) (b : β) (c : γ) :
    ((M.postprocess (fun abc => (abc.1.1, abc.2))).effect (a, c)) *
        ((M.postprocess (fun abc => abc.1)).effect (a, b)) =
      M.effect ((a, b), c) := by
  have habHerm := measurement_effect_hermitian
    (M.postprocess (fun abc => abc.1)) (a, b)
  have hacHerm := measurement_effect_hermitian
    (M.postprocess (fun abc => (abc.1.1, abc.2))) (a, c)
  have hjointHerm := measurement_effect_hermitian M ((a, b), c)
  have h := congrArg Matrix.conjTranspose (joint_marginal_product M hM a b c)
  rw [Matrix.conjTranspose_mul, hacHerm, habHerm, hjointHerm] at h
  exact h

/-- Operators placed on opposite tensor factors commute. -/
theorem left_right_commute {ιA ιB : Type*}
    [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB]
    (A : Op ιA) (B : Op ιB) :
    leftTensor (ι₂ := ιB) A * rightTensor (ι₁ := ιA) B =
      rightTensor (ι₁ := ιA) B * leftTensor (ι₂ := ιB) A := by
  rw [leftTensor_mul_rightTensor_eq_opTensor,
    rightTensor_mul_leftTensor_eq_opTensor]

/-- Reindexing an operator family along an equivalence preserves its distance. -/
theorem opFamilyDistSq_reindex {X α β ι : Type*}
    [Fintype α] [Fintype β] [Fintype ι] [DecidableEq ι]
    (μ : Distribution X) (e : α ≃ β) (A B : X → α → Op ι)
    (ψ : EuclideanSpace ℂ ι) :
    opFamilyDistSq μ A B ψ =
      opFamilyDistSq μ (fun x b => A x (e.symm b))
        (fun x b => B x (e.symm b)) ψ := by
  unfold opFamilyDistSq avgOver
  apply Finset.sum_congr rfl
  intro x _
  congr 1
  exact Fintype.sum_equiv e
    (fun a => ‖applyOperatorToState (A x a - B x a) ψ‖ ^ 2)
    (fun b => ‖applyOperatorToState (A x (e.symm b) - B x (e.symm b)) ψ‖ ^ 2)
    (by intro a; simp)

/-- Pointwise equal operator families have equal state-dependent distance. -/
theorem opFamilyDistSq_congr {X α ι : Type*}
    [Fintype α] [Fintype ι] [DecidableEq ι]
    (μ : Distribution X) (A B A' B' : X → α → Op ι)
    (ψ : EuclideanSpace ℂ ι)
    (hA : ∀ x a, A x a = A' x a) (hB : ∀ x a, B x a = B' x a) :
    opFamilyDistSq μ A B ψ = opFamilyDistSq μ A' B' ψ := by
  unfold opFamilyDistSq avgOver
  apply Finset.sum_congr rfl
  intro x _
  congr 1
  apply Finset.sum_congr rfl
  intro a _
  rw [hA x a, hB x a]

/-- Pointwise equal operator differences have equal state-dependent distance. -/
theorem opFamilyDistSq_congr_sub {X α ι : Type*}
    [Fintype α] [Fintype ι] [DecidableEq ι]
    (μ : Distribution X) (A B A' B' : X → α → Op ι)
    (ψ : EuclideanSpace ℂ ι)
    (h : ∀ x a, A x a - B x a = A' x a - B' x a) :
    opFamilyDistSq μ A B ψ = opFamilyDistSq μ A' B' ψ := by
  unfold opFamilyDistSq avgOver
  apply Finset.sum_congr rfl
  intro x _
  congr 1
  apply Finset.sum_congr rfl
  intro a _
  rw [h x a]

/-- Exchange the final two coordinates of a nested product. -/
def swapLast (α β γ : Type*) : ((α × γ) × β) ≃ ((α × β) × γ) where
  toFun p := ((p.1.1, p.2), p.1.2)
  invFun p := ((p.1.1, p.2), p.1.2)
  left_inv := by rintro ⟨⟨a, c⟩, b⟩; rfl
  right_inv := by rintro ⟨⟨a, b⟩, c⟩; rfl

/-- The inverse of `swapLast` has the same coordinate formula. -/
@[simp] theorem swapLast_symm_apply {α β γ : Type*}
    (p : (α × β) × γ) :
    (swapLast α β γ).symm p = ((p.1.1, p.2), p.1.2) :=
  rfl

end MIPStarRE.QPBT.DistanceCalculus
