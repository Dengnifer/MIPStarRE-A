import MIPStarRE.QPBT.Games.DistanceTheorems.Calculus
import MIPStarRE.QPBT.Games.DistanceTheorems.TensorSupport
import MIPStarRE.QPBT.Games.DistanceTheorems.ProjectiveRounding
import MIPStarRE.QPBT.Games.StrategyClasses
import MIPStarRE.LDT.Preliminaries.SwitchSandwichPrep.Core

/-! # State-dependent distance calculus

This module records the consistency and state-dependent distance estimates used
throughout the quantum Pauli basis test. The statements retain explicit
constants that the paper absorbs into asymptotic notation.

The operator-level inequalities they rest on live in
`MIPStarRE.QPBT.Games.DistanceTheorems.Calculus`.

## References

The source results are `fact:agreement` through
`lem:close-strategies-have-close-values` in
`blueprint/src/chapter/ch12_qpbt_games.tex:260-597`, with paper origin
`references/qpbt-paper/06_nonlocal_games_and_mipstar.tex:295-461` and
`:531-540`. The observable conversion lemmas come from
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:95-131`.
-/

open scoped BigOperators Matrix MatrixOrder ComplexOrder

namespace MIPStarRE.QPBT

open MIPStarRE.LDT hiding Measurement
open MIPStarRE.Quantum DistanceCalculus

/-- A selected sum of outcome probabilities changes by at most the square root
of the state-dependent distance when the first POVM family is projective. -/
private theorem abs_selected_value_sub_le_of_projective_left
    {X α ι : Type*} [Fintype X] [DecidableEq X]
    [Fintype α] [DecidableEq α] [Fintype ι] [DecidableEq ι]
    (μ : Distribution X) (hμ : μ.IsProbability)
    (A B : X → Measurement α ι) (ψ : EuclideanSpace ℂ ι)
    (hψ : ‖ψ‖ = 1) (selected : X → α → Prop)
    [∀ x a, Decidable (selected x a)]
    (hA : ∀ x, MIPStarRE.QPBT.Measurement.IsProjective (A x))
    (ζ : ℝ)
    (hAB : opFamilyDistSq μ (fun x a => (A x).effect a)
      (fun x a => (B x).effect a) ψ ≤ ζ) :
    |avgOver μ (fun x => ∑ a : α,
        if selected x a then stateQForm ψ ((A x).effect a) else 0) -
      avgOver μ (fun x => ∑ a : α,
        if selected x a then stateQForm ψ ((B x).effect a) else 0)| ≤
      2 * Real.sqrt ζ := by
  have hnorm_sq (M : Op ι) :
      ‖applyOperatorToState M ψ‖ ^ 2 = stateQForm ψ (Mᴴ * M) := by
    rw [@norm_sq_eq_re_inner ℂ]
    unfold stateQForm applyOperatorToState
    rw [Matrix.toEuclideanLin_conjTranspose_mul_self]
    change (inner ℂ (Matrix.toEuclideanLin M ψ) (Matrix.toEuclideanLin M ψ)).re =
      (inner ℂ ψ ((Matrix.toEuclideanLin M).adjoint
        (Matrix.toEuclideanLin M ψ))).re
    rw [LinearMap.adjoint_inner_right]
  have htotal (M : X → Measurement α ι) (x : X) :
      ∑ a : α, stateQForm ψ ((M x).effect a) = 1 := by
    calc
      ∑ a : α, stateQForm ψ ((M x).effect a) =
          stateQForm ψ (∑ a : α, (M x).effect a) := by
        simp [stateQForm, applyOperatorToState]
      _ = stateQForm ψ 1 := by rw [(M x).sum_eq_one]
      _ = 1 := by
        rw [stateQForm]
        simp [applyOperatorToState, hψ]
  let valueOn (M : X → Measurement α ι) (p : X → α → Prop)
      [∀ x a, Decidable (p x a)] : ℝ :=
    avgOver μ (fun x => ∑ a : α,
      if p x a then stateQForm ψ ((M x).effect a) else 0)
  have hone (p : X → α → Prop) [∀ x a, Decidable (p x a)] :
      valueOn A p ≤ valueOn B p + 2 * Real.sqrt ζ := by
    let u : X → α → EuclideanSpace ℂ ι :=
      fun x a => applyOperatorToState ((A x).effect a) ψ
    let w : X → α → EuclideanSpace ℂ ι :=
      fun x a => applyOperatorToState ((B x).effect a - (A x).effect a) ψ
    let cross : X → α → ℝ := fun x a => (inner ℂ (u x a) (w x a)).re
    have hA_norm (x : X) (a : α) :
        stateQForm ψ ((A x).effect a) = ‖u x a‖ ^ 2 := by
      symm
      calc
        ‖u x a‖ ^ 2 =
            stateQForm ψ (((A x).effect a)ᴴ * (A x).effect a) := by
          simpa only [u] using hnorm_sq ((A x).effect a)
        _ = stateQForm ψ ((A x).effect a) := by
          rw [measurement_effect_hermitian, (hA x a).isIdempotentElem.eq]
    have hB_norm_le (x : X) (a : α) :
        ‖applyOperatorToState ((B x).effect a) ψ‖ ^ 2 ≤
          stateQForm ψ ((B x).effect a) := by
      rw [hnorm_sq, measurement_effect_hermitian]
      exact quadratic_form_mono
        (MIPStarRE.Quantum.sq_le_self ((B x).pos a)
          (measurement_effect_le_one (B x) a)) ψ
    have hB_apply (x : X) (a : α) :
        applyOperatorToState ((B x).effect a) ψ = u x a + w x a := by
      simp [u, w, applyOperatorToState]
    have hpoint (x : X) (a : α) :
        stateQForm ψ ((A x).effect a) - stateQForm ψ ((B x).effect a) ≤
          -2 * cross x a := by
      rw [hA_norm x a]
      have hexpand :
          ‖applyOperatorToState ((B x).effect a) ψ‖ ^ 2 =
            ‖u x a‖ ^ 2 + 2 * cross x a + ‖w x a‖ ^ 2 := by
        rw [hB_apply x a, @norm_add_sq ℂ]
        rfl
      nlinarith [hB_norm_le x a, sq_nonneg ‖w x a‖]
    have hdiff : valueOn A p - valueOn B p ≤
        -2 * avgOver μ (fun x => ∑ a : α, if p x a then cross x a else 0) := by
      calc
        valueOn A p - valueOn B p = avgOver μ (fun x =>
            (∑ a : α, if p x a then stateQForm ψ ((A x).effect a) else 0) -
              ∑ a : α, if p x a then stateQForm ψ ((B x).effect a) else 0) := by
          simp [valueOn, avgOver, Finset.sum_sub_distrib, mul_sub]
        _ = avgOver μ (fun x => ∑ a : α, if p x a then
              stateQForm ψ ((A x).effect a) - stateQForm ψ ((B x).effect a)
            else 0) := by
          apply avgOver_congr
          intro x
          rw [← Finset.sum_sub_distrib]
          apply Finset.sum_congr rfl
          intro a _
          by_cases ha : p x a <;> simp [ha]
        _ ≤ avgOver μ (fun x => ∑ a : α,
            if p x a then -2 * cross x a else 0) := by
          apply avgOver_mono
          intro x
          apply Finset.sum_le_sum
          intro a _
          by_cases ha : p x a
          · simpa [ha] using hpoint x a
          · simp [ha]
        _ = -2 * avgOver μ (fun x => ∑ a : α,
            if p x a then cross x a else 0) := by
          rw [← avgOver_const_mul]
          apply avgOver_congr
          intro x
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro a _
          by_cases ha : p x a <;> simp [ha]
    have hcross_raw :=
      MIPStarRE.LDT.Preliminaries.weightedFinsetCauchySchwarz_on_selectedSupport
        μ p cross (fun x a => ‖u x a‖ ^ 2) (fun x a => ‖w x a‖ ^ 2)
        (fun x a _ => by
          calc
            |cross x a| ≤ ‖inner ℂ (u x a) (w x a)‖ := Complex.abs_re_le_norm _
            _ ≤ ‖u x a‖ * ‖w x a‖ := norm_inner_le_norm _ _
            _ = Real.sqrt (‖u x a‖ ^ 2) * Real.sqrt (‖w x a‖ ^ 2) := by
              rw [Real.sqrt_sq (norm_nonneg _), Real.sqrt_sq (norm_nonneg _)])
        (fun _ _ _ => sq_nonneg _) (fun _ _ _ => sq_nonneg _)
    have hu_avg :
        avgOver μ (fun x => ∑ a : α, if p x a then ‖u x a‖ ^ 2 else 0) ≤ 1 := by
      calc
        _ ≤ avgOver μ (fun _ => (1 : ℝ)) := by
          apply avgOver_mono
          intro x
          calc
            (∑ a : α, if p x a then ‖u x a‖ ^ 2 else 0) ≤
                ∑ a : α, ‖u x a‖ ^ 2 := by
              apply Finset.sum_le_sum
              intro a _
              by_cases ha : p x a <;> simp [ha]
            _ = ∑ a : α, stateQForm ψ ((A x).effect a) := by
              apply Finset.sum_congr rfl
              intro a _
              exact (hA_norm x a).symm
            _ = 1 := htotal A x
        _ = 1 := avgOver_const_of_isProbability μ hμ 1
    have hw_avg :
        avgOver μ (fun x => ∑ a : α, if p x a then ‖w x a‖ ^ 2 else 0) ≤ ζ := by
      calc
        _ ≤ avgOver μ (fun x => ∑ a : α, ‖w x a‖ ^ 2) := by
          apply avgOver_mono
          intro x
          apply Finset.sum_le_sum
          intro a _
          by_cases ha : p x a <;> simp [ha]
        _ = opFamilyDistSq μ (fun x a => (A x).effect a)
            (fun x a => (B x).effect a) ψ := by
          unfold opFamilyDistSq
          apply avgOver_congr
          intro x
          apply Finset.sum_congr rfl
          intro a _
          simp only [w]
          rw [show (B x).effect a - (A x).effect a =
              -((A x).effect a - (B x).effect a) by abel]
          simp only [applyOperatorToState, map_neg, LinearMap.neg_apply, norm_neg]
        _ ≤ ζ := hAB
    have hcross :
        |avgOver μ (fun x => ∑ a : α, if p x a then cross x a else 0)| ≤
          Real.sqrt ζ := by
      calc
        _ ≤ Real.sqrt
              (avgOver μ (fun x => ∑ a : α, if p x a then ‖u x a‖ ^ 2 else 0)) *
            Real.sqrt
              (avgOver μ (fun x => ∑ a : α, if p x a then ‖w x a‖ ^ 2 else 0)) :=
          hcross_raw
        _ ≤ 1 * Real.sqrt ζ := by
          exact mul_le_mul (by simpa using Real.sqrt_le_sqrt hu_avg)
            (Real.sqrt_le_sqrt hw_avg) (Real.sqrt_nonneg _) (by positivity)
        _ = Real.sqrt ζ := one_mul _
    have : valueOn A p - valueOn B p ≤ 2 * Real.sqrt ζ := by
      calc
        valueOn A p - valueOn B p ≤
            -2 * avgOver μ (fun x => ∑ a : α,
              if p x a then cross x a else 0) := hdiff
        _ ≤ 2 * |avgOver μ (fun x => ∑ a : α,
              if p x a then cross x a else 0)| := by
          nlinarith [neg_le_abs (avgOver μ (fun x => ∑ a : α,
            if p x a then cross x a else 0))]
        _ ≤ 2 * Real.sqrt ζ := mul_le_mul_of_nonneg_left hcross (by norm_num)
    linarith
  have hforward := hone selected
  let complement : X → α → Prop := fun x a => ¬ selected x a
  letI : ∀ x a, Decidable (complement x a) := fun x a => inferInstance
  have hbackward_complement := hone complement
  have hpartition (M : X → Measurement α ι) :
      valueOn M selected + valueOn M complement = 1 := by
    rw [← avgOver_add]
    calc
      avgOver μ (fun x =>
          (∑ a : α, if selected x a then stateQForm ψ ((M x).effect a) else 0) +
            ∑ a : α, if complement x a then stateQForm ψ ((M x).effect a) else 0) =
          avgOver μ (fun _ => (1 : ℝ)) := by
        apply avgOver_congr
        intro x
        rw [← Finset.sum_add_distrib]
        calc
          (∑ a : α,
              ((if selected x a then stateQForm ψ ((M x).effect a) else 0) +
                (if complement x a then stateQForm ψ ((M x).effect a) else 0))) =
              ∑ a : α, stateQForm ψ ((M x).effect a) := by
            apply Finset.sum_congr rfl
            intro a _
            by_cases ha : selected x a <;> simp [ha, complement]
          _ = 1 := htotal M x
      _ = 1 := avgOver_const_of_isProbability μ hμ 1
  have hresult : |valueOn A selected - valueOn B selected| ≤ 2 * Real.sqrt ζ := by
    rw [abs_le]
    constructor
    · nlinarith [hpartition A, hpartition B, hbackward_complement]
    · linarith
  simpa only [valueOn] using hresult

/-- Simultaneously reindexing a state and an operator preserves their quadratic form. -/
private theorem stateQForm_reindex
    {I J : Type*} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
    (e : I ≃ J) (ψ : EuclideanSpace ℂ I) (M : Op I) :
    stateQForm (reindexState e ψ) (reindexOp e.symm M) = stateQForm ψ M := by
  have hstate (j : J) : (reindexState e ψ).ofLp j = ψ.ofLp (e.symm j) := by
    rfl
  have hstate_star (j : J) : star (reindexState e ψ).ofLp j =
      star (ψ.ofLp (e.symm j)) := congrArg star (hstate j)
  have hop (j k : J) : reindexOp e.symm M j k = M (e.symm j) (e.symm k) := by
    rfl
  unfold stateQForm applyOperatorToState
  rw [EuclideanSpace.inner_eq_star_dotProduct, EuclideanSpace.inner_eq_star_dotProduct]
  change (Complex.re (∑ j : J,
      (∑ k : J, reindexOp e.symm M j k * (reindexState e ψ).ofLp k) *
        star (reindexState e ψ).ofLp j)) =
    Complex.re (∑ i : I, (∑ k : I, M i k * ψ.ofLp k) * star (ψ.ofLp i))
  simp_rw [hop, hstate, hstate_star]
  apply congrArg Complex.re
  have hinner (j : J) :
      (∑ k : J, M (e.symm j) (e.symm k) * ψ.ofLp (e.symm k)) =
        ∑ k : I, M (e.symm j) k * ψ.ofLp k :=
    e.symm.sum_comp (fun k : I => M (e.symm j) k * ψ.ofLp k)
  calc
    (∑ j : J, (∑ k : J, M (e.symm j) (e.symm k) * ψ.ofLp (e.symm k)) *
        star (ψ.ofLp (e.symm j))) =
      ∑ j : J, (∑ k : I, M (e.symm j) k * ψ.ofLp k) *
        star (ψ.ofLp (e.symm j)) := by simp_rw [hinner]
    _ = ∑ i : I, (∑ k : I, M i k * ψ.ofLp k) * star (ψ.ofLp i) :=
      e.symm.sum_comp (fun i : I => (∑ k : I, M i k * ψ.ofLp k) * star (ψ.ofLp i))

/-- The product POVM whose effects are Kronecker products of the two factor effects. -/
private noncomputable def tensorMeasurement
    {α β I J : Type*} [Fintype α] [Fintype β]
    [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
    (A : Measurement α I) (B : Measurement β J) :
    Measurement (α × β) (I × J) :=
  Measurement.ofSumEqOne
    (fun ab => heteroKron (A.effect ab.1) (B.effect ab.2))
    (fun ab => MIPStarRE.Quantum.kronecker_nonneg (A.pos ab.1) (B.pos ab.2))
    (by
      change ∑ ab : α × β, opTensor (A.effect ab.1) (B.effect ab.2) = 1
      rw [Fintype.sum_prod_type]
      calc
        (∑ a : α, ∑ b : β, opTensor (A.effect a) (B.effect b)) =
            ∑ a : α, leftTensor (A.effect a) *
              (∑ b : β, rightTensor (B.effect b)) := by
          apply Finset.sum_congr rfl
          intro a _
          rw [Matrix.mul_sum]
          apply Finset.sum_congr rfl
          intro b _
          exact (leftTensor_mul_rightTensor_eq_opTensor _ _).symm
        _ = 1 := by
          rw [rightTensor_finset_sum, B.sum_eq_one, rightTensor_one]
          simp_rw [Matrix.mul_one]
          rw [leftTensor_finset_sum, A.sum_eq_one, leftTensor_one])

/-- The product of two projective POVMs is projective. -/
private theorem tensorMeasurement_isProjective
    {α β I J : Type*} [Fintype α] [Fintype β]
    [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
    (A : Measurement α I) (B : Measurement β J)
    (hA : MIPStarRE.QPBT.Measurement.IsProjective A)
    (hB : MIPStarRE.QPBT.Measurement.IsProjective B) :
    MIPStarRE.QPBT.Measurement.IsProjective (tensorMeasurement A B) := by
  intro ab
  change IsProj (Matrix.kronecker (A.effect ab.1) (B.effect ab.2))
  refine { isIdempotentElem := ?_, isSelfAdjoint := ?_ }
  · calc
      Matrix.kronecker (A.effect ab.1) (B.effect ab.2) *
          Matrix.kronecker (A.effect ab.1) (B.effect ab.2) =
        Matrix.kronecker (A.effect ab.1 * A.effect ab.1)
          (B.effect ab.2 * B.effect ab.2) := by
            simpa using (Matrix.mul_kronecker_mul (A.effect ab.1) (A.effect ab.1)
              (B.effect ab.2) (B.effect ab.2)).symm
      _ = Matrix.kronecker (A.effect ab.1) (B.effect ab.2) := by
        rw [(hA ab.1).isIdempotentElem.eq, (hB ab.2).isIdempotentElem.eq]
  · exact (Matrix.IsHermitian.ext fun i j => by
      rcases i with ⟨i₁, i₂⟩
      rcases j with ⟨j₁, j₂⟩
      simp [Matrix.kronecker, (hA ab.1).isSelfAdjoint.isHermitian.apply,
        (hB ab.2).isSelfAdjoint.isHermitian.apply]).isSelfAdjoint

/-- Transport a POVM along an equivalence of its finite-dimensional coordinate type. -/
private noncomputable def reindexMeasurement
    {α I J : Type*} [Fintype α]
    [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
    (e : I ≃ J) (M : Measurement α J) : Measurement α I :=
  Measurement.ofSumEqOne
    (fun a => reindexOp e (M.effect a))
    (fun a => MIPStarRE.Quantum.reindex_nonneg e.symm (M.pos a))
    (by
      change ∑ a : α, (Matrix.reindexAlgEquiv ℂ ℂ e.symm) (M.effect a) = 1
      rw [← map_sum, M.sum_eq_one, map_one])

/-- Reindexing a projective POVM preserves projectivity. -/
private theorem reindexMeasurement_isProjective
    {α I J : Type*} [Fintype α]
    [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
    (e : I ≃ J) (M : Measurement α J)
    (hM : MIPStarRE.QPBT.Measurement.IsProjective M) :
    MIPStarRE.QPBT.Measurement.IsProjective (reindexMeasurement e M) := by
  intro a
  change IsProj (reindexOp e (M.effect a))
  refine { isIdempotentElem := ?_, isSelfAdjoint := ?_ }
  · change (Matrix.reindexAlgEquiv ℂ ℂ e.symm) (M.effect a) *
        (Matrix.reindexAlgEquiv ℂ ℂ e.symm) (M.effect a) =
      (Matrix.reindexAlgEquiv ℂ ℂ e.symm) (M.effect a)
    rw [← map_mul, (hM a).isIdempotentElem.eq]
  · exact (Matrix.IsHermitian.ext fun i j => by
      simp [reindexOp, Matrix.reindex_apply,
        (hM a).isSelfAdjoint.isHermitian.apply]).isSelfAdjoint

/-- The sum of the squared effects of a POVM is bounded by the identity. -/
private theorem measurement_sum_adjoint_mul_le_one
    {α I : Type*} [Fintype α] [Fintype I] [DecidableEq I]
    (M : Measurement α I) :
    ∑ a : α, (M.effect a)ᴴ * M.effect a ≤ 1 := by
  calc
    ∑ a : α, (M.effect a)ᴴ * M.effect a ≤ ∑ a : α, M.effect a := by
      apply Finset.sum_le_sum
      intro a _
      rw [measurement_effect_hermitian]
      exact MIPStarRE.Quantum.sq_le_self (M.pos a) (measurement_effect_le_one M a)
    _ = 1 := M.sum_eq_one

/-- Right tensor placement preserves the square-summability bound for POVM effects. -/
private theorem rightPlacedMeasurement_sum_adjoint_mul_le_one
    {α I J : Type*} [Fintype α]
    [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
    (M : Measurement α J) :
    ∑ a : α, (rightTensor (ι₁ := I) (M.effect a))ᴴ *
        rightTensor (ι₁ := I) (M.effect a) ≤ 1 := by
  calc
    ∑ a : α, (rightTensor (ι₁ := I) (M.effect a))ᴴ *
          rightTensor (ι₁ := I) (M.effect a) =
        rightTensor (ι₁ := I) (∑ a : α, (M.effect a)ᴴ * M.effect a) := by
      rw [← rightTensor_finset_sum]
      apply Finset.sum_congr rfl
      intro a _
      rw [rightTensor_conjTranspose, rightTensor_mul_rightTensor]
    _ ≤ rightTensor (ι₁ := I) (1 : Op J) :=
      rightTensor_mono (measurement_sum_adjoint_mul_le_one M)
    _ = 1 := rightTensor_one

/-- Left tensor placement preserves the square-summability bound for POVM effects. -/
private theorem leftPlacedMeasurement_sum_adjoint_mul_le_one
    {α I J : Type*} [Fintype α]
    [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
    (M : Measurement α I) :
    ∑ a : α, (leftTensor (ι₂ := J) (M.effect a))ᴴ *
        leftTensor (ι₂ := J) (M.effect a) ≤ 1 := by
  calc
    ∑ a : α, (leftTensor (ι₂ := J) (M.effect a))ᴴ *
          leftTensor (ι₂ := J) (M.effect a) =
        leftTensor (ι₂ := J) (∑ a : α, (M.effect a)ᴴ * M.effect a) := by
      rw [← leftTensor_finset_sum]
      apply Finset.sum_congr rfl
      intro a _
      rw [leftTensor_conjTranspose, leftTensor_mul_leftTensor]
    _ ≤ leftTensor (ι₂ := J) (1 : Op I) :=
      leftTensor_mono (measurement_sum_adjoint_mul_le_one M)
    _ = 1 := leftTensor_one

/-- Tensoring a left-side POVM perturbation with a fixed right POVM does not
increase state-dependent family distance. -/
private theorem opFamilyDistSq_tensor_left_le
    {X Y α β I J : Type*} [DecidableEq X]
    [Fintype α] [Fintype β]
    [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
    (μ : Distribution (X × Y)) (A A' : X → Measurement α I)
    (B : Y → Measurement β J) (ψ : EuclideanSpace ℂ (I × J)) (δ : ℝ)
    (h : opFamilyDistSq (μ.map Prod.fst)
      (fun x a => leftTensor ((A x).effect a))
      (fun x a => leftTensor ((A' x).effect a)) ψ ≤ δ) :
    opFamilyDistSq μ
      (fun xy ab => (tensorMeasurement (A xy.1) (B xy.2)).effect ab)
      (fun xy ab => (tensorMeasurement (A' xy.1) (B xy.2)).effect ab) ψ ≤ δ := by
  unfold opFamilyDistSq at h ⊢
  calc
    avgOver μ (fun xy => ∑ ab : α × β,
        ‖applyOperatorToState
          ((tensorMeasurement (A xy.1) (B xy.2)).effect ab -
            (tensorMeasurement (A' xy.1) (B xy.2)).effect ab) ψ‖ ^ 2) ≤
      avgOver μ (fun xy => ∑ a : α,
        ‖applyOperatorToState
          (leftTensor ((A xy.1).effect a) - leftTensor ((A' xy.1).effect a)) ψ‖ ^ 2) := by
      apply avgOver_mono
      intro xy
      rw [Fintype.sum_prod_type]
      apply Finset.sum_le_sum
      intro a _
      have hcontract := sum_norm_mul_apply_le
        (fun b : β => rightTensor (ι₁ := I) ((B xy.2).effect b))
        (leftTensor ((A xy.1).effect a) - leftTensor ((A' xy.1).effect a)) ψ
        (rightPlacedMeasurement_sum_adjoint_mul_le_one (I := I) (B xy.2))
      apply le_trans ?_ hcontract
      apply le_of_eq
      apply Finset.sum_congr rfl
      intro b _
      change ‖applyOperatorToState
          (opTensor ((A xy.1).effect a) ((B xy.2).effect b) -
            opTensor ((A' xy.1).effect a) ((B xy.2).effect b)) ψ‖ ^ 2 = _
      congr 2
      rw [Matrix.mul_sub, rightTensor_mul_leftTensor_eq_opTensor,
        rightTensor_mul_leftTensor_eq_opTensor, opTensor_sub_left]
    _ = avgOver (μ.map Prod.fst) (fun x => ∑ a : α,
        ‖applyOperatorToState
          (leftTensor ((A x).effect a) - leftTensor ((A' x).effect a)) ψ‖ ^ 2) := by
      exact (Distribution.avgOver_map μ Prod.fst (fun x => ∑ a : α,
        ‖applyOperatorToState
          (leftTensor ((A x).effect a) - leftTensor ((A' x).effect a)) ψ‖ ^ 2)).symm
    _ ≤ δ := h

/-- Tensoring a right-side POVM perturbation with a fixed left POVM does not
increase state-dependent family distance. -/
private theorem opFamilyDistSq_tensor_right_le
    {X Y α β I J : Type*} [DecidableEq Y]
    [Fintype α] [Fintype β]
    [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
    (μ : Distribution (X × Y)) (A : X → Measurement α I)
    (B B' : Y → Measurement β J) (ψ : EuclideanSpace ℂ (I × J)) (δ : ℝ)
    (h : opFamilyDistSq (μ.map Prod.snd)
      (fun y b => rightTensor ((B y).effect b))
      (fun y b => rightTensor ((B' y).effect b)) ψ ≤ δ) :
    opFamilyDistSq μ
      (fun xy ab => (tensorMeasurement (A xy.1) (B xy.2)).effect ab)
      (fun xy ab => (tensorMeasurement (A xy.1) (B' xy.2)).effect ab) ψ ≤ δ := by
  unfold opFamilyDistSq at h ⊢
  calc
    avgOver μ (fun xy => ∑ ab : α × β,
        ‖applyOperatorToState
          ((tensorMeasurement (A xy.1) (B xy.2)).effect ab -
            (tensorMeasurement (A xy.1) (B' xy.2)).effect ab) ψ‖ ^ 2) ≤
      avgOver μ (fun xy => ∑ b : β,
        ‖applyOperatorToState
          (rightTensor ((B xy.2).effect b) - rightTensor ((B' xy.2).effect b)) ψ‖ ^ 2) := by
      apply avgOver_mono
      intro xy
      rw [Fintype.sum_prod_type, Finset.sum_comm]
      apply Finset.sum_le_sum
      intro b _
      have hcontract := sum_norm_mul_apply_le
        (fun a : α => leftTensor (ι₂ := J) ((A xy.1).effect a))
        (rightTensor ((B xy.2).effect b) - rightTensor ((B' xy.2).effect b)) ψ
        (leftPlacedMeasurement_sum_adjoint_mul_le_one (J := J) (A xy.1))
      apply le_trans ?_ hcontract
      apply le_of_eq
      apply Finset.sum_congr rfl
      intro a _
      change ‖applyOperatorToState
          (opTensor ((A xy.1).effect a) ((B xy.2).effect b) -
            opTensor ((A xy.1).effect a) ((B' xy.2).effect b)) ψ‖ ^ 2 = _
      congr 2
      rw [Matrix.mul_sub, leftTensor_mul_rightTensor_eq_opTensor,
        leftTensor_mul_rightTensor_eq_opTensor]
    _ = avgOver (μ.map Prod.snd) (fun y => ∑ b : β,
        ‖applyOperatorToState
          (rightTensor ((B y).effect b) - rightTensor ((B' y).effect b)) ψ‖ ^ 2) := by
      exact (Distribution.avgOver_map μ Prod.snd (fun y => ∑ b : β,
        ‖applyOperatorToState
          (rightTensor ((B y).effect b) - rightTensor ((B' y).effect b)) ψ‖ ^ 2)).symm
    _ ≤ δ := h

/-- Reindexing a Kronecker product factorizes over the coordinate equivalences. -/
private theorem reindexOp_heteroKron
    {I I' J J' : Type*}
    (eI : I ≃ I') (eJ : J ≃ J') (A : Op I') (B : Op J') :
    reindexOp (Equiv.prodCongr eI eJ) (heteroKron A B) =
      heteroKron (reindexOp eI A) (reindexOp eJ B) := by
  rfl

/-- Strategy value as a selected sum over the product POVM. -/
private theorem strategy_value_eq_selected (G : Game) (S : Strategy G) :
    S.value = avgOver G.μ (fun xy => ∑ ab : G.AnswerA × G.AnswerB,
      if G.decide xy.1 xy.2 ab.1 ab.2 then
        stateQForm S.ψ ((tensorMeasurement (S.A xy.1) (S.B xy.2)).effect ab)
      else 0) := by
  unfold Strategy.value
  apply avgOver_congr
  intro xy
  rw [Fintype.sum_prod_type]
  rfl

/-- Strategies on identified local spaces and the same transported state have
close values. The asymptotic constant is universal for the game. This is
`lem:close-strategies-have-close-values`, blueprint
`ch12_qpbt_games.tex:584-597`, paper
`references/qpbt-paper/06_nonlocal_games_and_mipstar.tex:531-540`. -/
theorem abs_value_sub_le_of_areClose :
    ∃ C₀ : ℝ, 1 ≤ C₀ ∧ ∀ (G : Game) (S S' : Strategy G) (δ : ℝ)
      (_hδ0 : 0 ≤ δ) (_hδ1 : δ ≤ 1) (hclose : AreCloseStrategies G S S' δ),
      reindexState (Equiv.prodCongr (Equiv.cast hclose.hA).symm
        (Equiv.cast hclose.hB).symm) S'.ψ = S.ψ →
      (S.IsProjective ∨ S'.IsProjective) →
      |S.value - S'.value| ≤ C₀ * Real.rpow δ (1 / 2 : ℝ) := by
  refine ⟨4, by norm_num, ?_⟩
  intro G S S' δ hδ0 _hδ1 hclose hstate hprojective
  let eA : S.ιA ≃ S'.ιA := Equiv.cast hclose.hA
  let eB : S.ιB ≃ S'.ιB := Equiv.cast hclose.hB
  let A' : G.QuestionA → Measurement G.AnswerA S.ιA :=
    fun x => reindexMeasurement eA (S'.A x)
  let B' : G.QuestionB → Measurement G.AnswerB S.ιB :=
    fun y => reindexMeasurement eB (S'.B y)
  have hstate' : reindexState (Equiv.prodCongr eA eB).symm S'.ψ = S.ψ := by
    convert hstate using 1
    ext ij
    rfl
  let JS : G.QuestionA × G.QuestionB → G.AnswerA × G.AnswerB →
      Op (S.ιA × S.ιB) := fun xy ab =>
    (tensorMeasurement (S.A xy.1) (S.B xy.2)).effect ab
  let JM : G.QuestionA × G.QuestionB → G.AnswerA × G.AnswerB →
      Op (S.ιA × S.ιB) := fun xy ab =>
    (tensorMeasurement (S.A xy.1) (B' xy.2)).effect ab
  let JT : G.QuestionA × G.QuestionB → G.AnswerA × G.AnswerB →
      Op (S.ιA × S.ιB) := fun xy ab =>
    (tensorMeasurement (A' xy.1) (B' xy.2)).effect ab
  have hAlice : opFamilyDistSq (G.μ.map Prod.fst)
      (fun x a => leftTensor ((S.A x).effect a))
      (fun x a => leftTensor ((A' x).effect a)) S.ψ ≤ δ := by
    change opFamilyDistSq (G.μ.map Prod.fst)
      (fun x a => heteroKron ((S.A x).effect a) 1)
      (fun x a => heteroKron (reindexOp eA ((S'.A x).effect a)) 1) S.ψ ≤ δ
    exact hclose.alice
  have hBob : opFamilyDistSq (G.μ.map Prod.snd)
      (fun y b => rightTensor ((S.B y).effect b))
      (fun y b => rightTensor ((B' y).effect b)) S.ψ ≤ δ := by
    change opFamilyDistSq (G.μ.map Prod.snd)
      (fun y b => heteroKron 1 ((S.B y).effect b))
      (fun y b => heteroKron 1 (reindexOp eB ((S'.B y).effect b))) S.ψ ≤ δ
    exact hclose.bob
  have hBobJoint : opFamilyDistSq G.μ JS JM S.ψ ≤ δ := by
    simpa only [JS, JM] using opFamilyDistSq_tensor_right_le
      G.μ S.A S.B B' S.ψ δ hBob
  have hAliceJoint : opFamilyDistSq G.μ JM JT S.ψ ≤ δ := by
    simpa only [JM, JT] using opFamilyDistSq_tensor_left_le
      G.μ S.A A' B' S.ψ δ hAlice
  have hJoint : opFamilyDistSq G.μ JS JT S.ψ ≤ 4 * δ := by
    have h := opFamilyDistSq_le_of_le_of_le G.μ JS JM JT S.ψ δ δ
      hBobJoint hAliceJoint
    linarith
  let selected : G.QuestionA × G.QuestionB → G.AnswerA × G.AnswerB → Prop :=
    fun xy ab => G.decide xy.1 xy.2 ab.1 ab.2 = true
  letI : ∀ xy ab, Decidable (selected xy ab) := fun _ _ => inferInstance
  have hSValue : S.value = avgOver G.μ (fun xy => ∑ ab : G.AnswerA × G.AnswerB,
      if selected xy ab then stateQForm S.ψ (JS xy ab) else 0) := by
    simpa only [selected, Bool.if_true_right, JS] using strategy_value_eq_selected G S
  have hS'Value : S'.value = avgOver G.μ (fun xy => ∑ ab : G.AnswerA × G.AnswerB,
      if selected xy ab then stateQForm S.ψ (JT xy ab) else 0) := by
    rw [strategy_value_eq_selected G S']
    apply avgOver_congr
    intro xy
    apply Finset.sum_congr rfl
    intro ab _
    by_cases hwins : selected xy ab
    · have hwins' : G.decide xy.1 xy.2 ab.1 ab.2 = true := by
        simpa only [selected] using hwins
      simp only [hwins', hwins, if_true]
      change stateQForm S'.ψ
          (heteroKron ((S'.A xy.1).effect ab.1) ((S'.B xy.2).effect ab.2)) =
        stateQForm S.ψ
          (heteroKron (reindexOp eA ((S'.A xy.1).effect ab.1))
            (reindexOp eB ((S'.B xy.2).effect ab.2)))
      calc
        _ = stateQForm
            (reindexState (Equiv.prodCongr eA eB).symm S'.ψ)
            (reindexOp (Equiv.prodCongr eA eB)
              (heteroKron ((S'.A xy.1).effect ab.1)
                ((S'.B xy.2).effect ab.2))) :=
          (stateQForm_reindex (Equiv.prodCongr eA eB).symm S'.ψ _).symm
        _ = _ := by
          rw [hstate', reindexOp_heteroKron]
    · simp [hwins, selected] at *
  have hselected : |S.value - S'.value| ≤ 2 * Real.sqrt (4 * δ) := by
    rcases hprojective with hproj | hproj
    · rw [hSValue, hS'Value]
      exact abs_selected_value_sub_le_of_projective_left G.μ G.μ_prob
        (fun xy => tensorMeasurement (S.A xy.1) (S.B xy.2))
        (fun xy => tensorMeasurement (A' xy.1) (B' xy.2)) S.ψ S.ψ_norm
        selected (fun xy => tensorMeasurement_isProjective _ _ (hproj.1 xy.1)
          (hproj.2 xy.2)) (4 * δ) hJoint
    · rw [hSValue, hS'Value, abs_sub_comm]
      apply abs_selected_value_sub_le_of_projective_left G.μ G.μ_prob
        (fun xy => tensorMeasurement (A' xy.1) (B' xy.2))
        (fun xy => tensorMeasurement (S.A xy.1) (S.B xy.2)) S.ψ S.ψ_norm
        selected
      · intro xy
        exact tensorMeasurement_isProjective _ _
          (reindexMeasurement_isProjective eA _ (hproj.1 xy.1))
          (reindexMeasurement_isProjective eB _ (hproj.2 xy.2))
      · rw [opFamilyDistSq_symm]
        exact hJoint
  have hsqrt : Real.sqrt (4 * δ) = 2 * Real.sqrt δ := by
    rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 4)]
    norm_num
  calc
    |S.value - S'.value| ≤ 2 * Real.sqrt (4 * δ) := hselected
    _ = 4 * Real.sqrt δ := by rw [hsqrt]; ring
    _ = 4 * Real.rpow δ (1 / 2 : ℝ) :=
      congrArg (fun x : ℝ => 4 * x) (Real.sqrt_eq_rpow δ)

/-- Averaging contractions preserves state-dependent operator closeness.
This is `lem:avg-closeness`, blueprint
`blueprint/src/chapter/ch14_qpbt_observables.tex:304-325`, paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:100-113`.
The probability hypothesis is explicit because the proof uses Jensen's
inequality for the average. -/
theorem avg_closeness {X ι : Type*}
    [Fintype X] [DecidableEq X] [Fintype ι] [DecidableEq ι]
    (μ : Distribution X) (hμ : μ.IsProbability) (A B : X → Op ι)
    (α : X → ℂ) (hα : ∀ x, ‖α x‖ ≤ 1) (ψ : EuclideanSpace ℂ ι) :
    ‖applyOperatorToState
        (averageOperatorOverDistribution μ fun x =>
          α x • (A x - B x)) ψ‖ ^ 2 ≤
      opDistSq μ A B ψ := by
  let v : X → EuclideanSpace ℂ ι :=
    fun x => applyOperatorToState (A x - B x) ψ
  have happly :
      applyOperatorToState
          (averageOperatorOverDistribution μ fun x => α x • (A x - B x)) ψ =
        ∑ x ∈ μ.support, μ.weight x • (α x • v x) := by
    unfold averageOperatorOverDistribution applyOperatorToState
    rw [map_sum]
    simp only [LinearMap.sum_apply]
    apply Finset.sum_congr rfl
    intro x _
    rw [← smul_assoc, map_smul]
    simp only [v, applyOperatorToState, Complex.real_smul, map_sub,
      LinearMap.smul_apply, LinearMap.sub_apply]
    rw [← smul_assoc, Complex.real_smul]
  have hnorm :
      ‖∑ x ∈ μ.support, μ.weight x • (α x • v x)‖ ≤
        ∑ x ∈ μ.support, μ.weight x * ‖v x‖ := by
    calc
      ‖∑ x ∈ μ.support, μ.weight x • (α x • v x)‖ ≤
          ∑ x ∈ μ.support, ‖μ.weight x • (α x • v x)‖ :=
        norm_sum_le μ.support _
      _ ≤ ∑ x ∈ μ.support, μ.weight x * ‖v x‖ := by
        apply Finset.sum_le_sum
        intro x _
        rw [norm_smul_of_nonneg (μ.nonnegative x), norm_smul]
        exact mul_le_mul_of_nonneg_left
          (by simpa only [one_mul] using
            mul_le_of_le_one_left (norm_nonneg (v x)) (hα x))
          (μ.nonnegative x)
  have hrhs_nonneg :
      0 ≤ ∑ x ∈ μ.support, μ.weight x * ‖v x‖ ^ 2 :=
    Finset.sum_nonneg fun x _ => mul_nonneg (μ.nonnegative x) (sq_nonneg _)
  have havg_norm :
      |avgOver μ (fun x => ‖v x‖)| ≤
        Real.sqrt (avgOver μ (fun x => ‖v x‖ ^ 2)) := by
    exact MIPStarRE.LDT.Preliminaries.avgOver_abs_le_sqrt_of_pointwise μ
      (fun x => ‖v x‖) (fun x => ‖v x‖ ^ 2)
      (fun x => by rw [abs_norm, Real.sqrt_sq_eq_abs, abs_norm])
      (fun x => sq_nonneg ‖v x‖) (by rw [hμ.weight_sum_eq_one])
  have hnorm_sqrt :
      ‖∑ x ∈ μ.support, μ.weight x • (α x • v x)‖ ≤
        Real.sqrt (∑ x ∈ μ.support, μ.weight x * ‖v x‖ ^ 2) := by
    calc
      ‖∑ x ∈ μ.support, μ.weight x • (α x • v x)‖ ≤
          ∑ x ∈ μ.support, μ.weight x * ‖v x‖ := hnorm
      _ ≤ |avgOver μ (fun x => ‖v x‖)| := le_abs_self _
      _ ≤ Real.sqrt (avgOver μ (fun x => ‖v x‖ ^ 2)) := havg_norm
  rw [happly]
  unfold opDistSq opFamilyDistSq avgOver
  simp only [Fintype.sum_unique]
  change ‖∑ x ∈ μ.support, μ.weight x • (α x • v x)‖ ^ 2 ≤
    ∑ x ∈ μ.support, μ.weight x * ‖v x‖ ^ 2
  calc
    ‖∑ x ∈ μ.support, μ.weight x • (α x • v x)‖ ^ 2 ≤
        (Real.sqrt (∑ x ∈ μ.support, μ.weight x * ‖v x‖ ^ 2)) ^ 2 :=
      (sq_le_sq₀ (norm_nonneg _) (Real.sqrt_nonneg _)).2 hnorm_sqrt
    _ = ∑ x ∈ μ.support, μ.weight x * ‖v x‖ ^ 2 :=
      Real.sq_sqrt hrhs_nonneg

/-- Formalization-only auxiliary for `lem:povm-to-obs`: passing from arbitrary
answer-indexed operator families to unit-modulus weighted sums costs at most the
answer-alphabet cardinality. Paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:115-129` states
the specialization to POVMs. -/
theorem povm_to_obs {X α ι : Type*}
    [Fintype X] [DecidableEq X] [Fintype α]
    [Fintype ι] [DecidableEq ι]
    (μ : Distribution X) (A B : X → α → Op ι)
    (c : α → ℂ) (hc : ∀ a, ‖c a‖ = 1) (ψ : EuclideanSpace ℂ ι) :
    opDistSq μ (fun x => ∑ a, c a • A x a) (fun x => ∑ a, c a • B x a) ψ ≤
      Fintype.card α * opFamilyDistSq μ A B ψ := by
  have hpoint : ∀ x,
      ‖applyOperatorToState
          ((∑ a, c a • A x a) - ∑ a, c a • B x a) ψ‖ ^ 2 ≤
        (Fintype.card α : ℝ) *
          ∑ a, ‖applyOperatorToState (A x a - B x a) ψ‖ ^ 2 := by
    intro x
    have hrewrite :
        applyOperatorToState
            ((∑ a, c a • A x a) - ∑ a, c a • B x a) ψ =
          ∑ a, c a • applyOperatorToState (A x a - B x a) ψ := by
      simp [applyOperatorToState, ← Finset.sum_sub_distrib, ← smul_sub]
    rw [hrewrite]
    have hnorm :
        ‖∑ a, c a • applyOperatorToState (A x a - B x a) ψ‖ ≤
          ∑ a, ‖applyOperatorToState (A x a - B x a) ψ‖ := by
      calc
        ‖∑ a, c a • applyOperatorToState (A x a - B x a) ψ‖ ≤
            ∑ a, ‖c a • applyOperatorToState (A x a - B x a) ψ‖ :=
          norm_sum_le Finset.univ _
        _ = ∑ a, ‖applyOperatorToState (A x a - B x a) ψ‖ := by
          apply Finset.sum_congr rfl
          intro a _
          simp [norm_smul, hc a]
    calc
      ‖∑ a, c a • applyOperatorToState (A x a - B x a) ψ‖ ^ 2 ≤
          (∑ a, ‖applyOperatorToState (A x a - B x a) ψ‖) ^ 2 :=
        (sq_le_sq₀ (norm_nonneg _) (Finset.sum_nonneg fun _ _ => norm_nonneg _)).2 hnorm
      _ ≤ (Fintype.card α : ℝ) *
          ∑ a, ‖applyOperatorToState (A x a - B x a) ψ‖ ^ 2 := by
        simpa using (sq_sum_le_card_mul_sum_sq
          (s := Finset.univ)
          (f := fun a : α => ‖applyOperatorToState (A x a - B x a) ψ‖))
  unfold opDistSq opFamilyDistSq
  simp only [Fintype.sum_unique]
  calc
    avgOver μ (fun x =>
        ‖applyOperatorToState
          ((∑ a, c a • A x a) - ∑ a, c a • B x a) ψ‖ ^ 2) ≤
      avgOver μ (fun x =>
        (Fintype.card α : ℝ) *
          ∑ a, ‖applyOperatorToState (A x a - B x a) ψ‖ ^ 2) :=
      avgOver_mono μ _ _ hpoint
    _ = (Fintype.card α : ℝ) * avgOver μ (fun x =>
        ∑ a, ‖applyOperatorToState (A x a - B x a) ψ‖ ^ 2) :=
      avgOver_const_mul _ _ _

/-- Passing from answer-indexed POVM effects to unit-modulus weighted
observables costs at most the answer-alphabet cardinality. This is
`lem:povm-to-obs`, blueprint
`blueprint/src/chapter/ch14_qpbt_observables.tex:361-378`, paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:115-129`. -/
theorem povm_to_obs_of_measurements {X α ι : Type*}
    [Fintype X] [DecidableEq X] [Fintype α]
    [Fintype ι] [DecidableEq ι]
    (μ : Distribution X) (A B : X → Measurement α ι)
    (c : α → ℂ) (hc : ∀ a, ‖c a‖ = 1) (ψ : EuclideanSpace ℂ ι) :
    opDistSq μ (fun x => ∑ a, c a • (A x).effect a)
        (fun x => ∑ a, c a • (B x).effect a) ψ ≤
      Fintype.card α * opFamilyDistSq μ
        (fun x a => (A x).effect a) (fun x a => (B x).effect a) ψ := by
  exact povm_to_obs μ (fun x a => (A x).effect a)
    (fun x a => (B x).effect a) c hc ψ

/-- Orthonormalization of a consistent pair of POVMs. The resulting
Alice-side measurement is projective and remains close to the original one on
the unit bipartite state. This imported result is `lem:ortho`, blueprint
`blueprint/src/chapter/ch14_qpbt_observables.tex:390-410`, paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:131-153`;
the source cites KV11 and the self-contained proof [ML20]. -/
theorem exists_projective_close_of_consistent :
    ∃ η : ℝ → ℝ,
      (∃ C : ℝ, 1 ≤ C ∧ ∀ δ : ℝ, 0 ≤ δ →
        η δ ≤ C * Real.rpow δ (1 / 4 : ℝ)) ∧
      ∀ (ιA ιB α : Type) [Fintype ιA] [DecidableEq ιA]
        [Fintype ιB] [DecidableEq ιB] [Fintype α] [DecidableEq α]
        (ψ : EuclideanSpace ℂ (ιA × ιB)) (_hψ : ‖ψ‖ = 1)
        (Q : Measurement α ιA)
        (R : Measurement α ιB) (δ : ℝ),
        0 ≤ δ ∧ δ ≤ 1 →
        consistencyDefect (uniformDistribution Unit)
          (fun _ a => heteroKron (Q.effect a) 1)
          (fun _ a => heteroKron 1 (R.effect a)) ψ ≤ δ →
        ∃ Pm : Measurement α ιA,
          MIPStarRE.QPBT.Measurement.IsProjective Pm ∧
          opFamilyDistSq (uniformDistribution Unit)
            (fun _ a => heteroKron (Pm.effect a) 1)
            (fun _ a => heteroKron (Q.effect a) 1) ψ ≤ η δ := by
  refine ⟨fun δ => 220 * Real.rpow δ (1 / 4 : ℝ), ?_, ?_⟩
  · exact ⟨220, by norm_num, fun _ _ => le_rfl⟩
  · intro ιA ιB α _ _ _ _ _ _ ψ hψ Q R δ hδ hcons
    exact projective_rounding_with_explicit_constant ψ hψ Q R δ hδ.1 hcons

end MIPStarRE.QPBT
