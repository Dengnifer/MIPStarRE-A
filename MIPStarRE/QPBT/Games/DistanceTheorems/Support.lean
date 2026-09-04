import MIPStarRE.QPBT.Games.Consistency
import MIPStarRE.LDT.Basic.DistributionAvg
import MIPStarRE.LDT.MakingMeasurementsProjective.Defs
import MIPStarRE.LDT.Preliminaries.CauchySchwarz
import MIPStarRE.Quantum.FiniteHilbert

/-!
# Finite-dimensional operator estimates for state-dependent distance

This module contains finite-dimensional operator and finite-sum identities used
by the paper-facing distance theorems. It introduces no new mathematical
assumptions or source-facing statements.

## References

- `references/qpbt-paper/06_nonlocal_games_and_mipstar.tex:295-395`
- `references/ldt-paper/preliminaries.tex:649-666`
-/

open scoped BigOperators Matrix MatrixOrder ComplexOrder

namespace MIPStarRE.QPBT.DistanceCalculus

open MIPStarRE.LDT MIPStarRE.Quantum
open MIPStarRE.LDT.MakingMeasurementsProjective

/-- The squared norm of `M ψ` is the quadratic form of `Mᴴ M`. -/
private theorem norm_applyOperatorToState_sq_eq {ι : Type*}
    [Fintype ι] [DecidableEq ι]
    (M : Op ι) (ψ : EuclideanSpace ℂ ι) :
    ‖applyOperatorToState M ψ‖ ^ 2 =
      (inner ℂ ψ (applyOperatorToState (Mᴴ * M) ψ)).re := by
  rw [@norm_sq_eq_re_inner ℂ]
  unfold applyOperatorToState
  rw [Matrix.toEuclideanLin_conjTranspose_mul_self]
  change (inner ℂ (Matrix.toEuclideanLin M ψ) (Matrix.toEuclideanLin M ψ)).re =
    (inner ℂ ψ ((Matrix.toEuclideanLin M).adjoint (Matrix.toEuclideanLin M ψ))).re
  rw [LinearMap.adjoint_inner_right]

/-- Formalization-only auxiliary lemma for Fact 4.20: evaluation in a fixed
vector preserves operator order. -/
theorem quadratic_form_mono {ι : Type*}
    [Fintype ι] [DecidableEq ι]
    {S T : Op ι} (hST : S ≤ T) (v : EuclideanSpace ℂ ι) :
    (inner ℂ v (applyOperatorToState S v)).re ≤
      (inner ℂ v (applyOperatorToState T v)).re := by
  have hpsd : (T - S).PosSemidef := Matrix.le_iff.mp hST
  have hnonneg := hpsd.dotProduct_mulVec_nonneg v
  have hdiff : 0 ≤ (inner ℂ v (applyOperatorToState (T - S) v)).re := by
    simp only [applyOperatorToState, Matrix.toEuclideanLin,
      Matrix.toLpLin_apply, EuclideanSpace.inner_eq_star_dotProduct]
    rw [dotProduct_comm]
    exact (Complex.nonneg_iff.mp hnonneg).1
  rw [show T = S + (T - S) by abel]
  simp only [applyOperatorToState, map_add, LinearMap.add_apply, inner_add_right,
    Complex.add_re]
  exact le_add_of_nonneg_right hdiff

/-- Applying a product of operators agrees with successive application. -/
theorem applyOperatorToState_mul {ι : Type*}
    [Fintype ι] [DecidableEq ι]
    (M N : Op ι) (v : EuclideanSpace ℂ ι) :
    applyOperatorToState (M * N) v =
      applyOperatorToState M (applyOperatorToState N v) := by
  unfold applyOperatorToState
  simp [Matrix.toEuclideanLin, Matrix.toLpLin_mul_same]

/-- Finite-subset form of contraction by square-summable left multipliers. -/
private theorem finset_sum_norm_mul_apply_le {γ ι : Type*}
    [Fintype ι] [DecidableEq ι]
    (s : Finset γ) (C : γ → Op ι) (D : Op ι) (v : EuclideanSpace ℂ ι)
    (hC : ∑ c ∈ s, (C c)ᴴ * C c ≤ 1) :
    ∑ c ∈ s, ‖applyOperatorToState (C c * D) v‖ ^ 2 ≤
      ‖applyOperatorToState D v‖ ^ 2 := by
  calc
    ∑ c ∈ s, ‖applyOperatorToState (C c * D) v‖ ^ 2 =
        ∑ c ∈ s,
          (inner ℂ (applyOperatorToState D v)
            (applyOperatorToState ((C c)ᴴ * C c)
              (applyOperatorToState D v))).re := by
          apply Finset.sum_congr rfl
          intro c _
          rw [applyOperatorToState_mul]
          exact norm_applyOperatorToState_sq_eq (C c) _
    _ = (inner ℂ (applyOperatorToState D v)
          (applyOperatorToState (∑ c ∈ s, (C c)ᴴ * C c)
            (applyOperatorToState D v))).re := by
          simp [applyOperatorToState]
    _ ≤ (inner ℂ (applyOperatorToState D v)
          (applyOperatorToState (1 : Op ι) (applyOperatorToState D v))).re :=
      quadratic_form_mono hC _
    _ = ‖applyOperatorToState D v‖ ^ 2 := by
      simpa [applyOperatorToState] using
        (norm_applyOperatorToState_sq_eq (1 : Op ι) (applyOperatorToState D v)).symm

/-- Formalization-only auxiliary lemma for Fact 4.20: a square-summable family
of left multipliers contracts total squared norm. -/
theorem sum_norm_mul_apply_le {γ ι : Type*}
    [Fintype γ] [Fintype ι] [DecidableEq ι]
    (C : γ → Op ι) (D : Op ι) (v : EuclideanSpace ℂ ι)
    (hC : ∑ c : γ, (C c)ᴴ * C c ≤ 1) :
    ∑ c : γ, ‖applyOperatorToState (C c * D) v‖ ^ 2 ≤
      ‖applyOperatorToState D v‖ ^ 2 := by
  simpa using finset_sum_norm_mul_apply_le Finset.univ C D v (by simpa using hC)

/-- Formalization-only auxiliary lemma for the function-indexed multiplication
estimate at paper lines 347--361: fiber-indexed left multiplication contracts
the associated squared-norm sum. -/
theorem sum_norm_mul_funIndexed_apply_le {α Γ ι : Type*}
    [Fintype α] [Fintype Γ] [Fintype ι] [DecidableEq ι]
    (eval : Γ → α) (S : Γ → Op ι) (D : α → Op ι)
    (v : EuclideanSpace ℂ ι) (hS : ∑ g : Γ, (S g)ᴴ * S g ≤ 1) :
    ∑ g : Γ, ‖applyOperatorToState (S g * D (eval g)) v‖ ^ 2 ≤
      ∑ a : α, ‖applyOperatorToState (D a) v‖ ^ 2 := by
  classical
  rw [show (∑ g : Γ, ‖applyOperatorToState (S g * D (eval g)) v‖ ^ 2) =
      ∑ a : α, ∑ g ∈ Finset.univ.filter (fun g => eval g = a),
        ‖applyOperatorToState (S g * D a) v‖ ^ 2 by
    calc
      _ = ∑ a : α, ∑ g ∈ Finset.univ.filter (fun g => eval g = a),
          ‖applyOperatorToState (S g * D (eval g)) v‖ ^ 2 :=
        (Finset.sum_fiberwise Finset.univ eval
          (fun g => ‖applyOperatorToState (S g * D (eval g)) v‖ ^ 2)).symm
      _ = _ := by
        apply Finset.sum_congr rfl
        intro a _
        apply Finset.sum_congr rfl
        intro g hg
        rw [(Finset.mem_filter.mp hg).2]]
  apply Finset.sum_le_sum
  intro a _
  apply finset_sum_norm_mul_apply_le
  calc
    ∑ g ∈ Finset.univ.filter (fun g => eval g = a), (S g)ᴴ * S g ≤
        ∑ g : Γ, (S g)ᴴ * S g := by
      exact Finset.sum_le_sum_of_subset_of_nonneg
        (Finset.filter_subset _ _)
        (fun g _ _ => star_mul_self_nonneg (S g))
    _ ≤ 1 := hS

/-- Formalization-only auxiliary lemma for the projective-sum estimate at paper
lines 364--380: distinct effects of a projective measurement are orthogonal. -/
theorem projective_effect_mul_effect_eq_zero {α ι : Type*}
    [Fintype α] [Fintype ι] [DecidableEq ι]
    (M : MIPStarRE.Quantum.Measurement α ι)
    (hM : MIPStarRE.QPBT.Measurement.IsProjective M)
    {a b : α} (hab : a ≠ b) :
    M.effect a * M.effect b = 0 := by
  classical
  cases isEmpty_or_nonempty ι with
  | inl hι =>
      letI := hι
      exact Subsingleton.elim _ _
  | inr hι =>
      letI := hι
      let H : FiniteHilbertSpace :=
        { carrier := ι
          instFintype := inferInstance
          instDecidableEq := inferInstance
          instNonempty := inferInstance }
      let P : ProjMeas α ι :=
        { toMeasurement := MatrixMeasurement.toMeasurement (H := H) M
          proj := fun a => (hM a).isIdempotentElem.eq }
      simpa [P, H] using P.outcome_orthogonal a b hab

/-- Gram expansion for a finite sum with mutually orthogonal left projectors. -/
private theorem gram_finset_sum_projector_mul {α ι : Type*}
    [Fintype ι]
    (P D : α → Op ι) (hproj : ∀ a, IsProj (P a))
    (horth : ∀ {a b}, a ≠ b → P a * P b = 0) (s : Finset α) :
    (∑ a ∈ s, P a * D a)ᴴ * (∑ a ∈ s, P a * D a) =
      ∑ a ∈ s, (D a)ᴴ * P a * D a := by
  classical
  let T : α → Op ι := fun a => P a * D a
  have hstar (a : α) : (P a)ᴴ = P a := by
    simpa [Matrix.star_eq_conjTranspose] using (hproj a).isSelfAdjoint.star_eq
  calc
    _ = (∑ a ∈ s, (T a)ᴴ) * (∑ b ∈ s, T b) := by
      simp only [T, Matrix.conjTranspose_sum]
    _ = ∑ a ∈ s, ∑ b ∈ s, (T a)ᴴ * T b := by
      rw [Matrix.sum_mul]
      apply Finset.sum_congr rfl
      intro a _
      rw [Matrix.mul_sum]
    _ = ∑ a ∈ s, (D a)ᴴ * P a * D a := by
      apply Finset.sum_congr rfl
      intro a ha
      rw [Finset.sum_eq_single a]
      · simp only [T, Matrix.conjTranspose_mul, hstar a]
        rw [mul_assoc (D a)ᴴ (P a) (P a * D a),
          ← mul_assoc (P a) (P a) (D a), (hproj a).isIdempotentElem.eq]
        exact (mul_assoc (D a)ᴴ (P a) (D a)).symm
      · intro b _ hba
        calc
          (T a)ᴴ * T b = (D a)ᴴ * (P a * P b) * D b := by
            simp [T, Matrix.conjTranspose_mul, hstar a, mul_assoc]
          _ = 0 := by rw [horth (Ne.symm hba)]; simp
      · exact fun h => (h ha).elim

/-- Formalization-only auxiliary lemma for the projective-sum estimate at paper
lines 364--380: an orthogonal projective left sum is bounded by the full input
norm sum. -/
theorem norm_finset_sum_projector_mul_sq_le {α ι : Type*}
    [Fintype α] [Fintype ι] [DecidableEq ι]
    (P D : α → Op ι) (hproj : ∀ a, IsProj (P a))
    (horth : ∀ {a b}, a ≠ b → P a * P b = 0)
    (s : Finset α) (ψ : EuclideanSpace ℂ ι) :
    ‖applyOperatorToState (∑ a ∈ s, P a * D a) ψ‖ ^ 2 ≤
      ∑ a : α, ‖applyOperatorToState (D a) ψ‖ ^ 2 := by
  classical
  have hgram :
      (∑ a ∈ s, P a * D a)ᴴ * (∑ a ∈ s, P a * D a) ≤
        ∑ a : α, (D a)ᴴ * D a := by
    rw [gram_finset_sum_projector_mul P D hproj horth s]
    calc
      ∑ a ∈ s, (D a)ᴴ * P a * D a ≤
          ∑ a ∈ s, (D a)ᴴ * D a := by
        refine Finset.sum_le_sum ?_
        intro a _
        simpa [Matrix.star_eq_conjTranspose] using
          (star_left_conjugate_le_conjugate (hproj a).le_one (D a))
      _ ≤ ∑ a : α, (D a)ᴴ * D a :=
        Finset.sum_le_sum_of_subset_of_nonneg (by simp)
          (fun a _ _ => (Matrix.posSemidef_conjTranspose_mul_self (D a)).nonneg)
  rw [norm_applyOperatorToState_sq_eq]
  calc
    (inner ℂ ψ (applyOperatorToState
        ((∑ a ∈ s, P a * D a)ᴴ * (∑ a ∈ s, P a * D a)) ψ)).re ≤
        (inner ℂ ψ (applyOperatorToState (∑ a : α, (D a)ᴴ * D a) ψ)).re :=
      quadratic_form_mono hgram ψ
    _ = ∑ a : α,
          (inner ℂ ψ (applyOperatorToState ((D a)ᴴ * D a) ψ)).re := by
      simp [applyOperatorToState]
    _ = ∑ a : α, ‖applyOperatorToState (D a) ψ‖ ^ 2 := by
      apply Finset.sum_congr rfl
      intro a _
      exact (norm_applyOperatorToState_sq_eq (D a) ψ).symm

/-- Formalization-only definition for the agreement facts (Facts 4.13 and 4.14):
the real quadratic form of an operator evaluated in a state vector. -/
noncomputable def stateQForm {ι : Type*} [Fintype ι] [DecidableEq ι]
    (ψ : EuclideanSpace ℂ ι) (M : Op ι) : ℝ :=
  (inner ℂ ψ (applyOperatorToState M ψ)).re

/-- Formalization-only auxiliary lemma for the agreement facts (Facts 4.13 and
4.14): the state quadratic form is additive in its operator. -/
theorem stateQForm_add {ι : Type*} [Fintype ι] [DecidableEq ι]
    (ψ : EuclideanSpace ℂ ι) (M N : Op ι) :
    stateQForm ψ (M + N) = stateQForm ψ M + stateQForm ψ N := by
  simp [stateQForm, applyOperatorToState]

/-- The state quadratic form preserves operator subtraction. -/
private theorem stateQForm_sub {ι : Type*} [Fintype ι] [DecidableEq ι]
    (ψ : EuclideanSpace ℂ ι) (M N : Op ι) :
    stateQForm ψ (M - N) = stateQForm ψ M - stateQForm ψ N := by
  simp [stateQForm, applyOperatorToState]

/-- The state quadratic form commutes with a finite sum. -/
private theorem stateQForm_sum {α ι : Type*} [Fintype α]
    [Fintype ι] [DecidableEq ι]
    (ψ : EuclideanSpace ℂ ι) (M : α → Op ι) :
    stateQForm ψ (∑ a, M a) = ∑ a, stateQForm ψ (M a) := by
  simp [stateQForm, applyOperatorToState]

/-- The quadratic form of the identity is the squared vector norm. -/
private theorem stateQForm_one {ι : Type*} [Fintype ι] [DecidableEq ι]
    (ψ : EuclideanSpace ℂ ι) :
    stateQForm ψ (1 : Op ι) = ‖ψ‖ ^ 2 := by
  have hone : applyOperatorToState (1 : Op ι) ψ = ψ := by
    simp [applyOperatorToState]
  rw [stateQForm, hone]
  simpa using (inner_self_eq_norm_sq (𝕜 := ℂ) ψ)

/-- Formalization-only auxiliary lemma for the agreement facts (Facts 4.13 and
4.14): every effect of a complete measurement is bounded by the identity. -/
theorem measurement_effect_le_one {α ι : Type*} [Fintype α]
    [Fintype ι] [DecidableEq ι]
    (M : MIPStarRE.Quantum.Measurement α ι) (a : α) :
    M.effect a ≤ 1 := by
  calc
    M.effect a ≤ ∑ b : α, M.effect b :=
      Finset.single_le_sum (fun b _ => M.pos b) (Finset.mem_univ a)
    _ = 1 := M.sum_eq_one

/-- Formalization-only auxiliary lemma for the agreement facts (Facts 4.13 and
4.14): every positive measurement effect is Hermitian. -/
theorem measurement_effect_hermitian {α ι : Type*} [Fintype α]
    [Fintype ι] [DecidableEq ι]
    (M : MIPStarRE.Quantum.Measurement α ι) (a : α) :
    (M.effect a)ᴴ = M.effect a :=
  (Matrix.nonneg_iff_posSemidef.mp (M.pos a)).isHermitian.eq

/-- Expand the squared state-dependent distance between two measurement effects. -/
private theorem norm_effect_sub_effect_sq_expand {α ι : Type*} [Fintype α]
    [Fintype ι] [DecidableEq ι]
    (A B : MIPStarRE.Quantum.Measurement α ι)
    (ψ : EuclideanSpace ℂ ι) (a : α) :
    ‖applyOperatorToState (A.effect a - B.effect a) ψ‖ ^ 2 =
      stateQForm ψ (A.effect a * A.effect a) +
      stateQForm ψ (B.effect a * B.effect a) -
      2 * stateQForm ψ (A.effect a * B.effect a) := by
  rw [norm_applyOperatorToState_sq_eq]
  change stateQForm ψ ((A.effect a - B.effect a)ᴴ *
    (A.effect a - B.effect a)) = _
  rw [show (A.effect a - B.effect a)ᴴ * (A.effect a - B.effect a) =
      A.effect a * A.effect a - B.effect a * A.effect a -
        (A.effect a * B.effect a - B.effect a * B.effect a) by
    simp only [Matrix.conjTranspose_sub, measurement_effect_hermitian A a,
      measurement_effect_hermitian B a]
    noncomm_ring]
  rw [stateQForm_sub, stateQForm_sub, stateQForm_sub]
  have hcross : stateQForm ψ (B.effect a * A.effect a) =
      stateQForm ψ (A.effect a * B.effect a) := by
    unfold stateQForm applyOperatorToState
    rw [show B.effect a * A.effect a = (A.effect a * B.effect a)ᴴ by
      simp [Matrix.conjTranspose_mul, measurement_effect_hermitian A a,
        measurement_effect_hermitian B a]]
    rw [Matrix.toEuclideanLin_conjTranspose_eq_adjoint,
      LinearMap.adjoint_inner_right]
    simpa using (inner_re_symm (𝕜 := ℂ)
      ((Matrix.toEuclideanLin (A.effect a * B.effect a)) ψ) ψ)
  rw [hcross]
  ring

/-- Removing the diagonal term from a finite sum is subtraction of that term. -/
private theorem sum_if_eq_zero_else {α : Type*} [Fintype α] [DecidableEq α]
    (f : α → ℝ) (a : α) :
    (∑ b : α, if a = b then 0 else f b) = (∑ b : α, f b) - f a := by
  have herase := Finset.sum_erase_add (Finset.univ : Finset α) f
    (Finset.mem_univ a)
  calc
    (∑ b : α, if a = b then 0 else f b) =
        ∑ b ∈ (Finset.univ : Finset α).filter (fun b => b ≠ a), f b := by
      rw [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro b _
      by_cases h : a = b <;> simp [h, Ne.symm]
    _ = ∑ b ∈ (Finset.univ : Finset α).erase a, f b := by
      rw [Finset.filter_ne']
    _ = (∑ b : α, f b) - f a := by linarith

/-- Summing a complete measurement in the right factor leaves the first operator. -/
private theorem stateQForm_mul_sum_right {α ι : Type*} [Fintype α]
    [Fintype ι] [DecidableEq ι]
    (B : MIPStarRE.Quantum.Measurement α ι)
    (ψ : EuclideanSpace ℂ ι) (M : Op ι) :
    (∑ b : α, stateQForm ψ (M * B.effect b)) = stateQForm ψ M := by
  rw [← stateQForm_sum, ← Finset.mul_sum, B.sum_eq_one, mul_one]

/-- The quadratic forms of all effects sum to the squared vector norm. -/
private theorem stateQForm_effect_sum {α ι : Type*} [Fintype α]
    [Fintype ι] [DecidableEq ι]
    (A : MIPStarRE.Quantum.Measurement α ι)
    (ψ : EuclideanSpace ℂ ι) :
    (∑ a : α, stateQForm ψ (A.effect a)) = ‖ψ‖ ^ 2 := by
  rw [← stateQForm_sum, A.sum_eq_one, stateQForm_one]

/-- Formalization-only auxiliary lemma for the agreement facts (Facts 4.13 and
4.14): pointwise inconsistency is total mass minus diagonal overlap. -/
theorem point_defect_eq {α ι : Type*} [Fintype α] [DecidableEq α]
    [Fintype ι] [DecidableEq ι]
    (A B : MIPStarRE.Quantum.Measurement α ι)
    (ψ : EuclideanSpace ℂ ι) :
    (∑ a : α, ∑ b : α,
      if a = b then 0 else stateQForm ψ (A.effect a * B.effect b)) =
      ‖ψ‖ ^ 2 - ∑ a : α, stateQForm ψ (A.effect a * B.effect a) := by
  calc
    _ = ∑ a : α, ((∑ b : α, stateQForm ψ (A.effect a * B.effect b)) -
          stateQForm ψ (A.effect a * B.effect a)) := by
      apply Finset.sum_congr rfl
      intro a _
      exact sum_if_eq_zero_else
        (fun b => stateQForm ψ (A.effect a * B.effect b)) a
    _ = ∑ a : α, (stateQForm ψ (A.effect a) -
          stateQForm ψ (A.effect a * B.effect a)) := by
      apply Finset.sum_congr rfl
      intro a _
      rw [stateQForm_mul_sum_right B ψ]
    _ = (∑ a : α, stateQForm ψ (A.effect a)) -
          ∑ a : α, stateQForm ψ (A.effect a * B.effect a) := by
      rw [Finset.sum_sub_distrib]
    _ = _ := by rw [stateQForm_effect_sum]

/-- Formalization-only auxiliary lemma for the agreement facts (Facts 4.13 and
4.14): the matrix-vector term in `consistencyDefect` is the state quadratic
form. -/
theorem consistency_term_eq_stateQForm {ι : Type*}
    [Fintype ι] [DecidableEq ι]
    (ψ : EuclideanSpace ℂ ι) (M : Op ι) :
    (inner ℂ ψ ((EuclideanSpace.equiv ι ℂ).symm (M.mulVec ψ))).re =
      stateQForm ψ M := by
  rfl

/-- Formalization-only auxiliary lemma for the agreement facts (Facts 4.13 and
4.14), item 1: pointwise measurement distance is at most twice the
inconsistency defect. -/
theorem point_distance_le_two_defect {α ι : Type*}
    [Fintype α] [DecidableEq α] [Fintype ι] [DecidableEq ι]
    (A B : MIPStarRE.Quantum.Measurement α ι)
    (ψ : EuclideanSpace ℂ ι) :
    (∑ a : α, ‖applyOperatorToState (A.effect a - B.effect a) ψ‖ ^ 2) ≤
      2 * (∑ a : α, ∑ b : α,
        if a = b then 0 else stateQForm ψ (A.effect a * B.effect b)) := by
  have hterm (a : α) :
      ‖applyOperatorToState (A.effect a - B.effect a) ψ‖ ^ 2 ≤
        stateQForm ψ (A.effect a) + stateQForm ψ (B.effect a) -
          2 * stateQForm ψ (A.effect a * B.effect a) := by
    rw [norm_effect_sub_effect_sq_expand A B ψ a]
    have hA := quadratic_form_mono
      (MIPStarRE.Quantum.sq_le_self (A.pos a) (measurement_effect_le_one A a)) ψ
    have hB := quadratic_form_mono
      (MIPStarRE.Quantum.sq_le_self (B.pos a) (measurement_effect_le_one B a)) ψ
    exact sub_le_sub_right (add_le_add hA hB) _
  calc
    _ ≤ ∑ a : α, (stateQForm ψ (A.effect a) + stateQForm ψ (B.effect a) -
          2 * stateQForm ψ (A.effect a * B.effect a)) :=
      Finset.sum_le_sum fun a _ => hterm a
    _ = (∑ a : α, stateQForm ψ (A.effect a)) +
          (∑ a : α, stateQForm ψ (B.effect a)) -
          2 * (∑ a : α, stateQForm ψ (A.effect a * B.effect a)) := by
      rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.mul_sum]
    _ = 2 * (‖ψ‖ ^ 2 -
          ∑ a : α, stateQForm ψ (A.effect a * B.effect a)) := by
      rw [stateQForm_effect_sum A ψ, stateQForm_effect_sum B ψ]
      ring
    _ = _ := by rw [point_defect_eq A B ψ]

/-- Formalization-only auxiliary lemma for the agreement facts (Facts 4.13 and
4.14), item 2: projective measurements make distance exactly twice the
pointwise defect. -/
theorem point_distance_eq_two_defect_of_projective {α ι : Type*}
    [Fintype α] [DecidableEq α] [Fintype ι] [DecidableEq ι]
    (A B : MIPStarRE.Quantum.Measurement α ι)
    (ψ : EuclideanSpace ℂ ι)
    (hA : MIPStarRE.QPBT.Measurement.IsProjective A)
    (hB : MIPStarRE.QPBT.Measurement.IsProjective B) :
    (∑ a : α, ‖applyOperatorToState (A.effect a - B.effect a) ψ‖ ^ 2) =
      2 * (∑ a : α, ∑ b : α,
        if a = b then 0 else stateQForm ψ (A.effect a * B.effect b)) := by
  calc
    _ = ∑ a : α, (stateQForm ψ (A.effect a * A.effect a) +
          stateQForm ψ (B.effect a * B.effect a) -
          2 * stateQForm ψ (A.effect a * B.effect a)) := by
      apply Finset.sum_congr rfl
      intro a _
      exact norm_effect_sub_effect_sq_expand A B ψ a
    _ = ∑ a : α, (stateQForm ψ (A.effect a) + stateQForm ψ (B.effect a) -
          2 * stateQForm ψ (A.effect a * B.effect a)) := by
      apply Finset.sum_congr rfl
      intro a _
      rw [(hA a).isIdempotentElem.eq, (hB a).isIdempotentElem.eq]
    _ = (∑ a : α, stateQForm ψ (A.effect a)) +
          (∑ a : α, stateQForm ψ (B.effect a)) -
          2 * (∑ a : α, stateQForm ψ (A.effect a * B.effect a)) := by
      rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.mul_sum]
    _ = 2 * (‖ψ‖ ^ 2 -
          ∑ a : α, stateQForm ψ (A.effect a * B.effect a)) := by
      rw [stateQForm_effect_sum A ψ, stateQForm_effect_sum B ψ]
      ring
    _ = _ := by rw [point_defect_eq A B ψ]

/-- Formalization-only auxiliary lemma for the agreement facts (Facts 4.13 and
4.14), item 2: state-dependent squared distance between operator families is
nonnegative. -/
theorem opFamilyDistSq_nonneg {X α ι : Type*}
    [Fintype α] [Fintype ι] [DecidableEq ι]
    (μ : Distribution X) (M N : X → α → Op ι)
    (ψ : EuclideanSpace ℂ ι) :
    0 ≤ opFamilyDistSq μ M N ψ := by
  unfold opFamilyDistSq avgOver
  exact Finset.sum_nonneg fun x _ => mul_nonneg (μ.nonnegative x)
    (Finset.sum_nonneg fun a _ => sq_nonneg _)

/-- A Hermitian left factor moves to the first slot of the vector inner product. -/
private theorem stateQForm_mul_eq_re_inner_apply {ι : Type*}
    [Fintype ι] [DecidableEq ι]
    (A B : Op ι) (ψ : EuclideanSpace ℂ ι) (hA : Aᴴ = A) :
    stateQForm ψ (A * B) =
      (inner ℂ (applyOperatorToState A ψ)
        (applyOperatorToState B ψ)).re := by
  have hadjoint : (Matrix.toEuclideanLin A).adjoint =
      Matrix.toEuclideanLin A := by
    rw [← Matrix.toEuclideanLin_conjTranspose_eq_adjoint, hA]
  calc
    stateQForm ψ (A * B) =
        (inner ℂ ψ
          (applyOperatorToState A (applyOperatorToState B ψ))).re := by
      rw [stateQForm, applyOperatorToState_mul]
    _ = (inner ℂ ψ
          ((Matrix.toEuclideanLin A).adjoint
            (applyOperatorToState B ψ))).re := by
      rw [hadjoint]
      rfl
    _ = _ := by
      rw [LinearMap.adjoint_inner_right]
      rfl

/-- With a projective left measurement, defect is an inner-product error sum. -/
private theorem point_defect_eq_sum_inner_of_projective_left {α ι : Type*}
    [Fintype α] [DecidableEq α] [Fintype ι] [DecidableEq ι]
    (A B : MIPStarRE.Quantum.Measurement α ι)
    (ψ : EuclideanSpace ℂ ι)
    (hA : MIPStarRE.QPBT.Measurement.IsProjective A) :
    (∑ a : α, ∑ b : α,
      if a = b then 0 else stateQForm ψ (A.effect a * B.effect b)) =
      ∑ a : α, (inner ℂ (applyOperatorToState (A.effect a) ψ)
        (applyOperatorToState (A.effect a - B.effect a) ψ)).re := by
  calc
    _ = ‖ψ‖ ^ 2 - ∑ a : α,
          stateQForm ψ (A.effect a * B.effect a) := point_defect_eq A B ψ
    _ = (∑ a : α, stateQForm ψ (A.effect a)) -
          ∑ a : α, stateQForm ψ (A.effect a * B.effect a) := by
      rw [stateQForm_effect_sum]
    _ = ∑ a : α, (stateQForm ψ (A.effect a) -
          stateQForm ψ (A.effect a * B.effect a)) := by
      rw [Finset.sum_sub_distrib]
    _ = ∑ a : α, stateQForm ψ
          (A.effect a * (A.effect a - B.effect a)) := by
      apply Finset.sum_congr rfl
      intro a _
      rw [mul_sub, stateQForm_sub, (hA a).isIdempotentElem.eq]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro a _
      exact stateQForm_mul_eq_re_inner_apply _ _ ψ
        (measurement_effect_hermitian A a)

/-- Projective measurement components satisfy a Pythagorean norm identity. -/
private theorem sum_norm_effect_apply_sq_of_projective {α ι : Type*}
    [Fintype α] [Fintype ι] [DecidableEq ι]
    (A : MIPStarRE.Quantum.Measurement α ι)
    (ψ : EuclideanSpace ℂ ι)
    (hA : MIPStarRE.QPBT.Measurement.IsProjective A) :
    (∑ a : α, ‖applyOperatorToState (A.effect a) ψ‖ ^ 2) = ‖ψ‖ ^ 2 := by
  calc
    _ = ∑ a : α, stateQForm ψ (A.effect a * A.effect a) := by
      apply Finset.sum_congr rfl
      intro a _
      rw [norm_applyOperatorToState_sq_eq]
      change stateQForm ψ ((A.effect a)ᴴ * A.effect a) = _
      rw [measurement_effect_hermitian]
    _ = ∑ a : α, stateQForm ψ (A.effect a) := by
      apply Finset.sum_congr rfl
      intro a _
      rw [(hA a).isIdempotentElem.eq]
    _ = ‖ψ‖ ^ 2 := stateQForm_effect_sum A ψ

/-- Formalization-only auxiliary lemma for the agreement facts (Facts 4.13 and
4.14), item 3: pointwise projective-left defect obeys the Cauchy--Schwarz
square-root bound. -/
theorem abs_point_defect_le_sqrt_distance_of_projective_left {α ι : Type*}
    [Fintype α] [DecidableEq α] [Fintype ι] [DecidableEq ι]
    (A B : MIPStarRE.Quantum.Measurement α ι)
    (ψ : EuclideanSpace ℂ ι) (hψ : ‖ψ‖ = 1)
    (hA : MIPStarRE.QPBT.Measurement.IsProjective A) :
    |∑ a : α, ∑ b : α,
      if a = b then 0 else stateQForm ψ (A.effect a * B.effect b)| ≤
      Real.sqrt (∑ a : α,
        ‖applyOperatorToState (A.effect a - B.effect a) ψ‖ ^ 2) := by
  rw [point_defect_eq_sum_inner_of_projective_left A B ψ hA]
  let u : α → EuclideanSpace ℂ ι := fun a =>
    applyOperatorToState (A.effect a) ψ
  let v : α → EuclideanSpace ℂ ι := fun a =>
    applyOperatorToState (A.effect a - B.effect a) ψ
  calc
    |∑ a : α, (inner ℂ (u a) (v a)).re| ≤
        ∑ a : α, |(inner ℂ (u a) (v a)).re| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ a : α, ‖u a‖ * ‖v a‖ := by
      apply Finset.sum_le_sum
      intro a _
      exact (Complex.abs_re_le_norm _).trans (norm_inner_le_norm (u a) (v a))
    _ ≤ Real.sqrt (∑ a : α, ‖u a‖ ^ 2) *
          Real.sqrt (∑ a : α, ‖v a‖ ^ 2) := by
      simpa using Real.sum_mul_le_sqrt_mul_sqrt
        (Finset.univ : Finset α) (fun a => ‖u a‖) (fun a => ‖v a‖)
    _ = Real.sqrt (∑ a : α,
          ‖applyOperatorToState (A.effect a - B.effect a) ψ‖ ^ 2) := by
      rw [show (∑ a : α, ‖u a‖ ^ 2) = ‖ψ‖ ^ 2 by
        simpa [u] using sum_norm_effect_apply_sq_of_projective A ψ hA]
      rw [Real.sqrt_sq (norm_nonneg ψ), hψ]
      simp [v]

/-- Regard a unit Euclidean vector as an LDT pure state. -/
private noncomputable def pureStateOfUnitVector {ι : Type*}
    [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (ψ : EuclideanSpace ℂ ι) (hψ : ‖ψ‖ = 1) : PureState ι where
  vector := ψ.ofLp
  unit := by
    calc
      star ψ.ofLp ⬝ᵥ ψ.ofLp = ψ.ofLp ⬝ᵥ star ψ.ofLp := dotProduct_comm _ _
      _ = inner ℂ ψ ψ := (EuclideanSpace.inner_eq_star_dotProduct ψ ψ).symm
      _ = (‖ψ‖ ^ 2 : ℂ) := inner_self_eq_norm_sq_to_K ψ
      _ = 1 := by rw [hψ]; norm_num

/-- For a unit vector, `stateQForm` agrees with the LDT pure-state expectation. -/
private theorem stateQForm_eq_ev {ι : Type*}
    [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (ψ : EuclideanSpace ℂ ι) (hψ : ‖ψ‖ = 1) (T : Op ι) :
    stateQForm ψ T = ev (pureStateOfUnitVector ψ hψ : QuantumState ι) T := by
  rw [PureState.ev_eq_re_inner]
  simp only [pureStateOfUnitVector]
  change (inner ℂ ψ (WithLp.toLp 2 (T *ᵥ ψ.ofLp))).re =
    (star ψ.ofLp ⬝ᵥ T *ᵥ ψ.ofLp).re
  rw [EuclideanSpace.inner_eq_star_dotProduct, dotProduct_comm]

/-- Pure-state evaluation of `Tᴴ T` is the squared norm of `T ψ`. -/
private theorem ev_adjoint_mul_self_eq_norm_sq {ι : Type*}
    [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (ψ : EuclideanSpace ℂ ι) (hψ : ‖ψ‖ = 1) (T : Op ι) :
    ev (pureStateOfUnitVector ψ hψ : QuantumState ι) (Tᴴ * T) =
      ‖applyOperatorToState T ψ‖ ^ 2 := by
  rw [← stateQForm_eq_ev]
  exact (norm_applyOperatorToState_sq_eq T ψ).symm

/-- Formalization-only auxiliary lemma for Proposition 4.29: operator-family
distance controls the change in diagonal overlap. -/
theorem overlap_gap_le_of_opFamilyDistSq {X α ι : Type*}
    [Fintype α]
    [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (μ : Distribution X)
    (A B D : X → MIPStarRE.Quantum.Measurement α ι)
    (ψ : EuclideanSpace ℂ ι) (hμ : μ.IsProbability) (hψ : ‖ψ‖ = 1)
    (ζ : ℝ)
    (hBD : opFamilyDistSq μ (fun x a => (B x).effect a)
      (fun x a => (D x).effect a) ψ ≤ ζ) :
    |avgOver μ (fun x => ∑ a, stateQForm ψ ((A x).effect a * (B x).effect a)) -
      avgOver μ (fun x => ∑ a, stateQForm ψ ((A x).effect a * (D x).effect a))| ≤
        Real.sqrt ζ := by
  classical
  let ψp : PureState ι := pureStateOfUnitVector ψ hψ
  let H : FiniteHilbertSpace :=
    { carrier := ι
      instFintype := inferInstance
      instDecidableEq := inferInstance
      instNonempty := inferInstance }
  let As : X → SubMeas α ι := fun x =>
    (MatrixMeasurement.toMeasurement (H := H) (A x)).toSubMeas
  let Bs : X → SubMeas α ι := fun x =>
    (MatrixMeasurement.toMeasurement (H := H) (B x)).toSubMeas
  let Ds : X → SubMeas α ι := fun x =>
    (MatrixMeasurement.toMeasurement (H := H) (D x)).toSubMeas
  have hmass : ∑ x ∈ μ.support, μ.weight x ≤ 1 := by
    rw [hμ.weight_sum_eq_one]
  have hsdd : SDDRel (ψp : QuantumState ι) μ Bs Ds ζ := by
    constructor
    unfold sddError qSDD qSDDCore
    calc
      avgOver μ (fun x => ∑ a, ev (ψp : QuantumState ι)
          (((Bs x).outcome a - (Ds x).outcome a)ᴴ *
            ((Bs x).outcome a - (Ds x).outcome a))) =
          opFamilyDistSq μ (fun x a => (B x).effect a)
            (fun x a => (D x).effect a) ψ := by
        unfold opFamilyDistSq
        apply avgOver_congr
        intro x
        apply Finset.sum_congr rfl
        intro a _
        simpa [ψp, Bs, Ds, H] using
          ev_adjoint_mul_self_eq_norm_sq ψ hψ ((B x).effect a - (D x).effect a)
      _ ≤ ζ := hBD
  have hgap := MIPStarRE.LDT.Preliminaries.easyApproxFromApproxDelta
    (ψp : QuantumState ι) ψp.toQuantumState_isNormalized μ hmass Bs Ds As ζ hsdd
  have hBA : avgOver μ (fun x => ∑ a,
      ev (ψp : QuantumState ι) ((A x).effect a * (B x).effect a)) =
      avgOver μ (fun x => ∑ a,
        ev (ψp : QuantumState ι) ((B x).effect a * (A x).effect a)) := by
    apply avgOver_congr
    intro x
    apply Finset.sum_congr rfl
    intro a _
    exact ev_mul_comm_of_psd _ _ _ ((A x).pos a) ((B x).pos a)
  have hDA : avgOver μ (fun x => ∑ a,
      ev (ψp : QuantumState ι) ((A x).effect a * (D x).effect a)) =
      avgOver μ (fun x => ∑ a,
        ev (ψp : QuantumState ι) ((D x).effect a * (A x).effect a)) := by
    apply avgOver_congr
    intro x
    apply Finset.sum_congr rfl
    intro a _
    exact ev_mul_comm_of_psd _ _ _ ((A x).pos a) ((D x).pos a)
  rw [show avgOver μ (fun x => ∑ a,
      stateQForm ψ ((A x).effect a * (B x).effect a)) =
      avgOver μ (fun x => ∑ a,
        ev (ψp : QuantumState ι) ((A x).effect a * (B x).effect a)) by
    apply avgOver_congr
    intro x
    apply Finset.sum_congr rfl
    intro a _
    exact stateQForm_eq_ev ψ hψ _]
  rw [show avgOver μ (fun x => ∑ a,
      stateQForm ψ ((A x).effect a * (D x).effect a)) =
      avgOver μ (fun x => ∑ a,
        ev (ψp : QuantumState ι) ((A x).effect a * (D x).effect a)) by
    apply avgOver_congr
    intro x
    apply Finset.sum_congr rfl
    intro a _
    exact stateQForm_eq_ev ψ hψ _]
  rw [hBA, hDA]
  simpa only [ψp, As, Bs, Ds, H,
    MatrixMeasurement.toMeasurement_outcome] using hgap

/-- Formalization-only auxiliary lemma for Proposition 4.29: on a unit state and
probability distribution, defect is one minus diagonal overlap. -/
theorem consistencyDefect_eq_one_sub_overlap {X α ι : Type*}
    [Fintype X] [DecidableEq X] [Fintype α] [DecidableEq α]
    [Fintype ι] [DecidableEq ι]
    (μ : Distribution X) (A B : X → MIPStarRE.Quantum.Measurement α ι)
    (ψ : EuclideanSpace ℂ ι) (hμ : μ.IsProbability) (hψ : ‖ψ‖ = 1) :
    consistencyDefect μ (fun x a => (A x).effect a)
        (fun x a => (B x).effect a) ψ =
      1 - avgOver μ (fun x => ∑ a,
        stateQForm ψ ((A x).effect a * (B x).effect a)) := by
  unfold consistencyDefect
  simp_rw [consistency_term_eq_stateQForm]
  calc
    avgOver μ (fun x => ∑ a, ∑ b, if a = b then 0 else
        stateQForm ψ ((A x).effect a * (B x).effect b)) =
      avgOver μ (fun x => ‖ψ‖ ^ 2 - ∑ a,
        stateQForm ψ ((A x).effect a * (B x).effect a)) := by
      apply avgOver_congr
      intro x
      exact point_defect_eq (A x) (B x) ψ
    _ = avgOver μ (fun _ => ‖ψ‖ ^ 2) - avgOver μ (fun x => ∑ a,
        stateQForm ψ ((A x).effect a * (B x).effect a)) :=
      avgOver_sub μ _ _
    _ = _ := by
      rw [avgOver_const_of_isProbability μ hμ, hψ]
      norm_num

/-- Formalization-only auxiliary lemma for Proposition 4.29: state-dependent
operator-family distance is symmetric. -/
theorem opFamilyDistSq_symm {X α ι : Type*}
    [Fintype α] [Fintype ι] [DecidableEq ι]
    (μ : Distribution X) (A B : X → α → Op ι)
    (ψ : EuclideanSpace ℂ ι) :
    opFamilyDistSq μ A B ψ = opFamilyDistSq μ B A ψ := by
  unfold opFamilyDistSq
  apply avgOver_congr
  intro x
  apply Finset.sum_congr rfl
  intro a _
  simp only [applyOperatorToState, map_sub, LinearMap.sub_apply]
  rw [norm_sub_rev]

end MIPStarRE.QPBT.DistanceCalculus
