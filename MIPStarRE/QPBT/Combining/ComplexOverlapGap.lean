import MIPStarRE.QPBT.Combining.OverlapGap

/-!
# Complex measurement-weighted overlap estimates

The complex Cauchy--Schwarz estimate removes a projection from an ordered
product under a complete measurement. The deficit is a real quadratic form,
whereas the difference being bounded retains its complex modulus.

## References

Paper `claim:17-2`,
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1168-1201`;
blueprint `lem:claim-17-2-direct`.
-/

open scoped BigOperators MatrixOrder ComplexOrder

namespace MIPStarRE.QPBT

open MIPStarRE.LDT hiding Measurement
open MIPStarRE.Quantum MIPStarRE.QPBT.DistanceCalculus

/-- Complex Cauchy--Schwarz for a finite sum weighted by positive operators. -/
theorem norm_sum_inner_le_sqrt_mul_sqrt {α ι : Type*} [Fintype α]
    [Fintype ι] [DecidableEq ι] (A : α → Op ι) (hA : ∀ a, 0 ≤ A a)
    (u v : α → EuclideanSpace ℂ ι) :
    ‖∑ a, inner ℂ (u a) (applyOperatorToState (A a) (v a))‖ ≤
      Real.sqrt (∑ a, stateQForm (u a) (A a)) *
        Real.sqrt (∑ a, stateQForm (v a) (A a)) := by
  calc
    _ ≤ ∑ a, ‖inner ℂ (u a) (applyOperatorToState (A a) (v a))‖ :=
      norm_sum_le _ _
    _ ≤ ∑ a, Real.sqrt (stateQForm (u a) (A a)) *
        Real.sqrt (stateQForm (v a) (A a)) :=
      Finset.sum_le_sum fun a _ =>
        norm_inner_applyOperatorToState_le_sqrt_mul_sqrt (hA a) (u a) (v a)
    _ ≤ _ := Real.sum_sqrt_mul_sqrt_le _
      (fun a => stateQForm_nonneg (u a) (hA a))
      (fun a => stateQForm_nonneg (v a) (hA a))

/-- Removing the last projection from a measurement-weighted complex overlap
costs at most the square root of its averaged consistency deficit. The two
projection families need not commute with each other. This is a
formalization-only finite-distribution form of paper `claim:17-2`. -/
theorem norm_overlap_gap_le_sqrt_one_sub_of_isProj {X α ι : Type*} [Fintype α]
    [Fintype ι] [DecidableEq ι] (μ : Distribution X) (A : X → Measurement α ι)
    (B C : X → α → Op ι) (ψ : EuclideanSpace ℂ ι) (hμ : μ.IsProbability)
    (hψ : ‖ψ‖ = 1) (hB : ∀ x a, IsProj (B x a)) (hC : ∀ x a, IsProj (C x a))
    (hAB : ∀ x a, Commute ((A x).effect a) (B x a))
    (hAC : ∀ x a, Commute ((A x).effect a) (C x a)) :
    ‖(∑ x ∈ μ.support, (μ.weight x : ℂ) *
        ∑ a, inner ℂ ψ (applyOperatorToState ((A x).effect a * (C x a * B x a)) ψ)) -
      (∑ x ∈ μ.support, (μ.weight x : ℂ) *
        ∑ a, inner ℂ ψ (applyOperatorToState ((A x).effect a * C x a) ψ))‖ ≤
      Real.sqrt (1 - avgOver μ (fun x =>
        ∑ a, stateQForm ψ ((A x).effect a * B x a))) := by
  classical
  let f : X → ℂ := fun x => ∑ a,
    inner ℂ ψ (applyOperatorToState ((A x).effect a * (C x a * (1 - B x a))) ψ)
  let g : X → ℝ := fun x => ∑ a,
    stateQForm (applyOperatorToState (1 - B x a) ψ) ((A x).effect a)
  have hg : ∀ x, 0 ≤ g x := fun x =>
    Finset.sum_nonneg fun a _ => stateQForm_nonneg _ ((A x).pos a)
  have hpoint : ∀ x, ‖f x‖ ≤ Real.sqrt (g x) := by
    intro x
    have hrw : ∀ a,
        inner ℂ ψ (applyOperatorToState
          ((A x).effect a * (C x a * (1 - B x a))) ψ) =
        inner ℂ (applyOperatorToState (C x a) ψ)
          (applyOperatorToState ((A x).effect a)
            (applyOperatorToState (1 - B x a) ψ)) := by
      intro a
      rw [← mul_assoc, (hAC x a).eq, mul_assoc, applyOperatorToState_mul,
        applyOperatorToState_mul]
      change inner ℂ ψ (Matrix.toEuclideanLin (C x a) _) = _
      have hadj : (Matrix.toEuclideanLin (C x a)).adjoint =
          Matrix.toEuclideanLin (C x a) := by
        rw [← Matrix.toEuclideanLin_conjTranspose_eq_adjoint,
          (hC x a).isSelfAdjoint.isHermitian.eq]
      rw [← hadj, LinearMap.adjoint_inner_right]
      rfl
    have hfirst : (∑ a, stateQForm (applyOperatorToState (C x a) ψ)
        ((A x).effect a)) ≤ 1 := by
      calc
        _ ≤ ∑ a, stateQForm ψ ((A x).effect a) := by
          refine Finset.sum_le_sum fun a _ => ?_
          have hn := stateQForm_nonneg
            (applyOperatorToState (1 - C x a) ψ) ((A x).pos a)
          rw [stateQForm_applyOperatorToState_eq_of_isProj ψ (hC x a).one_sub
            ((Commute.one_right _).sub_right (hAC x a))] at hn
          rw [stateQForm_applyOperatorToState_eq_of_isProj ψ (hC x a) (hAC x a)]
          simpa [stateQForm, applyOperatorToState, mul_sub] using hn
        _ = 1 := sum_stateQForm_effect_eq_one (A x) ψ hψ
    calc
      ‖f x‖ = ‖∑ a, inner ℂ (applyOperatorToState (C x a) ψ)
          (applyOperatorToState ((A x).effect a)
            (applyOperatorToState (1 - B x a) ψ))‖ := by simp only [f, hrw]
      _ ≤ Real.sqrt (∑ a, stateQForm (applyOperatorToState (C x a) ψ)
          ((A x).effect a)) * Real.sqrt (g x) :=
        norm_sum_inner_le_sqrt_mul_sqrt _ (A x).pos _ _
      _ ≤ 1 * Real.sqrt (g x) := mul_le_mul_of_nonneg_right
        (by simpa using Real.sqrt_le_sqrt hfirst) (Real.sqrt_nonneg _)
      _ = _ := one_mul _
  have hsecond : avgOver μ g = 1 - avgOver μ (fun x =>
      ∑ a, stateQForm ψ ((A x).effect a * B x a)) := by
    have hx : ∀ x, g x = 1 - ∑ a, stateQForm ψ ((A x).effect a * B x a) := by
      intro x
      dsimp only [g]
      rw [← sum_stateQForm_effect_eq_one (A x) ψ hψ, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [stateQForm_applyOperatorToState_eq_of_isProj ψ (hB x a).one_sub
        ((Commute.one_right _).sub_right (hAB x a))]
      simp [stateQForm, applyOperatorToState, mul_sub]
    rw [avgOver_congr μ _ _ hx, avgOver_sub, avgOver_const_of_isProbability μ hμ]
  rw [norm_sub_rev, ← Finset.sum_sub_distrib]
  have hdiff : (∑ x ∈ μ.support,
      (((μ.weight x : ℂ) * ∑ a, inner ℂ ψ
        (applyOperatorToState ((A x).effect a * C x a) ψ)) -
      ((μ.weight x : ℂ) * ∑ a, inner ℂ ψ
        (applyOperatorToState ((A x).effect a * (C x a * B x a)) ψ)))) =
      ∑ x ∈ μ.support, (μ.weight x : ℂ) * f x := by
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [← mul_sub, ← Finset.sum_sub_distrib]
    congr 1
    exact Finset.sum_congr rfl fun a _ => by
      simp [applyOperatorToState, mul_sub]
  rw [hdiff, ← hsecond]
  calc
    _ ≤ ∑ x ∈ μ.support, ‖(μ.weight x : ℂ) * f x‖ := norm_sum_le _ _
    _ = avgOver μ (fun x => ‖f x‖) := by
      simp [avgOver, Complex.norm_real, abs_of_nonneg (μ.nonnegative _)]
    _ ≤ |avgOver μ (fun x => ‖f x‖)| := le_abs_self _
    _ ≤ _ := MIPStarRE.LDT.Preliminaries.avgOver_abs_le_sqrt_of_pointwise μ
      (fun x => ‖f x‖) g (fun x => by simpa using hpoint x) hg
      (by rw [hμ.weight_sum_eq_one])

end MIPStarRE.QPBT
