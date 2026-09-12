import MIPStarRE.QPBT.Combining.OverlapGap

/-!
# Complex measurement-weighted overlaps

These estimates retain the complex modulus in the Cauchy--Schwarz step for
the concrete X-Z-X measurement.

## References

Paper `claim:17-2`,
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1168-1201`.
-/

open scoped BigOperators Matrix MatrixOrder ComplexOrder

namespace MIPStarRE.QPBT

open MIPStarRE.LDT hiding Measurement
open MIPStarRE.Quantum MIPStarRE.QPBT.DistanceCalculus

/-- Complex weighted Cauchy--Schwarz, averaged over a finite distribution. -/
theorem norm_weighted_sum_inner_le_sqrt_mul_sqrt {X α ι : Type*} [Fintype α]
    [Fintype ι] [DecidableEq ι] (μ : Distribution X) (A : X → α → Op ι)
    (hA : ∀ x a, 0 ≤ A x a) (u v : X → α → EuclideanSpace ℂ ι) :
    ‖∑ x ∈ μ.support, (μ.weight x : ℂ) *
        ∑ a, inner ℂ (u x a) (applyOperatorToState (A x a) (v x a))‖ ≤
      Real.sqrt (avgOver μ (fun x =>
          ∑ a, stateQForm (u x a) (A x a))) *
        Real.sqrt (avgOver μ (fun x =>
          ∑ a, stateQForm (v x a) (A x a))) := by
  classical
  let g : X → ℝ := fun x => ∑ a, stateQForm (u x a) (A x a)
  let h : X → ℝ := fun x => ∑ a, stateQForm (v x a) (A x a)
  have hg : ∀ x, 0 ≤ g x := fun x =>
    Finset.sum_nonneg fun a _ => stateQForm_nonneg _ (hA x a)
  have hh : ∀ x, 0 ≤ h x := fun x =>
    Finset.sum_nonneg fun a _ => stateQForm_nonneg _ (hA x a)
  have hpoint : ∀ x,
      ‖∑ a, inner ℂ (u x a) (applyOperatorToState (A x a) (v x a))‖ ≤
        Real.sqrt (g x) * Real.sqrt (h x) := by
    intro x
    calc
      _ ≤ ∑ a, ‖inner ℂ (u x a) (applyOperatorToState (A x a) (v x a))‖ :=
        norm_sum_le _ _
      _ ≤ ∑ a, Real.sqrt (stateQForm (u x a) (A x a)) *
          Real.sqrt (stateQForm (v x a) (A x a)) :=
        Finset.sum_le_sum fun a _ =>
          norm_inner_applyOperatorToState_le_sqrt_mul_sqrt (hA x a) _ _
      _ ≤ Real.sqrt (∑ a, Real.sqrt (stateQForm (u x a) (A x a)) ^ 2) *
          Real.sqrt (∑ a, Real.sqrt (stateQForm (v x a) (A x a)) ^ 2) :=
        Real.sum_mul_le_sqrt_mul_sqrt _ _ _
      _ = _ := by
        simp only [Real.sq_sqrt (stateQForm_nonneg _ (hA x _)), g, h]
  change _ ≤ Real.sqrt (avgOver μ g) * Real.sqrt (avgOver μ h)
  calc
    _ ≤ ∑ x ∈ μ.support, ‖(μ.weight x : ℂ) *
        ∑ a, inner ℂ (u x a) (applyOperatorToState (A x a) (v x a))‖ :=
      norm_sum_le _ _
    _ ≤ ∑ x ∈ μ.support, μ.weight x * (Real.sqrt (g x) * Real.sqrt (h x)) := by
      refine Finset.sum_le_sum fun x _ => ?_
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (μ.nonnegative x)]
      exact mul_le_mul_of_nonneg_left (hpoint x) (μ.nonnegative x)
    _ = ∑ x ∈ μ.support,
        Real.sqrt (μ.weight x * g x) * Real.sqrt (μ.weight x * h x) := by
      refine Finset.sum_congr rfl fun x _ => ?_
      rw [Real.sqrt_mul (μ.nonnegative x), Real.sqrt_mul (μ.nonnegative x),
        show Real.sqrt (μ.weight x) * Real.sqrt (g x) *
            (Real.sqrt (μ.weight x) * Real.sqrt (h x)) =
          Real.sqrt (μ.weight x) * Real.sqrt (μ.weight x) *
            (Real.sqrt (g x) * Real.sqrt (h x)) by ring,
        Real.mul_self_sqrt (μ.nonnegative x)]
    _ ≤ Real.sqrt (∑ x ∈ μ.support, Real.sqrt (μ.weight x * g x) ^ 2) *
        Real.sqrt (∑ x ∈ μ.support, Real.sqrt (μ.weight x * h x) ^ 2) :=
      Real.sum_mul_le_sqrt_mul_sqrt _ _ _
    _ = _ := by
      simp only [Real.sq_sqrt (mul_nonneg (μ.nonnegative _) (hg _)),
        Real.sq_sqrt (mul_nonneg (μ.nonnegative _) (hh _)), avgOver]

/-- Removing a commuting projection from a complex overlap costs at most
the square root of its overlap deficit. The product may be supplied as a
separate family when it is formed before tensor placement. -/
theorem norm_overlap_gap_le_sqrt_one_sub_of_isProj {X α ι : Type*} [Fintype α]
    [Fintype ι] [DecidableEq ι] (μ : Distribution X) (A : X → Measurement α ι)
    (B C CB : X → α → Op ι) (ψ : EuclideanSpace ℂ ι) (hμ : μ.IsProbability)
    (hψ : ‖ψ‖ = 1) (hB : ∀ x a, IsProj (B x a)) (hC : ∀ x a, IsProj (C x a))
    (hAB : ∀ x a, Commute ((A x).effect a) (B x a))
    (hAC : ∀ x a, Commute ((A x).effect a) (C x a))
    (hCB : ∀ x a, CB x a = C x a * B x a) :
    ‖(∑ x ∈ μ.support, (μ.weight x : ℂ) * ∑ a,
        inner ℂ ψ (applyOperatorToState ((A x).effect a * CB x a) ψ)) -
      (∑ x ∈ μ.support, (μ.weight x : ℂ) * ∑ a,
        inner ℂ ψ (applyOperatorToState ((A x).effect a * C x a) ψ))‖ ≤
      Real.sqrt (1 - avgOver μ (fun x =>
        ∑ a, stateQForm ψ ((A x).effect a * B x a))) := by
  classical
  have hinner : ∀ x a,
      inner ℂ ψ (applyOperatorToState ((A x).effect a * C x a) ψ) -
        inner ℂ ψ (applyOperatorToState ((A x).effect a * CB x a) ψ) =
      inner ℂ (applyOperatorToState (C x a) ψ)
        (applyOperatorToState ((A x).effect a)
          (applyOperatorToState (1 - B x a) ψ)) := by
    intro x a
    rw [hCB, ← inner_sub_right]
    have hsub (M N : Op ι) :
        applyOperatorToState M ψ - applyOperatorToState N ψ =
          applyOperatorToState (M - N) ψ := by
      simp [applyOperatorToState]
    rw [hsub]
    rw [show (A x).effect a * C x a - (A x).effect a * (C x a * B x a) =
        C x a * ((A x).effect a * (1 - B x a)) by
          calc
            _ = ((A x).effect a * C x a) * (1 - B x a) := by noncomm_ring
            _ = _ := by rw [(hAC x a).eq, mul_assoc]]
    rw [applyOperatorToState_mul, applyOperatorToState_mul]
    have hadj : (Matrix.toEuclideanLin (C x a)).adjoint =
        Matrix.toEuclideanLin (C x a) := by
      rw [← Matrix.toEuclideanLin_conjTranspose_eq_adjoint,
        (hC x a).isSelfAdjoint.isHermitian.eq]
    have h := LinearMap.adjoint_inner_right (Matrix.toEuclideanLin (C x a)) ψ
      (applyOperatorToState ((A x).effect a) (applyOperatorToState (1 - B x a) ψ))
    rw [hadj] at h
    exact h
  have hdiff :
      (∑ x ∈ μ.support, (μ.weight x : ℂ) * ∑ a,
        inner ℂ ψ (applyOperatorToState ((A x).effect a * C x a) ψ)) -
      (∑ x ∈ μ.support, (μ.weight x : ℂ) * ∑ a,
        inner ℂ ψ (applyOperatorToState ((A x).effect a * CB x a) ψ)) =
      ∑ x ∈ μ.support, (μ.weight x : ℂ) * ∑ a,
        inner ℂ (applyOperatorToState (C x a) ψ)
          (applyOperatorToState ((A x).effect a)
            (applyOperatorToState (1 - B x a) ψ)) := by
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [← mul_sub, ← Finset.sum_sub_distrib]
    simp only [hinner]
  rw [norm_sub_rev, hdiff]
  have hcs := norm_weighted_sum_inner_le_sqrt_mul_sqrt μ
    (fun x a => (A x).effect a) (fun x a => (A x).pos a)
    (fun x a => applyOperatorToState (C x a) ψ)
    (fun x a => applyOperatorToState (1 - B x a) ψ)
  have hleft : avgOver μ (fun x => ∑ a,
      stateQForm (applyOperatorToState (C x a) ψ) ((A x).effect a)) ≤ 1 := by
    simp only [stateQForm_applyOperatorToState_eq_of_isProj ψ (hC _ _) (hAC _ _)]
    exact avgOver_sum_stateQForm_mul_le_one μ A C ψ hμ hψ hC hAC
  have hright : avgOver μ (fun x => ∑ a,
      stateQForm (applyOperatorToState (1 - B x a) ψ) ((A x).effect a)) =
      1 - avgOver μ (fun x => ∑ a, stateQForm ψ ((A x).effect a * B x a)) := by
    have hx : ∀ x, (∑ a,
        stateQForm (applyOperatorToState (1 - B x a) ψ) ((A x).effect a)) =
        1 - ∑ a, stateQForm ψ ((A x).effect a * B x a) := by
      intro x
      rw [← sum_stateQForm_effect_eq_one (A x) ψ hψ, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [stateQForm_applyOperatorToState_eq_of_isProj ψ (hB x a).one_sub
        ((Commute.one_right _).sub_right (hAB x a))]
      simp [stateQForm, applyOperatorToState, mul_sub]
    rw [avgOver_congr μ _ _ hx, avgOver_sub, avgOver_const_of_isProbability μ hμ]
  rw [hright] at hcs
  exact hcs.trans (by
    simpa using mul_le_mul_of_nonneg_right
      (Real.sqrt_le_sqrt hleft) (Real.sqrt_nonneg
        (1 - avgOver μ (fun x => ∑ a, stateQForm ψ ((A x).effect a * B x a)))))

end MIPStarRE.QPBT
