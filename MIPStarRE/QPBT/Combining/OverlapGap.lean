import MIPStarRE.QPBT.Games.DistanceTheorems.Support
import MIPStarRE.LDT.Preliminaries.SwitchSandwichPrep.InnerProduct

/-!
# Replacing one factor of a measurement-weighted overlap

The scalar estimates used to combine the two Pauli bases compare averaged
overlaps whose left factor is one complete measurement and whose right factors
are operator families at small state-dependent distance.  This module records
the corresponding Cauchy--Schwarz estimate.  The right-hand families are
arbitrary, so the estimate covers an ordered product of point effects, which
is not itself a measurement.

## References

The estimate is `lem:overlap-gap-distance` in
`blueprint/src/chapter/ch15_qpbt_combining.tex`; it is the Cauchy--Schwarz
step at paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1147-1166`.
-/

open scoped BigOperators Matrix MatrixOrder ComplexOrder

namespace MIPStarRE.QPBT

open MIPStarRE.LDT hiding Measurement
open MIPStarRE.Quantum MIPStarRE.QPBT.DistanceCalculus

/-- Replacing one operator family inside an overlap weighted on the left by a
complete measurement changes the average by at most the square root of the
state-dependent squared distance between the two families. -/
theorem abs_overlap_gap_le_sqrt_of_opFamilyDistSq {X α ι : Type*}
    [Fintype α] [Fintype ι] [DecidableEq ι]
    (μ : Distribution X) (A : X → Measurement α ι) (B C : X → α → Op ι)
    (ψ : EuclideanSpace ℂ ι) (hμ : μ.IsProbability) (hψ : ‖ψ‖ = 1)
    (ζ : ℝ) (hBC : opFamilyDistSq μ B C ψ ≤ ζ) :
    |avgOver μ (fun x => ∑ a : α, stateQForm ψ ((A x).effect a * B x a)) -
        avgOver μ (fun x => ∑ a : α, stateQForm ψ ((A x).effect a * C x a))| ≤
      Real.sqrt ζ := by
  classical
  have hnorm_sq : ∀ M : Op ι,
      ‖applyOperatorToState M ψ‖ ^ 2 = stateQForm ψ (Mᴴ * M) := by
    intro M
    rw [@norm_sq_eq_re_inner ℂ]
    unfold stateQForm applyOperatorToState
    rw [Matrix.toEuclideanLin_conjTranspose_mul_self]
    change (inner ℂ (Matrix.toEuclideanLin M ψ) (Matrix.toEuclideanLin M ψ)).re =
      (inner ℂ ψ ((Matrix.toEuclideanLin M).adjoint
        (Matrix.toEuclideanLin M ψ))).re
    rw [LinearMap.adjoint_inner_right]
  have hmul : ∀ M N : Op ι, Mᴴ = M →
      stateQForm ψ (M * N) =
        (inner ℂ (applyOperatorToState M ψ)
          (applyOperatorToState N ψ)).re := by
    intro M N hM
    have hadjoint : (Matrix.toEuclideanLin M).adjoint =
        Matrix.toEuclideanLin M := by
      rw [← Matrix.toEuclideanLin_conjTranspose_eq_adjoint, hM]
    calc
      stateQForm ψ (M * N) =
          (inner ℂ ψ
            (applyOperatorToState M (applyOperatorToState N ψ))).re := by
        rw [stateQForm, applyOperatorToState_mul]
      _ = (inner ℂ ψ ((Matrix.toEuclideanLin M).adjoint
            (applyOperatorToState N ψ))).re := by
        rw [hadjoint]
        rfl
      _ = _ := by
        rw [LinearMap.adjoint_inner_right]
        rfl
  have hleft : ∀ x : X,
      (∑ a : α, ‖applyOperatorToState ((A x).effect a) ψ‖ ^ 2) ≤ 1 := by
    intro x
    have htotal : (∑ a : α, stateQForm ψ ((A x).effect a)) = 1 := by
      calc
        (∑ a : α, stateQForm ψ ((A x).effect a)) =
            stateQForm ψ (∑ a : α, (A x).effect a) := by
          simp [stateQForm, applyOperatorToState]
        _ = stateQForm ψ 1 := by rw [(A x).sum_eq_one]
        _ = 1 := by rw [stateQForm]; simp [applyOperatorToState, hψ]
    calc
      (∑ a : α, ‖applyOperatorToState ((A x).effect a) ψ‖ ^ 2) ≤
          ∑ a : α, stateQForm ψ ((A x).effect a) := by
        refine Finset.sum_le_sum ?_
        intro a _
        rw [hnorm_sq, measurement_effect_hermitian]
        exact quadratic_form_mono (MIPStarRE.Quantum.sq_le_self ((A x).pos a)
          (measurement_effect_le_one (A x) a)) ψ
      _ = 1 := htotal
  have hgnonneg : ∀ x : X,
      0 ≤ ∑ a : α, ‖applyOperatorToState (B x a - C x a) ψ‖ ^ 2 :=
    fun x => Finset.sum_nonneg fun a _ => sq_nonneg _
  have hpoint : ∀ x : X,
      |∑ a : α, stateQForm ψ ((A x).effect a * (B x a - C x a))| ≤
        Real.sqrt (∑ a : α, ‖applyOperatorToState (B x a - C x a) ψ‖ ^ 2) := by
    intro x
    let u : α → EuclideanSpace ℂ ι := fun a =>
      applyOperatorToState ((A x).effect a) ψ
    let v : α → EuclideanSpace ℂ ι := fun a =>
      applyOperatorToState (B x a - C x a) ψ
    have hrw : (∑ a : α, stateQForm ψ ((A x).effect a * (B x a - C x a))) =
        ∑ a : α, (inner ℂ (u a) (v a)).re := by
      refine Finset.sum_congr rfl ?_
      intro a _
      exact hmul _ _ (measurement_effect_hermitian (A x) a)
    have hone : Real.sqrt (∑ a : α, ‖u a‖ ^ 2) ≤ 1 := by
      rw [← Real.sqrt_one]
      exact Real.sqrt_le_sqrt (hleft x)
    calc
      |∑ a : α, stateQForm ψ ((A x).effect a * (B x a - C x a))| =
          |∑ a : α, (inner ℂ (u a) (v a)).re| := by rw [hrw]
      _ ≤ ∑ a : α, |(inner ℂ (u a) (v a)).re| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ a : α, ‖u a‖ * ‖v a‖ := by
        refine Finset.sum_le_sum ?_
        intro a _
        exact (Complex.abs_re_le_norm _).trans (norm_inner_le_norm (u a) (v a))
      _ ≤ Real.sqrt (∑ a : α, ‖u a‖ ^ 2) * Real.sqrt (∑ a : α, ‖v a‖ ^ 2) := by
        simpa using Real.sum_mul_le_sqrt_mul_sqrt
          (Finset.univ : Finset α) (fun a => ‖u a‖) (fun a => ‖v a‖)
      _ ≤ 1 * Real.sqrt (∑ a : α, ‖v a‖ ^ 2) :=
        mul_le_mul_of_nonneg_right hone (Real.sqrt_nonneg _)
      _ = Real.sqrt (∑ a : α,
            ‖applyOperatorToState (B x a - C x a) ψ‖ ^ 2) := one_mul _
  have hdiff :
      avgOver μ (fun x => ∑ a : α, stateQForm ψ ((A x).effect a * B x a)) -
          avgOver μ (fun x => ∑ a : α,
            stateQForm ψ ((A x).effect a * C x a)) =
        avgOver μ (fun x => ∑ a : α,
          stateQForm ψ ((A x).effect a * (B x a - C x a))) := by
    rw [← avgOver_sub]
    refine avgOver_congr μ _ _ ?_
    intro x
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl ?_
    intro a _
    simp [stateQForm, applyOperatorToState, mul_sub]
  rw [hdiff]
  refine le_trans
    (MIPStarRE.LDT.Preliminaries.avgOver_abs_le_sqrt_of_pointwise μ _ _
      hpoint hgnonneg (by rw [hμ.weight_sum_eq_one])) ?_
  exact Real.sqrt_le_sqrt hBC

end MIPStarRE.QPBT
