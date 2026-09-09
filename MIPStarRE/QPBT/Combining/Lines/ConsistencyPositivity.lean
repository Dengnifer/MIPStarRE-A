import MIPStarRE.QPBT.Combining.Witnesses
import MIPStarRE.QPBT.Combining.Points.Placement

/-!
# Positivity of the consistency defect on opposite placements

The error-inflation estimates for restricted line distributions apply to
nonnegative averages.  This module supplies the missing nonnegativity: the
integrand of `consistencyDefect` for two complete measurements placed on
opposite registers is a state quadratic form of a positive operator.  Indeed,
after separating the two placements along the corresponding tensor
bipartition, the off-diagonal sum is
`∑_a (place p₁ E_a) (place p₂ (∑_{b ≠ a} F_b))`, a sum of products of
positive operators supported on complementary registers.

## References

The consistency defect is blueprint `def:consistency`, paper
`references/qpbt-paper/06_nonlocal_games_and_mipstar.tex:232-248`.  The
placements and their bipartitions are blueprint `def:expanded-state`, paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:420-450`.  The
nonnegativity is the hypothesis of items 1 and 2 of
blueprint `lem:restricted-line-mixture-bounds`, paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1052-1058`.
-/

open scoped BigOperators Matrix MatrixOrder ComplexOrder

namespace MIPStarRE.QPBT

open MIPStarRE.LDT hiding Measurement
open MIPStarRE.Quantum

noncomputable section

/-- The state quadratic form of the zero operator vanishes. -/
private theorem stateQForm_zero_local {ι : Type*} [Fintype ι] [DecidableEq ι]
    (ψ : EuclideanSpace ℂ ι) :
    DistanceCalculus.stateQForm ψ (0 : Op ι) = 0 := by
  simp [DistanceCalculus.stateQForm, applyOperatorToState]

namespace ProjectiveSetting

variable {P : AdmissibleParams} {ε : ℝ}

/-- A register placement maps the zero operator to zero. -/
private theorem place_zero_local (S : ProjectiveSetting P ε) (p : Placement) :
    S.place p (0 : Op (S.ExpandedLocalSpace p.side)) = 0 := by
  ext i j
  cases p <;> simp [place]

set_option synthInstance.maxSize 400 in
/-- Positive operators placed on `AA'` and on `BA''` have a positive product.
Paper `references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:420-450`,
blueprint `def:expanded-state`. -/
theorem place_AA'_mul_place_BA''_nonneg (S : ProjectiveSetting P ε)
    {X : Op (S.ExpandedLocalSpace .alice)} {Y : Op (S.ExpandedLocalSpace .bob)}
    (hX : 0 ≤ X) (hY : 0 ≤ Y) :
    0 ≤ S.place .AA' X * S.place .BA'' Y := by
  have key : ∀ (X' : Op (S.toStrategy.ιA × PauliRegister P))
      (Y' : Op (S.toStrategy.ιB × PauliRegister P)),
      0 ≤ X' → 0 ≤ Y' → 0 ≤ S.place .AA' X' * S.place .BA'' Y' := by
    intro X' Y' hX' hY'
    have hprod : S.place .AA' X' * S.place .BA'' Y' =
        reindexOp (aaBaBipartition P S.toStrategy.ιA S.toStrategy.ιB)
          (heteroKron X' (heteroKron Y'
            (1 : Op (PauliRegister P × PauliRegister P)))) := by
      rw [← reindexOp_aaBaBipartition_left S X',
        ← reindexOp_aaBaBipartition_right S Y',
        ← WinImplications.reindexOp_mul, heteroKron_mul, Matrix.mul_one,
        Matrix.one_mul]
    rw [hprod]
    refine reindexOp_nonneg _ ?_
    exact kronecker_nonneg hX'
      (kronecker_nonneg hY' Matrix.PosSemidef.one.nonneg)
  exact key X Y hX hY

set_option synthInstance.maxSize 400 in
/-- Positive operators placed on `AB''` and on `BB'` have a positive product.
Paper `references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:420-450`,
blueprint `def:expanded-state`. -/
theorem place_AB''_mul_place_BB'_nonneg (S : ProjectiveSetting P ε)
    {X : Op (S.ExpandedLocalSpace .alice)} {Y : Op (S.ExpandedLocalSpace .bob)}
    (hX : 0 ≤ X) (hY : 0 ≤ Y) :
    0 ≤ S.place .AB'' X * S.place .BB' Y := by
  have key : ∀ (X' : Op (S.toStrategy.ιA × PauliRegister P))
      (Y' : Op (S.toStrategy.ιB × PauliRegister P)),
      0 ≤ X' → 0 ≤ Y' → 0 ≤ S.place .AB'' X' * S.place .BB' Y' := by
    intro X' Y' hX' hY'
    have hprod : S.place .AB'' X' * S.place .BB' Y' =
        reindexOp (abBbBipartition P S.toStrategy.ιA S.toStrategy.ιB)
          (heteroKron X' (heteroKron Y'
            (1 : Op (PauliRegister P × PauliRegister P)))) := by
      rw [← reindexOp_abBbBipartition_left S X',
        ← reindexOp_abBbBipartition_right S Y',
        ← WinImplications.reindexOp_mul, heteroKron_mul, Matrix.mul_one,
        Matrix.one_mul]
    rw [hprod]
    refine reindexOp_nonneg _ ?_
    exact kronecker_nonneg hX'
      (kronecker_nonneg hY' Matrix.PosSemidef.one.nonneg)
  exact key X Y hX hY

/-- Positive operators placed on a directed opposite pair of registers have a
positive product.  Paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:420-450`,
blueprint `def:expanded-state`. -/
theorem place_mul_place_nonneg (S : ProjectiveSetting P ε)
    (p₁ p₂ : Placement) (hopp : p₁.IsOpposite p₂)
    {X : Op (S.ExpandedLocalSpace p₁.side)}
    {Y : Op (S.ExpandedLocalSpace p₂.side)}
    (hX : 0 ≤ X) (hY : 0 ≤ Y) :
    0 ≤ S.place p₁ X * S.place p₂ Y := by
  cases p₁ <;> cases p₂ <;> simp only [Placement.IsOpposite] at hopp
  · exact place_AA'_mul_place_BA''_nonneg S hX hY
  · rw [S.place_comm .BA'' .AA' (by trivial) X Y]
    exact place_AA'_mul_place_BA''_nonneg S hY hX
  · rw [S.place_comm .BB' .AB'' (by trivial) X Y]
    exact place_AB''_mul_place_BB'_nonneg S hY hX
  · exact place_AB''_mul_place_BB'_nonneg S hX hY

end ProjectiveSetting

/-! ## Nonnegativity of the pointwise consistency defect -/

/-- The off-diagonal outcome sum of two complete measurements placed on
opposite registers is a positive operator.  Formalization-only auxiliary for
blueprint `def:consistency`, paper
`references/qpbt-paper/06_nonlocal_games_and_mipstar.tex:232-248`. -/
theorem offDiagonalPlacedProduct_nonneg {P : AdmissibleParams} {ε : ℝ}
    {α : Type*} [Fintype α] [DecidableEq α] (S : ProjectiveSetting P ε)
    (p₁ p₂ : Placement) (hopp : p₁.IsOpposite p₂)
    (M₁ : MIPStarRE.Quantum.Measurement α (S.ExpandedLocalSpace p₁.side))
    (M₂ : MIPStarRE.Quantum.Measurement α (S.ExpandedLocalSpace p₂.side)) :
    0 ≤ ∑ a : α, ∑ b : α,
      if a = b then 0
      else S.place p₁ (M₁.effect a) * S.place p₂ (M₂.effect b) := by
  classical
  have hcomplement : ∀ a : α,
      0 ≤ ∑ b : α, if a = b then (0 : Op (S.ExpandedLocalSpace p₂.side))
        else M₂.effect b := by
    intro a
    refine Finset.sum_nonneg fun b _ => ?_
    by_cases h : a = b
    · rw [if_pos h]
    · rw [if_neg h]
      exact M₂.pos b
  have hrow : ∀ a : α,
      (∑ b : α, if a = b then (0 : Op (SixReg P S.toStrategy.ιA
          S.toStrategy.ιB))
        else S.place p₁ (M₁.effect a) * S.place p₂ (M₂.effect b)) =
      S.place p₁ (M₁.effect a) *
        S.place p₂ (∑ b : α, if a = b then 0 else M₂.effect b) := by
    intro a
    rw [ProjectiveSetting.place_finsetSum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun b _ => ?_
    by_cases h : a = b
    · rw [if_pos h, if_pos h, ProjectiveSetting.place_zero_local, mul_zero]
    · rw [if_neg h, if_neg h]
  rw [Finset.sum_congr rfl fun a _ => hrow a]
  refine Finset.sum_nonneg fun a _ => ?_
  exact ProjectiveSetting.place_mul_place_nonneg S p₁ p₂ hopp (M₁.pos a)
    (hcomplement a)

/-- The integrand of the consistency defect of two complete measurements placed
on opposite registers is nonnegative.  This is the positivity hypothesis needed
by items 1 and 2 of blueprint `lem:restricted-line-mixture-bounds`, paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1052-1058`. -/
theorem consistencyDefect_integrand_nonneg {P : AdmissibleParams} {ε : ℝ}
    {α : Type*} [Fintype α] [DecidableEq α] (S : ProjectiveSetting P ε)
    (p₁ p₂ : Placement) (hopp : p₁.IsOpposite p₂)
    (M₁ : MIPStarRE.Quantum.Measurement α (S.ExpandedLocalSpace p₁.side))
    (M₂ : MIPStarRE.Quantum.Measurement α (S.ExpandedLocalSpace p₂.side)) :
    0 ≤ ∑ a : α, ∑ b : α,
      if a = b then 0
      else (inner ℂ S.psiHat
        ((EuclideanSpace.equiv (SixReg P S.toStrategy.ιA S.toStrategy.ιB)
            ℂ).symm
          ((S.place p₁ (M₁.effect a) * S.place p₂ (M₂.effect b)).mulVec
            S.psiHat))).re := by
  classical
  have hform : (∑ a : α, ∑ b : α,
        if a = b then 0
        else (inner ℂ S.psiHat
          ((EuclideanSpace.equiv (SixReg P S.toStrategy.ιA S.toStrategy.ιB)
              ℂ).symm
            ((S.place p₁ (M₁.effect a) * S.place p₂ (M₂.effect b)).mulVec
              S.psiHat))).re) =
      DistanceCalculus.stateQForm S.psiHat
        (∑ a : α, ∑ b : α, if a = b then 0
          else S.place p₁ (M₁.effect a) * S.place p₂ (M₂.effect b)) := by
    rw [DistanceCalculus.stateQForm_finset_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [DistanceCalculus.stateQForm_finset_sum]
    refine Finset.sum_congr rfl fun b _ => ?_
    by_cases h : a = b
    · rw [if_pos h, if_pos h, stateQForm_zero_local]
    · rw [if_neg h, if_neg h]
      rfl
  rw [hform]
  exact DistanceCalculus.stateQForm_nonneg S.psiHat
    (offDiagonalPlacedProduct_nonneg S p₁ p₂ hopp M₁ M₂)

end

end MIPStarRE.QPBT
