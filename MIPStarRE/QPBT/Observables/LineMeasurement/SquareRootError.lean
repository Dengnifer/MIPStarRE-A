import MIPStarRE.QPBT.Observables.ExpandedPlacement

/-!
# Square-root error bounds for placed measurement families

The consistency conclusions of `lem:qld-comm-line-cons` are stated with the
common error `deltaLine ε = √ε`, while the individual estimates of the proof
are linear in `ε` or already of square-root form. This module records the two
elementary facts that convert those estimates into the common form: the
state-dependent distance between two placed complete measurements never
exceeds `4`, and a quantity bounded by both `a * ε` and `4` is bounded by
`(a + 4) * √ε`.

## References

`lem:qld-comm-line-cons`, blueprint
`blueprint/src/chapter/ch14_qpbt_observables.tex:1082-1210`, paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:559-679`.
-/

open scoped BigOperators Matrix MatrixOrder ComplexOrder

namespace MIPStarRE.QPBT

open MIPStarRE.LDT hiding Measurement
open MIPStarRE.Quantum

namespace DistanceCalculus

/-- The adjoint squares of the effects of a complete measurement sum to at
most the identity. Formalization-only auxiliary for the trivial distance
bound; the fiberwise form is private to
`Games/DistanceTheorems/TensorSupport.lean`. -/
theorem measurement_sum_adjoint_mul_le_one {α ι : Type*} [Fintype α]
    [Fintype ι] [DecidableEq ι] (M : MIPStarRE.Quantum.Measurement α ι) :
    ∑ a : α, (M.effect a)ᴴ * M.effect a ≤ 1 := by
  calc
    ∑ a : α, (M.effect a)ᴴ * M.effect a ≤ ∑ a : α, M.effect a := by
      refine Finset.sum_le_sum fun a _ => ?_
      rw [measurement_effect_hermitian M a]
      exact MIPStarRE.Quantum.sq_le_self (M.pos a) (measurement_effect_le_one M a)
    _ = 1 := M.sum_eq_one

/-- A left-placed complete measurement is square-summable on the product
space. Formalization-only auxiliary for the trivial distance bound. -/
theorem leftPlaced_sum_adjoint_mul_le_one {α ιA ιB : Type*} [Fintype α]
    [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB]
    (M : MIPStarRE.Quantum.Measurement α ιA) :
    ∑ a : α, (heteroKron (M.effect a) (1 : Op ιB))ᴴ *
      heteroKron (M.effect a) (1 : Op ιB) ≤ 1 := by
  calc
    ∑ a : α, (heteroKron (M.effect a) (1 : Op ιB))ᴴ *
          heteroKron (M.effect a) (1 : Op ιB) =
        ∑ a : α, leftTensor (ι₂ := ιB) ((M.effect a)ᴴ * M.effect a) := by
      refine Finset.sum_congr rfl fun a _ => ?_
      change (leftTensor (ι₂ := ιB) (M.effect a))ᴴ *
        leftTensor (ι₂ := ιB) (M.effect a) = _
      rw [leftTensor_conjTranspose, leftTensor_mul_leftTensor]
    _ = leftTensor (ι₂ := ιB) (∑ a : α, (M.effect a)ᴴ * M.effect a) :=
      leftTensor_finset_sum Finset.univ _
    _ ≤ leftTensor (ι₂ := ιB) (1 : Op ιA) :=
      leftTensor_mono (measurement_sum_adjoint_mul_le_one M)
    _ = 1 := leftTensor_one

/-- A right-placed complete measurement is square-summable on the product
space. Formalization-only auxiliary for the trivial distance bound. -/
theorem rightPlaced_sum_adjoint_mul_le_one {α ιA ιB : Type*} [Fintype α]
    [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB]
    (M : MIPStarRE.Quantum.Measurement α ιB) :
    ∑ a : α, (heteroKron (1 : Op ιA) (M.effect a))ᴴ *
      heteroKron (1 : Op ιA) (M.effect a) ≤ 1 := by
  calc
    ∑ a : α, (heteroKron (1 : Op ιA) (M.effect a))ᴴ *
          heteroKron (1 : Op ιA) (M.effect a) =
        ∑ a : α, rightTensor (ι₁ := ιA) ((M.effect a)ᴴ * M.effect a) := by
      refine Finset.sum_congr rfl fun a _ => ?_
      change (rightTensor (ι₁ := ιA) (M.effect a))ᴴ *
        rightTensor (ι₁ := ιA) (M.effect a) = _
      rw [rightTensor_conjTranspose, rightTensor_mul_rightTensor]
    _ = rightTensor (ι₁ := ιA) (∑ a : α, (M.effect a)ᴴ * M.effect a) :=
      rightTensor_finset_sum Finset.univ _
    _ ≤ rightTensor (ι₁ := ιA) (1 : Op ιB) :=
      rightTensor_mono (measurement_sum_adjoint_mul_le_one M)
    _ = 1 := rightTensor_one

/-- The squared distance between two square-summable operator families is at
most four on a unit vector. Formalization-only auxiliary bounding the
state-dependent distance of `def:povm-distance` trivially. -/
theorem sum_norm_sub_apply_sq_le_four {α ι : Type*} [Fintype α]
    [Fintype ι] [DecidableEq ι] (A B : α → Op ι) (ψ : EuclideanSpace ℂ ι)
    (hψ : ‖ψ‖ = 1) (hA : ∑ a : α, (A a)ᴴ * A a ≤ 1)
    (hB : ∑ a : α, (B a)ᴴ * B a ≤ 1) :
    ∑ a : α, ‖applyOperatorToState (A a - B a) ψ‖ ^ 2 ≤ 4 := by
  have hAsum : ∑ a : α, ‖applyOperatorToState (A a) ψ‖ ^ 2 ≤ 1 := by
    have h := sum_norm_mul_apply_le A 1 ψ hA
    simpa [WinImplications.applyOperatorToState_one, hψ] using h
  have hBsum : ∑ a : α, ‖applyOperatorToState (B a) ψ‖ ^ 2 ≤ 1 := by
    have h := sum_norm_mul_apply_le B 1 ψ hB
    simpa [WinImplications.applyOperatorToState_one, hψ] using h
  have hpoint (a : α) :
      ‖applyOperatorToState (A a - B a) ψ‖ ^ 2 ≤
        2 * ‖applyOperatorToState (A a) ψ‖ ^ 2 +
          2 * ‖applyOperatorToState (B a) ψ‖ ^ 2 := by
    have hdecomp : applyOperatorToState (A a - B a) ψ =
        applyOperatorToState (A a) ψ - applyOperatorToState (B a) ψ := by
      simp [applyOperatorToState]
    rw [hdecomp]
    have hpar := parallelogram_law_with_norm ℂ
      (applyOperatorToState (A a) ψ) (applyOperatorToState (B a) ψ)
    nlinarith [sq_nonneg ‖applyOperatorToState (A a) ψ +
      applyOperatorToState (B a) ψ‖]
  calc
    ∑ a : α, ‖applyOperatorToState (A a - B a) ψ‖ ^ 2 ≤
        ∑ a : α, (2 * ‖applyOperatorToState (A a) ψ‖ ^ 2 +
          2 * ‖applyOperatorToState (B a) ψ‖ ^ 2) :=
      Finset.sum_le_sum fun a _ => hpoint a
    _ = 2 * ∑ a : α, ‖applyOperatorToState (A a) ψ‖ ^ 2 +
        2 * ∑ a : α, ‖applyOperatorToState (B a) ψ‖ ^ 2 := by
      rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]
    _ ≤ 4 := by linarith

/-- The state-dependent distance between two complete measurements placed on
opposite tensor factors is at most four. This is the trivial bound used to
pass from a linear error to the common square-root error of
`lem:qld-comm-line-cons`, paper
`14_analysis_of_the_pauli_basis_test.tex:559-679`. -/
theorem opFamilyDistSq_placed_le_four {X α ιA ιB : Type*}
    [Fintype α] [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB]
    (μ : Distribution X) (hμ : μ.IsProbability)
    (A : X → MIPStarRE.Quantum.Measurement α ιA)
    (B : X → MIPStarRE.Quantum.Measurement α ιB)
    (ψ : EuclideanSpace ℂ (ιA × ιB)) (hψ : ‖ψ‖ = 1) :
    opFamilyDistSq μ (fun x a => heteroKron ((A x).effect a) 1)
      (fun x a => heteroKron 1 ((B x).effect a)) ψ ≤ 4 := by
  unfold opFamilyDistSq
  calc
    avgOver μ (fun x => ∑ a : α,
        ‖applyOperatorToState
          (heteroKron ((A x).effect a) 1 - heteroKron 1 ((B x).effect a)) ψ‖ ^ 2)
        ≤ avgOver μ (fun _ => (4 : ℝ)) := by
      apply avgOver_mono
      intro x
      exact sum_norm_sub_apply_sq_le_four _ _ ψ hψ
        (leftPlaced_sum_adjoint_mul_le_one (A x))
        (rightPlaced_sum_adjoint_mul_le_one (B x))
    _ = 4 := avgOver_const_of_isProbability μ hμ 4

end DistanceCalculus

/-- A nonnegative quantity bounded by a linear error `a * ε` with `1 ≤ a` and
by the trivial bound `4` is bounded by `(a + 4) * √ε`: for `ε ≤ 1` the linear
bound dominates, and for `ε ≥ 1` the trivial bound does. This is the passage
to the common square-root error of `lem:qld-comm-line-cons`, paper
`14_analysis_of_the_pauli_basis_test.tex:559-679`. -/
theorem le_mul_sqrt_of_le_mul_of_le_four {x ε a : ℝ} (ha : 1 ≤ a) (hx0 : 0 ≤ x)
    (hxa : x ≤ a * ε) (hx4 : x ≤ 4) : x ≤ (a + 4) * Real.sqrt ε := by
  have hε : 0 ≤ ε := by
    by_contra hneg
    have hlt : ε < 0 := lt_of_not_ge hneg
    nlinarith
  have hsqrt : 0 ≤ Real.sqrt ε := Real.sqrt_nonneg ε
  by_cases hε1 : ε ≤ 1
  · have hle : ε ≤ Real.sqrt ε := by
      rw [Real.le_sqrt hε hε]
      nlinarith
    calc
      x ≤ a * ε := hxa
      _ ≤ a * Real.sqrt ε := mul_le_mul_of_nonneg_left hle (by linarith)
      _ ≤ (a + 4) * Real.sqrt ε := by nlinarith
  · have hone : 1 ≤ Real.sqrt ε :=
      Real.one_le_sqrt.mpr (lt_of_not_ge hε1).le
    calc
      x ≤ 4 := hx4
      _ ≤ 4 * Real.sqrt ε := by nlinarith
      _ ≤ (a + 4) * Real.sqrt ε := by nlinarith

end MIPStarRE.QPBT
