import MIPStarRE.QPBT.Test.MagicSquareTheorems.Rigidity.AnticommutatorB
import MIPStarRE.QPBT.Test.MagicSquareTheorems.Rigidity.TwoQubitSwap

/-!
# Components of a bipartite pair of controlled swaps

The state estimate of `thm:ms-rigidity` compares the image of the shared state
under the tensor of the two players' controlled-swap embeddings with a
maximally entangled state on the extracted registers.  Written out in
coordinates, that image is the family of *residual components*

    `(X_A^b P^{Z_A}_b ⊗ X_B^c P^{Z_B}_c) v`

indexed by the two players' register labels `b` and `c`.  This file proves the
two estimates that the comparison needs, for one anticommuting pair on each
side, from the state-dependent hypotheses of the self-testing argument:

* an *off-diagonal* component, `b ≠ c`, is bounded by half the distance between
  the two players' phase reflections on the vector (`norm_swapComponent_01_le`,
  `norm_swapComponent_10_le`);
* the two *diagonal* components differ by at most the sum of the two
  cross-player distances and half the anticommutator defect of the pair on
  Alice's side (`norm_swapComponent_diag_sub_le`).

Neither estimate uses Bob's anticommutator defect, and neither assumes that the
vector is normalized: they are applied below both to the dilated state itself
and to its residual after the first controlled swap.

## References

blueprint `thm:ms-rigidity`,
paper `references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:612-652`;
the cited robust self-test is Coladangelo--Stark, arXiv:1709.09267v2,
Theorem 6.9, `references/cs-paper/self-testing.tex:660-730`.  The one-qubit
controlled swap is `binarySwapIsometry` in `Rigidity/Swap.lean`.
-/

open scoped BigOperators Matrix MatrixOrder ComplexOrder

namespace MIPStarRE.QPBT.MagicSquareRigidity

open MIPStarRE.LDT MIPStarRE.Quantum

noncomputable section

variable {ιA ιB : Type} [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB]

/-! ## Placement algebra -/

/-- A placed operator pair factors through the two one-sided placements. -/
theorem heteroKron_eq_left_mul_right (M : Op ιA) (N : Op ιB) :
    heteroKron M N = heteroKron M (1 : Op ιB) * heteroKron (1 : Op ιA) N := by
  rw [heteroKron_mul, mul_one, one_mul]

/-- The two one-sided placements commute. -/
theorem heteroKron_left_comm_right (M : Op ιA) (N : Op ιB) :
    heteroKron M (1 : Op ιB) * heteroKron (1 : Op ιA) N =
      heteroKron (1 : Op ιA) N * heteroKron M (1 : Op ιB) := by
  rw [heteroKron_mul, heteroKron_mul, mul_one, one_mul, mul_one, one_mul]

/-! ## Contractions -/

/-- The spectral effects of a binary observable are orthogonal projections. -/
theorem isProj_reflectionEffect {ι : Type} [Fintype ι] [DecidableEq ι]
    {Z : Op ι} (hZ : IsBinaryObservable Z) (b : ZMod 2) :
    IsProj (reflectionEffect Z b) :=
  reflectionMeasurement_projective Z hZ.conjTranspose_eq hZ.mul_self_eq_one b

/-- The spectral effects of a binary observable are contractions. -/
theorem contraction_reflectionEffect {ι : Type} [Fintype ι] [DecidableEq ι]
    {Z : Op ι} (hZ : IsBinaryObservable Z) (b : ZMod 2) :
    (reflectionEffect Z b)ᴴ * reflectionEffect Z b ≤ 1 :=
  conjTranspose_mul_le_one_of_isProj (isProj_reflectionEffect hZ b)

/-- A residual factor of a controlled swap is a contraction. -/
theorem contraction_swapFactor {ι : Type} [Fintype ι] [DecidableEq ι] {X Z : Op ι}
    (hX : IsBinaryObservable X) (hZ : IsBinaryObservable Z) (b : ZMod 2) :
    (X ^ b.val * reflectionEffect Z b)ᴴ * (X ^ b.val * reflectionEffect Z b) ≤ 1 := by
  have hP := contraction_reflectionEffect hZ b
  rcases zmod_two_eq_zero_or_one b with rfl | rfl
  · simpa only [ZMod.val_zero, pow_zero, one_mul] using hP
  · rw [ZMod.val_one, pow_one]
    exact conjTranspose_mul_le_one_mul (le_of_eq hX.isometry) hP

/-- A placed pair of contractions is a contraction. -/
theorem contraction_heteroKron {M : Op ιA} {N : Op ιB}
    (hM : Mᴴ * M ≤ 1) (hN : Nᴴ * N ≤ 1) :
    (heteroKron M N)ᴴ * heteroKron M N ≤ 1 := by
  rw [heteroKron_eq_left_mul_right]
  exact conjTranspose_mul_le_one_mul (conjTranspose_mul_le_one_leftTensor hM)
    (conjTranspose_mul_le_one_rightTensor hN)

/-! ## Elementary norm estimates -/

/-- The action on states is additive in the vector argument. -/
theorem applyOperatorToState_sub_vec {ι : Type} [Fintype ι] [DecidableEq ι] (M : Op ι)
    (u w : EuclideanSpace ℂ ι) :
    applyOperatorToState M u - applyOperatorToState M w = applyOperatorToState M (u - w) := by
  simp [applyOperatorToState]

/-- A contraction applied on the left contracts the distance between the
actions of two operators. -/
theorem norm_mul_sub_le {ι : Type} [Fintype ι] [DecidableEq ι] {M : Op ι} (A B : Op ι)
    (hM : Mᴴ * M ≤ 1) (v : EuclideanSpace ℂ ι) :
    ‖applyOperatorToState (M * A) v - applyOperatorToState (M * B) v‖ ≤
      ‖applyOperatorToState (A - B) v‖ := by
  rw [MIPStarRE.QPBT.DistanceCalculus.applyOperatorToState_mul,
    MIPStarRE.QPBT.DistanceCalculus.applyOperatorToState_mul, applyOperatorToState_sub_vec,
    ← applyOperatorToState_sub_op]
  exact norm_applyOperatorToState_le hM _

/-- The action of `1 + M` for a contraction `M` at most doubles the norm. -/
theorem norm_one_add_le {ι : Type} [Fintype ι] [DecidableEq ι] {M : Op ι}
    (hM : Mᴴ * M ≤ 1) (v : EuclideanSpace ℂ ι) :
    ‖applyOperatorToState (1 + M) v‖ ≤ 2 * ‖v‖ := by
  rw [applyOperatorToState_add_op, applyOperatorToState_one]
  refine le_trans (norm_add_le _ _) ?_
  have := norm_applyOperatorToState_le hM v
  linarith

/-- The action of `1 - M` for a contraction `M` at most doubles the norm. -/
theorem norm_one_sub_le {ι : Type} [Fintype ι] [DecidableEq ι] {M : Op ι}
    (hM : Mᴴ * M ≤ 1) (v : EuclideanSpace ℂ ι) :
    ‖applyOperatorToState (1 - M) v‖ ≤ 2 * ‖v‖ := by
  rw [applyOperatorToState_sub_op, applyOperatorToState_one]
  refine le_trans (norm_sub_le _ _) ?_
  have := norm_applyOperatorToState_le hM v
  linarith

/-! ## The two players' phase reflections -/

variable {XA ZA : Op ιA} {XB ZB : Op ιB}

/-- The placed spectral effects of the two players' phase reflections differ by
half the difference of the reflections themselves. -/
theorem heteroKron_reflection_sub_zero (ZA : Op ιA) (ZB : Op ιB) :
    heteroKron (1 : Op ιA) (reflectionEffect ZB 0) -
        heteroKron (reflectionEffect ZA 0) (1 : Op ιB) =
      (2 : ℂ)⁻¹ • (heteroKron (1 : Op ιA) ZB - heteroKron ZA (1 : Op ιB)) := by
  simp only [reflectionEffect, if_pos]
  rw [heteroKron_smul_right, heteroKron_smul_left, heteroKron_add_left,
    heteroKron_add_right, heteroKron_one_one]
  module

/-- The negative spectral effects of the two players' phase reflections differ
by half the difference of the reflections themselves. -/
theorem heteroKron_reflection_sub_one (ZA : Op ιA) (ZB : Op ιB) :
    heteroKron (1 : Op ιA) (reflectionEffect ZB 1) -
        heteroKron (reflectionEffect ZA 1) (1 : Op ιB) =
      (2 : ℂ)⁻¹ • (heteroKron ZA (1 : Op ιB) - heteroKron (1 : Op ιA) ZB) := by
  simp only [reflectionEffect, if_neg one_ne_zero]
  rw [heteroKron_smul_right, heteroKron_smul_left, heteroKron_sub_left,
    heteroKron_sub_right, heteroKron_one_one]
  module

/-- The mixed product of the two players' opposite spectral effects factors
through the difference of their phase reflections. -/
theorem heteroKron_reflection_zero_one (hZA : IsBinaryObservable ZA) (ZB : Op ιB) :
    heteroKron (reflectionEffect ZA 0) (reflectionEffect ZB 1) =
      (4 : ℂ)⁻¹ • ((1 + heteroKron ZA (1 : Op ιB)) *
        (heteroKron ZA (1 : Op ιB) - heteroKron (1 : Op ιA) ZB)) := by
  have hsq : heteroKron ZA (1 : Op ιB) * heteroKron ZA (1 : Op ιB) = 1 := by
    rw [heteroKron_mul, hZA.mul_self_eq_one, one_mul, heteroKron_one_one]
  have hfactor : heteroKron (reflectionEffect ZA 0) (reflectionEffect ZB 1) =
      (4 : ℂ)⁻¹ • ((1 + heteroKron ZA (1 : Op ιB)) *
        (1 - heteroKron (1 : Op ιA) ZB)) := by
    rw [heteroKron_eq_left_mul_right]
    simp only [reflectionEffect, if_pos, if_neg one_ne_zero]
    rw [heteroKron_smul_left, heteroKron_smul_right, heteroKron_add_left,
      heteroKron_sub_right, heteroKron_one_one]
    rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul]
    norm_num
  rw [hfactor]
  congr 1
  have hexp : (1 + heteroKron ZA (1 : Op ιB)) * (1 - heteroKron (1 : Op ιA) ZB) =
      (1 + heteroKron ZA (1 : Op ιB)) *
          (heteroKron ZA (1 : Op ιB) - heteroKron (1 : Op ιA) ZB) +
        (1 - heteroKron ZA (1 : Op ιB) * heteroKron ZA (1 : Op ιB)) := by
    noncomm_ring
  rw [hexp, hsq, sub_self, add_zero]

/-- The mixed product of the two players' opposite spectral effects, in the
other orientation, factors through the difference of their phase reflections. -/
theorem heteroKron_reflection_one_zero (hZA : IsBinaryObservable ZA) (ZB : Op ιB) :
    heteroKron (reflectionEffect ZA 1) (reflectionEffect ZB 0) =
      (4 : ℂ)⁻¹ • ((1 - heteroKron ZA (1 : Op ιB)) *
        (heteroKron (1 : Op ιA) ZB - heteroKron ZA (1 : Op ιB))) := by
  have hsq : heteroKron ZA (1 : Op ιB) * heteroKron ZA (1 : Op ιB) = 1 := by
    rw [heteroKron_mul, hZA.mul_self_eq_one, one_mul, heteroKron_one_one]
  have hfactor : heteroKron (reflectionEffect ZA 1) (reflectionEffect ZB 0) =
      (4 : ℂ)⁻¹ • ((1 - heteroKron ZA (1 : Op ιB)) *
        (1 + heteroKron (1 : Op ιA) ZB)) := by
    rw [heteroKron_eq_left_mul_right]
    simp only [reflectionEffect, if_pos, if_neg one_ne_zero]
    rw [heteroKron_smul_left, heteroKron_smul_right, heteroKron_sub_left,
      heteroKron_add_right, heteroKron_one_one]
    rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul]
    norm_num
  rw [hfactor]
  congr 1
  have hexp : (1 - heteroKron ZA (1 : Op ιB)) * (1 + heteroKron (1 : Op ιA) ZB) =
      (1 - heteroKron ZA (1 : Op ιB)) *
          (heteroKron (1 : Op ιA) ZB - heteroKron ZA (1 : Op ιB)) +
        (1 - heteroKron ZA (1 : Op ιB) * heteroKron ZA (1 : Op ιB)) := by
    noncomm_ring
  rw [hexp, hsq, sub_self, add_zero]

/-! ## Right placement of a binary observable -/

/-- The right placement of a binary observable is a binary observable.  This is
the right-hand counterpart of `isBinaryObservable_heteroKron_one`. -/
theorem isBinaryObservable_heteroKron_right {ι ι' : Type} [Fintype ι] [DecidableEq ι]
    [Fintype ι'] [DecidableEq ι'] {O : Op ι'} (hO : IsBinaryObservable O) :
    IsBinaryObservable (heteroKron (1 : Op ι) O) := by
  unfold heteroKron
  simp only [Matrix.kronecker]
  refine ⟨?_, ?_⟩
  · rw [Matrix.IsHermitian, Matrix.conjTranspose_kronecker, hO.conjTranspose_eq,
      Matrix.conjTranspose_one]
  · rw [← Matrix.mul_kronecker_mul, hO.mul_self_eq_one, Matrix.one_mul,
      Matrix.one_kronecker_one]

/-! ## The two off-diagonal components -/

/-- The residual component of the two controlled swaps at the label pair
`(0, 1)` is at most half the cross-player distance of the phase reflections. -/
theorem norm_swapComponent_01_le (hZA : IsBinaryObservable ZA)
    (hXB : IsBinaryObservable XB) (v : EuclideanSpace ℂ (ιA × ιB)) :
    ‖applyOperatorToState
        (heteroKron (reflectionEffect ZA 0) (XB * reflectionEffect ZB 1)) v‖ ≤
      (2 : ℝ)⁻¹ * ‖applyOperatorToState
        (heteroKron ZA (1 : Op ιB) - heteroKron (1 : Op ιA) ZB) v‖ := by
  have hsplit : heteroKron (reflectionEffect ZA 0) (XB * reflectionEffect ZB 1) =
      heteroKron (1 : Op ιA) XB *
        heteroKron (reflectionEffect ZA 0) (reflectionEffect ZB 1) := by
    rw [heteroKron_mul, one_mul]
  rw [hsplit, norm_applyOperatorToState_isometry_mul
      (isBinaryObservable_heteroKron_right (ι := ιA) hXB).isometry,
    heteroKron_reflection_zero_one hZA ZB, applyOperatorToState_smul, norm_smul,
    MIPStarRE.QPBT.DistanceCalculus.applyOperatorToState_mul]
  have hbound := norm_one_add_le
    (le_of_eq (isBinaryObservable_heteroKron_one (ι' := ιB) hZA).isometry)
    (applyOperatorToState
      (heteroKron ZA (1 : Op ιB) - heteroKron (1 : Op ιA) ZB) v)
  have hnorm : ‖(4 : ℂ)⁻¹‖ = (4 : ℝ)⁻¹ := by norm_num
  rw [hnorm]
  nlinarith [hbound, norm_nonneg (applyOperatorToState
    (heteroKron ZA (1 : Op ιB) - heteroKron (1 : Op ιA) ZB) v)]

/-- The residual component of the two controlled swaps at the label pair
`(1, 0)` is at most half the cross-player distance of the phase reflections. -/
theorem norm_swapComponent_10_le (hXA : IsBinaryObservable XA)
    (hZA : IsBinaryObservable ZA) (v : EuclideanSpace ℂ (ιA × ιB)) :
    ‖applyOperatorToState
        (heteroKron (XA * reflectionEffect ZA 1) (reflectionEffect ZB 0)) v‖ ≤
      (2 : ℝ)⁻¹ * ‖applyOperatorToState
        (heteroKron ZA (1 : Op ιB) - heteroKron (1 : Op ιA) ZB) v‖ := by
  have hsplit : heteroKron (XA * reflectionEffect ZA 1) (reflectionEffect ZB 0) =
      heteroKron XA (1 : Op ιB) *
        heteroKron (reflectionEffect ZA 1) (reflectionEffect ZB 0) := by
    rw [heteroKron_mul, one_mul]
  have hrev : ‖applyOperatorToState
        (heteroKron (1 : Op ιA) ZB - heteroKron ZA (1 : Op ιB)) v‖ =
      ‖applyOperatorToState
        (heteroKron ZA (1 : Op ιB) - heteroKron (1 : Op ιA) ZB) v‖ :=
    norm_applyOperatorToState_sub_comm _ _ v
  rw [hsplit, norm_applyOperatorToState_isometry_mul
      (isBinaryObservable_heteroKron_one (ι' := ιB) hXA).isometry,
    heteroKron_reflection_one_zero hZA ZB, applyOperatorToState_smul, norm_smul,
    MIPStarRE.QPBT.DistanceCalculus.applyOperatorToState_mul]
  have hbound := norm_one_sub_le
    (le_of_eq (isBinaryObservable_heteroKron_one (ι' := ιB) hZA).isometry)
    (applyOperatorToState
      (heteroKron (1 : Op ιA) ZB - heteroKron ZA (1 : Op ιB)) v)
  rw [hrev] at hbound
  have hnorm : ‖(4 : ℂ)⁻¹‖ = (4 : ℝ)⁻¹ := by norm_num
  rw [hnorm]
  nlinarith [hbound, norm_nonneg (applyOperatorToState
    (heteroKron ZA (1 : Op ιB) - heteroKron (1 : Op ιA) ZB) v)]

/-! ## The diagonal components -/

/-- Halving a placed operator halves the norm of its action. -/
theorem norm_apply_half_smul {ι : Type} [Fintype ι] [DecidableEq ι] (M : Op ι)
    (v : EuclideanSpace ℂ ι) :
    ‖applyOperatorToState ((2 : ℂ)⁻¹ • M) v‖ = (2 : ℝ)⁻¹ * ‖applyOperatorToState M v‖ := by
  rw [applyOperatorToState_smul, norm_smul]
  norm_num

/-- A placed operator with a product on the right splits into three factors. -/
theorem heteroKron_split_right (M : Op ιA) (N P : Op ιB) :
    heteroKron M (N * P) =
      heteroKron M (1 : Op ιB) * heteroKron (1 : Op ιA) N * heteroKron (1 : Op ιA) P := by
  rw [heteroKron_mul, heteroKron_mul]
  simp

/-- The two diagonal residual components of the two controlled swaps differ by
at most the two cross-player distances of the pair plus half Alice's
anticommutator defect. -/
theorem norm_swapComponent_diag_sub_le
    (hXA : IsBinaryObservable XA) (hZA : IsBinaryObservable ZA)
    (hXB : IsBinaryObservable XB) (_hZB : IsBinaryObservable ZB)
    (v : EuclideanSpace ℂ (ιA × ιB)) :
    ‖applyOperatorToState
          (heteroKron (XA * reflectionEffect ZA 1) (XB * reflectionEffect ZB 1)) v -
        applyOperatorToState
          (heteroKron (reflectionEffect ZA 0) (reflectionEffect ZB 0)) v‖ ≤
      ‖applyOperatorToState
          (heteroKron ZA (1 : Op ιB) - heteroKron (1 : Op ιA) ZB) v‖ +
        ‖applyOperatorToState
          (heteroKron XA (1 : Op ιB) - heteroKron (1 : Op ιA) XB) v‖ +
        (2 : ℝ)⁻¹ * ‖applyOperatorToState
          (heteroKron (XA * ZA + ZA * XA) (1 : Op ιB)) v‖ := by
  have hLXiso := (isBinaryObservable_heteroKron_one (ι' := ιB) hXA).isometry
  have hP0 : reflectionEffect ZA 0 * reflectionEffect ZA 0 = reflectionEffect ZA 0 :=
    (isProj_reflectionEffect hZA 0).isIdempotentElem.eq
  have hP1 : reflectionEffect ZA 1 * reflectionEffect ZA 1 = reflectionEffect ZA 1 :=
    (isProj_reflectionEffect hZA 1).isIdempotentElem.eq
  have hcLP0 : (heteroKron (reflectionEffect ZA 0) (1 : Op ιB))ᴴ *
      heteroKron (reflectionEffect ZA 0) (1 : Op ιB) ≤ 1 :=
    conjTranspose_mul_le_one_leftTensor (contraction_reflectionEffect hZA 0)
  have hcXP1 : (heteroKron (XA * reflectionEffect ZA 1) (1 : Op ιB))ᴴ *
      heteroKron (XA * reflectionEffect ZA 1) (1 : Op ιB) ≤ 1 :=
    conjTranspose_mul_le_one_leftTensor
      (conjTranspose_mul_le_one_mul (le_of_eq hXA.isometry)
        (contraction_reflectionEffect hZA 1))
  have hcG : (heteroKron (XA * reflectionEffect ZA 1) (1 : Op ιB) *
        heteroKron (1 : Op ιA) XB)ᴴ *
      (heteroKron (XA * reflectionEffect ZA 1) (1 : Op ιB) *
        heteroKron (1 : Op ιA) XB) ≤ 1 :=
    conjTranspose_mul_le_one_mul hcXP1
      (conjTranspose_mul_le_one_rightTensor (le_of_eq hXB.isometry))
  -- Step A: the `(0,0)` component is close to Alice's positive spectral effect.
  have hA1 : heteroKron (reflectionEffect ZA 0) (reflectionEffect ZB 0) =
      heteroKron (reflectionEffect ZA 0) (1 : Op ιB) *
        heteroKron (1 : Op ιA) (reflectionEffect ZB 0) :=
    heteroKron_eq_left_mul_right _ _
  have hA2 : heteroKron (reflectionEffect ZA 0) (1 : Op ιB) *
      heteroKron (reflectionEffect ZA 0) (1 : Op ιB) =
      heteroKron (reflectionEffect ZA 0) (1 : Op ιB) := by
    rw [heteroKron_mul, hP0, one_mul]
  have hA : ‖applyOperatorToState
        (heteroKron (reflectionEffect ZA 0) (reflectionEffect ZB 0)) v -
      applyOperatorToState (heteroKron (reflectionEffect ZA 0) (1 : Op ιB)) v‖ ≤
      (2 : ℝ)⁻¹ * ‖applyOperatorToState
        (heteroKron ZA (1 : Op ιB) - heteroKron (1 : Op ιA) ZB) v‖ := by
    have key := norm_mul_sub_le (M := heteroKron (reflectionEffect ZA 0) (1 : Op ιB))
      (heteroKron (1 : Op ιA) (reflectionEffect ZB 0))
      (heteroKron (reflectionEffect ZA 0) (1 : Op ιB)) hcLP0 v
    rw [← hA1, hA2, heteroKron_reflection_sub_zero, norm_apply_half_smul,
      norm_applyOperatorToState_sub_comm] at key
    exact key
  -- Step B: the `(1,1)` component is close to the transported product.
  have hB1 : heteroKron (XA * reflectionEffect ZA 1) (XB * reflectionEffect ZB 1) =
      heteroKron (XA * reflectionEffect ZA 1) (1 : Op ιB) * heteroKron (1 : Op ιA) XB *
        heteroKron (1 : Op ιA) (reflectionEffect ZB 1) :=
    heteroKron_split_right _ _ _
  have hB2 : heteroKron (XA * reflectionEffect ZA 1) (1 : Op ιB) *
        heteroKron (1 : Op ιA) XB *
        heteroKron (reflectionEffect ZA 1) (1 : Op ιB) =
      heteroKron (XA * reflectionEffect ZA 1) (1 : Op ιB) * heteroKron (1 : Op ιA) XB := by
    calc heteroKron (XA * reflectionEffect ZA 1) (1 : Op ιB) *
          heteroKron (1 : Op ιA) XB * heteroKron (reflectionEffect ZA 1) (1 : Op ιB)
        = heteroKron (XA * reflectionEffect ZA 1) (1 : Op ιB) *
            (heteroKron (1 : Op ιA) XB * heteroKron (reflectionEffect ZA 1) (1 : Op ιB)) := by
          rw [mul_assoc]
      _ = heteroKron (XA * reflectionEffect ZA 1) (1 : Op ιB) *
            (heteroKron (reflectionEffect ZA 1) (1 : Op ιB) * heteroKron (1 : Op ιA) XB) := by
          rw [heteroKron_left_comm_right]
      _ = heteroKron (XA * reflectionEffect ZA 1) (1 : Op ιB) *
            heteroKron (reflectionEffect ZA 1) (1 : Op ιB) * heteroKron (1 : Op ιA) XB := by
          rw [mul_assoc]
      _ = heteroKron (XA * reflectionEffect ZA 1) (1 : Op ιB) *
            heteroKron (1 : Op ιA) XB := by
          rw [heteroKron_mul, mul_one, mul_assoc, hP1]
  have hB : ‖applyOperatorToState
        (heteroKron (XA * reflectionEffect ZA 1) (XB * reflectionEffect ZB 1)) v -
      applyOperatorToState (heteroKron (XA * reflectionEffect ZA 1) (1 : Op ιB) *
        heteroKron (1 : Op ιA) XB) v‖ ≤
      (2 : ℝ)⁻¹ * ‖applyOperatorToState
        (heteroKron ZA (1 : Op ιB) - heteroKron (1 : Op ιA) ZB) v‖ := by
    have key := norm_mul_sub_le
      (M := heteroKron (XA * reflectionEffect ZA 1) (1 : Op ιB) * heteroKron (1 : Op ιA) XB)
      (heteroKron (1 : Op ιA) (reflectionEffect ZB 1))
      (heteroKron (reflectionEffect ZA 1) (1 : Op ιB)) hcG v
    rw [← hB1, hB2, heteroKron_reflection_sub_one, norm_apply_half_smul] at key
    exact key
  -- Step C: replace Bob's shift reflection by Alice's.
  have hC1 : heteroKron (XA * reflectionEffect ZA 1) (1 : Op ιB) *
      heteroKron XA (1 : Op ιB) =
      heteroKron (XA * reflectionEffect ZA 1 * XA) (1 : Op ιB) := by
    rw [heteroKron_mul, mul_one]
  have hC : ‖applyOperatorToState (heteroKron (XA * reflectionEffect ZA 1) (1 : Op ιB) *
        heteroKron (1 : Op ιA) XB) v -
      applyOperatorToState (heteroKron (XA * reflectionEffect ZA 1 * XA) (1 : Op ιB)) v‖ ≤
      ‖applyOperatorToState
        (heteroKron XA (1 : Op ιB) - heteroKron (1 : Op ιA) XB) v‖ := by
    have key := norm_mul_sub_le (M := heteroKron (XA * reflectionEffect ZA 1) (1 : Op ιB))
      (heteroKron (1 : Op ιA) XB) (heteroKron XA (1 : Op ιB)) hcXP1 v
    rw [hC1, norm_applyOperatorToState_sub_comm] at key
    exact key
  -- Step D: the conjugated negative effect is the positive effect up to the
  -- anticommutator.
  have hD : ‖applyOperatorToState
        (heteroKron (XA * reflectionEffect ZA 1 * XA) (1 : Op ιB)) v -
      applyOperatorToState (heteroKron (reflectionEffect ZA 0) (1 : Op ιB)) v‖ ≤
      (2 : ℝ)⁻¹ * ‖applyOperatorToState
        (heteroKron (XA * ZA + ZA * XA) (1 : Op ιB)) v‖ := by
    have hfac : heteroKron (XA * (XA * ZA + ZA * XA)) (1 : Op ιB) =
        heteroKron XA (1 : Op ιB) * heteroKron (XA * ZA + ZA * XA) (1 : Op ιB) := by
      rw [heteroKron_mul, mul_one]
    rw [← applyOperatorToState_sub_op, ← heteroKron_sub_left,
      X_mul_reflectionEffect_one_mul_X_sub_zero XA ZA hXA,
      heteroKron_smul_left, applyOperatorToState_smul, norm_smul, hfac,
      norm_applyOperatorToState_isometry_mul hLXiso,
      show ‖(-(2 : ℂ)⁻¹ : ℂ)‖ = (2 : ℝ)⁻¹ by rw [norm_neg]; norm_num]
  -- Assemble the four steps.
  have htri : ‖applyOperatorToState
        (heteroKron (XA * reflectionEffect ZA 1) (XB * reflectionEffect ZB 1)) v -
      applyOperatorToState
        (heteroKron (reflectionEffect ZA 0) (reflectionEffect ZB 0)) v‖ ≤
      ‖applyOperatorToState
          (heteroKron (XA * reflectionEffect ZA 1) (XB * reflectionEffect ZB 1)) v -
        applyOperatorToState (heteroKron (XA * reflectionEffect ZA 1) (1 : Op ιB) *
          heteroKron (1 : Op ιA) XB) v‖ +
      ‖applyOperatorToState (heteroKron (XA * reflectionEffect ZA 1) (1 : Op ιB) *
          heteroKron (1 : Op ιA) XB) v -
        applyOperatorToState (heteroKron (XA * reflectionEffect ZA 1 * XA) (1 : Op ιB)) v‖ +
      ‖applyOperatorToState (heteroKron (XA * reflectionEffect ZA 1 * XA) (1 : Op ιB)) v -
        applyOperatorToState (heteroKron (reflectionEffect ZA 0) (1 : Op ιB)) v‖ +
      ‖applyOperatorToState (heteroKron (reflectionEffect ZA 0) (1 : Op ιB)) v -
        applyOperatorToState
          (heteroKron (reflectionEffect ZA 0) (reflectionEffect ZB 0)) v‖ := by
    have h1 := norm_sub_le_norm_sub_add_norm_sub
      (applyOperatorToState
        (heteroKron (XA * reflectionEffect ZA 1) (XB * reflectionEffect ZB 1)) v)
      (applyOperatorToState (heteroKron (XA * reflectionEffect ZA 1) (1 : Op ιB) *
        heteroKron (1 : Op ιA) XB) v)
      (applyOperatorToState
        (heteroKron (reflectionEffect ZA 0) (reflectionEffect ZB 0)) v)
    have h2 := norm_sub_le_norm_sub_add_norm_sub
      (applyOperatorToState (heteroKron (XA * reflectionEffect ZA 1) (1 : Op ιB) *
        heteroKron (1 : Op ιA) XB) v)
      (applyOperatorToState (heteroKron (XA * reflectionEffect ZA 1 * XA) (1 : Op ιB)) v)
      (applyOperatorToState
        (heteroKron (reflectionEffect ZA 0) (reflectionEffect ZB 0)) v)
    have h3 := norm_sub_le_norm_sub_add_norm_sub
      (applyOperatorToState (heteroKron (XA * reflectionEffect ZA 1 * XA) (1 : Op ιB)) v)
      (applyOperatorToState (heteroKron (reflectionEffect ZA 0) (1 : Op ιB)) v)
      (applyOperatorToState
        (heteroKron (reflectionEffect ZA 0) (reflectionEffect ZB 0)) v)
    linarith
  have hAsym : ‖applyOperatorToState (heteroKron (reflectionEffect ZA 0) (1 : Op ιB)) v -
      applyOperatorToState
        (heteroKron (reflectionEffect ZA 0) (reflectionEffect ZB 0)) v‖ ≤
      (2 : ℝ)⁻¹ * ‖applyOperatorToState
        (heteroKron ZA (1 : Op ιB) - heteroKron (1 : Op ιA) ZB) v‖ := by
    rw [norm_sub_rev]
    exact hA
  linarith [htri, hB, hC, hD, hAsym]

end

end MIPStarRE.QPBT.MagicSquareRigidity
