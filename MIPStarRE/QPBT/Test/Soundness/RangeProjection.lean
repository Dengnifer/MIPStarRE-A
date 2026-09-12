import MIPStarRE.QPBT.Test.MagicSquareTheorems.Rigidity.GroundSlice

/-!
# Range projections in Pauli soundness

Inserting an orthogonal projection into a measurement comparison costs at most
twice the squared distance to a vector fixed by that projection. Summing over
the measurement outcomes introduces no factor depending on their number.

## References

These are formalization-only auxiliary estimates for the final proof of
blueprint `thm:pauli`. The range projection is omitted at
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1864-1875`;
the corrected calculation is given in `docs/paper-gaps/qpbt_extraction-transfer.tex`.
They do not construct the extraction data or prove Pauli soundness.
-/

open scoped BigOperators Matrix MatrixOrder ComplexOrder

namespace MIPStarRE.QPBT

open MIPStarRE.Quantum
open DistanceCalculus MagicSquareRigidity

/-- The identity conjugated by an isometry is its orthogonal range projection. -/
private theorem conjIsometry_one_isProj {ι κ : Type}
    [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (phi : EuclideanSpace ℂ ι →ₗᵢ[ℂ] EuclideanSpace ℂ κ) :
    IsProj (conjIsometry phi 1) := by
  constructor
  · change conjIsometry phi 1 * conjIsometry phi 1 = conjIsometry phi 1
    rw [conjIsometry_mul, Matrix.one_mul]
  · change star (conjIsometry phi 1) = conjIsometry phi 1
    simp [conjIsometry_eq, Matrix.star_eq_conjTranspose, Matrix.conjTranspose_mul]

/-- Intertwining identifies isometry conjugation with insertion of its range projection. -/
private theorem mul_conjIsometry_one_eq {ι κ : Type}
    [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (phi : EuclideanSpace ℂ ι →ₗᵢ[ℂ] EuclideanSpace ℂ κ) (M : Op ι) (N : Op κ)
    (hintertwine : N * isometryMatrix phi = isometryMatrix phi * M) :
    N * conjIsometry phi 1 = conjIsometry phi M := by
  rw [conjIsometry_eq, Matrix.mul_one, ← Matrix.mul_assoc, hintertwine]
  rfl

/-- Inserting a projection that fixes `theta` into a complete POVM costs at most
twice the squared distance from the comparison state to `theta`, in addition
to twice the original operator-family distance. This is blueprint
`thm:pauli-range-projection-support`, the analytic range-projection estimate
supporting `thm:pauli`. It holds for every complete POVM. -/
theorem sum_norm_mul_projection_sub_sq_le {α ι : Type*}
    [Fintype α] [Fintype ι] [DecidableEq ι]
    (N : MIPStarRE.Quantum.Measurement α ι) (T : α → Op ι)
    (Q : Op ι) (hQ : IsProj Q) (theta delta : EuclideanSpace ℂ ι)
    (htheta : applyOperatorToState Q theta = theta) :
    ∑ a : α, ‖applyOperatorToState (N.effect a * Q - T a) delta‖ ^ 2 ≤
      2 * (∑ a : α, ‖applyOperatorToState (N.effect a - T a) delta‖ ^ 2) +
        2 * ‖delta - theta‖ ^ 2 := by
  have hvanish : applyOperatorToState (1 - Q) theta = 0 := by
    have hfix : Matrix.toEuclideanLin Q theta = theta := htheta
    simp [applyOperatorToState, hfix]
  have hcomplement :
      ‖applyOperatorToState (1 - Q) delta‖ ^ 2 ≤ ‖delta - theta‖ ^ 2 := by
    have hnorm := norm_applyOperatorToState_le
      (conjTranspose_mul_le_one_of_isProj hQ.one_sub) (delta - theta)
    rw [applyOperatorToState_sub, hvanish, sub_zero] at hnorm
    exact pow_le_pow_left₀ (norm_nonneg _) hnorm 2
  have hsum := sum_norm_mul_apply_le N.effect (1 - Q) delta
    (MIPStarRE.QPBT.measurement_sum_adjoint_mul_le_one N)
  calc
    ∑ a : α, ‖applyOperatorToState (N.effect a * Q - T a) delta‖ ^ 2 ≤
        ∑ a : α, (2 * ‖applyOperatorToState (N.effect a - T a) delta‖ ^ 2 +
          2 * ‖applyOperatorToState (N.effect a * (1 - Q)) delta‖ ^ 2) := by
      apply Finset.sum_le_sum
      intro a _
      have hsplit : N.effect a * Q - T a =
          (N.effect a - T a) - N.effect a * (1 - Q) := by
        rw [mul_sub, mul_one]
        abel
      have hsplit_action : applyOperatorToState (N.effect a * Q - T a) delta =
          applyOperatorToState (N.effect a - T a) delta -
            applyOperatorToState (N.effect a * (1 - Q)) delta := by
        rw [hsplit]
        simp only [applyOperatorToState, map_sub, LinearMap.sub_apply]
      rw [hsplit_action]
      have hpar := parallelogram_law_with_norm ℂ
        (applyOperatorToState (N.effect a - T a) delta)
        (applyOperatorToState (N.effect a * (1 - Q)) delta)
      exact (le_add_of_nonneg_left (sq_nonneg
        ‖applyOperatorToState (N.effect a - T a) delta +
          applyOperatorToState (N.effect a * (1 - Q)) delta‖)).trans_eq
        (hpar.trans (mul_add 2 _ _))
    _ = 2 * (∑ a : α, ‖applyOperatorToState (N.effect a - T a) delta‖ ^ 2) +
        2 * (∑ a : α, ‖applyOperatorToState (N.effect a * (1 - Q)) delta‖ ^ 2) := by
      rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]
    _ ≤ _ := add_le_add le_rfl (mul_le_mul_of_nonneg_left
      (hsum.trans hcomplement) (by norm_num))

/-- The range-projection estimate for an isometry intertwining an operator
family with a complete POVM, as in blueprint `thm:pauli-isometry-transfer-support`.
The intertwining identity is an exact operator
identity, as obtained by adjoining a fixed ancilla and then conjugating by a
unitary in the final proof of blueprint `thm:pauli`. No state or operator
closeness is assumed: both errors appear explicitly on the right-hand side. -/
theorem sum_norm_conjIsometry_sub_sq_le {α ι κ : Type}
    [Fintype α] [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (phi : EuclideanSpace ℂ ι →ₗᵢ[ℂ] EuclideanSpace ℂ κ)
    (M : α → Op ι) (N : MIPStarRE.Quantum.Measurement α κ) (T : α → Op κ)
    (hintertwine : ∀ a : α,
      N.effect a * isometryMatrix phi = isometryMatrix phi * M a)
    (psi : EuclideanSpace ℂ ι) (delta : EuclideanSpace ℂ κ) :
    ∑ a : α, ‖applyOperatorToState (conjIsometry phi (M a) - T a) delta‖ ^ 2 ≤
      2 * (∑ a : α, ‖applyOperatorToState (N.effect a - T a) delta‖ ^ 2) +
        2 * ‖delta - phi psi‖ ^ 2 := by
  let Q : Op κ := conjIsometry phi 1
  have hQ : IsProj Q := conjIsometry_one_isProj phi
  have hmatrix : Matrix.toEuclideanLin (isometryMatrix phi) = phi.toLinearMap :=
    Matrix.toEuclideanLin.apply_symm_apply phi.toLinearMap
  have hfix : applyOperatorToState Q (phi psi) = phi psi := by
    change Matrix.toEuclideanLin (conjIsometry phi 1) (phi.toLinearMap psi) =
      phi.toLinearMap psi
    rw [conjIsometry_eq, Matrix.mul_one, ← hmatrix, ← toEuclideanLin_mul_apply,
      Matrix.mul_assoc, isometryMatrix_conjTranspose_mul, Matrix.mul_one]
  have hcompression (a : α) : N.effect a * Q = conjIsometry phi (M a) :=
    mul_conjIsometry_one_eq phi (M a) (N.effect a) (hintertwine a)
  simpa only [hcompression] using
    sum_norm_mul_projection_sub_sq_le N T Q hQ (phi psi) delta hfix

/-- Alice's isometry transfer on a bipartite comparison state. The state error
uses both local isometries, while each effect is conjugated only by Alice's
isometry, as required by blueprint `thm:pauli`. The exact local intertwining
identity is the one obtained from the ancilla extension and swap unitary.
This is blueprint `thm:pauli-isometry-transfer-alice-support`. -/
theorem sum_norm_leftTensor_conjIsometry_sub_sq_le {α ιA ιB κA κB : Type}
    [Fintype α] [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB]
    [Fintype κA] [DecidableEq κA] [Fintype κB] [DecidableEq κB]
    (phiA : EuclideanSpace ℂ ιA →ₗᵢ[ℂ] EuclideanSpace ℂ κA)
    (phiB : EuclideanSpace ℂ ιB →ₗᵢ[ℂ] EuclideanSpace ℂ κB)
    (M : α → Op ιA) (N : MIPStarRE.Quantum.Measurement α κA)
    (T : α → Op (κA × κB))
    (hintertwine : ∀ a : α,
      N.effect a * isometryMatrix phiA = isometryMatrix phiA * M a)
    (psi : EuclideanSpace ℂ (ιA × ιB)) (delta : EuclideanSpace ℂ (κA × κB)) :
    ∑ a : α, ‖applyOperatorToState
        (heteroKron (conjIsometry phiA (M a)) 1 - T a) delta‖ ^ 2 ≤
      2 * (∑ a : α, ‖applyOperatorToState (heteroKron (N.effect a) 1 - T a) delta‖ ^ 2) +
        2 * ‖delta - isometryTensor phiA phiB psi‖ ^ 2 := by
  let Q : Op (κA × κB) := heteroKron (conjIsometry phiA 1) 1
  have hQ : IsProj Q := by
    constructor
    · change Q * Q = Q
      simp only [Q, heteroKron_mul, Matrix.one_mul,
        (conjIsometry_one_isProj phiA).isIdempotentElem.eq]
    · change star Q = Q
      simp only [Q, Matrix.star_eq_conjTranspose, heteroKron, Matrix.kronecker,
        Matrix.conjTranspose_kronecker, Matrix.conjTranspose_one,
        (conjIsometry_one_isProj phiA).isSelfAdjoint.isHermitian.eq]
  have hfix : applyOperatorToState Q (isometryTensor phiA phiB psi) =
      isometryTensor phiA phiB psi := by
    dsimp only [Q]
    rw [applyOperatorToState_leftTensor_conjIsometry, heteroKron_one_one,
      applyOperatorToState_one]
  have hcompression (a : α) : (leftPlacedMeasurement N).effect a * Q =
      heteroKron (conjIsometry phiA (M a)) 1 := by
    change heteroKron (N.effect a) 1 * heteroKron (conjIsometry phiA 1) 1 = _
    rw [heteroKron_mul, Matrix.one_mul,
      mul_conjIsometry_one_eq phiA (M a) (N.effect a) (hintertwine a)]
  have hbound := sum_norm_mul_projection_sub_sq_le (leftPlacedMeasurement N) T Q hQ
    (isometryTensor phiA phiB psi) delta hfix
  simp only [hcompression] at hbound
  simpa only [leftPlacedMeasurement, MIPStarRE.Quantum.Measurement.ofSumEqOne] using hbound

/-- Bob's isometry transfer on a bipartite comparison state, with the same
state error and constants independent of the answer count as Alice's transfer.
This is blueprint `thm:pauli-isometry-transfer-bob-support`, the second
operator comparison needed in the proof of `thm:pauli`. -/
theorem sum_norm_rightTensor_conjIsometry_sub_sq_le {α ιA ιB κA κB : Type}
    [Fintype α] [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB]
    [Fintype κA] [DecidableEq κA] [Fintype κB] [DecidableEq κB]
    (phiA : EuclideanSpace ℂ ιA →ₗᵢ[ℂ] EuclideanSpace ℂ κA)
    (phiB : EuclideanSpace ℂ ιB →ₗᵢ[ℂ] EuclideanSpace ℂ κB)
    (M : α → Op ιB) (N : MIPStarRE.Quantum.Measurement α κB)
    (T : α → Op (κA × κB))
    (hintertwine : ∀ a : α,
      N.effect a * isometryMatrix phiB = isometryMatrix phiB * M a)
    (psi : EuclideanSpace ℂ (ιA × ιB)) (delta : EuclideanSpace ℂ (κA × κB)) :
    ∑ a : α, ‖applyOperatorToState
        (heteroKron 1 (conjIsometry phiB (M a)) - T a) delta‖ ^ 2 ≤
      2 * (∑ a : α, ‖applyOperatorToState (heteroKron 1 (N.effect a) - T a) delta‖ ^ 2) +
        2 * ‖delta - isometryTensor phiA phiB psi‖ ^ 2 := by
  let Q : Op (κA × κB) := heteroKron 1 (conjIsometry phiB 1)
  have hQ : IsProj Q := by
    constructor
    · change Q * Q = Q
      simp only [Q, heteroKron_mul, Matrix.one_mul,
        (conjIsometry_one_isProj phiB).isIdempotentElem.eq]
    · change star Q = Q
      simp only [Q, Matrix.star_eq_conjTranspose, heteroKron, Matrix.kronecker,
        Matrix.conjTranspose_kronecker, Matrix.conjTranspose_one,
        (conjIsometry_one_isProj phiB).isSelfAdjoint.isHermitian.eq]
  have hfix : applyOperatorToState Q (isometryTensor phiA phiB psi) =
      isometryTensor phiA phiB psi := by
    dsimp only [Q]
    rw [applyOperatorToState_rightTensor_conjIsometry, heteroKron_one_one,
      applyOperatorToState_one]
  have hcompression (a : α) : (rightPlacedMeasurement N).effect a * Q =
      heteroKron 1 (conjIsometry phiB (M a)) := by
    change heteroKron 1 (N.effect a) * heteroKron 1 (conjIsometry phiB 1) = _
    rw [heteroKron_mul, Matrix.one_mul,
      mul_conjIsometry_one_eq phiB (M a) (N.effect a) (hintertwine a)]
  have hbound := sum_norm_mul_projection_sub_sq_le (rightPlacedMeasurement N) T Q hQ
    (isometryTensor phiA phiB psi) delta hfix
  simp only [hcompression] at hbound
  simpa only [rightPlacedMeasurement, MIPStarRE.Quantum.Measurement.ofSumEqOne] using hbound

end MIPStarRE.QPBT
