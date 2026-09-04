import MIPStarRE.QPBT.Test.MagicSquareTheorems.Rigidity.Dilation

/-!
# Approximate anticommutation in the Magic Square game

This file builds the operator layer of the Magic Square rigidity argument on
the projective dilation of an arbitrary strategy.  Postprocessing a projective
measurement along a binary function produces a *reflection*, a self-adjoint
involution, and the reflections attached to one and the same question commute
exactly and multiply according to the sum of the postprocessing functions.  The
value-to-parity relations then bound, on the dilated state, the deviation of
each row or column product from the sign prescribed by the corresponding linear
equation, and the deviation between the two reflections attached to a common
cell by the two players.  From these estimates one extracts, at the two cells
labelled by the paper's first and fifth variables, a pair of reflections on each
side whose commutator is small and whose anticommutator is small.

All estimates are stated with explicit constants in the state-dependent norm
associated with the dilated state.

## References

The statement supported here is `thm:ms-rigidity` in
`blueprint/src/chapter/ch13_qpbt_test.tex:224-253`, from
`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:612-652`,
proved in Coladangelo--Stark, arXiv:1709.09267v2, Theorem 6.9; the operator
relations formalized here are the Magic Square instance of the solution-group
relations used there.
-/

open scoped BigOperators Matrix MatrixOrder ComplexOrder

namespace MIPStarRE.QPBT.MagicSquareRigidity

open MIPStarRE.LDT MIPStarRE.Quantum

noncomputable section

/-! ## Rectangular tensor placement -/

section Kron

/-- Formalization-only: the tensor placement is multiplicative. -/
private theorem heteroKron_mul {ιA ιB : Type} [Fintype ιA] [Fintype ιB]
    (M M' : Op ιA) (N N' : Op ιB) :
    heteroKron M N * heteroKron M' N' = heteroKron (M * M') (N * N') := by
  unfold heteroKron
  exact (Matrix.mul_kronecker_mul M M' N N').symm

/-- Formalization-only: the tensor placement of two identities is the identity. -/
private theorem heteroKron_one_one {ιA ιB : Type} [DecidableEq ιA] [DecidableEq ιB] :
    heteroKron (1 : Op ιA) (1 : Op ιB) = 1 := by
  unfold heteroKron
  exact Matrix.one_kronecker_one

/-- Formalization-only: the tensor placement commutes with adjoints. -/
private theorem heteroKron_conjTranspose {ιA ιB : Type} (M : Op ιA) (N : Op ιB) :
    (heteroKron M N)ᴴ = heteroKron Mᴴ Nᴴ := by
  unfold heteroKron
  exact Matrix.conjTranspose_kronecker M N

/-- Formalization-only: the tensor placement is additive in the first factor. -/
private theorem heteroKron_sub_left {ιA ιB : Type} (M M' : Op ιA) (N : Op ιB) :
    heteroKron M N - heteroKron M' N = heteroKron (M - M') N := by
  ext p q
  simp [heteroKron, Matrix.kronecker, sub_mul]

/-- Formalization-only: the tensor placement is additive in the second factor. -/
private theorem heteroKron_sub_right {ιA ιB : Type} (M : Op ιA) (N N' : Op ιB) :
    heteroKron M N - heteroKron M N' = heteroKron M (N - N') := by
  ext p q
  simp [heteroKron, Matrix.kronecker, mul_sub]

/-- Formalization-only: scalars pass through the first factor. -/
private theorem heteroKron_smul_left {ιA ιB : Type} (c : ℂ) (M : Op ιA) (N : Op ιB) :
    heteroKron (c • M) N = c • heteroKron M N := by
  unfold heteroKron
  exact Matrix.smul_kronecker c M N

/-- Formalization-only: finite sums pass through the first factor. -/
private theorem heteroKron_sum_left {ιA ιB γ : Type} [Fintype γ]
    (M : γ → Op ιA) (N : Op ιB) :
    heteroKron (∑ c, M c) N = ∑ c, heteroKron (M c) N := by
  ext p q
  simp [heteroKron, Matrix.kronecker, Matrix.sum_apply, Finset.sum_mul]

/-- Formalization-only: finite sums pass through the second factor. -/
private theorem heteroKron_sum_right {ιA ιB γ : Type} [Fintype γ]
    (M : Op ιA) (N : γ → Op ιB) :
    heteroKron M (∑ c, N c) = ∑ c, heteroKron M (N c) := by
  ext p q
  simp [heteroKron, Matrix.kronecker, Matrix.sum_apply, Finset.mul_sum]

end Kron

/-! ## The state-dependent norm -/

section StateNorm

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- Formalization-only: the action of an operator on a state is additive. -/
private theorem applyOperatorToState_sub (M N : Op ι) (ψ : EuclideanSpace ℂ ι) :
    applyOperatorToState (M - N) ψ =
      applyOperatorToState M ψ - applyOperatorToState N ψ := by
  unfold applyOperatorToState
  simp only [map_sub, LinearMap.sub_apply]

/-- Formalization-only: the action of an operator on a state is additive. -/
private theorem applyOperatorToState_add (M N : Op ι) (ψ : EuclideanSpace ℂ ι) :
    applyOperatorToState (M + N) ψ =
      applyOperatorToState M ψ + applyOperatorToState N ψ := by
  unfold applyOperatorToState
  simp only [map_add, LinearMap.add_apply]

/-- Formalization-only: the action of an operator on a state is homogeneous. -/
private theorem applyOperatorToState_smul (c : ℂ) (M : Op ι) (ψ : EuclideanSpace ℂ ι) :
    applyOperatorToState (c • M) ψ = c • applyOperatorToState M ψ := by
  unfold applyOperatorToState
  simp only [map_smul, LinearMap.smul_apply]

/-- Formalization-only: the identity operator fixes every state. -/
private theorem applyOperatorToState_one (ψ : EuclideanSpace ℂ ι) :
    applyOperatorToState (1 : Op ι) ψ = ψ := by
  unfold applyOperatorToState
  rw [Matrix.toLpLin_apply, Matrix.one_mulVec]

/-- Formalization-only: the zero operator annihilates every state. -/
private theorem applyOperatorToState_zero (ψ : EuclideanSpace ℂ ι) :
    applyOperatorToState (0 : Op ι) ψ = 0 := by
  unfold applyOperatorToState
  simp only [map_zero, LinearMap.zero_apply]

/-- Formalization-only: acting by a product is acting twice. -/
private theorem applyOperatorToState_mul (M N : Op ι) (ψ : EuclideanSpace ℂ ι) :
    applyOperatorToState (M * N) ψ =
      applyOperatorToState M (applyOperatorToState N ψ) := by
  unfold applyOperatorToState
  simp [Matrix.toEuclideanLin, Matrix.toLpLin_mul_same]

/-- Formalization-only: acting by a finite sum of operators is the sum of the
actions. -/
private theorem applyOperatorToState_sum {γ : Type} [Fintype γ]
    (M : γ → Op ι) (ψ : EuclideanSpace ℂ ι) :
    applyOperatorToState (∑ c, M c) ψ = ∑ c, applyOperatorToState (M c) ψ := by
  unfold applyOperatorToState
  simp only [map_sum, LinearMap.sum_apply]

/-- Formalization-only: the squared state-dependent norm of an operator is the
quadratic form of the operator composed with its adjoint. -/
private theorem norm_applyOperatorToState_sq (M : Op ι) (ψ : EuclideanSpace ℂ ι) :
    ‖applyOperatorToState M ψ‖ ^ 2 =
      (inner ℂ ψ (applyOperatorToState (Mᴴ * M) ψ)).re := by
  rw [@norm_sq_eq_re_inner ℂ]
  unfold applyOperatorToState
  rw [Matrix.toEuclideanLin_conjTranspose_mul_self]
  change (inner ℂ (Matrix.toEuclideanLin M ψ) (Matrix.toEuclideanLin M ψ)).re =
    (inner ℂ ψ ((Matrix.toEuclideanLin M).adjoint (Matrix.toEuclideanLin M ψ))).re
  rw [LinearMap.adjoint_inner_right]

/-- An isometric operator preserves the norm of every state. -/
theorem norm_applyOperatorToState_of_isometry {U : Op ι} (hU : Uᴴ * U = 1)
    (ψ : EuclideanSpace ℂ ι) : ‖applyOperatorToState U ψ‖ = ‖ψ‖ := by
  have h : ‖applyOperatorToState U ψ‖ ^ 2 = ‖ψ‖ ^ 2 := by
    rw [norm_applyOperatorToState_sq, hU, @norm_sq_eq_re_inner ℂ,
      applyOperatorToState_one]
    rfl
  have h1 : (0 : ℝ) ≤ ‖applyOperatorToState U ψ‖ := norm_nonneg _
  have h2 : (0 : ℝ) ≤ ‖ψ‖ := norm_nonneg _
  nlinarith [h, h1, h2]

/-- Multiplying on the left by an isometric operator does not change the
state-dependent norm. -/
theorem norm_applyOperatorToState_isometry_mul {U : Op ι} (hU : Uᴴ * U = 1)
    (M : Op ι) (ψ : EuclideanSpace ℂ ι) :
    ‖applyOperatorToState (U * M) ψ‖ = ‖applyOperatorToState M ψ‖ := by
  rw [applyOperatorToState_mul, norm_applyOperatorToState_of_isometry hU]

end StateNorm

/-! ## Reflections -/

/-- A *reflection* is a self-adjoint involution.  These are the binary
observables attached to two-outcome projective measurements; `thm:ms-rigidity`
uses them for the Magic Square cells, blueprint `ch13_qpbt_test.tex:224-253`. -/
structure IsReflection {ι : Type} [Fintype ι] [DecidableEq ι] (X : Op ι) : Prop where
  /-- The operator is self-adjoint. -/
  conjTranspose_eq : Xᴴ = X
  /-- The operator squares to the identity. -/
  mul_self_eq_one : X * X = 1

namespace IsReflection

variable {ι : Type} [Fintype ι] [DecidableEq ι] {X Y : Op ι}

/-- A reflection is isometric. -/
theorem isometry (hX : IsReflection X) : Xᴴ * X = 1 := by
  rw [hX.conjTranspose_eq, hX.mul_self_eq_one]

/-- The identity is a reflection. -/
theorem one : IsReflection (1 : Op ι) :=
  ⟨Matrix.conjTranspose_one, one_mul 1⟩

/-- The product of two commuting reflections is a reflection. -/
theorem mul (hX : IsReflection X) (hY : IsReflection Y) (hcomm : X * Y = Y * X) :
    IsReflection (X * Y) := by
  refine ⟨?_, ?_⟩
  · rw [Matrix.conjTranspose_mul, hX.conjTranspose_eq, hY.conjTranspose_eq, ← hcomm]
  · calc X * Y * (X * Y) = X * (Y * X) * Y := by noncomm_ring
      _ = X * (X * Y) * Y := by rw [hcomm]
      _ = X * X * (Y * Y) := by noncomm_ring
      _ = 1 := by rw [hX.mul_self_eq_one, hY.mul_self_eq_one, one_mul]

end IsReflection

/-- A reflection placed on Alice's tensor factor stays a reflection. -/
theorem IsReflection.heteroKron_left {ιA ιB : Type} [Fintype ιA] [DecidableEq ιA]
    [Fintype ιB] [DecidableEq ιB] {X : Op ιA} (hX : IsReflection X) :
    IsReflection (heteroKron X (1 : Op ιB)) := by
  refine ⟨?_, ?_⟩
  · rw [heteroKron_conjTranspose, hX.conjTranspose_eq, Matrix.conjTranspose_one]
  · rw [heteroKron_mul, hX.mul_self_eq_one, one_mul, heteroKron_one_one]

/-- A reflection placed on Bob's tensor factor stays a reflection. -/
theorem IsReflection.heteroKron_right {ιA ιB : Type} [Fintype ιA] [DecidableEq ιA]
    [Fintype ιB] [DecidableEq ιB] {Y : Op ιB} (hY : IsReflection Y) :
    IsReflection (heteroKron (1 : Op ιA) Y) := by
  refine ⟨?_, ?_⟩
  · rw [heteroKron_conjTranspose, hY.conjTranspose_eq, Matrix.conjTranspose_one]
  · rw [heteroKron_mul, hY.mul_self_eq_one, one_mul, heteroKron_one_one]

/-- Operators placed on the two tensor factors commute. -/
theorem heteroKron_comm {ιA ιB : Type} [Fintype ιA] [DecidableEq ιA]
    [Fintype ιB] [DecidableEq ιB] (X : Op ιA) (Y : Op ιB) :
    heteroKron X (1 : Op ιB) * heteroKron (1 : Op ιA) Y =
      heteroKron (1 : Op ιA) Y * heteroKron X (1 : Op ιB) := by
  rw [heteroKron_mul, heteroKron_mul, mul_one, one_mul, one_mul, mul_one]

/-! ## State-dependent closeness -/

/-- Two operators are *close within `δ` on `ψ`* when the state-dependent norm of
their difference is at most `δ`.  This is the relation written `M ≈_δ N` in
`thm:ms-rigidity`, blueprint `ch13_qpbt_test.tex:224-253`, paper
`08_classical_and_quantum_low_degree_tests.tex:612-652`. -/
def CloseOn {ι : Type} [Fintype ι] [DecidableEq ι]
    (ψ : EuclideanSpace ℂ ι) (δ : ℝ) (M N : Op ι) : Prop :=
  ‖applyOperatorToState (M - N) ψ‖ ≤ δ

namespace CloseOn

variable {ι : Type} [Fintype ι] [DecidableEq ι]
variable {ψ : EuclideanSpace ℂ ι} {δ η : ℝ} {M N P U : Op ι}

/-- Equal operators are close at every nonnegative scale. -/
theorem of_eq (h : M = N) (hδ : 0 ≤ δ) : CloseOn ψ δ M N := by
  have hzero : applyOperatorToState (M - N) ψ = 0 := by
    rw [h, sub_self, applyOperatorToState_zero]
  rw [CloseOn, hzero, norm_zero]
  exact hδ

/-- Closeness is symmetric. -/
theorem symm (h : CloseOn ψ δ M N) : CloseOn ψ δ N M := by
  have happ : applyOperatorToState (N - M) ψ = -applyOperatorToState (M - N) ψ := by
    rw [show N - M = (0 : Op ι) - (M - N) by abel, applyOperatorToState_sub,
      applyOperatorToState_zero, zero_sub]
  rw [CloseOn, happ, norm_neg]
  exact h

/-- Enlarging the scale preserves closeness. -/
theorem mono (h : CloseOn ψ δ M N) (hδ : δ ≤ η) : CloseOn ψ η M N :=
  le_trans h hδ

/-- Closeness composes by the triangle inequality. -/
theorem trans (h₁ : CloseOn ψ δ M N) (h₂ : CloseOn ψ η N P) :
    CloseOn ψ (δ + η) M P := by
  have hsplit : M - P = (M - N) + (N - P) := by abel
  calc ‖applyOperatorToState (M - P) ψ‖
      = ‖applyOperatorToState (M - N) ψ + applyOperatorToState (N - P) ψ‖ := by
        rw [hsplit, applyOperatorToState_add]
    _ ≤ ‖applyOperatorToState (M - N) ψ‖ + ‖applyOperatorToState (N - P) ψ‖ :=
        norm_add_le _ _
    _ ≤ δ + η := add_le_add h₁ h₂

/-- Multiplying on the left by an isometric operator preserves closeness. -/
theorem isometry_mul (hU : Uᴴ * U = 1) (h : CloseOn ψ δ M N) :
    CloseOn ψ δ (U * M) (U * N) := by
  have hsub : U * M - U * N = U * (M - N) := by noncomm_ring
  rw [CloseOn, hsub, norm_applyOperatorToState_isometry_mul hU]
  exact h

end CloseOn

/-! ## Sign observables of a projective measurement -/

section SignObs

variable {α d : Type} [Fintype α] [DecidableEq α] [Fintype d] [DecidableEq d]

/-- The `±1`-valued observable attached to a measurement together with a binary
relabelling of its answers: an answer labelled `0` carries the eigenvalue `1`
and an answer labelled `1` carries the eigenvalue `-1`.  For the Magic Square
these are the cell observables of `thm:ms-rigidity`, blueprint
`ch13_qpbt_test.tex:224-253`, paper
`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:612-652`. -/
noncomputable def signObs (M : MIPStarRE.Quantum.Measurement α d) (f : α → ZMod 2) : Op d :=
  ∑ a, (bitSign (f a) : ℂ) • M.effect a

/-- The sign observable is the observable of the binary measurement obtained by
relabelling the answers. -/
theorem signObs_eq_obsOf_postprocess (M : MIPStarRE.Quantum.Measurement α d)
    (f : α → ZMod 2) : signObs M f = obsOf (M.postprocess f) := by
  classical
  have hcases : ∀ x : ZMod 2, x = 0 ∨ x = 1 := by decide
  have key : ∀ a : α, (bitSign (f a) : ℂ) • M.effect a =
      (if f a = 0 then M.effect a else 0) - (if f a = 1 then M.effect a else 0) := by
    intro a
    rcases hcases (f a) with h | h <;> rw [h] <;>
      norm_num [bitSign, ZMod.val_one, neg_one_smul]
  rw [signObs, obsOf, MIPStarRE.Quantum.Measurement.postprocess_effect,
    MIPStarRE.Quantum.Measurement.postprocess_effect, Finset.sum_filter,
    Finset.sum_filter, ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun a _ => key a

/-- Formalization-only: the effects of a projective measurement are mutually
orthogonal, so two spectral combinations of them multiply coefficientwise. -/
private theorem sum_smul_effect_mul (M : MIPStarRE.Quantum.Measurement α d)
    (hM : MIPStarRE.QPBT.Measurement.IsProjective M) (c e : α → ℂ) :
    (∑ a, c a • M.effect a) * (∑ a, e a • M.effect a) =
      ∑ a, (c a * e a) • M.effect a := by
  classical
  have horth : ∀ a b : α, a ≠ b → M.effect a * M.effect b = 0 := fun a b hab =>
    mul_eq_zero_of_isProj_family hM M.sum_le_one hab
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun a _ => ?_
  have hidem : M.effect a * M.effect a = M.effect a := (hM a).isIdempotentElem
  rw [Matrix.smul_mul, Matrix.mul_sum, Finset.smul_sum, Finset.sum_eq_single a]
  · rw [Matrix.mul_smul, smul_smul, hidem]
  · intro b _ hba
    rw [Matrix.mul_smul, horth a b (Ne.symm hba), smul_zero, smul_zero]
  · intro ha
    exact absurd (Finset.mem_univ a) ha

/-- Sign observables of one projective measurement multiply by adding their
relabellings. -/
theorem signObs_mul (M : MIPStarRE.Quantum.Measurement α d)
    (hM : MIPStarRE.QPBT.Measurement.IsProjective M) (f g : α → ZMod 2) :
    signObs M f * signObs M g = signObs M (fun a => f a + g a) := by
  rw [signObs, signObs, sum_smul_effect_mul M hM, signObs]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [← Complex.ofReal_mul, ← bit_sign_add]

omit [DecidableEq α] in
/-- The sign observable of the zero relabelling is the identity. -/
theorem signObs_const_zero (M : MIPStarRE.Quantum.Measurement α d) :
    signObs M (fun _ => 0) = 1 := by
  have hb : ((bitSign (0 : ZMod 2) : ℝ) : ℂ) = 1 := by norm_num [bitSign]
  rw [signObs]
  simp only [hb, one_smul]
  exact M.sum_eq_one

/-- A sign observable of a projective measurement is an involution. -/
theorem signObs_mul_self (M : MIPStarRE.Quantum.Measurement α d)
    (hM : MIPStarRE.QPBT.Measurement.IsProjective M) (f : α → ZMod 2) :
    signObs M f * signObs M f = 1 := by
  rw [signObs_mul M hM]
  have hzero : (fun a => f a + f a) = fun _ : α => (0 : ZMod 2) := by
    funext a
    exact (by decide : ∀ x : ZMod 2, x + x = 0) (f a)
  rw [hzero, signObs_const_zero]

omit [DecidableEq α] in
/-- A sign observable of a projective measurement is self-adjoint. -/
theorem signObs_conjTranspose (M : MIPStarRE.Quantum.Measurement α d)
    (hM : MIPStarRE.QPBT.Measurement.IsProjective M) (f : α → ZMod 2) :
    (signObs M f)ᴴ = signObs M f := by
  rw [← Matrix.star_eq_conjTranspose, signObs, star_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [star_smul]
  congr 1
  · simp
  · exact (hM a).isSelfAdjoint

/-- A sign observable of a projective measurement is a reflection. -/
theorem isReflection_signObs (M : MIPStarRE.Quantum.Measurement α d)
    (hM : MIPStarRE.QPBT.Measurement.IsProjective M) (f : α → ZMod 2) :
    IsReflection (signObs M f) :=
  ⟨signObs_conjTranspose M hM f, signObs_mul_self M hM f⟩

/-- Sign observables of one projective measurement commute. -/
theorem signObs_comm (M : MIPStarRE.Quantum.Measurement α d)
    (hM : MIPStarRE.QPBT.Measurement.IsProjective M) (f g : α → ZMod 2) :
    signObs M f * signObs M g = signObs M g * signObs M f := by
  rw [signObs_mul M hM, signObs_mul M hM]
  congr 1
  funext a
  exact add_comm _ _

end SignObs

end

end MIPStarRE.QPBT.MagicSquareRigidity
