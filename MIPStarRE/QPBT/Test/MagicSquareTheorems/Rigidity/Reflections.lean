import MIPStarRE.QPBT.Test.MagicSquareTheorems.Rigidity.GroundSlice

/-!
# Reflections and the state-dependent metric on operators

The self-testing argument for the Magic Square game manipulates `±1`-valued
observables rather than positive operator valued measures.  This file records
the algebra of such observables and the estimates that convert Born masses into
operator bounds.

Postprocessing a projective measurement along a binary relabelling of its
answers produces a *reflection*, that is, a self-adjoint involution; two
reflections coming from one and the same measurement commute, and their product
is the reflection attached to the sum of the two relabellings.  Two operators
are compared through the norm of the difference of their actions on a fixed
state, which is the relation written `M ≈ N` in the source; this comparison is
symmetric, satisfies the triangle inequality, and is unchanged by multiplication
on the left by an isometric operator.  Finally, a real spectral combination of
the joint effects of the two players has state-dependent norm controlled by the
Born mass of the answer pairs carrying a nonzero coefficient; this is the step
that turns each rejection mass of the value-to-parity layer into an operator
estimate.

## References

The statements supported here are the operator relations in `thm:ms-rigidity`,
blueprint `blueprint/src/chapter/ch13_qpbt_test.tex:224-253`, from
`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:612-652`,
proved in Coladangelo--Stark, arXiv:1709.09267v2, Theorem 6.9.
-/

open scoped BigOperators Matrix MatrixOrder ComplexOrder

namespace MIPStarRE.QPBT.MagicSquareRigidity

open MIPStarRE.LDT MIPStarRE.Quantum

noncomputable section

/-! ## Rectangular tensor placement -/

section Kron

/-- Formalization-only: the tensor placement commutes with adjoints. -/
theorem heteroKron_conjTranspose {ιA ιB : Type} (M : Op ιA) (N : Op ιB) :
    (heteroKron M N)ᴴ = heteroKron Mᴴ Nᴴ := by
  unfold heteroKron
  exact Matrix.conjTranspose_kronecker M N

/-- Formalization-only: scalars pass through the first factor. -/
theorem heteroKron_smul_left {ιA ιB : Type} (c : ℂ) (M : Op ιA) (N : Op ιB) :
    heteroKron (c • M) N = c • heteroKron M N := by
  unfold heteroKron
  exact Matrix.smul_kronecker c M N

/-- Formalization-only: finite sums pass through the first factor. -/
theorem heteroKron_sum_left {ιA ιB γ : Type} [Fintype γ]
    (M : γ → Op ιA) (N : Op ιB) :
    heteroKron (∑ c, M c) N = ∑ c, heteroKron (M c) N := by
  ext p q
  simp [heteroKron, Matrix.kronecker, Matrix.sum_apply, Finset.sum_mul]

/-- Formalization-only: finite sums pass through the second factor. -/
theorem heteroKron_sum_right {ιA ιB γ : Type} [Fintype γ]
    (M : Op ιA) (N : γ → Op ιB) :
    heteroKron M (∑ c, N c) = ∑ c, heteroKron M (N c) := by
  ext p q
  simp [heteroKron, Matrix.kronecker, Matrix.sum_apply, Finset.mul_sum]

end Kron

/-! ## The state-dependent norm -/

section StateNorm

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- Formalization-only: the action of an operator on a state is homogeneous. -/
theorem applyOperatorToState_smul (c : ℂ) (M : Op ι) (ψ : EuclideanSpace ℂ ι) :
    applyOperatorToState (c • M) ψ = c • applyOperatorToState M ψ := by
  unfold applyOperatorToState
  simp only [map_smul, LinearMap.smul_apply]

/-- Formalization-only: the zero operator annihilates every state; the
companion `applyOperatorToState_zero` annihilates the zero state instead. -/
theorem applyOperatorToState_zero_op (ψ : EuclideanSpace ℂ ι) :
    applyOperatorToState (0 : Op ι) ψ = 0 := by
  unfold applyOperatorToState
  simp only [map_zero, LinearMap.zero_apply]

/-- Formalization-only: acting by a finite sum of operators is the sum of the
actions. -/
theorem applyOperatorToState_sum {γ : Type} [Fintype γ]
    (M : γ → Op ι) (ψ : EuclideanSpace ℂ ι) :
    applyOperatorToState (∑ c, M c) ψ = ∑ c, applyOperatorToState (M c) ψ := by
  unfold applyOperatorToState
  simp only [map_sum, LinearMap.sum_apply]

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
    rw [h, sub_self, applyOperatorToState_zero_op]
  rw [CloseOn, hzero, norm_zero]
  exact hδ

/-- Closeness is symmetric. -/
theorem symm (h : CloseOn ψ δ M N) : CloseOn ψ δ N M := by
  have happ : applyOperatorToState (N - M) ψ = -applyOperatorToState (M - N) ψ := by
    rw [show N - M = -(M - N) by abel]
    unfold applyOperatorToState
    simp only [map_neg, LinearMap.neg_apply]
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
        rw [hsplit, applyOperatorToState_add_op]
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

omit [DecidableEq α] in
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

omit [DecidableEq α] in
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

omit [DecidableEq α] in
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

omit [DecidableEq α] in
/-- A sign observable of a projective measurement is a reflection. -/
theorem isReflection_signObs (M : MIPStarRE.Quantum.Measurement α d)
    (hM : MIPStarRE.QPBT.Measurement.IsProjective M) (f : α → ZMod 2) :
    IsReflection (signObs M f) :=
  ⟨signObs_conjTranspose M hM f, signObs_mul_self M hM f⟩

omit [DecidableEq α] in
/-- Sign observables of one projective measurement commute. -/
theorem signObs_comm (M : MIPStarRE.Quantum.Measurement α d)
    (hM : MIPStarRE.QPBT.Measurement.IsProjective M) (f g : α → ZMod 2) :
    signObs M f * signObs M g = signObs M g * signObs M f := by
  rw [signObs_mul M hM, signObs_mul M hM]
  congr 1
  funext a
  exact add_comm _ _

end SignObs

/-! ## Deviation of joint spectral combinations on the strategy state -/

section JointDefect

/-- Formalization-only: scalars pass through the second tensor factor. -/
theorem heteroKron_smul_right {ιA ιB : Type} (c : ℂ) (M : Op ιA) (N : Op ιB) :
    heteroKron M (c • N) = c • heteroKron M N := by
  unfold heteroKron
  exact Matrix.kronecker_smul c M N

/-- Formalization-only: the tensor placement of two orthogonal projections is an
orthogonal projection. -/
private theorem isProj_heteroKron {ιA ιB : Type} [Fintype ιA] [DecidableEq ιA]
    [Fintype ιB] [DecidableEq ιB] {A : Op ιA} {B : Op ιB}
    (hA : IsProj A) (hB : IsProj B) : IsProj (heteroKron A B) := by
  have hAi : A * A = A := hA.isIdempotentElem
  have hBi : B * B = B := hB.isIdempotentElem
  have hAs : Aᴴ = A := by
    rw [← Matrix.star_eq_conjTranspose]; exact hA.isSelfAdjoint
  have hBs : Bᴴ = B := by
    rw [← Matrix.star_eq_conjTranspose]; exact hB.isSelfAdjoint
  constructor
  · change heteroKron A B * heteroKron A B = heteroKron A B
    rw [heteroKron_mul, hAi, hBi]
  · change star (heteroKron A B) = heteroKron A B
    rw [Matrix.star_eq_conjTranspose, heteroKron_conjTranspose, hAs, hBs]

/-- Formalization-only: a real spectral combination of the effects of a
projective measurement is self-adjoint. -/
private theorem sum_real_smul_effect_conjTranspose {α d : Type} [Fintype α]
    [Fintype d] [DecidableEq d] (M : MIPStarRE.Quantum.Measurement α d)
    (hM : MIPStarRE.QPBT.Measurement.IsProjective M) (c : α → ℝ) :
    (∑ a, ((c a : ℝ) : ℂ) • M.effect a)ᴴ = ∑ a, ((c a : ℝ) : ℂ) • M.effect a := by
  rw [← Matrix.star_eq_conjTranspose, star_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [star_smul]
  congr 1
  · simp
  · exact (hM a).isSelfAdjoint

/-- Formalization-only: the quadratic form of a real spectral combination on a
state is the corresponding real combination of the individual quadratic
forms. -/
private theorem re_inner_apply_sum_real_smul {ι γ : Type} [Fintype ι] [DecidableEq ι]
    [Fintype γ] (r : γ → ℝ) (K : γ → Op ι) (ψ : EuclideanSpace ℂ ι) :
    (inner ℂ ψ (applyOperatorToState (∑ c, ((r c : ℝ) : ℂ) • K c) ψ)).re =
      ∑ c, r c * (inner ℂ ψ (applyOperatorToState (K c) ψ)).re := by
  rw [applyOperatorToState_sum, inner_sum, Complex.re_sum]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [applyOperatorToState_smul, inner_smul_right]
  simp

variable {G : Game}

/-- Formalization-only: the joint effects of the two players form a projective
measurement on the composite space when both local measurements are
projective. -/
private noncomputable def jointMeasurement (T : Strategy G) (x : G.QuestionA)
    (y : G.QuestionB) :
    MIPStarRE.Quantum.Measurement (G.AnswerA × G.AnswerB) (T.ιA × T.ιB) :=
  MIPStarRE.Quantum.Measurement.ofSumEqOne
    (fun ab => heteroKron ((T.A x).effect ab.1) ((T.B y).effect ab.2))
    (fun ab => kronecker_nonneg ((T.A x).pos ab.1) ((T.B y).pos ab.2))
    (by
      rw [Fintype.sum_prod_type]
      calc ∑ a : G.AnswerA, ∑ b : G.AnswerB,
            heteroKron ((T.A x).effect a) ((T.B y).effect b)
          = ∑ a : G.AnswerA, heteroKron ((T.A x).effect a)
              (∑ b : G.AnswerB, (T.B y).effect b) := by
            exact Finset.sum_congr rfl fun a _ => (heteroKron_sum_right _ _).symm
        _ = heteroKron (∑ a : G.AnswerA, (T.A x).effect a) (1 : Op T.ιB) := by
            rw [(T.B y).sum_eq_one, heteroKron_sum_left]
        _ = 1 := by rw [(T.A x).sum_eq_one, heteroKron_one_one])

/-- Formalization-only: the effects of the joint measurement. -/
private theorem jointMeasurement_effect (T : Strategy G) (x : G.QuestionA)
    (y : G.QuestionB) (ab : G.AnswerA × G.AnswerB) :
    (jointMeasurement T x y).effect ab =
      heteroKron ((T.A x).effect ab.1) ((T.B y).effect ab.2) := rfl

/-- Formalization-only: the quadratic form of a joint effect is the Born weight
of the corresponding answer pair. -/
private theorem re_inner_jointMeasurement_effect (T : Strategy G) (x : G.QuestionA)
    (y : G.QuestionB) (ab : G.AnswerA × G.AnswerB) :
    (inner ℂ T.ψ (applyOperatorToState ((jointMeasurement T x y).effect ab) T.ψ)).re =
      outcomeWeight T x y ab.1 ab.2 := rfl

/-- A real spectral combination of the joint effects deviates from zero, in the
state-dependent norm, by at most the mass of the answer pairs carrying a nonzero
coefficient, scaled by the squared coefficient bound.  This is the estimate that
converts each Magic Square rejection mass into an operator bound;
`thm:ms-rigidity`, blueprint `ch13_qpbt_test.tex:224-253`. -/
theorem norm_apply_joint_defect_sq_le (T : Strategy G) (x : G.QuestionA)
    (y : G.QuestionB) (hA : MIPStarRE.QPBT.Measurement.IsProjective (T.A x))
    (hB : MIPStarRE.QPBT.Measurement.IsProjective (T.B y))
    (coef : G.AnswerA → G.AnswerB → ℝ) (E : G.AnswerA → G.AnswerB → Prop)
    [DecidableRel E] (hbound : ∀ a b, coef a b ^ 2 ≤ 4)
    (hsupp : ∀ a b, ¬ E a b → coef a b = 0) :
    ‖applyOperatorToState
        (∑ a : G.AnswerA, ∑ b : G.AnswerB, ((coef a b : ℝ) : ℂ) •
          heteroKron ((T.A x).effect a) ((T.B y).effect b)) T.ψ‖ ^ 2 ≤
      4 * outcomeEventWeight T x y E := by
  classical
  set J := jointMeasurement T x y with hJ
  have hJproj : MIPStarRE.QPBT.Measurement.IsProjective J := fun ab =>
    isProj_heteroKron (hA ab.1) (hB ab.2)
  have hcollapse : (∑ a : G.AnswerA, ∑ b : G.AnswerB, ((coef a b : ℝ) : ℂ) •
      heteroKron ((T.A x).effect a) ((T.B y).effect b)) =
      ∑ ab : G.AnswerA × G.AnswerB, ((coef ab.1 ab.2 : ℝ) : ℂ) • J.effect ab := by
    rw [Fintype.sum_prod_type]
    rfl
  have hsa : (∑ ab : G.AnswerA × G.AnswerB, ((coef ab.1 ab.2 : ℝ) : ℂ) • J.effect ab)ᴴ =
      ∑ ab : G.AnswerA × G.AnswerB, ((coef ab.1 ab.2 : ℝ) : ℂ) • J.effect ab :=
    sum_real_smul_effect_conjTranspose J hJproj (fun ab => coef ab.1 ab.2)
  have hsq : ∀ ab : G.AnswerA × G.AnswerB,
      ((coef ab.1 ab.2 : ℝ) : ℂ) * ((coef ab.1 ab.2 : ℝ) : ℂ) =
        ((coef ab.1 ab.2 ^ 2 : ℝ) : ℂ) := by
    intro ab
    rw [← Complex.ofReal_mul, sq]
  rw [hcollapse, norm_applyOperatorToState_sq, hsa,
    sum_smul_effect_mul J hJproj]
  simp only [hsq]
  rw [re_inner_apply_sum_real_smul]
  have hterm : ∀ ab : G.AnswerA × G.AnswerB,
      coef ab.1 ab.2 ^ 2 *
          (inner ℂ T.ψ (applyOperatorToState (J.effect ab) T.ψ)).re ≤
        (if E ab.1 ab.2 then 4 * outcomeWeight T x y ab.1 ab.2 else 0) := by
    intro ab
    have hw : 0 ≤ outcomeWeight T x y ab.1 ab.2 := outcomeWeight_nonneg T x y ab.1 ab.2
    rw [re_inner_jointMeasurement_effect]
    by_cases hE : E ab.1 ab.2
    · rw [if_pos hE]
      exact mul_le_mul_of_nonneg_right (hbound ab.1 ab.2) hw
    · rw [if_neg hE, hsupp ab.1 ab.2 hE]
      simp
  calc ∑ ab : G.AnswerA × G.AnswerB, coef ab.1 ab.2 ^ 2 *
        (inner ℂ T.ψ (applyOperatorToState (J.effect ab) T.ψ)).re
      ≤ ∑ ab : G.AnswerA × G.AnswerB,
          (if E ab.1 ab.2 then 4 * outcomeWeight T x y ab.1 ab.2 else 0) :=
        Finset.sum_le_sum fun ab _ => hterm ab
    _ = 4 * outcomeEventWeight T x y E := by
        rw [Fintype.sum_prod_type, outcomeEventWeight, Finset.mul_sum]
        refine Finset.sum_congr rfl fun a _ => ?_
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun b _ => ?_
        by_cases hE : E a b <;> simp [hE]

/-- Formalization-only: expansion of a product of two local spectral
combinations into the joint effects. -/
theorem joint_expand (T : Strategy G) (x : G.QuestionA) (y : G.QuestionB)
    (u : G.AnswerA → ℂ) (v : G.AnswerB → ℂ) :
    heteroKron (∑ a, u a • (T.A x).effect a) (∑ b, v b • (T.B y).effect b) =
      ∑ a, ∑ b, (u a * v b) • heteroKron ((T.A x).effect a) ((T.B y).effect b) := by
  rw [heteroKron_sum_left]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [heteroKron_smul_left, heteroKron_sum_right, Finset.smul_sum]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [heteroKron_smul_right, smul_smul]

/-- Formalization-only: the identity as a spectral combination of the effects of
a measurement. -/
theorem smul_one_eq_sum_smul_effect {α d : Type} [Fintype α] [Fintype d]
    [DecidableEq d] (M : MIPStarRE.Quantum.Measurement α d) (s : ℂ) :
    s • (1 : Op d) = ∑ a, s • M.effect a := by
  rw [← Finset.smul_sum, M.sum_eq_one]

end JointDefect

end

end MIPStarRE.QPBT.MagicSquareRigidity
