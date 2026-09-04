import MIPStarRE.LDT.MakingMeasurementsProjective.NaimarkFull
import MIPStarRE.QPBT.Test.MagicSquareTheorems.Rigidity.Relations

/-!
# A simultaneous projective dilation of a Magic Square strategy

The rigidity argument for the Magic Square game is stated for an arbitrary
tensor-product strategy, whose measurements are positive operator valued
measures.  The self-testing argument, however, manipulates projections.  This
file removes that discrepancy by dilating an arbitrary strategy to a projective
one without changing any observable quantity.

Each local Hilbert space `ℂ^ι` is enlarged by one auxiliary register whose
basis is indexed by `Option MsAnswer`, and the original space is identified with
the *ground slice* `ℂ^ι ⊗ |⊥⟩`.  The one-measurement Naimark lemma of the low
individual degree development supplies, for every question separately, a family
of projections on the enlarged space whose compression to the ground slice
returns the original effects; the ancilla is the same for all questions, so the
identification of `ℂ^ι` with the ground slice is a single isometry serving every
question at once.  Folding the deficiency `1 - ∑_a P_a` into one distinguished
answer turns the dilated family into a complete projective measurement without
disturbing the compression, because the original effects already sum to the
identity.

Since the dilated state is the image of the original state under the two ground
embeddings, every Born probability, and hence the game value and all the
rejection, malformed-answer, cell-consistency and parity masses of the
value-to-parity layer, is unchanged.  Conversely, the local isometries produced
by a rigidity argument applied to the dilated strategy compose with the ground
embeddings to give local isometries of the original strategy, and the
state-dependent norms occurring in the conclusion of `thm:ms-rigidity` transfer
along that composition.

## References

The rigidity statement supported here is `thm:ms-rigidity` in
`blueprint/src/chapter/ch13_qpbt_test.tex:224-253`, from
`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:612-652`,
proved in Coladangelo--Stark, Theorem 6.9.  The dilation reuses the
one-measurement Naimark lemma of
`references/ldt-paper/orthonormalization.tex:121-159`, formalized as
`MIPStarRE.LDT.MakingMeasurementsProjective.oneMeasNaimark`.
-/

open scoped BigOperators Matrix MatrixOrder ComplexOrder

namespace MIPStarRE.QPBT.MagicSquareRigidity

open MIPStarRE.LDT MIPStarRE.Quantum
open MIPStarRE.LDT.MakingMeasurementsProjective

noncomputable section

/-! ## Orthogonality inside a subnormalized family of projections -/

/-- Formalization-only auxiliary lemma for the dilation of `thm:ms-rigidity`
(blueprint `ch13_qpbt_test.tex:224-253`).  If an orthogonal projection `P` and a
positive semidefinite operator `Q` satisfy `P + Q ≤ 1`, then `P` annihilates
`Q`.  Indeed `Tr(P Q)` is nonnegative because both operators are positive
semidefinite, while `0 ≤ Tr(P (1 - P - Q)) = -Tr(P Q)` because `1 - P - Q` is
positive semidefinite and `P` is idempotent; so the pairing vanishes and the
product of two positive semidefinite operators with vanishing trace pairing is
zero. -/
theorem mul_eq_zero_of_isProj_of_add_le_one {d : Type*} [Fintype d] [DecidableEq d]
    {P Q : Op d} (hP : IsProj P) (hQ : 0 ≤ Q) (hPQ : P + Q ≤ 1) :
    P * Q = 0 := by
  have hrest : (0 : Op d) ≤ 1 - (P + Q) := sub_nonneg.mpr hPQ
  have hexpand : P * (1 - (P + Q)) = -(P * Q) := by
    have hPP : P * P = P := hP.isIdempotentElem
    rw [Matrix.mul_sub, Matrix.mul_add, hPP, Matrix.mul_one]
    abel
  have hle : Complex.re (Matrix.trace (P * Q)) ≤ 0 := by
    have h := trace_mul_nonneg_of_nonneg hP.nonneg hrest
    rw [hexpand] at h
    simpa using h
  have hge : 0 ≤ Complex.re (Matrix.trace (P * Q)) :=
    trace_mul_nonneg_of_nonneg hP.nonneg hQ
  exact mul_eq_zero_of_nonneg_of_trace_mul_eq_zero hP.nonneg hQ (le_antisymm hle hge)

/-- Formalization-only auxiliary lemma for the dilation of `thm:ms-rigidity`
(blueprint `ch13_qpbt_test.tex:224-253`).  A finite family of orthogonal
projections whose sum is at most the identity is mutually orthogonal: for two
distinct indices the two projections already sum to at most the identity, so the
previous lemma applies. -/
theorem mul_eq_zero_of_isProj_family {d α : Type*} [Fintype d] [DecidableEq d]
    [Fintype α] [DecidableEq α] {P : α → Op d} (hP : ∀ a, IsProj (P a))
    (hsum : ∑ a, P a ≤ 1) {a b : α} (hab : a ≠ b) :
    P a * P b = 0 := by
  refine mul_eq_zero_of_isProj_of_add_le_one (hP a) (hP b).nonneg ?_
  refine le_trans ?_ hsum
  have hpair : ∑ c ∈ ({a, b} : Finset α), P c = P a + P b := by
    rw [Finset.sum_pair hab]
  rw [← hpair]
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
    (fun c _ _ => (hP c).nonneg)

/-- Formalization-only auxiliary lemma for the dilation of `thm:ms-rigidity`
(blueprint `ch13_qpbt_test.tex:224-253`).  The sum of a mutually orthogonal
family of projections is again an orthogonal projection; mutual orthogonality is
supplied by the hypothesis that the sum is at most the identity. -/
theorem isProj_sum_of_isProj_of_sum_le_one {d α : Type*} [Fintype d] [DecidableEq d]
    [Fintype α] [DecidableEq α] {P : α → Op d} (hP : ∀ a, IsProj (P a))
    (hsum : ∑ a, P a ≤ 1) :
    IsProj (∑ a, P a) := by
  constructor
  · show (∑ a, P a) * (∑ a, P a) = ∑ a, P a
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Matrix.mul_sum, Finset.sum_eq_single a]
    · exact (hP a).isIdempotentElem
    · exact fun b _ hba => mul_eq_zero_of_isProj_family hP hsum (Ne.symm hba)
    · intro ha
      exact absurd (Finset.mem_univ a) ha
  · show star (∑ a, P a) = ∑ a, P a
    rw [star_sum]
    exact Finset.sum_congr rfl fun a _ => (hP a).isSelfAdjoint

/-! ## The ground slice of an enlarged local space -/

/-- The linear map sending a vector `x` of `ℂ^ι` to `x ⊗ |⊥⟩`, where `|⊥⟩` is the
basis vector of the auxiliary register `ℂ^{Option α}` indexed by the adjoined
point.  Formalization-only support for the dilation used by `thm:ms-rigidity`,
blueprint `ch13_qpbt_test.tex:224-253`. -/
def naimarkEmbeddingMap (ι α : Type) [Fintype ι] [DecidableEq ι]
    [Fintype α] [DecidableEq α] :
    EuclideanSpace ℂ ι →ₗ[ℂ] EuclideanSpace ℂ (ι × Option α) where
  toFun x := (EuclideanSpace.equiv (ι × Option α) ℂ).symm
    (fun p => if p.2 = none then x p.1 else 0)
  map_add' x y := by
    ext p
    by_cases h : p.2 = none <;> simp [h]
  map_smul' c x := by
    ext p
    by_cases h : p.2 = none <;> simp [h]

/-- The isometric identification of a local Hilbert space `ℂ^ι` with the *ground
slice* `ℂ^ι ⊗ |⊥⟩` of the enlarged space `ℂ^{ι × Option α}`.  This single
embedding serves every question of the dilation supporting `thm:ms-rigidity`,
blueprint `ch13_qpbt_test.tex:224-253`, paper
`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:612-652`. -/
noncomputable def naimarkEmbedding (ι α : Type) [Fintype ι] [DecidableEq ι]
    [Fintype α] [DecidableEq α] :
    EuclideanSpace ℂ ι →ₗᵢ[ℂ] EuclideanSpace ℂ (ι × Option α) :=
  LinearMap.isometryOfInner (naimarkEmbeddingMap ι α) <| by
    intro x y
    simp [PiLp.inner_apply, Fintype.sum_prod_type, naimarkEmbeddingMap]

@[simp]
theorem naimarkEmbedding_apply {ι α : Type} [Fintype ι] [DecidableEq ι]
    [Fintype α] [DecidableEq α] (x : EuclideanSpace ℂ ι) (p : ι × Option α) :
    naimarkEmbedding ι α x p = if p.2 = none then x p.1 else 0 := rfl

/-- The compression of an operator on the enlarged space to the ground slice.
Formalization-only support for the dilation of `thm:ms-rigidity`, blueprint
`ch13_qpbt_test.tex:224-253`. -/
def naimarkCompression {ι α : Type} [Fintype ι] [DecidableEq ι]
    [Fintype α] [DecidableEq α] (M : Op (ι × Option α)) : Op ι :=
  M.submatrix (fun i => (i, none)) (fun j => (j, none))

@[simp]
theorem naimarkCompression_apply {ι α : Type} [Fintype ι] [DecidableEq ι]
    [Fintype α] [DecidableEq α] (M : Op (ι × Option α)) (i j : ι) :
    naimarkCompression (α := α) M i j = M (i, none) (j, none) := rfl

/-- The compression of the zero operator to the ground slice vanishes. -/
@[simp]
theorem naimarkCompression_zero {ι α : Type} [Fintype ι] [DecidableEq ι]
    [Fintype α] [DecidableEq α] :
    naimarkCompression (α := α) (0 : Op (ι × Option α)) = 0 := by
  ext i j; simp

/-- The compression to the ground slice is additive. -/
theorem naimarkCompression_add {ι α : Type} [Fintype ι] [DecidableEq ι]
    [Fintype α] [DecidableEq α] (M N : Op (ι × Option α)) :
    naimarkCompression (α := α) (M + N) =
      naimarkCompression (α := α) M + naimarkCompression (α := α) N := by
  ext i j; simp

/-- The compression to the ground slice commutes with finite sums. -/
theorem naimarkCompression_sum {ι α β : Type} [Fintype ι] [DecidableEq ι]
    [Fintype α] [DecidableEq α] [Fintype β] (M : β → Op (ι × Option α)) :
    naimarkCompression (α := α) (∑ b, M b) = ∑ b, naimarkCompression (α := α) (M b) := by
  ext i j; simp [Matrix.sum_apply]

/-- The compression of the identity to the ground slice is the identity. -/
@[simp]
theorem naimarkCompression_one {ι α : Type} [Fintype ι] [DecidableEq ι]
    [Fintype α] [DecidableEq α] :
    naimarkCompression (α := α) (1 : Op (ι × Option α)) = 1 := by
  ext i j
  by_cases h : i = j <;> simp [Matrix.one_apply, h]

/-- The operator on the enlarged space that acts as `M` on the ground slice and
annihilates its orthogonal complement.  Formalization-only support for the
dilation of `thm:ms-rigidity`, blueprint `ch13_qpbt_test.tex:224-253`. -/
def naimarkInflation {ι α : Type} [Fintype ι] [DecidableEq ι]
    [Fintype α] [DecidableEq α] (M : Op ι) : Op (ι × Option α) :=
  Matrix.of fun p q => if p.2 = none ∧ q.2 = none then M p.1 q.1 else 0

@[simp]
theorem naimarkInflation_apply {ι α : Type} [Fintype ι] [DecidableEq ι]
    [Fintype α] [DecidableEq α] (M : Op ι) (p q : ι × Option α) :
    naimarkInflation (α := α) M p q =
      if p.2 = none ∧ q.2 = none then M p.1 q.1 else 0 := rfl

/-- Inflating an operator to the enlarged space and compressing it back returns
the original operator. -/
@[simp]
theorem naimarkCompression_naimarkInflation {ι α : Type} [Fintype ι] [DecidableEq ι]
    [Fintype α] [DecidableEq α] (M : Op ι) :
    naimarkCompression (α := α) (naimarkInflation (α := α) M) = M := by
  ext i j; simp

/-- The compression to the ground slice respects differences. -/
theorem naimarkCompression_sub {ι α : Type} [Fintype ι] [DecidableEq ι]
    [Fintype α] [DecidableEq α] (M N : Op (ι × Option α)) :
    naimarkCompression (α := α) (M - N) =
      naimarkCompression (α := α) M - naimarkCompression (α := α) N := by
  ext i j; simp

/-! ## The dilated projective measurement -/

/-- A one-measurement Naimark dilation of a positive operator valued measure,
chosen once and for all.  It provides orthogonal projections on the enlarged
space `ℂ^{d × Option α}` whose ground-slice compressions are the given effects;
see `references/ldt-paper/orthonormalization.tex:121-159`. -/
noncomputable def naimarkData {α d : Type} [Fintype α] [DecidableEq α]
    [Fintype d] [DecidableEq d] (M : MIPStarRE.Quantum.Measurement α d) : OneMeasNaimarkData α d :=
  Classical.choose (oneMeasNaimark M.toSubmeasurement)

/-- The chosen dilation dilates the intended measurement. -/
theorem naimarkData_source {α d : Type} [Fintype α] [DecidableEq α]
    [Fintype d] [DecidableEq d] (M : MIPStarRE.Quantum.Measurement α d) :
    (naimarkData M).source = M.toSubmeasurement :=
  Classical.choose_spec (oneMeasNaimark M.toSubmeasurement)

/-- The dilated projections indexed by genuine answers already sum to at most the
identity, since the projection attached to the adjoined point is positive
semidefinite. -/
theorem naimarkData_sum_some_le_one {α d : Type} [Fintype α] [DecidableEq α]
    [Fintype d] [DecidableEq d] (M : MIPStarRE.Quantum.Measurement α d) :
    ∑ a : α, (naimarkData M).liftedEffect (some a) ≤ 1 := by
  have hsplit : ∑ oa : Option α, (naimarkData M).liftedEffect oa =
      (naimarkData M).liftedEffect none +
        ∑ a : α, (naimarkData M).liftedEffect (some a) :=
    Fintype.sum_option (f := fun oa => (naimarkData M).liftedEffect oa)
  have hle := (naimarkData M).lifted_sum_le_one
  rw [hsplit] at hle
  have hnone : (0 : Op (d × Option α)) ≤ (naimarkData M).liftedEffect none :=
    (naimarkData M).lifted_pos none
  exact le_trans (le_add_of_nonneg_left hnone) hle

/-- The sum of the dilated projections indexed by genuine answers is itself an
orthogonal projection. -/
theorem naimarkData_isProj_sum_some {α d : Type} [Fintype α] [DecidableEq α]
    [Fintype d] [DecidableEq d] (M : MIPStarRE.Quantum.Measurement α d) :
    IsProj (∑ a : α, (naimarkData M).liftedEffect (some a)) :=
  isProj_sum_of_isProj_of_sum_le_one
    (fun a => (naimarkData M).lifted_isProj (some a))
    (naimarkData_sum_some_le_one M)

/-- The effects of the dilated measurement.  The projection attached to the
answer `a` is the Naimark projection of `a`, except that the distinguished answer
`a₀` also absorbs the deficiency `1 - ∑_a P_a`, which makes the family complete.
Formalization-only construction supporting `thm:ms-rigidity`, blueprint
`ch13_qpbt_test.tex:224-253`. -/
noncomputable def naimarkDilatedEffect {α d : Type} [Fintype α] [DecidableEq α]
    [Fintype d] [DecidableEq d] (M : MIPStarRE.Quantum.Measurement α d) (a₀ a : α) :
    Op (d × Option α) :=
  (naimarkData M).liftedEffect (some a) +
    (if a = a₀ then 1 - ∑ b : α, (naimarkData M).liftedEffect (some b) else 0)

/-- The dilated effects are positive semidefinite. -/
theorem naimarkDilatedEffect_pos {α d : Type} [Fintype α] [DecidableEq α]
    [Fintype d] [DecidableEq d] (M : MIPStarRE.Quantum.Measurement α d) (a₀ a : α) :
    0 ≤ naimarkDilatedEffect M a₀ a := by
  unfold naimarkDilatedEffect
  refine add_nonneg ((naimarkData M).lifted_pos (some a)) ?_
  by_cases h : a = a₀
  · simpa [h] using sub_nonneg.mpr (naimarkData_sum_some_le_one M)
  · simp [h]

/-- The dilated effects sum to the identity. -/
theorem naimarkDilatedEffect_sum {α d : Type} [Fintype α] [DecidableEq α]
    [Fintype d] [DecidableEq d] (M : MIPStarRE.Quantum.Measurement α d) (a₀ : α) :
    ∑ a : α, naimarkDilatedEffect M a₀ a = 1 := by
  unfold naimarkDilatedEffect
  rw [Finset.sum_add_distrib, Finset.sum_ite_eq' Finset.univ a₀]
  simp only [Finset.mem_univ, if_pos]
  abel

/-- Every dilated effect is an orthogonal projection. -/
theorem naimarkDilatedEffect_isProj {α d : Type} [Fintype α] [DecidableEq α]
    [Fintype d] [DecidableEq d] (M : MIPStarRE.Quantum.Measurement α d) (a₀ a : α) :
    IsProj (naimarkDilatedEffect M a₀ a) := by
  unfold naimarkDilatedEffect
  by_cases h : a = a₀
  · subst h
    refine IsStarProjection.add
      ((naimarkData M).lifted_isProj (some a)) ?_ ?_
    · simpa using (naimarkData_isProj_sum_some M).one_sub
    · have hmul : (naimarkData M).liftedEffect (some a) *
          ∑ b : α, (naimarkData M).liftedEffect (some b) =
          (naimarkData M).liftedEffect (some a) := by
        rw [Matrix.mul_sum, Finset.sum_eq_single a]
        · exact ((naimarkData M).lifted_isProj (some a)).isIdempotentElem
        · intro b _ hba
          exact mul_eq_zero_of_isProj_family
            (fun c => (naimarkData M).lifted_isProj (some c))
            (naimarkData_sum_some_le_one M) (Ne.symm hba)
        · intro ha
          exact absurd (Finset.mem_univ a) ha
      simp [Matrix.mul_sub, hmul]
  · simpa [h] using (naimarkData M).lifted_isProj (some a)

/-- The dilated measurement: a complete projective measurement on the enlarged
local space whose ground-slice compression is the original positive operator
valued measure.  Formalization-only construction supporting `thm:ms-rigidity`,
blueprint `ch13_qpbt_test.tex:224-253`. -/
noncomputable def naimarkDilatedMeasurement {α d : Type} [Fintype α] [DecidableEq α]
    [Fintype d] [DecidableEq d] (M : MIPStarRE.Quantum.Measurement α d) (a₀ : α) :
    MIPStarRE.Quantum.Measurement α (d × Option α) :=
  MIPStarRE.Quantum.Measurement.ofSumEqOne (naimarkDilatedEffect M a₀)
    (naimarkDilatedEffect_pos M a₀) (naimarkDilatedEffect_sum M a₀)

@[simp]
theorem naimarkDilatedMeasurement_effect {α d : Type} [Fintype α] [DecidableEq α]
    [Fintype d] [DecidableEq d] (M : MIPStarRE.Quantum.Measurement α d) (a₀ a : α) :
    (naimarkDilatedMeasurement M a₀).effect a = naimarkDilatedEffect M a₀ a := rfl

/-- The dilated measurement is projective, which is the property the self-testing
argument of `thm:ms-rigidity` uses. -/
theorem naimarkDilatedMeasurement_isProjective {α d : Type} [Fintype α] [DecidableEq α]
    [Fintype d] [DecidableEq d] (M : MIPStarRE.Quantum.Measurement α d) (a₀ : α) :
    MIPStarRE.QPBT.Measurement.IsProjective (naimarkDilatedMeasurement M a₀) :=
  fun a => naimarkDilatedEffect_isProj M a₀ a

/-- The compression of a dilated effect to the ground slice is the original
effect.  This is the defining property of a Naimark dilation, and the reason the
dilated strategy reproduces every Born probability of the original one. -/
theorem naimarkCompression_naimarkDilatedEffect {α d : Type} [Fintype α] [DecidableEq α]
    [Fintype d] [DecidableEq d] (M : MIPStarRE.Quantum.Measurement α d) (a₀ a : α) :
    naimarkCompression (naimarkDilatedEffect M a₀ a) = M.effect a := by
  have hlift : ∀ b : α,
      naimarkCompression ((naimarkData M).liftedEffect (some b)) = M.effect b := by
    intro b
    ext i j
    have h := (naimarkData M).compression_none_none b i j
    rw [naimarkData_source M] at h
    simpa using h
  have hdef : naimarkCompression
      (1 - ∑ b : α, (naimarkData M).liftedEffect (some b)) = 0 := by
    rw [naimarkCompression_sub, naimarkCompression_one, naimarkCompression_sum]
    simp only [hlift]
    rw [M.sum_eq_one, sub_self]
  unfold naimarkDilatedEffect
  rw [naimarkCompression_add, hlift]
  by_cases h : a = a₀
  · simp [h, hdef]
  · simp [h]

/-! ## The dilated state -/

/-- The image of a bipartite state under the two ground embeddings.  This is the
state of the dilated strategy supporting `thm:ms-rigidity`, blueprint
`ch13_qpbt_test.tex:224-253`. -/
noncomputable def naimarkDilatedState (α : Type) [Fintype α] [DecidableEq α]
    {ιA ιB : Type} [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB]
    (ψ : EuclideanSpace ℂ (ιA × ιB)) :
    EuclideanSpace ℂ ((ιA × Option α) × (ιB × Option α)) :=
  isometryTensor (naimarkEmbedding ιA α) (naimarkEmbedding ιB α) ψ

theorem naimarkDilatedState_apply (α : Type) [Fintype α] [DecidableEq α]
    {ιA ιB : Type} [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB]
    (ψ : EuclideanSpace ℂ (ιA × ιB)) (p : (ιA × Option α) × (ιB × Option α)) :
    naimarkDilatedState α ψ p =
      if p.1.2 = none ∧ p.2.2 = none then ψ (p.1.1, p.2.1) else 0 := by
  classical
  obtain ⟨⟨i, oa⟩, ⟨j, ob⟩⟩ := p
  simp only [naimarkDilatedState, isometryTensor]
  by_cases hoa : oa = none
  · by_cases hob : ob = none
    · simp [hoa, hob, EuclideanSpace.equiv, eq_comm]
    · simp [hob]
  · simp [hoa]

end

end MIPStarRE.QPBT.MagicSquareRigidity
