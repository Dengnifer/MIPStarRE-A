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

The rigidity statement supported here is blueprint
`thm:ms-rigidity`, from
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
(blueprint `thm:ms-rigidity`).  If an orthogonal projection `P` and a
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
(blueprint `thm:ms-rigidity`).  A finite family of orthogonal
projections whose sum is at most the identity is mutually orthogonal: for two
distinct indices the two projections already sum to at most the identity, so the
previous lemma applies. -/
theorem mul_eq_zero_of_isProj_family {d α : Type*} [Fintype d] [DecidableEq d]
    [Fintype α] {P : α → Op d} (hP : ∀ a, IsProj (P a))
    (hsum : ∑ a, P a ≤ 1) {a b : α} (hab : a ≠ b) :
    P a * P b = 0 := by
  classical
  refine mul_eq_zero_of_isProj_of_add_le_one (hP a) (hP b).nonneg ?_
  refine le_trans ?_ hsum
  have hpair : ∑ c ∈ ({a, b} : Finset α), P c = P a + P b := by
    rw [Finset.sum_pair hab]
  rw [← hpair]
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
    (fun c _ _ => (hP c).nonneg)

/-- Formalization-only auxiliary lemma for the dilation of `thm:ms-rigidity`
(blueprint `thm:ms-rigidity`).  The sum of a mutually orthogonal
family of projections is again an orthogonal projection; mutual orthogonality is
supplied by the hypothesis that the sum is at most the identity. -/
theorem isProj_sum_of_isProj_of_sum_le_one {d α : Type*} [Fintype d] [DecidableEq d]
    [Fintype α] {P : α → Op d} (hP : ∀ a, IsProj (P a))
    (hsum : ∑ a, P a ≤ 1) :
    IsProj (∑ a, P a) := by
  classical
  constructor
  · change (∑ a, P a) * (∑ a, P a) = ∑ a, P a
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Matrix.mul_sum, Finset.sum_eq_single a]
    · exact (hP a).isIdempotentElem
    · exact fun b _ hba => mul_eq_zero_of_isProj_family hP hsum (Ne.symm hba)
    · intro ha
      exact absurd (Finset.mem_univ a) ha
  · change star (∑ a, P a) = ∑ a, P a
    rw [star_sum]
    exact Finset.sum_congr rfl fun a _ => (hP a).isSelfAdjoint

/-! ## The ground slice of an enlarged local space -/

/-- The linear map sending a vector `x` of `ℂ^ι` to `x ⊗ |⊥⟩`, where `|⊥⟩` is the
basis vector of the auxiliary register `ℂ^{Option α}` indexed by the adjoined
point.  Formalization-only support for the dilation used by blueprint
`thm:ms-rigidity`. -/
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
embedding serves every question of the dilation supporting blueprint
`thm:ms-rigidity`, paper
`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:612-652`. -/
noncomputable def naimarkEmbedding (ι α : Type) [Fintype ι] [DecidableEq ι]
    [Fintype α] [DecidableEq α] :
    EuclideanSpace ℂ ι →ₗᵢ[ℂ] EuclideanSpace ℂ (ι × Option α) :=
  LinearMap.isometryOfInner (naimarkEmbeddingMap ι α) <| by
    intro x y
    simp [PiLp.inner_apply, Fintype.sum_prod_type, naimarkEmbeddingMap]

/-- The coordinates of the ground embedding: the amplitude is carried to the
auxiliary basis vector `|⊥⟩` and vanishes on the other auxiliary vectors. -/
@[simp]
theorem naimarkEmbedding_apply {ι α : Type} [Fintype ι] [DecidableEq ι]
    [Fintype α] [DecidableEq α] (x : EuclideanSpace ℂ ι) (p : ι × Option α) :
    naimarkEmbedding ι α x p = if p.2 = none then x p.1 else 0 := rfl

/-- The compression of an operator on the enlarged space to the ground slice.
Formalization-only support for the dilation of blueprint
`thm:ms-rigidity`. -/
def naimarkCompression {ι α : Type} [Fintype ι] [DecidableEq ι]
    [Fintype α] [DecidableEq α] (M : Op (ι × Option α)) : Op ι :=
  M.submatrix (fun i => (i, none)) (fun j => (j, none))

/-- The entries of the ground-slice compression. -/
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
dilation of blueprint `thm:ms-rigidity`. -/
def naimarkInflation {ι α : Type} [Fintype ι] [DecidableEq ι]
    [Fintype α] [DecidableEq α] (M : Op ι) : Op (ι × Option α) :=
  Matrix.of fun p q => if p.2 = none ∧ q.2 = none then M p.1 q.1 else 0

/-- The entries of the inflation of an operator to the enlarged space. -/
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
Formalization-only construction supporting blueprint
`thm:ms-rigidity`. -/
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
valued measure.  Formalization-only construction supporting blueprint
`thm:ms-rigidity`. -/
noncomputable def naimarkDilatedMeasurement {α d : Type} [Fintype α] [DecidableEq α]
    [Fintype d] [DecidableEq d] (M : MIPStarRE.Quantum.Measurement α d) (a₀ : α) :
    MIPStarRE.Quantum.Measurement α (d × Option α) :=
  MIPStarRE.Quantum.Measurement.ofSumEqOne (naimarkDilatedEffect M a₀)
    (naimarkDilatedEffect_pos M a₀) (naimarkDilatedEffect_sum M a₀)

/-- The effects of the dilated measurement are the dilated effects. -/
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
state of the dilated strategy supporting blueprint
`thm:ms-rigidity`. -/
noncomputable def naimarkDilatedState (α : Type) [Fintype α] [DecidableEq α]
    {ιA ιB : Type} [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB]
    (ψ : EuclideanSpace ℂ (ιA × ιB)) :
    EuclideanSpace ℂ ((ιA × Option α) × (ιB × Option α)) :=
  isometryTensor (naimarkEmbedding ιA α) (naimarkEmbedding ιB α) ψ

/-- The coordinates of the dilated state: the original amplitudes sit on the
ground slice, where both auxiliary registers carry the adjoined basis vector,
and all remaining coordinates vanish. -/
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

/-- The quadratic form of an operator on a pure state, written out in the
computational basis.  Formalization-only support for the dilation of
blueprint `thm:ms-rigidity`. -/
theorem inner_applyOperatorToState {ι : Type} [Fintype ι] [DecidableEq ι]
    (K : Op ι) (u : EuclideanSpace ℂ ι) :
    inner ℂ u (applyOperatorToState K u) =
      ∑ p : ι, ∑ q : ι, (starRingEnd ℂ) (u p) * (K p q * u q) := by
  simp [PiLp.inner_apply, RCLike.inner_apply, applyOperatorToState,
    Matrix.mulVec, dotProduct, Finset.mul_sum, mul_comm]

/-- On the ground slice the dilated state factors as the original amplitude
times the two indicator amplitudes of the auxiliary registers. -/
theorem naimarkDilatedState_apply_mul (α : Type) [Fintype α] [DecidableEq α]
    {ιA ιB : Type} [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB]
    (ψ : EuclideanSpace ℂ (ιA × ιB)) (i : ιA) (oa : Option α) (j : ιB) (ob : Option α) :
    naimarkDilatedState α ψ ((i, oa), (j, ob)) =
      (if oa = none then (1 : ℂ) else 0) *
        ((if ob = none then (1 : ℂ) else 0) * ψ (i, j)) := by
  rw [naimarkDilatedState_apply]
  by_cases h1 : oa = none <;> by_cases h2 : ob = none <;> simp [h1, h2]

/-- The quadratic form of a product operator on the dilated state agrees with the
quadratic form of the two ground-slice compressions on the original state.  This
is the identity that makes the dilation invisible to every observable quantity of
the strategy. -/
theorem inner_heteroKron_naimarkDilatedState (α : Type) [Fintype α] [DecidableEq α]
    {ιA ιB : Type} [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB]
    (ψ : EuclideanSpace ℂ (ιA × ιB))
    (M : Op (ιA × Option α)) (N : Op (ιB × Option α)) :
    inner ℂ (naimarkDilatedState α ψ)
        (applyOperatorToState (heteroKron M N) (naimarkDilatedState α ψ)) =
      inner ℂ ψ (applyOperatorToState
        (heteroKron (naimarkCompression M) (naimarkCompression N)) ψ) := by
  classical
  rw [inner_applyOperatorToState, inner_applyOperatorToState]
  simp [Fintype.sum_prod_type, Fintype.sum_option, naimarkDilatedState_apply_mul,
    heteroKron, Matrix.kroneckerMap_apply, mul_comm, mul_assoc]

/-- The ground embeddings are isometric, so the dilated state is again a unit
vector when the original one is. -/
theorem naimarkDilatedState_norm (α : Type) [Fintype α] [DecidableEq α]
    {ιA ιB : Type} [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB]
    (ψ : EuclideanSpace ℂ (ιA × ιB)) :
    ‖naimarkDilatedState α ψ‖ = ‖ψ‖ := by
  classical
  rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq]
  congr 1
  simp [Fintype.sum_prod_type, Fintype.sum_option, naimarkDilatedState_apply_mul]

/-! ## The dilated Magic Square strategy -/

/-- The projective dilation of an arbitrary Magic Square strategy.  Both local
spaces acquire one auxiliary register indexed by `Option MsAnswer`, the state is
carried to the ground slice, and each question measurement is replaced by its
Naimark dilation, the deficiency being absorbed by the answer `bit 0`.  This is
the projective strategy on which the self-testing argument of `thm:ms-rigidity`
operates; blueprint `thm:ms-rigidity`, paper
`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:612-652`. -/
noncomputable def msDilatedStrategy (S : Strategy msGame) : Strategy msGame where
  ιA := S.ιA × Option MsAnswer
  ιB := S.ιB × Option MsAnswer
  ψ := naimarkDilatedState MsAnswer S.ψ
  ψ_norm := by
    show ‖naimarkDilatedState MsAnswer S.ψ‖ = 1
    rw [naimarkDilatedState_norm]
    exact S.ψ_norm
  A x := naimarkDilatedMeasurement (α := MsAnswer) (S.A x) (MsAnswer.bit 0)
  B y := naimarkDilatedMeasurement (α := MsAnswer) (S.B y) (MsAnswer.bit 0)

/-- The state of the dilated strategy is the image of the original state under
the two ground embeddings. -/
@[simp]
theorem msDilatedStrategy_psi (S : Strategy msGame) :
    (msDilatedStrategy S).ψ = naimarkDilatedState MsAnswer S.ψ := rfl

/-- Alice's dilated question measurements are the Naimark dilations of her
original ones. -/
@[simp]
theorem msDilatedStrategy_A_effect (S : Strategy msGame) (x : MsType) (a : MsAnswer) :
    ((msDilatedStrategy S).A x).effect a =
      naimarkDilatedEffect (α := MsAnswer) (S.A x) (MsAnswer.bit 0) a := rfl

/-- Bob's dilated question measurements are the Naimark dilations of his
original ones. -/
@[simp]
theorem msDilatedStrategy_B_effect (S : Strategy msGame) (y : MsType) (b : MsAnswer) :
    ((msDilatedStrategy S).B y).effect b =
      naimarkDilatedEffect (α := MsAnswer) (S.B y) (MsAnswer.bit 0) b := rfl

/-- Every question measurement of the dilated strategy is projective, which is
the hypothesis under which the Coladangelo--Stark self-test is stated. -/
theorem msDilatedStrategy_isProjective_A (S : Strategy msGame) (x : MsType) :
    MIPStarRE.QPBT.Measurement.IsProjective ((msDilatedStrategy S).A x) :=
  naimarkDilatedMeasurement_isProjective (α := MsAnswer) (S.A x) (MsAnswer.bit 0)

/-- Every question measurement of the dilated strategy is projective on Bob's
side as well. -/
theorem msDilatedStrategy_isProjective_B (S : Strategy msGame) (y : MsType) :
    MIPStarRE.QPBT.Measurement.IsProjective ((msDilatedStrategy S).B y) :=
  naimarkDilatedMeasurement_isProjective (α := MsAnswer) (S.B y) (MsAnswer.bit 0)

/-! ## Preservation of the value-to-parity layer -/

/-- The dilation preserves every conditioned Born mass. -/
theorem ms_dilated_strategy_outcome_weight (S : Strategy msGame) (x y : MsType)
    (a b : MsAnswer) :
    outcomeWeight (msDilatedStrategy S) x y a b = outcomeWeight S x y a b := by
  change (inner ℂ (naimarkDilatedState MsAnswer S.ψ)
      (applyOperatorToState
        (heteroKron (naimarkDilatedEffect (α := MsAnswer) (S.A x) (MsAnswer.bit 0) a)
          (naimarkDilatedEffect (α := MsAnswer) (S.B y) (MsAnswer.bit 0) b))
        (naimarkDilatedState MsAnswer S.ψ))).re =
    (inner ℂ S.ψ (applyOperatorToState
      (heteroKron ((S.A x).effect a) ((S.B y).effect b)) S.ψ)).re
  rw [inner_heteroKron_naimarkDilatedState, naimarkCompression_naimarkDilatedEffect,
    naimarkCompression_naimarkDilatedEffect]

/-- The dilation preserves Alice's marginal Born masses. -/
theorem ms_dilated_strategy_alice_outcome_weight (S : Strategy msGame) (x : MsType)
    (a : MsAnswer) :
    aliceOutcomeWeight (msDilatedStrategy S) x a = aliceOutcomeWeight S x a := by
  rw [← sum_outcome_weight_right (msDilatedStrategy S) x x a,
    ← sum_outcome_weight_right S x x a]
  exact Finset.sum_congr rfl fun b _ => ms_dilated_strategy_outcome_weight S x x a b

/-- The dilation preserves Bob's marginal Born masses. -/
theorem ms_dilated_strategy_bob_outcome_weight (S : Strategy msGame) (y : MsType)
    (b : MsAnswer) :
    bobOutcomeWeight (msDilatedStrategy S) y b = bobOutcomeWeight S y b := by
  rw [← sum_outcome_weight_left (msDilatedStrategy S) y y b,
    ← sum_outcome_weight_left S y y b]
  exact Finset.sum_congr rfl fun a _ => ms_dilated_strategy_outcome_weight S y y a b

/-- The dilation preserves the mass of every answer event. -/
theorem ms_dilated_strategy_outcome_event_weight (S : Strategy msGame) (x y : MsType)
    (E : MsAnswer → MsAnswer → Prop) [DecidableRel E] :
    outcomeEventWeight (msDilatedStrategy S) x y E = outcomeEventWeight S x y E := by
  unfold outcomeEventWeight
  exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by
    by_cases h : E a b <;> simp [h, ms_dilated_strategy_outcome_weight]

/-- The dilation preserves the mass of every event depending only on Alice's
answer. -/
theorem ms_dilated_strategy_alice_event_weight (S : Strategy msGame) (x : MsType)
    (E : MsAnswer → Prop) [DecidablePred E] :
    aliceEventWeight (msDilatedStrategy S) x E = aliceEventWeight S x E := by
  unfold aliceEventWeight
  exact Finset.sum_congr rfl fun a _ => by
    by_cases h : E a <;> simp [h, ms_dilated_strategy_alice_outcome_weight]

/-- The dilation preserves the mass of every event depending only on Bob's
answer. -/
theorem ms_dilated_strategy_bob_event_weight (S : Strategy msGame) (y : MsType)
    (E : MsAnswer → Prop) [DecidablePred E] :
    bobEventWeight (msDilatedStrategy S) y E = bobEventWeight S y E := by
  unfold bobEventWeight
  exact Finset.sum_congr rfl fun b _ => by
    by_cases h : E b <;> simp [h, ms_dilated_strategy_bob_outcome_weight]

/-- The dilation preserves the conditioned rejection mass. -/
theorem ms_dilated_strategy_rejection_mass (S : Strategy msGame) (x y : MsType) :
    rejectionMass (msDilatedStrategy S) x y = rejectionMass S x y :=
  ms_dilated_strategy_outcome_event_weight S x y _

/-- The dilation preserves the value of the Magic Square game, so a strategy of
value at least `1 - ε` dilates to a projective strategy of the same value. -/
theorem ms_dilated_strategy_value (S : Strategy msGame) :
    (msDilatedStrategy S).value = S.value := by
  rw [strategy_value_eq_acceptance_mass, strategy_value_eq_acceptance_mass]
  congr 1
  funext xy
  exact ms_dilated_strategy_outcome_event_weight S xy.1 xy.2 _

/-- The dilation preserves the total rejection mass, hence the whole
value-to-parity layer applies verbatim to the dilated strategy. -/
theorem ms_dilated_strategy_total_rejection_mass (S : Strategy msGame) :
    totalRejectionMass (msDilatedStrategy S) = totalRejectionMass S := by
  unfold totalRejectionMass
  congr 1
  funext xy
  exact ms_dilated_strategy_rejection_mass S xy.1 xy.2

/-- The dilation preserves Alice's malformed variable-answer mass. -/
theorem ms_dilated_strategy_alice_variable_wrong_form_mass (S : Strategy msGame) (j : Fin 9) :
    aliceVariableWrongFormMass (msDilatedStrategy S) j = aliceVariableWrongFormMass S j :=
  ms_dilated_strategy_alice_event_weight S _ _

/-- The dilation preserves Bob's malformed variable-answer mass. -/
theorem ms_dilated_strategy_bob_variable_wrong_form_mass (S : Strategy msGame) (j : Fin 9) :
    bobVariableWrongFormMass (msDilatedStrategy S) j = bobVariableWrongFormMass S j :=
  ms_dilated_strategy_bob_event_weight S _ _

/-- The dilation preserves Alice's malformed constraint-answer mass. -/
theorem ms_dilated_strategy_alice_constraint_wrong_form_mass (S : Strategy msGame) (i : Fin 6) :
    aliceConstraintWrongFormMass (msDilatedStrategy S) i = aliceConstraintWrongFormMass S i :=
  ms_dilated_strategy_alice_event_weight S _ _

/-- The dilation preserves Bob's malformed constraint-answer mass. -/
theorem ms_dilated_strategy_bob_constraint_wrong_form_mass (S : Strategy msGame) (i : Fin 6) :
    bobConstraintWrongFormMass (msDilatedStrategy S) i = bobConstraintWrongFormMass S i :=
  ms_dilated_strategy_bob_event_weight S _ _

/-- The dilation preserves the forward cell-consistency defect. -/
theorem ms_dilated_strategy_forward_cell_mismatch_mass (S : Strategy msGame)
    (i : Fin 6) (k : Fin 3) :
    forwardCellMismatchMass (msDilatedStrategy S) i k = forwardCellMismatchMass S i k :=
  ms_dilated_strategy_outcome_event_weight S _ _ _

/-- The dilation preserves the reverse cell-consistency defect. -/
theorem ms_dilated_strategy_reverse_cell_mismatch_mass (S : Strategy msGame)
    (i : Fin 6) (k : Fin 3) :
    reverseCellMismatchMass (msDilatedStrategy S) i k = reverseCellMismatchMass S i k :=
  ms_dilated_strategy_outcome_event_weight S _ _ _

/-- The dilation preserves Alice's row or column parity-failure mass. -/
theorem ms_dilated_strategy_alice_parity_failure_mass (S : Strategy msGame) (i : Fin 6) :
    aliceParityFailureMass (msDilatedStrategy S) i = aliceParityFailureMass S i :=
  ms_dilated_strategy_alice_event_weight S _ _

/-- The dilation preserves Bob's row or column parity-failure mass. -/
theorem ms_dilated_strategy_bob_parity_failure_mass (S : Strategy msGame) (i : Fin 6) :
    bobParityFailureMass (msDilatedStrategy S) i = bobParityFailureMass S i :=
  ms_dilated_strategy_bob_event_weight S _ _

/-! ## Composition of the dilation with later local isometries -/

/-- The matrix of a linear isometry of Euclidean spaces in the computational
bases.  Formalization-only support for blueprint
`thm:ms-rigidity`. -/
noncomputable def isometryMatrix {ι ι' : Type} [Fintype ι] [DecidableEq ι]
    [Fintype ι'] [DecidableEq ι']
    (φ : EuclideanSpace ℂ ι →ₗᵢ[ℂ] EuclideanSpace ℂ ι') : Matrix ι' ι ℂ :=
  Matrix.toEuclideanLin.symm φ.toLinearMap

/-- Conjugation by an isometry is conjugation by its matrix. -/
theorem conjIsometry_eq {ι ι' : Type} [Fintype ι] [DecidableEq ι]
    [Fintype ι'] [DecidableEq ι']
    (φ : EuclideanSpace ℂ ι →ₗᵢ[ℂ] EuclideanSpace ℂ ι') (M : Op ι) :
    conjIsometry φ M = isometryMatrix φ * M * (isometryMatrix φ)ᴴ := rfl

/-- The matrix of an isometry acts on vectors as the isometry does. -/
theorem isometryMatrix_mulVec {ι ι' : Type} [Fintype ι] [DecidableEq ι]
    [Fintype ι'] [DecidableEq ι']
    (φ : EuclideanSpace ℂ ι →ₗᵢ[ℂ] EuclideanSpace ℂ ι') (x : EuclideanSpace ℂ ι) :
    isometryMatrix φ *ᵥ WithLp.ofLp x = WithLp.ofLp (φ x) := by
  have h : Matrix.toEuclideanLin (isometryMatrix φ) = φ.toLinearMap :=
    Matrix.toEuclideanLin.apply_symm_apply φ.toLinearMap
  have h' : Matrix.toEuclideanLin (isometryMatrix φ) x = φ x := by rw [h]; rfl
  simpa using congrArg WithLp.ofLp h'

/-- The columns of the matrix of an isometry are the images of the basis
vectors. -/
theorem isometryMatrix_apply {ι ι' : Type} [Fintype ι] [DecidableEq ι]
    [Fintype ι'] [DecidableEq ι']
    (φ : EuclideanSpace ℂ ι →ₗᵢ[ℂ] EuclideanSpace ℂ ι') (k : ι') (i : ι) :
    isometryMatrix φ k i =
      φ ((EuclideanSpace.equiv ι ℂ).symm (Pi.single i 1)) k := by
  have h := congrFun (isometryMatrix_mulVec φ
    ((EuclideanSpace.equiv ι ℂ).symm (Pi.single i 1))) k
  rw [← h]
  simp [Matrix.mulVec, dotProduct, EuclideanSpace.equiv, eq_comm]

/-- The matrix of a composite isometry is the product of the two matrices. -/
theorem isometryMatrix_comp {ι κ ν : Type} [Fintype ι] [DecidableEq ι]
    [Fintype κ] [DecidableEq κ] [Fintype ν] [DecidableEq ν]
    (φ : EuclideanSpace ℂ κ →ₗᵢ[ℂ] EuclideanSpace ℂ ν)
    (E : EuclideanSpace ℂ ι →ₗᵢ[ℂ] EuclideanSpace ℂ κ) :
    isometryMatrix (φ.comp E) = isometryMatrix φ * isometryMatrix E := by
  ext k i
  have h := congrFun (isometryMatrix_mulVec φ
    (E ((EuclideanSpace.equiv ι ℂ).symm (Pi.single i 1)))) k
  rw [isometryMatrix_apply, Matrix.mul_apply]
  simp only [isometryMatrix_apply E]
  simpa [Matrix.mulVec, dotProduct] using h.symm

/-- Conjugating by a composite isometry is conjugating twice.  This is how the
ground embeddings of the dilation combine with the local isometries produced by
the self-testing argument of blueprint
`thm:ms-rigidity`. -/
theorem conjIsometry_comp {ι κ ν : Type} [Fintype ι] [DecidableEq ι]
    [Fintype κ] [DecidableEq κ] [Fintype ν] [DecidableEq ν]
    (φ : EuclideanSpace ℂ κ →ₗᵢ[ℂ] EuclideanSpace ℂ ν)
    (E : EuclideanSpace ℂ ι →ₗᵢ[ℂ] EuclideanSpace ℂ κ) (M : Op ι) :
    conjIsometry (φ.comp E) M = conjIsometry φ (conjIsometry E M) := by
  rw [conjIsometry_eq, conjIsometry_eq, conjIsometry_eq, isometryMatrix_comp]
  simp [Matrix.conjTranspose_mul, Matrix.mul_assoc]

/-- The two-sided isometry image of a bipartite state, written through the
Kronecker product of the two isometry matrices. -/
theorem isometryTensor_apply_eq {ιA ιB κA κB : Type}
    [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB]
    [Fintype κA] [DecidableEq κA] [Fintype κB] [DecidableEq κB]
    (φA : EuclideanSpace ℂ ιA →ₗᵢ[ℂ] EuclideanSpace ℂ κA)
    (φB : EuclideanSpace ℂ ιB →ₗᵢ[ℂ] EuclideanSpace ℂ κB)
    (ψ : EuclideanSpace ℂ (ιA × ιB)) (p : κA × κB) :
    isometryTensor φA φB ψ p =
      ∑ q : ιA × ιB,
        Matrix.kronecker (isometryMatrix φA) (isometryMatrix φB) p q * ψ q := by
  simp [isometryTensor, Matrix.kronecker, Fintype.sum_prod_type, isometryMatrix_apply,
    EuclideanSpace.equiv, mul_assoc]

/-- Applying two local isometries after two others is the same as applying their
composites.  Together with `conjIsometry_comp` this is the composition rule used
to turn a rigidity witness for the dilated strategy into one for the original
strategy. -/
theorem isometryTensor_comp {ιA ιB κA κB νA νB : Type}
    [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB]
    [Fintype κA] [DecidableEq κA] [Fintype κB] [DecidableEq κB]
    [Fintype νA] [DecidableEq νA] [Fintype νB] [DecidableEq νB]
    (φA : EuclideanSpace ℂ κA →ₗᵢ[ℂ] EuclideanSpace ℂ νA)
    (φB : EuclideanSpace ℂ κB →ₗᵢ[ℂ] EuclideanSpace ℂ νB)
    (EA : EuclideanSpace ℂ ιA →ₗᵢ[ℂ] EuclideanSpace ℂ κA)
    (EB : EuclideanSpace ℂ ιB →ₗᵢ[ℂ] EuclideanSpace ℂ κB)
    (ψ : EuclideanSpace ℂ (ιA × ιB)) :
    isometryTensor (φA.comp EA) (φB.comp EB) ψ =
      isometryTensor φA φB (isometryTensor EA EB ψ) := by
  ext p
  rw [isometryTensor_apply_eq, isometryTensor_apply_eq]
  simp only [isometryTensor_apply_eq, isometryMatrix_comp, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun r _ => ?_
  have hk : (isometryMatrix φA * isometryMatrix EA).kronecker
        (isometryMatrix φB * isometryMatrix EB) =
      (isometryMatrix φA).kronecker (isometryMatrix φB) *
        (isometryMatrix EA).kronecker (isometryMatrix EB) :=
    Matrix.mul_kronecker_mul _ _ _ _
  rw [hk, Matrix.mul_apply, Finset.sum_mul]
  exact Finset.sum_congr rfl fun x _ => by ring

/-- The ground embeddings of the dilation composed with two later local
isometries carry the original state exactly as those isometries carry the
dilated state. -/
theorem isometryTensor_comp_naimarkEmbedding (α : Type) [Fintype α] [DecidableEq α]
    {ιA ιB κA κB : Type} [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB]
    [Fintype κA] [DecidableEq κA] [Fintype κB] [DecidableEq κB]
    (φA : EuclideanSpace ℂ (ιA × Option α) →ₗᵢ[ℂ] EuclideanSpace ℂ κA)
    (φB : EuclideanSpace ℂ (ιB × Option α) →ₗᵢ[ℂ] EuclideanSpace ℂ κB)
    (ψ : EuclideanSpace ℂ (ιA × ιB)) :
    isometryTensor (φA.comp (naimarkEmbedding ιA α)) (φB.comp (naimarkEmbedding ιB α)) ψ =
      isometryTensor φA φB (naimarkDilatedState α ψ) :=
  isometryTensor_comp φA φB _ _ ψ

/-! ## Transfer of state-dependent bounds -/

/-- Conjugating an operator by the ground embedding inflates it: the result acts
as the original operator on the ground slice and annihilates the orthogonal
complement. -/
theorem conjIsometry_naimarkEmbedding {ι α : Type} [Fintype ι] [DecidableEq ι]
    [Fintype α] [DecidableEq α] (M : Op ι) :
    conjIsometry (naimarkEmbedding ι α) M = naimarkInflation (α := α) M := by
  ext p q
  rw [conjIsometry_eq]
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, isometryMatrix_apply,
    naimarkEmbedding_apply, naimarkInflation_apply, EuclideanSpace.equiv]
  by_cases hp : p.2 = none
  · by_cases hq : q.2 = none <;> simp [hp, hq, eq_comm]
  · simp [hp]

/-- Conjugating an operator by the ground embedding followed by a later local
isometry is conjugating its inflation by that isometry.  This is the form in
which the conclusions of a self-testing argument applied to the dilated strategy
are read back on the original strategy. -/
theorem conjIsometry_comp_naimarkEmbedding {ι α κ : Type} [Fintype ι] [DecidableEq ι]
    [Fintype α] [DecidableEq α] [Fintype κ] [DecidableEq κ]
    (φ : EuclideanSpace ℂ (ι × Option α) →ₗᵢ[ℂ] EuclideanSpace ℂ κ) (M : Op ι) :
    conjIsometry (φ.comp (naimarkEmbedding ι α)) M =
      conjIsometry φ (naimarkInflation (α := α) M) := by
  rw [conjIsometry_comp, conjIsometry_naimarkEmbedding]

/-- Compressing one of Alice's dilated Magic Square effects to the ground slice
returns her original effect. -/
theorem naimarkCompression_msDilatedStrategy_A_effect (S : Strategy msGame)
    (x : MsType) (a : MsAnswer) :
    naimarkCompression (α := MsAnswer) (((msDilatedStrategy S).A x).effect a) =
      (S.A x).effect a :=
  naimarkCompression_naimarkDilatedEffect (α := MsAnswer) (S.A x) (MsAnswer.bit 0) a

/-- Compressing one of Bob's dilated Magic Square effects to the ground slice
returns his original effect. -/
theorem naimarkCompression_msDilatedStrategy_B_effect (S : Strategy msGame)
    (y : MsType) (b : MsAnswer) :
    naimarkCompression (α := MsAnswer) (((msDilatedStrategy S).B y).effect b) =
      (S.B y).effect b :=
  naimarkCompression_naimarkDilatedEffect (α := MsAnswer) (S.B y) (MsAnswer.bit 0) b

/-- The action of an operator on the dilated state only sees its ground-slice
columns. -/
theorem applyOperatorToState_naimarkDilatedState (α : Type) [Fintype α] [DecidableEq α]
    {ιA ιB : Type} [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB]
    (K : Op ((ιA × Option α) × (ιB × Option α)))
    (ψ : EuclideanSpace ℂ (ιA × ιB)) (p : (ιA × Option α) × (ιB × Option α)) :
    applyOperatorToState K (naimarkDilatedState α ψ) p =
      ∑ k : ιA, ∑ l : ιB, K p ((k, none), (l, none)) * ψ (k, l) := by
  classical
  simp [applyOperatorToState, Matrix.mulVec, dotProduct, Fintype.sum_prod_type,
    Fintype.sum_option, naimarkDilatedState_apply_mul]

/-- Inflated operators act on the dilated state exactly as the original
operators act on the original state.  This is the identity that transfers
state-dependent effect bounds back to the undilated strategy. -/
theorem applyOperatorToState_heteroKron_naimarkInflation
    (α : Type) [Fintype α] [DecidableEq α]
    {ιA ιB : Type} [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB]
    (M : Op ιA) (N : Op ιB) (ψ : EuclideanSpace ℂ (ιA × ιB)) :
    applyOperatorToState
        (heteroKron (naimarkInflation (α := α) M) (naimarkInflation (α := α) N))
        (naimarkDilatedState α ψ) =
      naimarkDilatedState α (applyOperatorToState (heteroKron M N) ψ) := by
  classical
  ext p
  rw [applyOperatorToState_naimarkDilatedState, naimarkDilatedState_apply]
  obtain ⟨⟨i, oa⟩, ⟨j, ob⟩⟩ := p
  by_cases hoa : oa = none
  · by_cases hob : ob = none
    · simp [hoa, hob, heteroKron, applyOperatorToState, Matrix.mulVec, dotProduct,
        Fintype.sum_prod_type, mul_assoc]
    · simp [hob, heteroKron]
  · simp [hoa, heteroKron]

/-- The state-dependent norm of an inflated operator on the dilated state equals
the state-dependent norm of the original operator on the original state. -/
theorem norm_applyOperatorToState_heteroKron_naimarkInflation
    (α : Type) [Fintype α] [DecidableEq α]
    {ιA ιB : Type} [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB]
    (M : Op ιA) (N : Op ιB) (ψ : EuclideanSpace ℂ (ιA × ιB)) :
    ‖applyOperatorToState
        (heteroKron (naimarkInflation (α := α) M) (naimarkInflation (α := α) N))
        (naimarkDilatedState α ψ)‖ =
      ‖applyOperatorToState (heteroKron M N) ψ‖ := by
  rw [applyOperatorToState_heteroKron_naimarkInflation, naimarkDilatedState_norm]

/-- Every average squared distance between two families of *inflated*
operators, measured on the dilated state, is the corresponding distance between
the original families measured on the original state.  This identity concerns
inflations only: the dilated projectors of `msDilatedStrategy` are not
inflations, and their difference from the inflated original effects on the
dilated state is the leakage out of the ground slice, which is controlled in
`Rigidity/Transfer.lean` (`ms_effect_transfer_A`, `ms_effect_transfer_B`,
`ms_anticommutator_transfer_A`, `ms_anticommutator_transfer_B`) by the
cell-consistency masses of the value-to-parity layer.  Blueprint
`thm:ms-rigidity`, paper
`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:612-652`. -/
theorem opFamilyDistSq_naimarkInflation (α : Type) [Fintype α] [DecidableEq α]
    {X γ ιA ιB : Type} [Fintype γ] [Fintype ιA] [DecidableEq ιA]
    [Fintype ιB] [DecidableEq ιB]
    (μ : Distribution X) (M N : X → γ → Op ιA) (P : X → γ → Op ιB)
    (ψ : EuclideanSpace ℂ (ιA × ιB)) :
    opFamilyDistSq μ
        (fun x c => heteroKron (naimarkInflation (α := α) (M x c))
          (naimarkInflation (α := α) (P x c)))
        (fun x c => heteroKron (naimarkInflation (α := α) (N x c))
          (naimarkInflation (α := α) (P x c)))
        (naimarkDilatedState α ψ) =
      opFamilyDistSq μ (fun x c => heteroKron (M x c) (P x c))
        (fun x c => heteroKron (N x c) (P x c)) ψ := by
  unfold opFamilyDistSq
  congr 1
  funext x
  refine Finset.sum_congr rfl fun c _ => ?_
  have hkron : ∀ {ρA ρB : Type} [Fintype ρA] [DecidableEq ρA] [Fintype ρB] [DecidableEq ρB]
      (X Y : Op ρA) (Z : Op ρB),
      heteroKron X Z - heteroKron Y Z = heteroKron (X - Y) Z := by
    intro ρA ρB _ _ _ _ X Y Z
    ext p q
    simp [heteroKron, Matrix.kronecker, sub_mul]
  have hinfl : naimarkInflation (α := α) (M x c) - naimarkInflation (α := α) (N x c) =
      naimarkInflation (α := α) (M x c - N x c) := by
    ext p q
    by_cases h : p.2 = none ∧ q.2 = none <;> simp [h]
  rw [hkron, hkron, hinfl, norm_applyOperatorToState_heteroKron_naimarkInflation]

end

end MIPStarRE.QPBT.MagicSquareRigidity
