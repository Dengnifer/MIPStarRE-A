import MIPStarRE.QPBT.Algebra.Subspaces

/-!
# Reduced row echelon form and the canonical complement

For matrices with independent rows, reduced row echelon form consists of ordered
pivot columns, an identity matrix in those columns, and zeros before each pivot.
This module compares its nonpivot indices with the intrinsic prefix-rank
definition of `canonicalComplement`.

Independent input rows have such a matrix with the same row span and an
invertible change of row basis. The pivot index set depends only on that span.
An explicit row combination gives the complementary-subspace decomposition.
The canonical complement has the asserted cardinality and independence, and
for register subspaces it consists of the remaining standard basis vectors.

The arbitrary-field and zero-dimensional cases are extensions of the paper's
ambient convention of a finite field and positive ambient dimension. The results
include an executable decomposition once an RREF matrix is supplied, but do not
provide an executable elimination algorithm or a complexity theorem for finding it.

## References

* `references/qpbt-paper/04_preliminaries.tex:219-222`, ambient convention.
* `references/qpbt-paper/04_preliminaries.tex:303-373`,
  Definition `def:canonical-complement` and Lemma `lem:canonical-complement`.
* `audits/2026-09-21_issue-676-canonical-complement-alignment.md`, issue #676.
-/

open scoped BigOperators

namespace MIPStarRE.QPBT

variable {K : Type*} [Field K] {m n : ℕ}

/-- Conventional reduced row echelon form for a matrix with no zero rows.
The order embedding lists the leading columns from left to right. This is
Lean-only linear algebra supporting paper `def:canonical-complement`; no rank
formula or complement identity is part of the predicate. -/
structure IsReducedRowEchelon (B : Matrix (Fin m) (Fin n) K)
    (pivot : Fin m ↪o Fin n) : Prop where
  pivot_entry : ∀ i j, B i (pivot j) = if i = j then 1 else 0
  zero_before : ∀ i j, j < pivot i → B i j = 0

/-- The pivot columns witness linear independence of the rows of an RREF matrix. -/
lemma IsReducedRowEchelon.linearIndependent_rows
    {B : Matrix (Fin m) (Fin n) K} {pivot : Fin m ↪o Fin n}
    (hB : IsReducedRowEchelon B pivot) : LinearIndependent K B.row := by
  classical
  apply Fintype.linearIndependent_iff.mpr
  intro c hc i
  have hi := congrFun hc (pivot i)
  simpa [Matrix.row, Finset.sum_apply, hB.pivot_entry] using hi

/-- The rank of the first `k` columns is the number of pivots in those columns.
Rows whose pivots lie beyond the prefix restrict to zero, and the remaining
rows are independent on their pivot columns. -/
lemma IsReducedRowEchelon.prefixRank_eq_card
    {B : Matrix (Fin m) (Fin n) K} {pivot : Fin m ↪o Fin n}
    (hB : IsReducedRowEchelon B pivot) {k : ℕ} (hk : k ≤ n) :
    prefixRank (Submodule.span K (Set.range B.row)) k hk =
      (Finset.univ.filter fun i => (pivot i).val < k).card := by
  classical
  let s := Finset.univ.filter fun i => (pivot i).val < k
  let b : s → Fin k → K := fun i => prefixMap k n hk (B.row i.val)
  have hb : LinearIndependent K b := by
    apply Fintype.linearIndependent_iff.mpr
    intro c hc i
    have hi := congrFun hc
      ⟨(pivot i.val).val, (Finset.mem_filter.mp i.property).2⟩
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at hi
    change (∑ j : s, c j * B j.val (pivot i.val)) = 0 at hi
    simpa [hB.pivot_entry, ← Subtype.ext_iff] using hi
  have hspan :
      Submodule.span K (Set.range (fun i => prefixMap k n hk (B.row i))) =
        Submodule.span K (Set.range b) := by
    apply le_antisymm
    · apply Submodule.span_le.mpr
      rintro _ ⟨i, rfl⟩
      by_cases hi : (pivot i).val < k
      · exact Submodule.subset_span ⟨⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩⟩,
          rfl⟩
      · have hz : prefixMap k n hk (B.row i) = 0 := by
          funext j
          apply hB.zero_before
          change j.val < (pivot i).val
          exact lt_of_lt_of_le j.isLt (Nat.le_of_not_lt hi)
        change prefixMap k n hk (B.row i) ∈ _
        rw [hz]
        exact Submodule.zero_mem _
    · apply Submodule.span_mono
      rintro _ ⟨i, rfl⟩
      exact ⟨i.val, rfl⟩
  rw [prefixRank, Submodule.map_span, ← Set.range_comp]
  change Module.finrank K
    (Submodule.span K (Set.range (fun i => prefixMap k n hk (B.row i)))) = s.card
  rw [hspan, finrank_span_eq_card hb]
  exact Fintype.card_coe s

/-- The intrinsic canonical complement of the row span of an RREF matrix is
exactly its nonpivot index set. This identifies the index sets underlying paper
`def:canonical-complement`, independently of an elimination algorithm. -/
theorem IsReducedRowEchelon.canonicalComplement_eq_nonpivot_indices
    {B : Matrix (Fin m) (Fin n) K} {pivot : Fin m ↪o Fin n}
    (hB : IsReducedRowEchelon B pivot) :
    canonicalComplement (Submodule.span K (Set.range B.row)) =
      (Finset.univ.image pivot)ᶜ := by
  classical
  ext j
  simp only [canonicalComplement, Finset.mem_filter, Finset.mem_univ, true_and,
    hB.prefixRank_eq_card, Finset.mem_compl, Finset.mem_image]
  constructor
  · intro hcard hpivot
    obtain ⟨i, hi⟩ := hpivot
    have hsub : (Finset.univ.filter fun a => (pivot a).val < j.val) ⊆
        (Finset.univ.filter fun a => (pivot a).val < j.val + 1) := by
      intro a ha
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha ⊢
      omega
    have heq := Finset.eq_of_subset_of_card_le hsub hcard.le
    have hi' : i ∈ Finset.univ.filter fun a => (pivot a).val < j.val + 1 := by
      simp [hi]
    rw [← heq] at hi'
    simp [hi] at hi'
  · intro hpivot
    congr 1
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    have hne : (pivot i).val ≠ j.val := by
      intro h
      exact hpivot ⟨i, Fin.ext h⟩
    omega

/-- Independent input rows have an RREF matrix with exactly the same row span.
The proof constructs its rows by projection along the intrinsic coordinate
complement, then verifies the conventional entrywise conditions. This is an
abstract existence theorem supporting paper `def:canonical-complement`, not a
Gaussian-elimination algorithm. -/
theorem exists_isReducedRowEchelon_span_eq
    (A : Matrix (Fin m) (Fin n) K) (hA : LinearIndependent K A.row) :
    ∃ (B : Matrix (Fin m) (Fin n) K) (pivot : Fin m ↪o Fin n),
      IsReducedRowEchelon B pivot ∧
        Submodule.span K (Set.range B.row) = Submodule.span K (Set.range A.row) := by
  classical
  let W := Submodule.span K (Set.range A.row)
  let C := canonicalComplement W
  let P := Cᶜ
  let T := registerSubmodule K C
  have hcomp : IsCompl W T := isCompl_registerSubmodule_canonicalComplement W
  have hW : Module.finrank K W = m := by
    simpa [W] using finrank_span_eq_card hA
  have hT : Module.finrank K T = C.card := by
    change Module.finrank K (registerSubmodule K C) = C.card
    rw [registerSubmodule_eq_spanSubset, Pi.dim_spanSubset]
    simp
  have hcard : P.card = m := by
    have hdim := Submodule.finrank_add_eq_of_isCompl hcomp
    have hpartition := Finset.card_add_card_compl C
    rw [hW, hT, Module.finrank_fin_fun] at hdim
    simp only [Fintype.card_fin] at hpartition
    dsimp [P]
    omega
  let pivot : Fin m ↪o Fin n := P.orderEmbOfFin hcard
  let B : Matrix (Fin m) (Fin n) K :=
    fun i => W.projection T hcomp (Pi.single (pivot i) 1)
  have hmem (i : Fin m) : B.row i ∈ W :=
    Submodule.projection_apply_mem hcomp _
  have hpivot (i j : Fin m) : B i (pivot j) = if i = j then 1 else 0 := by
    have hx := Submodule.sub_projection_mem hcomp (Pi.single (pivot i) (1 : K))
    change _ ∈ registerSubmodule K C at hx
    rw [registerSubmodule_eq_spanSubset] at hx
    have hj : pivot j ∉ C := Finset.mem_compl.mp (P.orderEmbOfFin_mem hcard j)
    have hz := Pi.mem_spanSubset_iff.mp hx (pivot j) hj
    change (Pi.single (pivot i) (1 : K) : Fin n → K) (pivot j) - B i (pivot j) = 0 at hz
    rw [← sub_eq_zero.mp hz]
    simp [Pi.single_apply, pivot.injective.eq_iff, eq_comm]
  have hB : IsReducedRowEchelon B pivot := by
    refine ⟨hpivot, ?_⟩
    intro i j hj
    have hz : ∀ (r : ℕ) (hr : r < n), r < (pivot i).val → B i ⟨r, hr⟩ = 0 := by
      intro r
      induction r using Nat.strong_induction_on with
      | h r ih =>
        intro hr hri
        let a : Fin n := ⟨r, hr⟩
        by_cases ha : a ∈ C
        · apply coordinate_eq_zero_of_prefixRank_eq W a
          · simpa [C, canonicalComplement] using ha
          · exact hmem i
          · intro b hb
            exact ih b.val hb b.isLt (lt_trans hb hri)
        · have haP : a ∈ P := Finset.mem_compl.mpr ha
          have harange : a ∈ Set.range pivot := by
            rw [Finset.range_orderEmbOfFin]
            exact haP
          obtain ⟨l, hl⟩ := harange
          have hil : i ≠ l := by
            intro h
            subst l
            have heq := congrArg Fin.val hl
            dsimp [a] at heq
            omega
          change B i a = 0
          rw [← hl, hpivot, if_neg hil]
    exact hz j.val j.isLt hj
  refine ⟨B, pivot, hB, ?_⟩
  apply Submodule.eq_of_le_of_finrank_eq
  · exact Submodule.span_le.mpr (Set.range_subset_iff.mpr hmem)
  · rw [finrank_span_eq_card hB.linearIndependent_rows, Fintype.card_fin]
    exact hW.symm

/-- Independent rows have a reduced row echelon presentation `A = U * B` with
`U` invertible, the same row span, and precisely the intrinsic canonical
complement as nonpivot indices. This establishes the abstract correspondence
with paper `def:canonical-complement` and the change of basis used in
`lem:canonical-complement`. Arbitrary fields and zero ambient dimension extend
the paper's domain; no algorithmic complexity assertion is made. -/
theorem exists_isReducedRowEchelon
    (A : Matrix (Fin m) (Fin n) K) (hA : LinearIndependent K A.row) :
    ∃ (B : Matrix (Fin m) (Fin n) K) (pivot : Fin m ↪o Fin n)
      (U : Matrix (Fin m) (Fin m) K),
      IsUnit U ∧ A = U * B ∧ IsReducedRowEchelon B pivot ∧
        Submodule.span K (Set.range B.row) = Submodule.span K (Set.range A.row) ∧
        canonicalComplement (Submodule.span K (Set.range A.row)) =
          (Finset.univ.image pivot)ᶜ := by
  classical
  obtain ⟨B, pivot, hB, hspan⟩ := exists_isReducedRowEchelon_span_eq A hA
  have hcoeff : ∀ i, ∃ c : Fin m → K, ∑ j, c j • B.row j = A.row i := by
    intro i
    apply (Submodule.mem_span_range_iff_exists_fun K).mp
    rw [hspan]
    exact Submodule.subset_span ⟨i, rfl⟩
  choose c hc using hcoeff
  let U : Matrix (Fin m) (Fin m) K := Matrix.of c
  have hmul : A = U * B := by
    ext i j
    have hij := congrFun (hc i) j
    simpa [U, Matrix.mul_apply, Matrix.row, Finset.sum_apply, smul_eq_mul] using hij.symm
  have hunit : IsUnit U := by
    apply Matrix.linearIndependent_rows_iff_isUnit.mp
    apply LinearIndependent.of_comp B.vecMulLinear
    change LinearIndependent K (U * B).row
    rwa [← hmul]
  refine ⟨B, pivot, U, hunit, hmul, hB, hspan, ?_⟩
  rw [← hspan]
  exact hB.canonicalComplement_eq_nonpivot_indices

/-- The pivot index set is independent of the chosen row basis and its order:
any two RREF matrices spanning the same subspace have the same pivots. This is
the basis-independence assertion accompanying blueprint
`def:canonical-complement`. -/
theorem IsReducedRowEchelon.pivot_indices_eq_of_span_eq
    {m' : ℕ} {B : Matrix (Fin m) (Fin n) K} {D : Matrix (Fin m') (Fin n) K}
    {pivot : Fin m ↪o Fin n} {pivot' : Fin m' ↪o Fin n}
    (hB : IsReducedRowEchelon B pivot) (hD : IsReducedRowEchelon D pivot')
    (hspan : Submodule.span K (Set.range B.row) = Submodule.span K (Set.range D.row)) :
    Finset.univ.image pivot = Finset.univ.image pivot' := by
  have h := congrArg canonicalComplement hspan
  rw [hB.canonicalComplement_eq_nonpivot_indices,
    hD.canonicalComplement_eq_nonpivot_indices] at h
  exact compl_injective h

/-- The row-span component used in the proof of paper `lem:canonical-complement`,
`references/qpbt-paper/04_preliminaries.tex:357-371`. Given an RREF matrix and its
pivots, its value at `x` is the row combination with coefficients `x (pivot i)`.
This finite matrix product is executable; finding the RREF matrix is separate. -/
def rowEchelonComponent (B : Matrix (Fin m) (Fin n) K) (pivot : Fin m ↪o Fin n)
    (x : Fin n → K) : Fin n → K :=
  Matrix.vecMul (x ∘ pivot) B

/-- The explicit row combination belongs to the row span, without any RREF
assumption. This supports the decomposition in paper `lem:canonical-complement`. -/
lemma rowEchelonComponent_mem_span (B : Matrix (Fin m) (Fin n) K)
    (pivot : Fin m ↪o Fin n) (x : Fin n → K) :
    rowEchelonComponent B pivot x ∈ Submodule.span K (Set.range B.row) := by
  rw [← range_vecMulLinear]
  exact ⟨x ∘ pivot, rfl⟩

/-- The explicit row component agrees with the input on every pivot coordinate,
as required in paper `lem:canonical-complement`. -/
lemma IsReducedRowEchelon.rowEchelonComponent_pivot
    {B : Matrix (Fin m) (Fin n) K} {pivot : Fin m ↪o Fin n}
    (hB : IsReducedRowEchelon B pivot) (x : Fin n → K) (i : Fin m) :
    rowEchelonComponent B pivot x (pivot i) = x (pivot i) := by
  simp [rowEchelonComponent, Matrix.vecMul_apply_eq_sum, hB.pivot_entry]

/-- Subtracting the explicit row component leaves a vector supported on the
nonpivot coordinates. This is the constructive step of paper
`lem:canonical-complement`, `references/qpbt-paper/04_preliminaries.tex:363-371`. -/
lemma IsReducedRowEchelon.sub_rowEchelonComponent_mem
    {B : Matrix (Fin m) (Fin n) K} {pivot : Fin m ↪o Fin n}
    (hB : IsReducedRowEchelon B pivot) (x : Fin n → K) :
    x - rowEchelonComponent B pivot x ∈
      registerSubmodule K (Finset.univ.image pivot)ᶜ := by
  rw [registerSubmodule_eq_spanSubset]
  apply Pi.mem_spanSubset_iff.mpr
  intro j hj
  have hj' : j ∈ Finset.univ.image pivot := by simpa using hj
  obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hj'
  simp [hB.rowEchelonComponent_pivot]

/-- An RREF row span is complementary to the span of its nonpivot standard
basis vectors. This auxiliary proves the decomposition and trivial intersection
directly from the entrywise conditions, following paper `lem:canonical-complement`.
The paper-facing theorem below derives these conditions from the input rows. -/
theorem IsReducedRowEchelon.isCompl_span_nonpivot
    {B : Matrix (Fin m) (Fin n) K} {pivot : Fin m ↪o Fin n}
    (hB : IsReducedRowEchelon B pivot) :
    IsCompl (Submodule.span K (Set.range B.row))
      (registerSubmodule K (Finset.univ.image pivot)ᶜ) := by
  classical
  constructor
  · apply Submodule.disjoint_def.mpr
    intro x hx hxC
    rw [registerSubmodule_eq_spanSubset] at hxC
    obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun K).mp hx
    have hc0 (i : Fin m) : c i = 0 := by
      have hx0 := Pi.mem_spanSubset_iff.mp hxC (pivot i) (by simp)
      have hi := congrFun hc (pivot i)
      simpa [Finset.sum_apply, Matrix.row, hB.pivot_entry, hx0] using hi
    rw [← hc]
    simp [hc0]
  · apply Submodule.codisjoint_iff_exists_add_eq.mpr
    intro x
    exact ⟨rowEchelonComponent B pivot x, x - rowEchelonComponent B pivot x,
      rowEchelonComponent_mem_span B pivot x, hB.sub_rowEchelonComponent_mem x,
      add_sub_cancel _ _⟩

/-- Paper `lem:canonical-complement`,
`references/qpbt-paper/04_preliminaries.tex:342-373`: the span of independent
input rows and the span of their canonical nonpivot standard basis vectors are
complementary. RREF existence and correspondence with `canonicalComplement` are
derived from row independence, not assumed. Arbitrary fields and zero ambient
dimension extend the paper's domain. -/
theorem isCompl_span_rows_canonicalComplement
    (A : Matrix (Fin m) (Fin n) K) (hA : LinearIndependent K A.row) :
    IsCompl (Submodule.span K (Set.range A.row))
      (registerSubmodule K (canonicalComplement (Submodule.span K (Set.range A.row)))) := by
  obtain ⟨B, pivot, _, _, _, hB, hspan, hC⟩ := exists_isReducedRowEchelon A hA
  rw [hC, ← hspan]
  exact hB.isCompl_span_nonpivot

/-- The canonical complement of `m` independent rows has `n - m` coordinate
indices, as asserted in paper `def:canonical-complement`. Distinct indices give
distinct standard basis vectors. -/
theorem card_canonicalComplement_span_rows
    (A : Matrix (Fin m) (Fin n) K) (hA : LinearIndependent K A.row) :
    (canonicalComplement (Submodule.span K (Set.range A.row))).card = n - m := by
  obtain ⟨_, pivot, _, _, _, _, _, hC⟩ := exists_isReducedRowEchelon A hA
  rw [hC, Finset.card_compl, Finset.card_image_of_injective _ pivot.injective]
  simp

/-- The standard basis vectors selected by the canonical complement are linearly
independent, as asserted in paper `def:canonical-complement`. This is the
restriction of Mathlib's standard basis independence theorem. -/
theorem linearIndependent_canonicalComplement (W : Submodule K (Fin n → K)) :
    LinearIndependent K
      (fun j : (canonicalComplement W) => (Pi.single j.val (1 : K) : Fin n → K)) := by
  exact (Pi.linearIndependent_single_one (Fin n) K).comp _ Subtype.val_injective

/-- For a register subspace, the canonical complement consists of the remaining
standard basis indices. This is the remark following paper
`def:canonical-complement`, `references/qpbt-paper/04_preliminaries.tex:333-340`. -/
theorem canonicalComplement_registerSubmodule (S : Finset (Fin n)) :
    canonicalComplement (registerSubmodule K S) = Sᶜ := by
  let pivot : Fin S.card ↪o Fin n := S.orderEmbOfFin rfl
  let B : Matrix (Fin S.card) (Fin n) K := fun i => Pi.single (pivot i) 1
  have hB : IsReducedRowEchelon B pivot := by
    constructor
    · intro i j
      simp [B, Pi.single_apply, pivot.injective.eq_iff, eq_comm]
    · intro i j hj
      exact Pi.single_eq_of_ne (ne_of_lt hj) _
  have hspan : Submodule.span K (Set.range B.row) = registerSubmodule K S := by
    unfold registerSubmodule
    congr 1
    ext v
    constructor
    · rintro ⟨i, rfl⟩
      exact ⟨pivot i, S.orderEmbOfFin_mem rfl i, rfl⟩
    · rintro ⟨j, hj, rfl⟩
      have hj' : j ∈ Set.range pivot := by
        rw [Finset.range_orderEmbOfFin]
        exact hj
      obtain ⟨i, rfl⟩ := hj'
      exact ⟨i, rfl⟩
  rw [← hspan, hB.canonicalComplement_eq_nonpivot_indices]
  rw [Finset.image_orderEmbOfFin_univ]

/-- For a register subspace, its canonical complement spans its dot-product
orthogonal. This is the second assertion of the remark following paper
`def:canonical-complement`, `references/qpbt-paper/04_preliminaries.tex:333-340`. -/
theorem registerSubmodule_canonicalComplement_eq_dotOrthogonal (S : Finset (Fin n)) :
    registerSubmodule K (canonicalComplement (registerSubmodule K S)) =
      dotOrthogonal (registerSubmodule K S) := by
  rw [canonicalComplement_registerSubmodule, registerSubmodule_eq_spanSubset]
  ext x
  rw [Pi.mem_spanSubset_iff]
  change (∀ j, j ∉ (Sᶜ : Finset (Fin n)) → x j = 0) ↔
    ∀ v, v ∈ registerSubmodule K S → dotProduct x v = 0
  constructor
  · intro hx v hv
    rw [registerSubmodule_eq_spanSubset] at hv
    apply Finset.sum_eq_zero
    intro j _
    by_cases hj : j ∈ S
    · rw [hx j (by simpa using hj), zero_mul]
    · have hvj := Pi.mem_spanSubset_iff.mp hv j hj
      rw [hvj, mul_zero]
  · intro hx j hj
    have hj' : j ∈ S := by simpa using hj
    have hv : Pi.single j (1 : K) ∈ registerSubmodule K S :=
      Submodule.subset_span ⟨j, hj', rfl⟩
    simpa using hx _ hv

end MIPStarRE.QPBT
