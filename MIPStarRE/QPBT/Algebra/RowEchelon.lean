import MIPStarRE.QPBT.Algebra.Subspaces

/-!
# Reduced row echelon form and the canonical complement

For matrices with independent rows, reduced row echelon form consists of ordered
pivot columns, an identity matrix in those columns, and zeros before each pivot.
This module compares its nonpivot indices with the intrinsic prefix-rank
definition of `canonicalComplement`.

Independent input rows have such a matrix with the same row span and an
invertible change of row basis. The pivot index set depends only on that span.

The arbitrary-field and zero-dimensional cases are extensions of the paper's
ambient convention of a finite field and positive ambient dimension. The results
concern abstract existence and equality, not an executable elimination algorithm
or its complexity.

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

end MIPStarRE.QPBT
