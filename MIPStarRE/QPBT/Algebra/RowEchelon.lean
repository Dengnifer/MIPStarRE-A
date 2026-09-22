import MIPStarRE.QPBT.Algebra.Subspaces

/-!
# Reduced row echelon form and the canonical complement

For matrices with independent rows, reduced row echelon form consists of ordered
pivot columns, an identity matrix in those columns, and zeros before each pivot.
This module compares its nonpivot indices with the intrinsic prefix-rank
definition of `canonicalComplement`.

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

end MIPStarRE.QPBT
