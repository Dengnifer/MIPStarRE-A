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

end MIPStarRE.QPBT
