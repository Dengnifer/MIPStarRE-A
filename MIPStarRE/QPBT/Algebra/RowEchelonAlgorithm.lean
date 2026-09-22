import MIPStarRE.QPBT.Algebra.RowEchelon

/-!
# Executable Gauss-Jordan elimination

This module develops the algorithmic part of paper `def:canonical-complement`.
Matrices are materialized as vectors of vectors: evaluating an entry of an
intermediate matrix never repeats an earlier field operation. Columns are
processed from left to right, with the first available nonzero row as pivot.

The computational data are field operations and decidable equality. Arithmetic
operation counts use unit cost for field operations and equality tests, without
asserting bit complexity for an arbitrary field representation.

## References

* `references/qpbt-paper/04_preliminaries.tex:303-333`,
  Definition `def:canonical-complement` and its efficiency remark.
* Issue #690, continuing the algorithmic obligation of issue #676.
-/

namespace MIPStarRE.QPBT

namespace GaussianElimination

variable {K : Type*} {m n : ℕ}

/-- Array-backed storage for a finite matrix. This is computational storage for
Mathlib matrices, not a different algebraic notion of matrix. -/
abbrev StoredMatrix (K : Type*) (m n : ℕ) := Vector (Vector K n) m

/-- Read a stored matrix as a Mathlib matrix. -/
def toMatrix (A : StoredMatrix K m n) : Matrix (Fin m) (Fin n) K :=
  fun i j => A[i.val][j.val]

/-- Evaluate each entry once and store the resulting matrix. -/
def ofMatrix (A : Matrix (Fin m) (Fin n) K) : StoredMatrix K m n :=
  Vector.ofFn fun i => Vector.ofFn fun j => A i j

@[simp] lemma toMatrix_ofMatrix (A : Matrix (Fin m) (Fin n) K) :
    toMatrix (ofMatrix A) = A := by
  funext i j
  simp [toMatrix, ofMatrix]

variable [Field K]

/-- Swap the selected row into position `r`, normalize it, and clear its column
in every other row. Both the normalized row and the result are materialized. -/
def eliminateColumn (A : StoredMatrix K m n) (r s : Fin m) (c : Fin n) :
    StoredMatrix K m n :=
  let B := fun i j => toMatrix A (Equiv.swap r s i) j
  let v := Vector.ofFn fun j => B r j / B r c
  Vector.ofFn fun i =>
    if i = r then v else Vector.ofFn fun j => B i j - B i c * v[j.val]

/-- Entrywise formula for the materialized pivot step. -/
lemma eliminateColumn_apply (A : StoredMatrix K m n) (r s i : Fin m) (c j : Fin n) :
    toMatrix (eliminateColumn A r s c) i j =
      if i = r then toMatrix A s j / toMatrix A s c
      else toMatrix A (Equiv.swap r s i) j -
        toMatrix A (Equiv.swap r s i) c * (toMatrix A s j / toMatrix A s c) := by
  by_cases hi : i = r <;> simp [eliminateColumn, toMatrix, hi]

/-- A pivot step with a nonzero pivot preserves the entire row span. The inverse
row expressions recover the swapped input rows from the normalized pivot row. -/
theorem eliminateColumn_span (A : StoredMatrix K m n) (r s : Fin m) (c : Fin n)
    (hc : toMatrix A s c ≠ 0) :
    Submodule.span K (Set.range (toMatrix (eliminateColumn A r s c)).row) =
      Submodule.span K (Set.range (toMatrix A).row) := by
  let B := toMatrix (eliminateColumn A r s c)
  have hp : B.row r = (toMatrix A s c)⁻¹ • (toMatrix A).row s := by
    ext j
    simp [B, Matrix.row, eliminateColumn_apply, div_eq_mul_inv, mul_comm]
  have hi (i : Fin m) (hir : i ≠ r) :
      B.row i = (toMatrix A).row (Equiv.swap r s i) -
        toMatrix A (Equiv.swap r s i) c • B.row r := by
    ext j
    simp [B, Matrix.row, eliminateColumn_apply, hir]
  have hrow (i : Fin m) : (toMatrix A).row i ∈
      Submodule.span K (Set.range (toMatrix A).row) := Submodule.subset_span ⟨i, rfl⟩
  have hnew (i : Fin m) : B.row i ∈ Submodule.span K (Set.range B.row) :=
    Submodule.subset_span ⟨i, rfl⟩
  have hpr : B.row r ∈ Submodule.span K (Set.range (toMatrix A).row) := by
    rw [hp]
    exact Submodule.smul_mem _ _ (hrow s)
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro _ ⟨i, rfl⟩
    by_cases hir : i = r
    · subst i
      exact hpr
    · rw [hi i hir]
      exact Submodule.sub_mem _ (hrow _) (Submodule.smul_mem _ _ hpr)
  · apply Submodule.span_le.mpr
    rintro _ ⟨i, rfl⟩
    have hs : (toMatrix A).row s = toMatrix A s c • B.row r := by
      rw [hp, smul_smul, mul_inv_cancel₀ hc, one_smul]
    by_cases his : i = s
    · subst i
      rw [hs]
      exact Submodule.smul_mem _ _ (hnew r)
    · have hswap : Equiv.swap r s i ≠ r := by
        intro h
        apply his
        simpa using congrArg (Equiv.swap r s) h
      have hback : (toMatrix A).row i =
          B.row (Equiv.swap r s i) + toMatrix A i c • B.row r := by
        rw [hi _ hswap, Equiv.swap_apply_self]
        exact (sub_add_cancel _ _).symm
      rw [hback]
      exact Submodule.add_mem _ (hnew _) (Submodule.smul_mem _ _ (hnew r))

end GaussianElimination

end MIPStarRE.QPBT
