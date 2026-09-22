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

end GaussianElimination

end MIPStarRE.QPBT
