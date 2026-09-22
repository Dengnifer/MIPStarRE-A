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

`gaussianElimination_correct` proves RREF and row-span correctness for arbitrary
input rows. `gaussianElimination_of_linearIndependent` gives the source's
independent-row case. `gaussianElimination_cost_le_poly` bounds the actual
program's charged arithmetic and zero tests by `n * (m + n + 2*m*n)`.

## References

* `references/qpbt-paper/04_preliminaries.tex:303-333`,
  Definition `def:canonical-complement` and its efficiency remark.
* Issue #690, continuing the algorithmic obligation of issue #676.
-/

open scoped BigOperators

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

/-- Tabulate counted computations, evaluating each computation once. Reading the
stored results and summing their natural-number costs perform no field operations. -/
def tabulateCounted {α : Type*} {k : ℕ} (f : Fin k → α × ℕ) : Vector α k × ℕ :=
  let samples := Vector.ofFn f
  (samples.map Prod.fst, ∑ i : Fin k, samples[i.val].2)

/-- Counted pivot elimination. A division costs one field operation; each
nonpivot entry uses one multiplication and one subtraction. The normalized
pivot row is stored before it is used by the other rows. -/
def eliminateColumnCounted (A : StoredMatrix K m n) (r s : Fin m) (c : Fin n) :
    StoredMatrix K m n × ℕ :=
  let B := fun i j => toMatrix A (Equiv.swap r s i) j
  let v := tabulateCounted fun j => (B r j / B r c, 1)
  let result := tabulateCounted fun i =>
    if i = r then (v.1, 0)
    else tabulateCounted fun j => (B i j - B i c * v.1[j.val], 2)
  (result.1, v.2 + result.2)

/-- Swap the selected row into position `r`, normalize it, and clear its column
in every other row. Both the normalized row and the result are materialized. -/
def eliminateColumn (A : StoredMatrix K m n) (r s : Fin m) (c : Fin n) :
    StoredMatrix K m n :=
  (eliminateColumnCounted A r s c).1

/-- Entrywise formula for the materialized pivot step. -/
lemma eliminateColumn_apply (A : StoredMatrix K m n) (r s i : Fin m) (c j : Fin n) :
    toMatrix (eliminateColumn A r s c) i j =
      if i = r then toMatrix A s j / toMatrix A s c
      else toMatrix A (Equiv.swap r s i) j -
        toMatrix A (Equiv.swap r s i) c * (toMatrix A s j / toMatrix A s c) := by
  by_cases hi : i = r <;>
    simp [eliminateColumn, eliminateColumnCounted, tabulateCounted, toMatrix, hi]

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

/-- The arithmetic count of the actual materialized pivot step is bounded by
`n + 2*m*n`. The estimate permits charging the pivot row as an additional
eliminated row; no search or matrix evaluation is hidden in a field operation. -/
theorem eliminateColumnCounted_cost (A : StoredMatrix K m n)
    (r s : Fin m) (c : Fin n) :
    (eliminateColumnCounted A r s c).2 ≤ n + m * (2 * n) := by
  simp only [eliminateColumnCounted, tabulateCounted, Vector.getElem_ofFn]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul, mul_one]
  apply Nat.add_le_add_left
  calc
    (∑ i : Fin m, (if i = r then (_, 0) else (_, n * 2)).2) ≤
        ∑ _i : Fin m, 2 * n := by
      apply Finset.sum_le_sum
      intro i _
      split_ifs <;> simp [Nat.mul_comm]
    _ = m * (2 * n) := by simp

/-- The selected column becomes a unit column. Any column in which both swapped
rows were zero remains unchanged, preserving previously completed pivot columns. -/
theorem eliminateColumn_entries (A : StoredMatrix K m n) (r s : Fin m) (c : Fin n)
    (hc : toMatrix A s c ≠ 0) :
    (∀ i, toMatrix (eliminateColumn A r s c) i c = if i = r then 1 else 0) ∧
      ∀ j, toMatrix A r j = 0 → toMatrix A s j = 0 →
        ∀ i, toMatrix (eliminateColumn A r s c) i j = toMatrix A i j := by
  constructor
  · intro i
    rw [eliminateColumn_apply, div_self hc]
    split_ifs <;> simp
  · intro j hr hs i
    rw [eliminateColumn_apply, hs, zero_div]
    by_cases hir : i = r
    · subst i
      simp [hr]
    · by_cases his : i = s
      · subst i
        simp [hir, hr, hs]
      · simp [hir, Equiv.swap_apply_of_ne_of_ne hir his]

variable [DecidableEq K]

/-- Scan a supplied row list in order. Each inspected row is charged one zero
test, including a conservative charge when its index is below `r` and the field
test is skipped. The caller uses `List.finRange m`, so this is a bounded search. -/
def findPivot (A : StoredMatrix K m n) (r : ℕ) (c : Fin n) :
    List (Fin m) → Option (Fin m) × ℕ
  | [] => (none, 0)
  | i :: is =>
    if r ≤ i.val ∧ toMatrix A i c ≠ 0 then (some i, 1)
    else
      let rest := findPivot A r c is
      (rest.1, rest.2 + 1)

/-- The search returns the first eligible row, and charges at most the list
length. Its specification reuses Lean's list search rather than an existence
oracle or enumeration of candidate reduced matrices. -/
theorem findPivot_spec (A : StoredMatrix K m n) (r : ℕ) (c : Fin n)
    (is : List (Fin m)) :
    (findPivot A r c is).1 =
        is.find? (fun i => decide (r ≤ i.val ∧ toMatrix A i c ≠ 0)) ∧
      (findPivot A r c is).2 ≤ is.length := by
  induction is with
  | nil => simp [findPivot]
  | cons i is ih =>
    by_cases hi : r ≤ i.val ∧ toMatrix A i c ≠ 0
    · simp [findPivot, hi]
    · simpa [findPivot, hi] using ih

/-- Computational elimination state. Only the first `rank` pivot entries are
used; the other entries are storage that has not yet been assigned a pivot. -/
structure State (K : Type*) (m n : ℕ) where
  entries : StoredMatrix K m n
  rank : ℕ
  pivots : Vector ℕ m
  operations : ℕ

/-- Initial state, before any column has been inspected. -/
def initialState (A : StoredMatrix K m n) : State K m n :=
  ⟨A, 0, Vector.replicate m 0, 0⟩

/-- Process one column, selecting the first available nonzero row. A column
without a pivot leaves the matrix unchanged and still charges for its search. -/
def step (S : State K m n) (c : Fin n) : State K m n :=
  if hr : S.rank < m then
    let search := findPivot S.entries S.rank c (List.finRange m)
    match search.1 with
    | none => { S with operations := S.operations + search.2 }
    | some s =>
      let result := eliminateColumnCounted S.entries ⟨S.rank, hr⟩ s c
      ⟨result.1, S.rank + 1, S.pivots.set S.rank c.val hr,
        S.operations + search.2 + result.2⟩
  else S

/-- Run the first `k` column iterations. Calls at `k > n` remain at the final
state; the public algorithm calls this function at exactly `k = n`. -/
def runColumns (A : StoredMatrix K m n) : ℕ → State K m n
  | 0 => initialState A
  | k + 1 =>
    let S := runColumns A k
    if hk : k < n then step S ⟨k, hk⟩ else S

/-- Partial RREF invariant after `k` columns. Completed pivots are ordered and
reduced; unprocessed rows vanish in the inspected columns. This is a loop
invariant for the executable program, not an assumption on the input matrix. -/
structure Invariant (A : StoredMatrix K m n) (k : ℕ) (S : State K m n) : Prop where
  rank_le : S.rank ≤ m
  pivot_lt : ∀ i : Fin m, i.val < S.rank → S.pivots[i.val] < k
  pivot_strict : ∀ i j : Fin m, i < j → j.val < S.rank →
    S.pivots[i.val] < S.pivots[j.val]
  pivot_entry : ∀ t : Fin m, t.val < S.rank → ∀ c : Fin n,
    S.pivots[t.val] = c.val → ∀ i,
      toMatrix S.entries i c = if i = t then 1 else 0
  zero_before : ∀ i : Fin m, i.val < S.rank → ∀ c : Fin n,
    c.val < S.pivots[i.val] → toMatrix S.entries i c = 0
  remaining_zero : ∀ i : Fin m, S.rank ≤ i.val → ∀ c : Fin n,
    c.val < k → toMatrix S.entries i c = 0
  span_eq : Submodule.span K (Set.range (toMatrix S.entries).row) =
    Submodule.span K (Set.range (toMatrix A).row)
  cost_le : S.operations ≤ k * (m + n + m * (2 * n))

omit [DecidableEq K] in
/-- The initial state satisfies the invariant for every matrix, including empty
row and column index types. No independence or rank certificate is required. -/
theorem initialState_invariant (A : StoredMatrix K m n) :
    Invariant A 0 (initialState A) := by
  refine ⟨Nat.zero_le _, ?_, ?_, ?_, ?_, ?_, rfl, by simp [initialState]⟩
  · intro i hi
    exact (Nat.not_lt_zero _ hi).elim
  · intro i j hij hj
    exact (Nat.not_lt_zero _ hj).elim
  · intro t ht
    exact (Nat.not_lt_zero _ ht).elim
  · intro i hi
    exact (Nat.not_lt_zero _ hi).elim
  · intro i hi c hc
    exact (Nat.not_lt_zero _ hc).elim

/-- One column iteration preserves the partial RREF conditions and row span,
and adds at most `m + n + 2*m*n` charged field operations and zero tests. -/
theorem Invariant.step {A : StoredMatrix K m n} {S : State K m n} (c : Fin n)
    (h : Invariant A c.val S) : Invariant A (c.val + 1) (step S c) := by
  by_cases hr : S.rank < m
  · have hsearch := findPivot_spec S.entries S.rank c (List.finRange m)
    have hsearch_cost : (findPivot S.entries S.rank c (List.finRange m)).2 ≤ m := by
      simpa using hsearch.2
    cases hf : (findPivot S.entries S.rank c (List.finRange m)).1 with
    | none =>
      have hz (i : Fin m) (hi : S.rank ≤ i.val) : toMatrix S.entries i c = 0 := by
        have hh := List.find?_eq_none.mp (hsearch.1.symm.trans hf) i (List.mem_finRange i)
        simpa [hi] using hh
      simp only [GaussianElimination.step, dif_pos hr, hf]
      refine ⟨h.rank_le, ?_, h.pivot_strict, h.pivot_entry, h.zero_before, ?_,
        h.span_eq, ?_⟩
      · intro i hi
        exact Nat.lt_succ_of_lt (h.pivot_lt i hi)
      · intro i hi j hj
        by_cases hjc : j.val < c.val
        · exact h.remaining_zero i hi j hjc
        · have heq : j = c := Fin.ext (by omega)
          subst j
          exact hz i hi
      · have hc := h.cost_le
        dsimp only
        rw [Nat.add_mul, Nat.one_mul]
        omega
    | some s =>
      have hs : S.rank ≤ s.val ∧ toMatrix S.entries s c ≠ 0 := by
        simpa using List.find?_some (hsearch.1.symm.trans hf)
      let r : Fin m := ⟨S.rank, hr⟩
      have hcol := eliminateColumn_entries S.entries r s c hs.2
      have hpres (j : Fin n) (hj : j.val < c.val) (i : Fin m) :
          toMatrix (eliminateColumn S.entries r s c) i j = toMatrix S.entries i j :=
        hcol.2 j (h.remaining_zero r (Nat.le_refl _) j hj)
          (h.remaining_zero s hs.1 j hj) i
      have hcost := eliminateColumnCounted_cost S.entries r s c
      simp only [GaussianElimination.step, dif_pos hr, hf]
      change Invariant A (c.val + 1)
        ⟨eliminateColumn S.entries r s c, S.rank + 1,
          S.pivots.set S.rank c.val hr,
          S.operations + (findPivot S.entries S.rank c (List.finRange m)).2 +
            (eliminateColumnCounted S.entries r s c).2⟩
      refine ⟨by dsimp only; omega, ?_, ?_, ?_, ?_, ?_,
        (eliminateColumn_span S.entries r s c hs.2).trans h.span_eq, ?_⟩
      · intro i hi
        dsimp only at hi ⊢
        rw [Vector.getElem_set]
        split_ifs with hir
        · omega
        · exact Nat.lt_succ_of_lt (h.pivot_lt i (by omega))
      · intro i j hij hj
        dsimp only at hj ⊢
        have hij' : i.val < j.val := hij
        have hir : S.rank ≠ i.val := by omega
        simp only [Vector.getElem_set, if_neg hir]
        split_ifs with hjr
        · exact h.pivot_lt i (by omega)
        · exact h.pivot_strict i j hij (by omega)
      · intro t ht j hj i
        dsimp only at ht hj ⊢
        by_cases htr : S.rank = t.val
        · have hteq : t = r := Fin.ext htr.symm
          have hjeq : j = c := by
            apply Fin.ext
            simpa [Vector.getElem_set, htr] using hj.symm
          subst t
          subst j
          exact hcol.1 i
        · have ht' : t.val < S.rank := by omega
          have hj' : S.pivots[t.val] = j.val := by
            simpa [Vector.getElem_set, htr] using hj
          rw [hpres j (by rw [← hj']; exact h.pivot_lt t ht') i]
          exact h.pivot_entry t ht' j hj' i
      · intro i hi j hj
        dsimp only at hi hj ⊢
        by_cases hir : S.rank = i.val
        · have hieq : i = r := Fin.ext hir.symm
          have hjc : j.val < c.val := by
            simpa [Vector.getElem_set, hir] using hj
          subst i
          rw [eliminateColumn_apply, if_pos rfl, h.remaining_zero s hs.1 j hjc,
            zero_div]
        · have hi' : i.val < S.rank := by omega
          have hj' : j.val < S.pivots[i.val] := by
            simpa [Vector.getElem_set, hir] using hj
          rw [hpres j (lt_trans hj' (h.pivot_lt i hi')) i]
          exact h.zero_before i hi' j hj'
      · intro i hi j hj
        dsimp only at hi hj ⊢
        by_cases hjc : j.val < c.val
        · rw [hpres j hjc i]
          exact h.remaining_zero i (by omega) j hjc
        · have hjeq : j = c := Fin.ext (by omega)
          subst j
          rw [hcol.1, if_neg]
          intro hir
          have := congrArg Fin.val hir
          dsimp [r] at this
          omega
      · dsimp only
        have hc := h.cost_le
        rw [Nat.add_mul, Nat.one_mul]
        omega
  · simp only [GaussianElimination.step, dif_neg hr]
    refine ⟨h.rank_le, ?_, h.pivot_strict, h.pivot_entry, h.zero_before, ?_,
      h.span_eq, ?_⟩
    · intro i hi
      exact Nat.lt_succ_of_lt (h.pivot_lt i hi)
    · intro i hi j hj
      have := i.isLt
      omega
    · have hc := h.cost_le
      rw [Nat.add_mul, Nat.one_mul]
      omega

/-- Induction over the bounded column loop derives the invariant from the input
matrix alone. In particular, correctness certificates are not program inputs. -/
theorem runColumns_invariant (A : StoredMatrix K m n) (k : ℕ) (hk : k ≤ n) :
    Invariant A k (runColumns A k) := by
  induction k with
  | zero => exact initialState_invariant A
  | succ k ih =>
    have hkn : k < n := by omega
    rw [runColumns, dif_pos hkn]
    exact (ih (by omega)).step ⟨k, hkn⟩

/-- The computed nonpivot indices. Only assigned pivot entries are inspected;
the finite scan uses integer comparisons and no field operations. -/
def State.nonpivotIndices (S : State K m n) : Finset (Fin n) :=
  Finset.univ.filter fun j => ∀ i : Fin m, i.val < S.rank → S.pivots[i.val] ≠ j.val

end GaussianElimination

open GaussianElimination

variable {K : Type*} [Field K] [DecidableEq K] {m n : ℕ}

/-- Deterministic, materialized Gauss-Jordan elimination. The input is stored
matrix data, with field operations and decidable equality supplied by the caller.
Exactly `n` bounded column iterations are executed. This constructs the reduced
matrix and nonpivot indices used in paper `def:canonical-complement`. -/
def gaussianElimination (A : StoredMatrix K m n) : State K m n :=
  runColumns A n

/-- The computed nonzero rows. The bound used to index storage is proved by the
loop invariant, rather than supplied by the caller. No field arithmetic occurs
when this view of the stored output is read. -/
def gaussianEliminationRows (A : StoredMatrix K m n) :
    Matrix (Fin (gaussianElimination A).rank) (Fin n) K :=
  let S := gaussianElimination A
  let h := runColumns_invariant A n (Nat.le_refl n)
  fun i => toMatrix S.entries ⟨i.val, lt_of_lt_of_le i.isLt h.rank_le⟩

/-- Increasing pivot embedding read from the computed pivot array. The bound and
ordering proofs are consequences of the loop invariant and are erased at run time. -/
def gaussianEliminationPivots (A : StoredMatrix K m n) :
    Fin (gaussianElimination A).rank ↪o Fin n :=
  let S := gaussianElimination A
  let h := runColumns_invariant A n (Nat.le_refl n)
  OrderEmbedding.ofStrictMono
    (fun i => ⟨S.pivots[i.val]'(lt_of_lt_of_le i.isLt h.rank_le),
      h.pivot_lt ⟨i.val, lt_of_lt_of_le i.isLt h.rank_le⟩ i.isLt⟩)
    (by
      intro i j hij
      exact h.pivot_strict ⟨i.val, lt_of_lt_of_le i.isLt h.rank_le⟩
        ⟨j.val, lt_of_lt_of_le j.isLt h.rank_le⟩ hij j.isLt)

/-- Correctness of the executable elimination program for arbitrary input rows.
Its nonzero rows satisfy conventional RREF, span exactly the input row space,
and its computed nonpivot indices are the existing canonical complement. The
other stored rows are zero. This supplies the construction in paper
`def:canonical-complement`; the independent-row specialization follows below. -/
theorem gaussianElimination_correct (A : StoredMatrix K m n) :
    IsReducedRowEchelon (gaussianEliminationRows A) (gaussianEliminationPivots A) ∧
      Submodule.span K (Set.range (gaussianEliminationRows A).row) =
        Submodule.span K (Set.range (toMatrix A).row) ∧
      (∀ i : Fin m, (gaussianElimination A).rank ≤ i.val →
        (toMatrix (gaussianElimination A).entries).row i = 0) ∧
      canonicalComplement (Submodule.span K (Set.range (toMatrix A).row)) =
        (gaussianElimination A).nonpivotIndices := by
  let S := gaussianElimination A
  have h : Invariant A n S := runColumns_invariant A n (Nat.le_refl n)
  have hB : IsReducedRowEchelon (gaussianEliminationRows A)
      (gaussianEliminationPivots A) := by
    constructor
    · intro i j
      have he := h.pivot_entry ⟨j.val, lt_of_lt_of_le j.isLt h.rank_le⟩ j.isLt
        (gaussianEliminationPivots A j) rfl ⟨i.val, lt_of_lt_of_le i.isLt h.rank_le⟩
      simpa only [gaussianEliminationRows, Fin.ext_iff] using he
    · intro i j hj
      exact h.zero_before ⟨i.val, lt_of_lt_of_le i.isLt h.rank_le⟩ i.isLt j hj
  have hz (i : Fin m) (hi : S.rank ≤ i.val) : (toMatrix S.entries).row i = 0 := by
    funext j
    exact h.remaining_zero i hi j j.isLt
  have hspan : Submodule.span K (Set.range (gaussianEliminationRows A).row) =
      Submodule.span K (Set.range (toMatrix A).row) := by
    rw [← h.span_eq]
    apply le_antisymm
    · apply Submodule.span_le.mpr
      rintro _ ⟨i, rfl⟩
      exact Submodule.subset_span ⟨⟨i.val, lt_of_lt_of_le i.isLt h.rank_le⟩, rfl⟩
    · apply Submodule.span_le.mpr
      rintro _ ⟨i, rfl⟩
      by_cases hi : i.val < S.rank
      · exact Submodule.subset_span ⟨⟨i.val, hi⟩, rfl⟩
      · rw [hz i (Nat.le_of_not_lt hi)]
        exact Submodule.zero_mem _
  refine ⟨hB, hspan, hz, ?_⟩
  rw [← hspan, hB.canonicalComplement_eq_nonpivot_indices]
  ext j
  simp only [State.nonpivotIndices, Finset.mem_compl, Finset.mem_image,
    Finset.mem_univ, true_and, Finset.mem_filter]
  constructor
  · intro hj i hi heq
    apply hj
    refine ⟨⟨i.val, hi⟩, ?_⟩
    exact Fin.ext heq
  · rintro hj ⟨i, hi⟩
    exact hj ⟨i.val, lt_of_lt_of_le i.isLt h.rank_le⟩ i.isLt (congrArg Fin.val hi)

/-- For the independent rows of paper `def:canonical-complement`, all `m` output
rows are pivot rows. The full stored output is RREF with the input row span,
and its computed nonpivot indices are precisely the source complement. The only
effectivity data beyond the paper's field are executable operations and equality. -/
theorem gaussianElimination_of_linearIndependent (A : StoredMatrix K m n)
    (hA : LinearIndependent K (toMatrix A).row) :
    (gaussianElimination A).rank = m ∧
      ∃ pivot : Fin m ↪o Fin n,
        IsReducedRowEchelon (toMatrix (gaussianElimination A).entries) pivot ∧
          Submodule.span K (Set.range (toMatrix (gaussianElimination A).entries).row) =
            Submodule.span K (Set.range (toMatrix A).row) ∧
          canonicalComplement (Submodule.span K (Set.range (toMatrix A).row)) =
            (gaussianElimination A).nonpivotIndices := by
  have hc := gaussianElimination_correct A
  have h := runColumns_invariant A n (Nat.le_refl n)
  have hin := finrank_span_eq_card hA
  have hout := finrank_span_eq_card hc.1.linearIndependent_rows
  rw [hc.2.1] at hout
  simp only [Fintype.card_fin] at hin hout
  have hrank : (gaussianElimination A).rank = m := hout.symm.trans hin
  let e := (Fin.castOrderIso hrank.symm).toOrderEmbedding
  refine ⟨hrank, e.trans (gaussianEliminationPivots A), ?_, h.span_eq, hc.2.2.2⟩
  constructor
  · intro i j
    have he := hc.1.pivot_entry (e i) (e j)
    simpa [gaussianEliminationRows, e, Fin.ext_iff] using he
  · intro i j hj
    exact hc.1.zero_before (e i) j hj

/-- Polynomial arithmetic-operation bound for the executable program, including
its pivot searches. Each of the `n` columns charges at most `m` zero tests, `n`
divisions, and `2*m*n` multiplications/subtractions. Short-circuited zero tests
may be overcharged. Counts come from the same materialized computations as the
matrix output, not from a separate nominal loop counter.

Array access and storage use no field operations. Tabulation, cost summation,
row scanning, and pivot-array updates make bounded passes of sizes at most
`m`, `n`, and `m*n` per column. The result is an arithmetic bound under unit-cost
field operations/equality, not a bit-complexity claim about a field encoding. -/
theorem gaussianElimination_cost_le_poly (A : StoredMatrix K m n) :
    (gaussianElimination A).operations ≤ n * (m + n + m * (2 * n)) :=
  (runColumns_invariant A n (Nat.le_refl n)).cost_le

end MIPStarRE.QPBT
