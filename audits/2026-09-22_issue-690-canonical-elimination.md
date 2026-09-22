---
title: "Issue 690 executable canonical elimination"
date: 2026-09-22
purpose: >
  Records the deterministic elimination program, its RREF and row-span proofs,
  the canonical nonpivot correspondence, and its arithmetic-operation model.
issue: "#690, continuing #676"
---

# Executable canonical elimination

## Result and Source

`MIPStarRE/QPBT/Algebra/RowEchelonAlgorithm.lean` supplies the remaining
algorithmic construction for Definition `def:canonical-complement` in
`references/qpbt-paper/04_preliminaries.tex:303-333`. The source transforms
independent coordinate rows to reduced row echelon form by a canonical
Gaussian-elimination algorithm and selects the standard vectors in nonpivot
columns. Its following remark asserts efficient computation, without specifying
an exponent or a bit representation for field elements.

The new program chooses columns from left to right and chooses the first
available nonzero row in each column. Its output satisfies the predecessor's
`IsReducedRowEchelon` predicate and has exactly the original row span.
Its computed nonpivot indices equal the existing `canonicalComplement`.
Its charged field arithmetic and zero tests are bounded by

```text
n * (m + n + 2*m*n).
```

All these results are proved from input data. No RREF certificate, invariant,
row-span identity, complement equality, or complexity bound is a caller
hypothesis. No proof hole remains in the new module. The result is ready for
independent review; this audit does not change blueprint completion marks,
paper-gap statuses, or the project's completion disposition.

## Program and Mathematical Proof

`StoredMatrix K m n` is an array-backed `Vector (Vector K n) m`.
`toMatrix` reads it as a Mathlib matrix. `ofMatrix` materializes a Mathlib
matrix, and `toMatrix_ofMatrix` proves that all its entries are preserved.
The storage type therefore does not change the underlying linear algebra.

For a selected column `c`, `findPivot` scans the finite list of row indices
in increasing order. An eligible row has index at least the number of
completed pivots and has a nonzero entry in column `c`. `findPivot_spec`
identifies the result with Lean's `List.find?` and bounds the number of
charged tests by the list length. There is no unbounded search or enumeration
of candidate matrices.

Let `r` be the next pivot position and `s` the selected row. Write `B` for
the input with rows `r` and `s` interchanged. The pivot step stores the row
`v[j] = B[r,j] / B[r,c]`, then stores `v` in row `r` and
`B[i,j] - B[i,c] * v[j]` in every other row. The normalized row is evaluated
before it is used to compute the other rows. Later entry access consequently
does not repeat its field operations.

`eliminateColumn_span` proves both span inclusions. Each output row is a
linear combination of input rows. Conversely, multiply the normalized pivot
row by the original nonzero pivot to recover the selected input row, and add
the removed multiple back to each other row. `eliminateColumn_entries`
proves that column `c` becomes a unit column and that a column zero in both
swapped rows stays unchanged.

The loop invariant records ordered pivot columns with identity entries,
zeros before each completed pivot, zeros in inspected columns of unprocessed
rows, equality of row spans, and the accumulated cost bound. The initial
state satisfies it for every input matrix. `Invariant.step` proves its
preservation in the pivot, unsuccessful-search, and exhausted-row cases;
`runColumns_invariant` then proves it after all columns have been processed.
This invariant is proved internally, not attached to the source hypotheses.

`gaussianElimination_correct` proves that the computed nonzero rows are in
conventional RREF and span the input row space, while all remaining stored
rows vanish. It applies the predecessor's
`IsReducedRowEchelon.canonicalComplement_eq_nonpivot_indices` to identify the
computed nonpivot set. `gaussianElimination_of_linearIndependent` additionally
proves that the computed rank is `m` and that the full stored matrix is RREF.
The rank equality follows because an independent finite family has dimension
equal to its cardinality, applied to both row families with their proved
common span. This uses Mathlib's `finrank_span_eq_card`.

The pivot embedding and reduced-row view read the computed arrays. Their
index bounds and ordering proofs come from the loop invariant and are erased
at execution. They do not select an abstract RREF witness. The predecessor's
abstract RREF existence theorem is not used in the new construction.

## Cost Model

The input is materialized field data, with executable field operations and
`DecidableEq K`. A field division, multiplication, subtraction, and equality
test each have unit arithmetic cost. No claim about bit complexity or the
internal implementation of a supplied field operation is made.

`tabulateCounted` evaluates each computation once into an array of value/count
pairs. It reads these stored values to construct the result and sums the
stored natural-number counts. The normalized row uses `n` divisions. Each
other row uses `n` multiplications and `n` subtractions. The proved bound for
one actual pivot computation is `n + m*(2*n)`; this conservatively allows
charging the pivot row as another eliminated row.

Every inspected search row is charged one zero test. If an index comparison
already rejects that row, the omitted field test is still charged. Thus the
counter is an upper bound on field operations and tests, not a claim that
every charged test was executed. At most `m` rows are inspected per column.
The same column program accumulates these search charges and the counts from
the materialized pivot computations. The invariant bounds this actual counter
after `k` columns by `k*(m+n+m*(2*n))`.
`gaussianElimination_cost_le_poly` specializes the bound at `k = n`.

The representation also accounts for access and materialization. Array reads
perform no field arithmetic. Per column, list construction and search make
bounded passes of size `m`; normalized-row tabulation and count summation have
size `n`; result tabulation and count summation have size at most `m*n`.
Updating the pivot array requires at most a copy of `m` indices. There are
exactly `n` column iterations, including the constant-work exhausted-row cases.
Extracting the nonpivot set compares at most `m*n` stored natural numbers.
These finite passes give polynomial administrative work in the usual
unit-cost array model. The formal numeric theorem counts field operations and
zero tests; it is not a machine-instruction or memory-allocation theorem.

`ofMatrix` evaluates each of the `m*n` supplied entries once. The elimination
bound starts with stored input; it does not purport to bound arbitrary
computation hidden in a user-supplied function producing matrix entries.

## Statement Integrity

| Aspect | Paper | Lean | Verdict |
| --- | --- | --- | --- |
| Field | Finite field by the convention at lines 219-222; elimination over arbitrary fields | `Field K` and `DecidableEq K`, with operations supplied as executable data | Faithful effectivity data; arbitrary-field extension |
| Dimensions | Positive ambient dimension, finite row family | Natural `m`, `n`, including zero | Exact on the source domain; degenerate extension |
| Source input | `m` independent vectors, as coordinate rows | `LinearIndependent K (toMatrix A).row` for stored rows | Exact indexed representation |
| Algorithm | Canonical Gaussian elimination | Left-to-right columns, first eligible row, materialized Gauss-Jordan updates | Concrete deterministic realization |
| Reduced output | RREF with unchanged row span | The existing entrywise `IsReducedRowEchelon` and row-span equality | Exact |
| Complement | Standard basis vectors outside the pivot columns | Computed indices equal `canonicalComplement`; the predecessor supplies the corresponding standard vectors | Exact indexed representation |
| Efficiency | Efficient computation, unspecified exponent | At most `n*(m+n+2*m*n)` charged field operations/tests | Polynomial arithmetic interpretation, not a bit-complexity claim |

The verdict for the source's independent-row statement is **faithful boundary
hypotheses**. There is no added mathematical premise or weakened conclusion.
The general correctness theorem also handles dependent rows by retaining the
nonzero rows and proving that the trailing stored rows vanish. The predecessor's
cardinality, independence, register-subspace, and complementarity theorems remain
available through the proved equality of complement indices.

## Validation and Handoff

The baseline `RowEchelon.lean` and the complete new module pass focused
`lake env lean` checks without warnings. Import products were emitted only
under this worktree's private `.lake/build/lib/lean/`. The new module contains
no proof holes, nonstandard proof primitives, placeholder tactics, or debugging
commands. Whitespace and the 100-character Lean line limit are clean.

The focused runtime and axiom harness is
`~/.cache/mipstarre-dev/sessions/prover-690-20260922-01-checks.lean`, with output
in the adjacent `prover-690-20260922-01-checks.log`. It checks:

- Over `ZMod 2`, a row swap followed by elimination above a later pivot:
  `[[0,1,1],[1,1,0]]` becomes `[[1,0,1],[0,1,1]]`, with 22 charged operations.
- Over `ZMod 3`, dependent rows and nontrivial division:
  `[[0,2,1],[0,1,2]]` becomes `[[0,1,2],[0,0,0]]`, with 14 charges.
- Over `ZMod 5`, an initial zero row and a later-column pivot:
  `[[0,0,0],[0,2,4]]` becomes `[[0,1,2],[0,0,0]]`, with 15 charges.
- Over the rationals, `[[2,4],[1,3]]` becomes the identity matrix.
- The computed pivot embedding and reduced-row view read the expected data.
- Empty rows, empty columns, the empty matrix, and a nonempty all-zero matrix
  have the expected ranks, complements, unchanged entries, and operation counts.
- Transitive axiom closure contains only `propext`, `Classical.choice`, and
  `Quot.sound` across all 28 authored declarations, including the two structures.

The nondegenerate examples use executable assertions; the boundary examples
also reduce by kernel `decide`. General correctness is proved in the module,
independently of these computations. Classical axioms in library proofs and
erased certificates do not constitute a choice-based algorithm; all executable
definitions compile, and the pivot and row views execute in the harness.

`dup_check.py check --ref 7c9d311279d67ebf5fd51bcdc91ec0ecad037e3e --branch HEAD`
reports no duplicate among the 26 declarations recognized by its scanner.
The initial five proposed-name check against `github/main` also passed.
Normal hooks ran on every completed milestone commit. Full build, publication,
root-import integration, blueprint adoption, and independent review belong to
main under this assignment. No full build or publication was performed here.
The reviewer should examine the counted tabulation, `Invariant.step`, and the
transition from its final instance to the existing RREF predicate first.

## Preserved Accounting

This is session `prover-690-20260922-01`, admitted at
`7c9d311279d67ebf5fd51bcdc91ec0ecad037e3e` with a 3600-second whole-task limit
and no extension or child session. It continues the algorithmic obligation of
issue #676 rather than replacing the canonical complement with a different
definition. The predecessor module, chapter 11, shared imports, gap statuses,
completion marks, and prior audits are unchanged.

All preceding prefix-rank and RREF author, CI, repair, and review costs remain
part of that history. In particular, the earlier audits retain the 900-second
comparison attempt, interrupted 385-second locator repair, 480-second recovery,
300-second audit repair, and the failed first RREF review followed by its
successful review. Their budgets and measured durations are not recomputed or
merged into a new baseline, and missing token measurements are not treated as
zero. The dispatcher's session registry remains authoritative for this
session's final token and wall-time costs.
