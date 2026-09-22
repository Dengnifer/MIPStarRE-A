---
title: "Issue 676 reduced row echelon correspondence"
date: 2026-09-22
purpose: >
  Records the proved correspondence between conventional reduced row echelon
  form and the intrinsic canonical complement, including existence from
  independent input rows.
issue: "#676"
---

# Reduced row echelon correspondence

## Result and Scope

`MIPStarRE/QPBT/Algebra/RowEchelon.lean` proves the mathematical correspondence
requested by issue #676. For every matrix `A : Matrix (Fin m) (Fin n) K`
with linearly independent rows, `exists_isReducedRowEchelon` constructs a
matrix `B`, an increasing pivot map `pivot : Fin m ↪o Fin n`, and an invertible
square matrix `U`, with all of the following conclusions:

- `A = U * B`;
- `B` satisfies conventional entrywise reduced row echelon conditions;
- the row spans of `A` and `B` coincide;
- `canonicalComplement` of that span is exactly the complement of the pivot
  index set.

Existence is proved from row independence. No RREF certificate, rank identity,
complement identity, or construction hypothesis is assumed in that theorem.
The new module is imported by `MIPStarRE/QPBT.lean`.

This is an abstract existence and correspondence result. It does not implement
Gaussian elimination, certify a particular executable implementation, or prove
a running-time bound. Source adoption, blueprint completion marks, and gap
status remain for main and independent review; none is changed here.

## Source Comparison

The source is `references/qpbt-paper/04_preliminaries.tex:303-373`, Definition
`def:canonical-complement` and Lemma `lem:canonical-complement`. Under the
ambient convention at lines 219-222, the field is finite and the ambient
dimension is positive. The definition itself notes that Gaussian elimination
works over arbitrary fields.

The source begins with independent row vectors, reduces their matrix to RREF,
and selects the standard basis vectors in nonpivot columns. Its proof writes
`A = U B` for an invertible `U` and uses the unchanged row span. Lean proves
these algebraic properties and the equality with the pre-existing intrinsic
prefix-rank construction. Lean stores coordinate indices; applying the
standard basis map gives the source's set of vectors, and `registerSubmodule`
gives their span.

Statement-integrity comparison:

| Item | Source | Lean |
| --- | --- | --- |
| Field | Finite field under the ambient convention | Arbitrary `Field K` |
| Dimensions | Finite row family, positive ambient dimension | Natural `m`, `n`, including zero |
| Input | Linearly independent row vectors | `LinearIndependent K A.row` |
| Coordinate order | Columns `1, ..., n`, left to right | `Fin n`, in increasing order |
| Reduced form | Leading ones, zeros before them and elsewhere in their columns | Increasing pivot map and the same entrywise identities |
| Change of basis | `A = U B`, `U` invertible | `A = U * B`, `IsUnit U` |
| Selected complement | Standard basis vectors outside the pivot columns | The same indices selected by `canonicalComplement` |

Verdict: **exact for the algebraic correspondence on the source domain**,
with explicitly documented arbitrary-field and zero-dimensional extensions.
No extra load-bearing assumptions or weakened algebraic conclusions occur.
The algorithmic presentation and efficiency assertion are outside this result.
Existing paper-labelled theorem statements and all source definitions are
unchanged.

## Mathematical Argument

For an RREF matrix `B`, restrict its rows to the first `k` columns. A row whose
pivot is at least `k` becomes zero. The other rows are independent: evaluation
at their pivot columns recovers each coefficient of a linear combination.
These rows therefore form a basis of the prefix row span. This proves
`IsReducedRowEchelon.prefixRank_eq_card`. Together with the predecessor's
`prefixRank_span_rows_eq_rank_submatrix`, it also identifies the Mathlib rank
of the prefix submatrix with the number of pivots below `k`.

Consequently, adding coordinate `j` leaves the prefix rank unchanged exactly
when `j` is not a pivot. This proves
`IsReducedRowEchelon.canonicalComplement_eq_nonpivot_indices` for every matrix
satisfying the entrywise RREF conditions, independently of its construction.

For existence, let `W` be the span of the input rows, let `C` be its intrinsic
canonical complement, and let `T` be the coordinate subspace spanned by `C`.
The already-proved intrinsic complementarity theorem gives `W ⊕ T = K^n`.
If `P` is the complement of `C`, the dimension formula gives `|P| = m`.
Enumerate `P` increasingly as `pivot` and project each `e_(pivot i)` onto `W`
along `T`. Use these projections as the rows of `B`.

Projection changes only coordinates in `C`, so the pivot columns of `B`
form the identity matrix. To verify the leading-zero condition, induct on
coordinates before a row's proposed pivot. At an earlier pivot, the identity
condition gives zero. At a coordinate of `C`, the intrinsic lemma
`coordinate_eq_zero_of_prefixRank_eq` gives zero once all preceding
coordinates vanish. The resulting rows satisfy RREF and are independent.
They lie in `W`, and equality of dimensions proves that they span `W`.
This is `exists_isReducedRowEchelon_span_eq`.

Finally, express each original row in these new rows. The coefficient matrix
is `U`, and the coefficient identities give `A = U * B`. The linear map
given by right multiplication by `B` sends the rows of `U` to the independent
rows of `A`, so the rows of `U` are independent. Mathlib's characterization
of invertible square matrices then gives `IsUnit U`.

The use of intrinsic complementarity in this existence proof is not circular.
Its predecessor proof uses rank monotonicity, coordinate vanishing, and a
dimension count; it does not use RREF or the new correspondence theorem.
Conversely, the new prefix-rank formula and nonpivot comparison use only the
entrywise RREF conditions.

## Basis Independence and Boundary Cases

`IsReducedRowEchelon.pivot_indices_eq_of_span_eq` proves that two RREF matrices
with the same row span have the same pivot index set. Thus the comparison is
independent of the chosen input basis, its ordering, and the particular RREF
construction. Full uniqueness of the RREF matrix is not needed or asserted.

All six theorems allow `m = 0`. The pivot index set is then empty, and its
complement is every ambient coordinate. They also allow `n = 0`; row
independence forces `m = 0`, and both coordinate sets are empty. No artificial
nonemptiness assumption or exceptional default branch is present. For a
square matrix with independent rows, the pivot embedding is a bijection, so
the nonpivot set is empty. The zero ambient dimension case is an extension,
not part of the paper's stated ambient convention.

## Validation and Accounting

- The baseline `Subspaces.lean`, the new `RowEchelon.lean`, and the modified
  `MIPStarRE/QPBT.lean` each pass focused `lake env lean` checks.
- The scan `rg -n "sorry|axiom"` of both changed Lean files returns no matches.
- A transitive `#print axioms` check of all six new lemmas reports only
  `propext`, `Classical.choice`, and `Quot.sound`.
- The forbidden-proof-token and debugging-command scan is clean, as are
  whitespace and the new module's 100-character line-length checks.
- Normal hooks run on every milestone commit. No hook bypass is used.
- Searches of Mathlib linear algebra and the local algebra modules found no
  existing rectangular RREF interface or duplicate of these declarations.
- No full `lake build` is run: main owns full CI and independent review under
  the explicit assignment. Only this worktree's private build products are
  written; shared packages and the hot cache are untouched.

The starting head is `bff84964581fd85bfa7d52d6a5fc97b1406d0df3`. This work
preserves the predecessor's source audit and prefix-rank lemma. The original
900-second comparison attempt, interrupted 385-second locator repair,
480-second recovery, 300-second audit repair, and all earlier issue #676
work, CI, and review costs remain part of its history. This session is the
separately authorized 1800-second successor, with its first committed
mathematical checkpoint well before 900 seconds and no self-extension.

No proof obligation remains in the assigned mathematical correspondence.
The independent reviewer should examine the entrywise predicate, the
projection argument for leading zeros, the invertibility proof, and the
distinction between abstract correspondence and executable elimination.
