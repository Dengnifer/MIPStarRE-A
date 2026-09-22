---
title: "Issue 676 canonical-complement source alignment"
date: 2026-09-21
purpose: >
  Audits the agreement between the paper's reduced-row-echelon canonical
  complement and Lean's intrinsic prefix-rank construction.
issue: "#676"
pr: "#678"
---

# Issue 676 canonical-complement source alignment

## Verdict

The proposed equivalence is mathematically correct for the source domain, with
the same left-to-right coordinate order and the same row convention. It is not
currently expressible as `canonicalComplement_eq_nonpivot_indices`, because the
repository and Mathlib have no reduced-row-echelon-form object, pivot-index
function, or correctness theorem for rectangular matrices over an arbitrary
field.

This change proves the bounded existing-API part:
`prefixRank_span_rows_eq_rank_submatrix`. For a matrix `A`, it identifies the
prefix rank of the span of the rows of `A` with the Mathlib rank of the matrix
obtained by retaining the first `k` columns. The remaining work is specifically
the RREF pivot-count theorem and the RREF existence/correctness interface.

No definition, game, blueprint mark, exemption, or paper-gap status is changed.

## Source and Lean audit

Under the ambient convention at
`references/qpbt-paper/04_preliminaries.tex:219-222`, the source definition at
lines 303-320 has the following domain:

- a finite field `F`;
- an ambient space `F^n`, with `n >= 1`, and its ordered standard basis;
- `m` linearly independent row vectors `v_1, ..., v_m`;
- the `m x n` row matrix `A` whose row `i` is `v_i`;
- a reduced row echelon matrix `B` obtained from `A` by row operations.

The definition notes that its Gaussian-elimination algorithm works over
arbitrary fields. This observation supports Lean's broader field generality,
but it does not change the paper's ambient finite-field, positive-dimensional
source domain.

Its pivot set `J` consists of the columns containing the leading `1` of each
row of `B`, and its canonical complement is the set of standard basis vectors
with indices outside `J`. The source lemma at lines 342-373 asserts that their
span complements the row span.

Lean defines `canonicalComplement W` for every submodule
`W : Submodule K (Fin n -> K)` over an arbitrary field `K` and for every `n`,
including `n = 0`. An index `j` is included exactly when
restriction from the first `j` coordinates to the first `j + 1` coordinates
does not increase the finrank of `W`. Thus Lean stores coordinate indices;
`registerSubmodule` supplies the corresponding span of standard basis vectors.
The theorem `isCompl_registerSubmodule_canonicalComplement` already proves the
source lemma's two complementary-subspace conclusions for this intrinsic set.

The Lean domain generalizes the source from finite fields and positive ambient
dimension to arbitrary fields and all finite dimensions. It also gives a
basis-independent formulation of the construction.
Given the source rows, take
`W = Submodule.span K (Set.range A.row)`. Conversely, every such finite
submodule has a finite basis. No additional mathematical hypothesis is hidden
in Lean's use of `W`.

## Equivalence check

Let `A = U B`, as in the source proof, where `U` is invertible and `B` is in
reduced row echelon form. For every `k`, restricting to the first `k` columns
commutes with left multiplication:

```text
A[*, 0:k] = U * B[*, 0:k].
```

Hence the two prefix matrices have the same row rank. In an RREF matrix with
independent rows, the prefix through column `k - 1` has rank equal to the number
of pivot columns below `k`: rows whose pivot is below `k` remain independent on
their pivot columns, while a row whose pivot is at least `k` is zero throughout
that prefix. Therefore, for a zero-based index `j`,

```text
j is a pivot  iff  rank(B[*, 0:j+1]) > rank(B[*, 0:j]).
```

Since adding one column changes rank by at most one, nonpivot columns are
exactly the equality steps used by `canonicalComplement`.

The source numbers coordinates from `1` to `n`; Lean uses `Fin n`, numbered
from `0` to `n - 1`. `prefixMap k n` retains precisely indices `< k`, so source
column `j + 1` corresponds to Lean index `j`. There is no reversal or transpose:
both constructions treat the supplied vectors as rows and scan columns from
left to right.

For a concrete order check over `F_2`, take the one-row matrix
`A = [0, 1, 1]`. It is already in RREF, with source pivot column `2` and
nonpivot columns `1` and `3`. Its prefix ranks for `k = 0, 1, 2, 3` are
`0, 0, 1, 1`, so Lean selects zero-based indices `0` and `2`, exactly the same
coordinates.

## Basis independence and degenerate cases

If two independent row families span the same subspace, their matrices differ
by invertible left multiplication. The displayed prefix identity therefore
shows that every prefix rank, and hence every selected index, is independent of
the chosen basis and its ordering.

- `m = 0` or `W = bottom`: every prefix rank is zero, so all coordinates are
  nonpivot coordinates.
- `m = n` with independent rows or `W = top`: every added coordinate increases
  prefix rank, so the complement is empty.
- `n = 0`: this case is outside the paper's positive-dimensional source domain.
  Lean permits it; its index set is empty, and the corresponding extension of
  the RREF construction has `m = 0` and no coordinate indices.

The source-domain cases agree with the conventional RREF construction, and the
zero-dimensional Lean generalization extends that agreement degenerately.

## Existing API boundary

The checked bridge theorem uses existing Mathlib declarations
`Submodule.map_span`, `Matrix.rank_eq_finrank_span_row`, matrix `submatrix`, and
`Fin.castLE`. Mathlib also proves rank invariance under invertible left
multiplication as `Matrix.rank_mul_eq_right_of_isUnit_det`.

The API search found no reusable RREF definition or ordered pivot-set theorem.
`Matrix.Pivot` in `Mathlib.LinearAlgebra.Matrix.Transvection` gives a two-sided
diagonal reduction for square matrices. It performs column operations and does
not preserve or expose the source's pivot columns, so it cannot establish this
identity. The Gaussian-elimination implementation under the `linarith` tactic
is tactic-internal simplex code, not a rectangular matrix RREF API.

The duplicate-work guard was clean on `github/main` for both
`canonicalComplement_eq_nonpivot_indices` and the bridge theorem added here.

## Bounded next action

Add a rectangular RREF interface over an arbitrary field with:

1. a matrix output row-equivalent to the input by invertible left
   multiplication;
2. an ordered pivot map for nonzero rows and the standard RREF axioms;
3. a theorem that the rank of each first-`k` column prefix is the number of
   pivots below `k`;
4. existence and basis-independence for matrices with linearly independent
   rows.

Then `prefixRank_span_rows_eq_rank_submatrix` and rank invariance under the
invertible row operation give
`canonicalComplement_eq_nonpivot_indices` by extensionality. An executable
Gaussian-elimination routine and a complexity theorem are separate obligations;
they do not follow from complementarity or from the equivalence of pivot sets.

No source-domain counterexample was found. Consequently the current
`canonicalProjOfKernel`, `canonicalProjPerp`, and `lineRepMap` consumers require
no semantic change. A genuine pivot-set mismatch would alter their chosen
images and canonical line representatives, but the coordinate audit above rules
out that mismatch.
