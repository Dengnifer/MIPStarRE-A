---
title: "Issue 676 canonical-complement theorem and algorithmic obligation"
date: 2026-09-22
purpose: >
  Records completion of the source complement lemma and the nonalgorithmic
  assertions of its definition, with an explicit remaining computation target.
issue: "#676"
---

# Canonical complement: theorem and computation

## Disposition of the Two Source Nodes

The source is `references/qpbt-paper/04_preliminaries.tex:303-373`, Definition
`def:canonical-complement` and Lemma `lem:canonical-complement`. The standing
convention at lines 219-222 specifies a finite field and positive ambient
dimension.

The lemma is proved for the source object. The new theorem
`isCompl_span_rows_canonicalComplement` starts with a matrix of independent
rows, derives an RREF presentation and the equality of its nonpivot indices
with the intrinsic complement, and proves the two complementary-subspace
conclusions. Its blueprint statement and proof both carry completion marks.
The auxiliary node `lem:canonical-complement-rref` states the explicit
coordinate calculation used in the proof and also carries both marks.

The definition remains unmarked. Its source object, number and independence of
selected vectors, basis independence, and register-subspace assertions are
represented and proved. Its retained assertion of efficient computation by
Gaussian elimination has no certified executable implementation or complexity
bound. No exemption is granted for that remaining assertion.

This note supersedes only the canonical-node completion disposition in the
earlier audits. It preserves their mathematical results and all predecessor
costs. No global paper-gap status or noncanonical completion row is changed.

## The Algorithmic Claim in the Source

The definition says to transform the input row matrix to reduced row echelon
form by a canonical Gaussian-elimination algorithm over arbitrary fields.
The following remark, at lines 323-330, explains this presentation by the
efficient computability of the resulting set. The source does not supply
pseudocode, an operation-count polynomial, a machine model, or a bit encoding
for arbitrary field elements.

For an effective field, the usual interpretation is a deterministic algorithm
using field arithmetic and zero tests, with polynomially many such operations
in the matrix dimensions. An assertion about bit complexity additionally
requires a representation and bounds for these field operations. An arbitrary
abstract field alone does not supply that computational structure.

The predecessor theorem `exists_isReducedRowEchelon` constructs a mathematical
RREF presentation through projections and existence of coordinates. It proves
no operational property of an elimination program. The new executable function
`rowEchelonComponent` takes an RREF matrix and its pivot map as data; it does
not find either from the input matrix. Neither result discharges the source's
algorithmic assertion.

The remaining construction target is therefore precise:

1. Define a deterministic executable elimination function on finite matrices,
   relative to executable field operations and decidable equality.
2. From independent input rows alone, prove that its returned matrix and pivot
   embedding satisfy `IsReducedRowEchelon` and have the original row span.
   The existing nonpivot correspondence then identifies its output with
   `canonicalComplement`; no new correspondence hypothesis is needed.
3. Define a cost semantics for the actual implementation, counting arithmetic
   operations and zero tests, and prove a polynomial bound in `m` and `n`.
   Matrix access, materialization, and repeated evaluation must be accounted
   for by the chosen representation, rather than ignored by a nominal loop
   count. No bit-complexity claim follows without a field encoding.

Suggested construction and verification names are `gaussianElimination`,
`gaussianElimination_correct`, and `gaussianElimination_cost_le_poly`.
These are future targets, not existing declarations or assumed hypotheses.
Issue #676 remains open for this work. The definition's source prose and its
algorithmic assertion have not been weakened to obtain a completion mark.

Searches of the installed Mathlib found no rectangular RREF implementation or
correctness interface beyond this project's predecessor module. Mathlib's
Gaussian-elimination code under `Tactic/Linarith/Oracle/SimplexAlgorithm/Gauss`
is an internal rational simplex procedure; it does not provide this arbitrary
field theorem and cost specification. The square-matrix transvection API uses
column operations as well, so it does not preserve the required pivot set.
This change consequently completes the coordinate construction using the
existing matrix and span APIs and records the elimination program separately.

## Constructive Mathematical Content

Let the nonzero RREF rows be `b_i`, with increasing pivot positions `p_i`.
For an input vector `x`, define

```text
v = sum_i x[p_i] * b_i.
```

The function `rowEchelonComponent` implements this expression using Mathlib's
`Matrix.vecMul`. Mathlib's `range_vecMulLinear` places `v` in the row span.
The identities `b_i[p_j] = delta_ij` give `v[p_j] = x[p_j]`; thus `x - v`
is supported on the nonpivot coordinates. If a row combination also has that
support, evaluation at each pivot makes all its coefficients zero. This proves
the direct-sum assertion in `IsReducedRowEchelon.isCompl_span_nonpivot`.

The source-facing theorem obtains `B`, its pivot embedding, and an invertible
change of rows from `exists_isReducedRowEchelon`. It substitutes the proved
row-span and nonpivot equalities into the preceding calculation. There is no
RREF certificate, complement identity, or existence statement in its
hypotheses. The predecessor's intrinsic complement proof is independent of
RREF, so using it in the established RREF existence proof introduces no cycle.

The pivot embedding has exactly `m` distinct images. Taking its complement in
`Fin n` proves `card_canonicalComplement_span_rows`. Restricting Mathlib's
`Pi.linearIndependent_single_one` proves
`linearIndependent_canonicalComplement`. This also ensures that the selected
indices represent distinct vectors: the source set has exactly `n - m`
members, not merely an enumeration of that length.

For a register subspace indexed by `S`, list `S` increasingly and use the
corresponding standard basis vectors as rows. This matrix already satisfies
RREF. The predecessor nonpivot theorem gives
`canonicalComplement_registerSubmodule`, namely that the selected indices are
`S`'s complement. A vector is orthogonal to every standard vector indexed by
`S` exactly when its coordinates on `S` vanish. This proves
`registerSubmodule_canonicalComplement_eq_dotOrthogonal`.

These results add one executable definition and nine proved lemmas or theorems
to `Algebra/RowEchelon.lean`. The six predecessor RREF results and their proofs
are reused without alteration.

## Statement Integrity

| Item | Paper | Lean | Verdict |
| --- | --- | --- | --- |
| Ambient field and dimension | Finite field, `n >= 1` | `Field K`, natural `n` | Exact on the source domain; documented extensions |
| Input to the complement lemma | `m` independent coordinate vectors | Matrix `A` with `LinearIndependent K A.row` | Exact indexed encoding |
| Source object | Standard vectors in the RREF nonpivot columns | The same indices in `canonicalComplement`, with vectors supplied by `Pi.single` | Exact; equality is derived |
| Complement lemma conclusion | `S + T = V` and `S intersect T = {0}` | `IsCompl` of the row span and `registerSubmodule` on those indices | Exact |
| Number and independence | `n - m` independent standard vectors | Cardinality of the index set and linear independence of the corresponding vector family | Exact indexed encoding |
| Register case | Remaining standard vectors, spanning the orthogonal | Complement of `S`; equality with `dotOrthogonal` | Exact |
| Basis independence | A subspace formulation is possible; blueprint states basis independence | Equal row spans give equal pivot sets | Proved; no full RREF matrix uniqueness claim is needed |
| Algorithmic presentation | Canonical Gaussian elimination, efficiently computable complement | Abstract RREF existence; executable decomposition from supplied RREF data | Remaining obligation; definition unmarked |

The new source theorem has no extra assumptions and no weakened conclusion.
The RREF hypotheses of the auxiliary are discharged in the source theorem.
All results allow empty row families and zero ambient dimension; the latter
is an extension, not a restriction of the paper. No new axiom, proof hole,
conditional source theorem, or divergent fallback is introduced.

## Validation and Preserved Accounting

Focused checks of `RowEchelon.lean`, `MIPStarRE/QPBT.lean`, and
`MIPStarRE.lean` pass. Import products are generated only in this worktree's
private `.lake/build`. A temporary focused harness checks the axiom closure of
all ten new declarations: only `propext`, `Classical.choice`, and `Quot.sound`
occur. It also verifies the empty-row and zero-dimensional cases, the identity
matrix case, and computes the row components over the rationals and `ZMod 2`.
For `B = [0, 1, 1]` and `x = [2, 3, 5]` over the rationals, the computed
components are `[0, 3, 3]` and `[2, 0, 2]`.

`leanblueprint web` passes without errors or warnings. The generated
declaration list resolves through `lake exe checkdecls`; the source-sync check
passes with only the pre-existing warnings outside the edited canonical
paragraphs. Proof-hole, forbidden-token, whitespace, and Lean line-length
checks are clean. No full `lake build`, publication, or independent review is
performed in this worker session; main retains those operations.

The admitted base is `f5300f2094d545415fa09e738203c61832279998`, reviewed in
PR #685, review `5275826301`. This work is session `orc-676-20260922-05`, under
the separately admitted 3600-second limit with no extension or child session.
The earlier prefix-rank and RREF author and review records remain intact,
including the failed 900-second first RREF review
`reviewer-pr685-20260922-01`, followed by the successful 291-second review.
Historical admitted budgets are not substituted for measured wall times, and
missing token measurements are not treated as zero. The dispatcher's registry
remains authoritative for the present session's total cost.
