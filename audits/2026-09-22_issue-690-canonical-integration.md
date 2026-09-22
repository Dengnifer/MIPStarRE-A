---
title: "Issue 690 canonical-complement source integration"
date: 2026-09-22
purpose: >
  Compares the executable elimination and its arithmetic cost with the source
  definition, and records the corresponding blueprint adoption.
issue: "#690, continuing #676"
---

# Canonical-complement source integration

## Source and Scope

The source is Definition `def:canonical-complement` and its following remarks
in `references/qpbt-paper/04_preliminaries.tex:303-340`, with the ambient
finite-field convention at lines 219-222. Independent coordinate rows are
reduced by a canonical Gaussian-elimination algorithm valid over arbitrary
fields. The complement consists of the standard basis vectors in the nonpivot
columns. The source explicitly asserts efficient computation, without a
particular arithmetic exponent or an arbitrary-field bit representation.

This author-side integration starts at
`8f55fc058512f43f69c8c869de349613bbf2de59`. It reads and checks the construction
documented in [the algorithm audit](2026-09-22_issue-690-canonical-elimination.md).
It imports `Algebra.RowEchelonAlgorithm` from `MIPStarRE.QPBT`, links its
construction and proofs in chapter 11, and marks the canonical definition.
It changes no algebraic definition, theorem statement, or proof. The preceding
RREF module and all predecessor audits remain intact.

## Construction and Mathematical Correspondence

The program takes a materialized matrix over `Field K`, with `DecidableEq K`.
It scans columns from left to right, searches a bounded list for the first
eligible nonzero row, interchanges that row with the next pivot row, divides
by the nonzero pivot, and clears its column in every other row. The normalized
row and resulting matrix are stored before subsequent use.

The entrywise row formulas in `eliminateColumn_apply` agree with this
description. `eliminateColumn_span` proves both span inclusions by reversing
the row operations. `eliminateColumn_entries` establishes a unit pivot column
and preservation of earlier columns. `findPivot_spec` identifies the search
with the first eligible list element and bounds its charges by the list length.

`Invariant.step` preserves ordered unit pivot columns, leading zeros, zeros
in inspected columns of the remaining rows, and equality of row spans.
`runColumns_invariant` derives this invariant from the input alone.
`gaussianElimination_correct` applies it to the nonzero-row view, proves that
all trailing rows vanish, and identifies the computed nonpivot set with
`canonicalComplement` using the existing RREF correspondence.
`gaussianElimination_of_linearIndependent` uses equality of row-space
dimensions to show that all `m` rows are pivot rows for independent input.
Neither theorem takes a correctness certificate or a complement identity as
an input. The output rows and pivots read the computed storage, rather than
an abstract existence witness.

The source complement is a set of vectors. Lean represents its coordinate
indices by a finite set and its vectors by the corresponding standard basis
vectors. The retained cardinality, independence, basis-independence, and
register-subspace theorems establish the other assertions of the source
definition and remarks.

New algorithm formulas use paper rows `a=1,...,m` and columns `b=1,...,n`.
Their formal indices are `i=a-1` and `j=b-1`, and
`p_paper(a)=p_Lean(a-1)+1`. After `r` completed pivots, paper row `r+1`
has formal index `r`. The new correctness entry explains that the prefix
lengths `b,b-1` become `j+1,j`; it introduces no coordinate sums with an
implicit index conversion.

## Cost Model and Verdict

Each field division, multiplication, subtraction, and equality test has unit
cost. `tabulateCounted` first evaluates each entry computation into a stored
value/count pair, then reads these pairs to extract values and sum their
charges. The normalized pivot row costs `n` divisions. Clearing the remaining
rows costs at most `2*m*n` operations, conservatively including the pivot
row in that upper bound. Every inspected search row costs one test, even when
an index comparison short-circuits the field test. There are at most `m`
inspected rows per column.

The program accumulates those charges as it constructs the matrices.
`gaussianElimination_cost_le_poly` proves the bound
`n*(m+n+m*(2*n))`, arithmetically the displayed `n*(m+n+2*m*n)`.
This is a bound on the actual conservative counter, not an unrelated nominal
counter or a caller-supplied complexity assertion.

The bound starts with stored input. `ofMatrix` tabulates each input entry once;
arbitrary computation within an external entry-producing function is outside
the theorem. Array reads perform no field arithmetic. The code makes bounded
passes of sizes at most `m`, `n`, and `m*n` per column for row search,
tabulation, summation of counts, and pivot updates. The nonpivot selection
performs at most `m*n` comparisons of stored pivot indices. These observations
explain polynomial administrative work in the ordinary array model; there is
no formal instruction-count, memory-allocation, or field-encoding theorem.

The source's arbitrary-field elimination is therefore realized in the
unit-cost arithmetic model. Executable field operations and equality specify
how to run an algorithm over a supplied field; they do not assume the desired
RREF, span, complement, or efficiency conclusion. An unrestricted
representation-uniform bit-complexity statement over arbitrary fields would
require information the source passage does not supply, and is not claimed
here. The source definition receives its mark on this explicit arithmetic
interpretation, with no permanent exemption or altered mathematical domain.

## Statement Integrity

| Aspect | Paper | Linked Lean result | Verdict |
| --- | --- | --- | --- |
| Field | Finite ambient field; elimination valid over arbitrary fields | `Field K` with supplied operations and `DecidableEq K` | Faithful computational boundary data |
| Dimensions | Finite row family, positive ambient dimension | Natural `m,n`, including zero | Exact on source domain, with degenerate extensions |
| Input | Independent coordinate rows | Stored matrix and `LinearIndependent K (toMatrix A).row` | Same mathematical hypothesis |
| Reduced form | Ordered leading ones with reduced pivot columns | Existing entrywise `IsReducedRowEchelon` on the computed output | Exact |
| Row span | Preserved by elimination | Equality with the input row span, proved internally | Exact |
| Complement | Nonpivot standard basis vectors | Computed nonpivot indices equal the intrinsic complement | Faithful finite-index representation |
| Efficiency | Efficient arbitrary-field Gaussian elimination | Polynomial charged-operation bound for the executable program | Faithful unit-cost arithmetic interpretation |

The overall verdict is **faithful boundary hypotheses**, with no added
mathematical premise and no weakened conclusion. General dependent-row
correctness and zero-dimensional cases extend the source domain. No claim is
made that this closes any unrelated source discrepancy or the QPBT track.

## Blueprint Changes and Dependencies

The definition `def:canonical-complement` now links the actual program, its
independent-row correctness, and its cost theorem in place of abstract RREF
existence as its construction evidence. Its other source-matching links remain.
The new auxiliary entries are `def:gaussian-elimination`,
`thm:gaussian-elimination-correct`, and `thm:gaussian-elimination-cost`.
The definition has a statement mark; both theorems have statement and proof
marks. The source canonical definition gains a statement mark. No mark is
removed.

The algorithm definition has no mathematical dependency on the canonical
complement: it defines elementary row operations and the finite search.
The canonical definition uses that algorithm and the register subspace.
Correctness uses the algorithm and the existing intrinsic correspondence;
the cost theorem uses only the algorithm. Thus the added dependency edges
are acyclic and do not make correctness an input to the algorithm.

`lem:canonical-complement`, `lem:canonical-complement-rref`, and their proofs
are unchanged. The concurrent PR691 index-documentation repair belongs to its
separate worktree. The older prefix-rank and decomposition paragraphs are
preserved here. Main must refresh this branch against the actually merged
parent and retain both its index clarification and these localized additions;
no live parent worktree is imported by this session.

The completion record removes only the canonical definition's unresolved
algorithmic row. The gap register removes its obsolete canonical construction
target and records the new evidence, without changing any global gap status
or unrelated Pauli, Magic Square, or subline entry.

## Evidence

All focused checks passed using this checkout's Lean/Mathlib v4.32.0 pin.

- `texra-blueprint bbl` regenerated the web bibliography, and
  `leanblueprint web`, run from `blueprint/`, completed with no warning,
  unresolved reference, or error in its log.
- `python3 scripts/check_blueprint_latex.py --root blueprint/src` passed.
- `python3 scripts/blueprint_lean_sync.py --root . --update-lean-decls --ci`
  regenerated 1,889 declaration names; the final `--ci` check after the web
  build also passed. The generated `blueprint/lean_decls` is ignored by the
  repository and is not force-added. The only warnings are the unchanged four
  orphan marks in chapter 16 and two statement-only marks in chapters 13 and 14.
- `lake env lean MIPStarRE/QPBT/Algebra/RowEchelonAlgorithm.lean` passed without
  warnings. Focused checks of `MIPStarRE/QPBT.lean` and `MIPStarRE.lean` also
  passed, emitting their import products only into this worktree's private
  `.lake/build/lib/lean/`.
- `lake exe checkdecls blueprint/lean_decls` resolved all 1,889 names after
  the root export was refreshed. It rebuilt only the checker executable.
- A harness importing only `MIPStarRE` resolved all 18 distinct declarations
  linked by the four changed/new entries and rejected any axiom other than
  `propext`, `Classical.choice`, and `Quot.sound`. All passed. It also printed
  the three principal theorem types for the source comparison.
- The predecessor's complete runtime and axiom harness was rerun successfully:
  arithmetic over `ZMod 2`, `ZMod 3`, `ZMod 5`, and the rationals; row swaps,
  dependent and zero rows; computed row/pivot views; charges 22, 14, and 15;
  kernel checks of empty rows, empty columns, empty and zero matrices; and
  standard-axiom closure of all 28 algorithm declarations.
- The repository parser confirms the source definition and algorithm
  definition have statement marks, and the two new theorems and two preserved
  canonical lemmas have both statement and proof marks. The new dependency
  edges were inspected against the proofs and have no cycle.
- Proof-hole, forbidden-proof-token, placeholder, and debug-command scans of
  the algorithm and edited aggregate module found no matches.
  `scripts/install_git_hooks.sh --check` and `git diff --check` passed.
  Commit-time hook results are captured in the dispatch receipt.

Evidence is under `~/.cache/mipstarre-dev/sessions/`, with common prefix
`blueprint-690-20260922-01-`: `web.log`, `sync.log`, `sync.json`,
`exports.lean`, `exports.log`, `runtime.log`, and `checkdecls.log`.
The runtime harness source remains `prover-690-20260922-01-checks.lean`.

No full `lake build`, blueprint PDF build, publication, or independent review
was performed. Full CI, publication, and independent review belong to main.
This author-side comparison is not an independent PR review; the latter must
inspect both the elimination proof and its cost semantics.

## Preserved Accounting

This is session `blueprint-690-20260922-01`, started at
`2026-09-22T19:34:28+09:00`, admitted for one 3600-second integration task.
It preserves the completed 2429-second prover result, all twelve milestone
commits through the admitted head, and every earlier issue #676/#690 author,
repair, CI, and review cost, including unsuccessful attempts. Historical
budgets are not substituted for measurements and missing measurements are not
reported as zero. The earlier audit and dispatcher registry remain the
accounting authorities. No self-extension or descendant session is used.
