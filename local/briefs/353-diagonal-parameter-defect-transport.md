# Issue 353: diagonal parameter-defect transport

## Goal

Identify the diagonal coefficient defect used by the same-line rejection bound
with the diagonal parameter-evaluation defect bounded for the supplied
extended-line witness.

## Method

Expand both definitions over the common product of the diagonal-line marginal
and the uniform affine parameter. Compose the two measurement postprocessings,
use `diagonalRead_eval` to identify evaluation before and after the diagonal
coefficient projection, and convert `consistencyDefect` to the corresponding
mismatch average.

## Boundaries

The result is an exact equality and retains zero diagonal directions. It adds
no projectivity, nonzero-direction, producer, collision, branch-sum, or
passing-value hypothesis. It does not construct an extended-line witness or
claim the source-labelled QPBT theorem.

## Source and Statement Integrity

The source context is Lemma `lem:qld-4-13` and the classical low-degree-game
construction in the proof of `lem:qld-4-7` in
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1020-1034` and
`:1279-1288`. The paper does not separately state this comparison between Lean
encodings of the same evaluation defect.

The Lean assumptions are exactly an admissible parameter tuple, a
`ProjectiveSetting`, a `CombinedPointsWitness`, and an `ExtendedLinesWitness`.
The conclusion is equality of the two pre-existing diagonal defects. The proof
uses only measurement postprocessing, `diagonalRead_eval`, and the existing
consistency-defect mismatch identity.

Verdict: formalization-only transport with faithful boundary hypotheses and no
additional load-bearing assumptions. The source-labelled blueprint entry
`lem:qld-4-7` remains unchanged.

## Verification

The focused Lean check and target module build pass. The theorem's axioms and
source-integrity scans are recorded in the PR testing evidence.
