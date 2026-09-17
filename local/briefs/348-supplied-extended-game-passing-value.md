# Issue 348: supplied extended-game passing value

## Goal

Bound the seven potentially rejecting branches of the directly indexed
low-degree strategy supplied by an `ExtendedLinesWitness`, then derive the same
passing-value lower bound for that strategy and its Naimark projectivization.

## Method

Combine the point-point bound, the four oriented line-point bounds, and the two
same-line coefficient bounds. The axis and diagonal transport identities
rewrite the latter defects to the parameter-evaluation defects already bounded
from the supplied witness. The extended coefficient-collision estimate then
absorbs both collision losses into `5 * (m * d / q)`.

The exact seven-branch value identity divides the rejection sum by nine. The
direct rejection cap and the scalar capped-envelope theorem give
`directPassingErrorEnvelope (deltaQ + deltaL) (m * d / q)`. Exact Naimark value
preservation transports the lower bound to `projectiveStrategy`.

## Boundaries

The result assumes an existing `CombinedPointsWitness` and
`ExtendedLinesWitness`. It neither constructs these witnesses nor applies
low-degree soundness. It adds no projectivity of the supplied line POVMs,
nonzero-direction, producer, branch-sum, or passing-value hypothesis. Zero
diagonal directions remain in the underlying laws.

## Source and Statement Integrity

The source context is Lemma `lem:qld-4-13` and the first paragraph of the proof
of `lem:qld-4-7` in
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1020-1034` and
`:1279-1288`. The paper asserts that the supplied measurements form a strategy
with sufficiently high value but does not separately state this explicit
seven-branch scalar estimate.

The Lean assumptions are an admissible parameter tuple, a `ProjectiveSetting`,
a `CombinedPointsWitness` at error `deltaQ`, and an `ExtendedLinesWitness` at
error `deltaL`. The Lean conclusions are the seven-branch rejection bound,
the original strategy's passing-value bound, and the identical lower bound for
its exact Naimark projectivization.

Verdict: formalization-only supplied-witness consequences with faithful
boundary hypotheses and no additional load-bearing assumptions. The
source-labelled blueprint entry `lem:qld-4-7` remains unchanged.

## Verification

Focused Lean checks, the target module build, aggregate import checking, axiom
inspection, and source-integrity scans are recorded in the PR evidence.
