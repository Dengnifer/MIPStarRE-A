# Issue 340: ground-slice POVM compression

## Objective

Provide the reusable fixed-coordinate compression needed to pull POVMs from a
Naimark-padded local space back to the original player space. Package the exact
transport of `consistencyDefect` across `padState` so direct low-degree
soundness bounds can be reused without an additional error term.

## Mathematical contract

For a POVM on `I × κ` and `k₀ : κ`, restrict each effect to the principal block
indexed by `i ↦ (i, k₀)`. Positivity follows from
`Matrix.PosSemidef.submatrix`, while completeness follows by evaluating the
original sum-to-identity equation on that block. The construction must commute
with deterministic outcome postprocessing.

For two such POVM families and a bipartite state padded at `a₀` and `b₀`, every
off-diagonal term in `consistencyDefect` is unchanged by compression. The proof
uses `heteroKron_mul` and `stateQForm_padState` term by term.

## Source and boundaries

This is formalization-only infrastructure for the Naimark steps in the first
paragraph of paper `lem:qld-4-7`,
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1279-1289`.
It does not prove the source lemma, preserve projectivity under compression, or
introduce a producer or passing-value assumption. In particular, it uses one
fixed ancillary coordinate rather than the existing normalized average over
all diagonal blocks.

## Validation

- Type-check `MIPStarRE/QPBT/Games/MeasurementCompression.lean`.
- Scan the changed Lean file for proof holes and prohibited bypasses.
- Verify only documentation and aggregate imports changed outside the new
  module.
