# Issue 360: supplied-witness direct soundness

## Goal

Apply arbitrary-strategy directly indexed low-degree soundness to the concrete
strategy determined by a supplied `CombinedPointsWitness` and
`ExtendedLinesWitness`.

## Method

Use the passing-value theorem from issue #348 with error
`3 * (sqrt (deltaQ + deltaL) + m * d / q)`. Admissibility makes `m`, `d`, and
`q` positive, hence the error is positive. Apply issue #346's direct soundness
theorem for arbitrary strategies at `k = 1` and unfold the supplied strategy's
carrier, measurements, and state.

## Boundaries

The theorem assumes only the supplied point and extended-line witnesses. It
returns two polynomial-tuple POVMs on the original expanded player carriers
and the existing three `deltaLd` bounds. It does not construct either witness,
add a game-passing premise, assert projectivity after Naimark compression, or
produce a global paired measurement.

## Source And Statement Integrity

The source context is the first paragraph of the proof of paper
`lem:qld-4-7`,
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1277-1289`.
That paragraph applies low-degree soundness to measurements already supplied by
the preceding construction.

The Lean assumptions are an admissible parameter tuple, a projective setting,
a supplied `CombinedPointsWitness`, and a supplied `ExtendedLinesWitness`. The
Lean conclusion is the existence of two polynomial-tuple POVMs on the original
expanded carriers satisfying the two point-versus-polynomial consistency
bounds and the polynomial self-consistency bound.

Verdict: formalization-only supplied-witness consequence with faithful boundary
hypotheses. The source-labelled blueprint entry `lem:qld-4-7` remains
unchanged.

## Verification

Run focused Lean checking, proof-debt and prohibited-construct scans, aggregate
re-export checking, axiom inspection, hooks, and normal checked publication.
