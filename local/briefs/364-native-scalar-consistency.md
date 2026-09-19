# Issue 364: Preserve supplied polynomial consistency

## Goal

Preserve two distinct formalization-only consequences of supplied combined
point and extended-line witnesses: polynomial-tuple POVMs and their ordinary
scalar-polynomial marginals on the original expanded player spaces. Each
interface exposes the same three unrounded `deltaLd` consistency bounds.

## Source scope

Paper `lem:qld-4-7`,
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1267-1289`,
constructs projective separated polynomial pairs. The declarations preserved
here cover only the first proof paragraph after the combined point and line
measurements have been supplied. They do not construct those witnesses, prove
projectivity or polynomial separation, or produce the paired measurement.
Issue #527's correspondence qualification and source gaps #598 and #524 remain
unchanged.

## Interfaces

`exists_direct_polynomial_measurements_of_supplied_witnesses` returns two
`DirectPolyMeasTuple` witnesses. Its only assumptions are admissible parameters,
a projective setting, a `CombinedPointsWitness`, and an `ExtendedLinesWitness`.
The passing premise required by arbitrary-strategy soundness is derived
internally from `strategy_value_ge_directPassingErrorEnvelope`.

`exists_scalar_polynomial_measurements_of_supplied_witnesses` returns two
ordinary `PolyMeas` witnesses with the same assumptions and quantifier order.
It takes the unique tuple coordinate, uses the public PR623 point-readout
identity, and applies consistency data processing. All three conclusions keep
the exact bound
`deltaLd a b (directPassingErrorEnvelope (deltaQ + deltaL) (m*d/q)) q (2*m+2) d 1`.

## Provenance

The tuple proof is adapted from commit `0ca9cfca` as preserved at PR363 head
`462953fc`. The scalar proof is adapted from Dengnifer's commit `c39d7f25`;
the original blueprint provenance is commit `e6ff9607`, co-authored by Claude
Opus 5. The prior read-only report remains
`/tmp/opus-report-pr365-20260917.md`, SHA-256
`f6ef4a42a8c7c950f0dcd0054f425abb4dbdb69fc07a14cba2abad1f00e51ea8`.
No numeric prior cost was recorded in the available issue brief, so none is
invented or reset here.

## Statement integrity

For both interfaces, the Lean assumptions are exactly the explicit supplied
witness scope above; no passing premise, bridge package, producer assumption,
support premise, or projectivity premise is added. The conclusions preserve the
original witness types and all three exact defects. Replacing the expanded
expression `3 * (sqrt (deltaQ + deltaL) + m*d/q)` by
`directPassingErrorEnvelope` is definitional equality. Verdict: exact
formalization-only supplied-witness auxiliaries, not statements of the source
lemma.
