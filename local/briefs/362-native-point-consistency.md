# Issue 362: Native supplied-point consistency interface

## Goal

Identify the scalar point readout in the directly indexed low-degree strategy
with the supplied joint point measurement coarse-grained by
`alpha * a + beta * b`, on the original expanded player carrier.

## Method

Unfold `answerMeasurement` at `directLdPointQuestionOf`, the singleton
`pointAnswer`, `directLdPointValuesOrZero`, and
`CombinedPointsWitness.extendedQ`. Compose the three finite outcome maps with
`Measurement.postprocess_comp`. The singleton coordinate is represented by an
explicit inhabitant of `Fin P.extendedDirectLd.k`; the remaining scalar map
reduces by `Equiv.apply_symm_apply`.

## Boundaries

This packet proves only the exact measurement equality
`ExtendedLineGame.point_values_measurement_eq_suppliedQ`. It introduces no
probability, consistency, projectivity, support, producer, global-pair,
compressed-space, or good-polynomial-shape premise. The scalar polynomial
soundness corollary requires three further consistency-defect rewrites and is
left to a separate bounded packet. No polynomial evaluation lemma is
duplicated; later work must reuse `directPolyMeasTuple_evaluation_marginal`.

## Source And Statement Integrity

The source context is the first paragraph of paper `lem:qld-4-7`,
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1277-1289`.
The Lean theorem is an exact formalization-only interface between two existing
encodings of the paper's point measurement. It does not prove the existential
or quantitative conclusion of `lem:qld-4-7`.

Verdict: exact Lean-only consequence with no additional mathematical
hypothesis. The source-labelled blueprint entry remains unchanged.

## Blueprint

Three formalization-support nodes are added to
`blueprint/src/chapter/ch15_qpbt_combining.tex`:
`lem:qld-placement-completeness` and `lem:qld-affine-distance-contraction`,
which record finite-sum and averaged-distance facts already proved in
`MIPStarRE/QPBT/Combining/PointsDataProcessing.lean` and used by the proof of
`lem:qld-4-12`, and `lem:qld-supplied-scalar-point-measurement`, which is the
node of the theorem proved here. The only other blueprint edit is the addition
of the two support labels to the existing `\uses` list of the `lem:qld-4-12`
proof, so that neither support node is left unreferenced; its statement and
prose are untouched.

## Dependencies

- Parent issue #119.
- The module sits directly on `MIPStarRE.QPBT.Combining.ExtendedLineGame`.
  Issue #360 (supplied-witness direct soundness) is not a prerequisite: it was
  withdrawn in review round 1 of PR 361 and its module is not in `main`, so
  this packet reproves the interface against the current `main` definitions.

## Verification

Type-check the focused module first, scan for prohibited proof constructs,
inspect the public theorem's axiom closure from a probe outside the worktree,
verify hooks, and use checked publication. Canonical CI, review, and
integration remain independently owned.
