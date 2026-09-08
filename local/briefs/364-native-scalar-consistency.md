# Issue 364: Native scalar polynomial consistency

## Goal

Specialize supplied-witness direct soundness at its unique polynomial
coordinate.  Return ordinary `PolyMeas` outcomes on the original expanded
player spaces, with both point-polynomial bounds stated against
`CombinedPointsWitness.extendedQ` and with the polynomial-polynomial bound
retained unchanged.

## Method

Apply `consistencyDefect_postprocess_le` to each conclusion of
`exists_direct_polynomial_measurements_of_supplied_witnesses`.  For point
outcomes, postprocess by unique-coordinate selection followed by
`extendedDirectScalarEquiv`; rewrite with
`point_values_measurement_eq_suppliedQ`.  For polynomial outcomes, use
`directPolyMeasTupleMarginal` and the existing
`directPolyMeasTuple_evaluation_marginal` theorem, then postcompose evaluation
with `extendedDirectScalarEquiv`.  Marginalize both sides of the third bound at
the same unique coordinate.

## Boundaries

The question distribution remains the direct-point distribution already used
by supplied direct soundness.  No evaluation helper is duplicated, and no
additional premise, witness producer, global paired measurement, projectivity,
good-polynomial-shape, or Pauli-orthogonality claim is introduced.

This theorem is a Lean-only interface for the first paragraph of paper
`lem:qld-4-7`, `references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:
1277-1289`; it does not complete the source lemma.

## Dependencies

- Parent issue #119.
- PR #361 at `e359144058ca4245614ab5697d8a62589f62a860`.
- PR #363 at `1ad9bd26a92841de9f71d752df83644c3d7b90e9`.

## Verification

Type-check the focused module and root import, scan changed Lean files for
proof holes and kernel bypasses, inspect the theorem's axiom closure, verify
hooks, and publish through the checked stacked-PR path.  Canonical CI and
independent review remain later exact-head gates.
