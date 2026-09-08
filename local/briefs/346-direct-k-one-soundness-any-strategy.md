# Issue 346: arbitrary-strategy direct soundness at k = 1

## Objective

Remove the projectivity premise from the formalization-only directly indexed
low-degree soundness route at simultaneity parameter `1`. Return the two
polynomial-tuple POVMs on the original player carriers while preserving all
three consistency bounds with exactly the projective theorem's error function.

## Mathematical contract

Given an arbitrary strategy for `directLdGame D`, dilate both question-indexed
POVM families by the existing one-measurement Naimark construction and pad the
state at the two distinguished ancillary coordinates. The resulting strategy
is projective and has exactly the original game value.

Apply `exists_direct_ld_soundness_of_k_eq_one` to this dilated strategy. Compress
the two returned polynomial-tuple POVMs to the original local spaces using
issue #340's fixed-coordinate compression. The exact padded-state defect
identity transports the two point/polynomial defects and the polynomial
self-consistency defect without any additional error.

## Source and boundaries

This is Lean-only support for the Naimark step in the first paragraph of the
proof of paper `lem:qld-4-7`,
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1277-1289`.
The projective input theorem has the consistency conclusions of paper
`lem:ld-soundness`,
`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:413-458`.

The generic passing-value premise belongs to direct low-degree soundness. This
packet does not add it to a paper-labelled QPBT producer, does not claim
completion of `lem:qld-4-7`, and does not assert that compression preserves
projectivity. It adds no bridge, producer, ancillary-benignness, or extra-qubit
hypothesis.

## Validation

- Type-check
  `MIPStarRE/QPBT/Combining/DirectLowDegree/AnyStrategySoundness.lean`.
- Verify the aggregate direct-low-degree import.
- Scan changed Lean files for proof holes and prohibited proof bypasses.
- Check that the public theorem returns POVMs on exactly the original carriers
  and retains all three bounds with the unchanged `deltaLd` expression.
