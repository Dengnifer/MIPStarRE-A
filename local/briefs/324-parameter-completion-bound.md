# Issue 324: parameter versus completed evaluation

## Scope

Prove that `directEvalOpt` at the affine point represented by a parameter, when
successful, agrees with `evalCoefficient` at that parameter.  Use this fact to
bound parameter-evaluation mismatch by completed-readout mismatch and the two
`none` marginals for arbitrary bipartite strategy POVMs.

## Source

- `references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:230-390`
- `references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1267-1402`

This is formalization-only support for the same-line comparison.  It is not a
new strategy construction, a witness producer, or a full passing theorem.

## Boundaries

- Base: `c5d519c097153a5e6dafbc32f438044eb28603b2`.
- Prerequisite: closed issue #244, which supplies
  `ExtendedLineGame.directEvalOpt_eq_some_iff`.
- No nonzero-direction or degree-versus-field-size hypothesis.
- No collision, projectivity, symmetry, producer, or passing premise.
- The two later comparisons from `none` mass to line-point rejection are out of
  scope and remain owned by their separate packet.
