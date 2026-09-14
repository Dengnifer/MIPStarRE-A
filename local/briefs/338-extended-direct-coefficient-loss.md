# Issue 338: extended direct coefficient loss

## Scope

The extended directly indexed low-degree parameters have dimension
`2 * P.m + 2`, while retaining degree `P.d` and field size `P.q`. The axis and
diagonal coefficient-collision estimates therefore contribute respectively
`P.d / P.q` and `(2 * P.m + 2) * P.d / P.q`.

The new scalar lemma bounds their sum by
`5 * P.m * P.d / P.q`. It uses
`P.one_le_m` and positivity of the admissible field size, with no additional
degree, divisibility, or nonzero-direction hypothesis.

## Source alignment

The collision terms originate in
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1595-1603` and
`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:331-344`.
The comparison constant is a Lean-only arithmetic auxiliary and does not claim
a complete same-line passing bound.

## Dependency

Issue #327 supplies the axis and diagonal coefficient-POVM bounds whose scalar
losses are combined here.
