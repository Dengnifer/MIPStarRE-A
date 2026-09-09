# Issue 327: resampled coefficient consistency

## Scope

This packet combines the direct coefficient-POVM consistency estimate with the
exact affine resampling laws for directly indexed axis and diagonal lines.  It
rewrites the independently sampled line-and-parameter consistency defect as an
expectation over the original joint line-point law.

For zero diagonal directions, the sampled point does not determine the affine
parameter.  The joint integrand therefore retains the full uniform parameter
average in exactly that case.  No nonzero-direction premise, collision input,
or replacement by separate marginals is introduced.

## Source alignment

The joint direct line laws come from
`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:243-287`
and `references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1020-1116`.
The declarations are Lean-only averaging and reindexing auxiliaries.  They do
not formalize the remaining `Option.none` event conversion or a complete
passing-value bound.

## Dependencies

- Issue #314: exact affine resampling of the joint direct line-point laws.
- Issue #322: coefficient consistency from uniformly evaluated consistency and
  the direct coefficient collision bound.
