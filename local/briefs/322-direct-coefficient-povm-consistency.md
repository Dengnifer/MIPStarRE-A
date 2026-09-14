# Direct coefficient POVM consistency

Issue #322 is a Lean-only auxiliary under #119, stacked on the coefficient
collision theorem from #316. The line-answer coefficient representation is
described in
`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:331-344`,
and the relevant polynomial collision estimate appears in
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1595-1603`.

The new theorem specializes
`SandwichProduct.consistencyDefect_codewords_le_evaluated_add` to POVMs whose
outcomes are `DirectDegPoly D degree`. It bounds their full coefficient-outcome
consistency defect by the defect after evaluation at an independent uniform
scalar parameter, plus `degree / D.q`, using
`directCoefficientCollision_avg_le` to discharge the collision premise.

The result applies to arbitrary POVMs and assumes only a probability
distribution and a unit bipartite state. It adds no projectivity,
coefficient-injectivity, nonzero-direction, `degree < D.q`, or collision
hypothesis. It does not compare completed point evaluations, construct a
strategy or witness, or prove the full passing-value bound or source lemma
`lem:qld-4-7`.

Completion requires focused Lean and standard-only axiom checks, followed by
normal publication, canonical CI, independent review, and merge. Existing
#119 usage, the 307-second resampling scout, the 1169-second resampling proof
packet, and the B8 budget of 13 attempts / 26509 seconds remain unchanged.
