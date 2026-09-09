# Direct line affine resampling

Issue #314 is an auxiliary proof task under #119, using the directly indexed
low-degree transport integrated by #244. The joint line-point distribution is
defined in
`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:243-287`
and used in the QPBT analysis at
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1020-1116`.

The two new expectation identities show that the original joint axis and
prefix-diagonal line-point laws are recovered by first sampling their actual
line marginal and then sampling a uniform affine parameter on that line. The
proof reindexes the scalar parameter with `Equiv.addRight`, reconstructs the
sampled point with `directLineRepParameter_spec`, and translates the common
direct sample without changing its canonical line description.

The diagonal identity includes zero directions and adds no nonzero,
divisibility, injectivity, or collision hypothesis. These are Lean-only
distribution auxiliaries. They do not prove the passing bound in
`lem:qld-4-7`, construct a strategy, or discharge the separate coefficient
collision obligation for the same-line branches of #119.

Completion requires focused Lean and standard-only axiom checks, followed by
the normal publication, canonical CI, independent review, and merge gates.
Existing #119 usage and the B8 budget of 13 attempts / 26509 seconds remain
unchanged.
