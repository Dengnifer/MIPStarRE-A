# Direct coefficient collision bound

Issue #316 is a bounded auxiliary proof packet under #119.  A line answer in
the low-degree verifier is a vector of `degree + 1` coefficients, as described
in `references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:331-344`.
The same-line rejection analysis needs the probability that two distinct such
vectors agree when evaluated at an independent uniform affine parameter.

The new theorem uses the existing `linePolynomialOfCoefficients` conversion,
proves its injectivity on the fixed coefficient carrier, and applies Mathlib's
univariate polynomial root count to the nonzero difference.  The cardinality
identity for `DirectScalarQ D` then gives the exact bound `degree / D.q`.  No
assumption `degree < D.q` is present; the bound may exceed one.

This is a Lean-only transport auxiliary for the supplied-witness passing-value
route.  It does not concern completed evaluation at zero-direction lines, add
a collision or injectivity premise, construct a strategy or witness, or prove
the full passing-value theorem or source lemma `lem:qld-4-7`.  Issue #67 and
#117 are closed lifecycle prerequisites.  The B8 budget remains unchanged at
13 attempts / 26,509 seconds.
