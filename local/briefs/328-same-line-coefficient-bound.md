# Same-line coefficient rejection bounds

Issue #328 is a Lean-only auxiliary under #119, stacked on the exact same-line
branch identities from #317 and the generic coefficient-POVM consistency bound
from #322. The source calculation applies the low-degree verifier to the
supplied extended-line measurements in
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1279-1288`;
the coefficient collision step is reflected around lines 1595--1603.

The focused module defines the consistency defects obtained by evaluating the
axis and diagonal coefficient measurements at an independent uniform affine
parameter. Data processing removes the singleton direct-game answer wrapper,
and the generic coefficient estimate then bounds the two same-line rejection
probabilities with losses `D.d / D.q` and `(D.m * D.d) / D.q`, respectively,
for `D := P.extendedDirectLd`.

The probability laws and unit-state premise are discharged by the existing
direct line-point distributions and `ExtendedLineGame.pairState_norm`. No
collision, projectivity, injectivity, degree-field, resampling, completed-
evaluation, or source-facing hypothesis is added. This packet does not convert
failed completed evaluation, prove a resampling law, or establish the full
passing-value bound or `lem:qld-4-7`.

Completion requires focused Lean and standard-only axiom validation, followed
by normal publication, canonical CI, independent review, and merge. Existing
#119 usage and the B8 budget of 13 attempts / 26509 seconds remain unchanged.
