# Capped direct-game error envelope

Issue #326 is a formalization-only arithmetic sub-issue of #119. Its source
context is the classical low-degree-game application in
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1279-1288`.
The detailed supplied-witness transport boundary is recorded in
`/tmp/qpbt-119-direct-game-transport-contract-20260907.md`.

For nonnegative real numbers `Q`, `L`, and `r`, prove

`Q + 16 L + 4 sqrt(Q + 2 L) + 5 r <= 9 (2 (Q + L) + sqrt(Q + L) + r)`.

Define `directPassingErrorEnvelope x y = 3 (sqrt x + y)`. Prove that this
function satisfies `IsPolyErr₂` with witnesses `3`, `1/2`, and `1`, is positive
when its second input is positive, and bounds the preceding expression after
division by nine and capping by one.

The cap is mathematically necessary for the global `IsPolyErr₂` domain. The
uncapped function `2 x + sqrt x + y` has square-root behavior near zero and
linear growth at infinity, so no single positive power of `x` bounds it on the
whole nonnegative half-line. The resulting module is scalar arithmetic only:
it does not prove any direct-game branch estimate, a passing-value theorem, or
the existence of a witness or strategy. It adds no source hypothesis, bridge,
residual input, or blueprint certification.

Completion requires single-file Lean validation, a proof-hole and forbidden
token scan, standard-only axiom checks for the public theorems, and normal
checked publication. Canonical CI, independent review, and merge remain with
the integration coordinator.
