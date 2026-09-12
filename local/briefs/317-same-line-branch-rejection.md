# Issue 317: same-line branch rejection

## Source

- `references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1020-1034`
- `references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1279-1288`
- Blueprint `lem:qld-4-7`

## Contract

The concrete strategy from issue #244 answers an axis or diagonal question by
coarse-graining the supplied extended-line POVM through `axisAnswer` or
`diagonalAnswer`. These maps use `axisRead` and `diagonalRead`, respectively,
and construct the unique coefficient tuple required by
`P.extendedDirectLd.k = 1`.

This packet defines the two coefficient-answer consistency defects on
`ExtendedLineGame.pairState`. Their question laws are the first marginals of
`directALinePointDist P.extendedDirectLd` and
`directDLinePointDist P.extendedDirectLd`. It proves that they are exactly the
`(.aline, .aline)` and `(.dline, .dline)` branch rejection probabilities.

The proof uses the verifier's equality clauses and the established zero effects
of wrong-format answer tags. It introduces no passing premise, coefficient
agreement hypothesis, evaluation injectivity, or numerical rejection bound.

## Declarations

- `ExtendedLineGame.axisCoefficientAnswerDefect`
- `ExtendedLineGame.diagonalCoefficientAnswerDefect`
- `ExtendedLineGame.aline_aline_rejection_eq_axisCoefficientAnswerDefect`
- `ExtendedLineGame.dline_dline_rejection_eq_diagonalCoefficientAnswerDefect`

These declarations are formalization-only components of the future passing-
value calculation. They do not prove `lem:qld-4-7` or construct either supplied
witness.
