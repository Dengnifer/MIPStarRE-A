# Issue 351: axis parameter-defect transport

The coefficient-evaluation defect used in the same-axis rejection estimate
equals the parameter-evaluation defect of the supplied direct-game strategy:

```lean
axisParameterEvaluatedCoefficientDefect lines =
  axisParameterEvaluationDefect lines
```

Both definitions use the axis coefficient truncation `axisRead`. In the
first, the supplied line POVM is postprocessed by truncation and then by
evaluation. In the second, the game measurement wraps the truncated vector
in the axis answer constructor, and its unique coordinate is extracted
before evaluation. Finite postprocessing composition identifies these
measurements. The product-distribution averaging identity and pushforward
averaging preserve exactly the actual axis-line marginal and an independent
uniform affine parameter.

The source interpretation of truncation is proved separately. The supplied
`ExtendedLinesWitness.axis_degree` field makes every unsupported coefficient
effect zero. Consequently, a pair of outcomes has zero Born mass whenever
either vector exceeds degree `d`. On the remaining effects,
`axisRead_eval_of_effect_ne_zero` identifies truncated and original
coefficient evaluation. Summing the fibers gives equality of the two
evaluation measurements. This uses the supplied degree-support conclusion,
not a degree bound relative to the field size or polynomial-function
injectivity.

## Statement Integrity

The source passages are `lem:qld-4-13`,
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1020-1034`,
and the classical-game construction in the proof of `lem:qld-4-7`,
lines 1279-1288. The paper supplies extended-line POVMs with outcomes of
degree at most `md+1`; for axis lines their supported outcomes have degree
at most `d`. The classical-game construction expressly allows line POVMs
that are not projective.

The Lean assumptions are the existing admissible parameters,
`ProjectiveSetting`, `CombinedPointsWitness`, and supplied
`ExtendedLinesWitness`. The exact defect equality adds no assumptions.
The support lemmas take an axis line; the zero-mass statement assumes that
at least one specified outcome lies outside degree `d`, precisely the event
whose mass it proves zero.

The paper conclusion supplies the degree-supported POVMs and uses them in
the classical low-degree game. It does not name the two separate defect
encodings compared here. The Lean conclusion is their exact equality under
the same line marginal and independent uniform parameter, together with
the zero-mass and effect identities just described.

Verdict: formalization-only identities for the supplied-witness
construction, with faithful boundary hypotheses and no additional
load-bearing assumptions. No projectivity, equal-player, symmetry,
passing-value, witness-producer, or degree-less-than-field-size premise is
introduced. These results do not prove the existence of the supplied
witnesses or the source theorem `lem:qld-4-7`; its blueprint status is
unchanged.

## Verification

The focused Lean check, the new target-module build, and the QPBT aggregate
typecheck pass; the focused source produces no warnings. A `Lean.collectAxioms`
allowlist check for all three public theorems permits only `propext`,
`Classical.choice`, and `Quot.sound`. The new source has no proof holes,
added axioms, kernel bypasses, placeholder tactics, debug commands,
heartbeat overrides, or linter suppressions. Worktree hook installation was
checked. The two prerequisite modules were built in this worktree before
the focused check.

This packet preserves the predecessor's 25-minute checkpoint and all
issue-348 history. It does not alter the existing issue-348 drafts or the
B8 budget of 13 attempts and 26509 working seconds.
