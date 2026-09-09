# Issue 341: parameter-evaluated line bounds

## Goal

Bound the independently parameter-evaluated axis and diagonal line defects by
`6 * deltaL + 2 * sqrt (deltaQ + 2 * deltaL)` for the supplied extended-line
witness.

## Method

Specialize the generic parameter/completed-read bridge from #324. Use affine
resampling from #314 to recover the actual joint line-point laws, then apply
the completed same-line comparison and failed-read mass bounds from #321 and
#332. Zero diagonal directions remain in the distribution.

## Boundaries

No line projectivity, nonzero-direction premise, coefficient collision, line
witness construction, or full passing-value conclusion is included.

## Source and Statement Integrity

The source is `references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex`,
Lemma `lem:qld-4-10` (689--709), Lemma `lem:qld-4-13` (1020--1034), and the
classical-game construction in the proof of `lem:qld-4-7` (1279--1288).
The last passage expressly allows nonprojective line measurements.

The paper supplies projective joint point measurements with self-consistency
error `deltaQ`, and line POVMs with both oriented line/point consistency
errors bounded by `deltaL`. Its construction uses these measurements in the
classical low-degree game. The paper does not state the separate numerical
parameter-evaluation bound proved here.

The Lean assumptions are an admissible parameter tuple, a `ProjectiveSetting`,
a `CombinedPointsWitness` at error `deltaQ`, and an `ExtendedLinesWitness`
at error `deltaL`. The proofs use the witnesses as supplied. In particular,
they do not construct either witness or assume projectivity of a line POVM.

The Lean conclusions bound the probability that Alice's and Bob's line
coefficient vectors disagree at an independent uniform affine parameter by
`6 * deltaL + 2 * sqrt (deltaQ + 2 * deltaL)`, separately for the actual axis
and diagonal line marginals. Zero diagonal directions remain in the law.
On answer tags incompatible with the question, the coefficient read is
arbitrary, and the corresponding joint Born weight is proved zero before
the event comparison is used.

For each line kind, the completed-read comparison contributes
`2 * deltaL + 2 * sqrt (deltaQ + 2 * deltaL)`. Each failed-read marginal is
bounded by its oriented line/point rejection probability, hence by
`2 * deltaL`. The exact affine-resampling identities identify the averages
with those in the supplied-witness estimates, including degenerate lines.

Verdict: these are formalization-only quantitative consequences of the
supplied witnesses, with faithful finite-field and finite-dimensional
boundary hypotheses and no additional load-bearing assumptions. They are
not an existence statement for the witnesses or the global polynomial-pair
measurement. The source-labelled blueprint entry `lem:qld-4-7` remains
`\notready` and is not linked to these auxiliary estimates with `\leanok`.

## Verification

The focused Lean check and target module build pass. Both public bounds
depend only on `propext`, `Classical.choice`, and `Quot.sound`; their
transitive proof dependencies contain no `sorryAx`. The new source contains
no proof holes, additional axioms, tactic placeholders, debug commands,
or heartbeat or linter overrides. Worktree hook installation was checked.
