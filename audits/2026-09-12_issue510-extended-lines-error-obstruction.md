# Extended-line error obstruction, issue #510

The target `MIPStarRE.QPBT.exists_extendedLinesWitness` is not discharged.
Its signature and proof body remain unchanged from
`ae124f8f09ee002444ac5b9711822c0f1daae142`. This packet proves
`not_exists_combining_quarter_power_bound`, an independent obstruction to
absorbing the first estimate in the printed proof into the requested error
function. It is not a counterexample to the existence of the measurements.

## Source and calculation

The source is `references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex`:
`lem:qld-4-13` at lines 1020-1034, the first estimate
`eq:qld-combined-lines-consistency` at lines 1134-1137, and the second route
at lines 1241-1245. The blueprint retains the requested error form and records
the gap in `rem:qld-4-13-source-defects`. The analysis already appears in
`docs/paper-gaps/qpbt_combined-lines-error-term.tex`.

The first estimate contains the nonnegative term `m * epsilon^(1/4)`.
Take `m_n = 2^(2n+1)`, `d_n = 1`, `q_n = m_n^3`, and
`epsilon_n = m_n^(-4)`. These are admissible numerical parameters:
`q_n = 2^(6n+3)` has odd exponent, `m_n` divides `q_n`, and `d_n >= 1`.
Both `m_n^2 * epsilon_n` and `m_n*d_n/q_n` equal `m_n^(-2)` and tend
to zero. But `min(1, m_n * epsilon_n^(1/4)) = 1`. Consequently no function
satisfying `IsPolyErr₂` can dominate this capped term uniformly on the
admissible numerical domain.

The Lean proof uses Mathlib's divergence of powers with base greater than one,
the limit of reciprocals at infinity, continuity of positive real powers at
zero, and preservation of inequalities under limits. It constructs the
admissible parameters internally. It assumes no strategy, measurement,
line witness, conditional construction, or unproved mathematical lemma.

This establishes non-derivability by scalar domination of the printed first
estimate. It does not show that any strategy attains that estimate. A better
estimate for the actual consistency defect could still prove the target.
The second printed route additionally uses a joint product law not supplied
by the subline lemma, and its separate dimension prefactor does not resolve
the error-form issue.

## Saved proof search

`git log --all -G exists_extendedLinesWitness` was searched for
`MIPStarRE/QPBT/Combining/Apply.lean`, including saved branch commits.

- `ffd86ea4daa8d84b92bd6390bb86e1077d359e0e` contains the existential
  assembly from `exists_combinedPointsWitness` and
  `exists_extendedLinesWitness_ofPointsWitness`. Its own documentation says
  the axiom closure contains `sorryAx`. This is not a discharged proof of the
  current target, and its already preserved assembly was not duplicated.
- `f6a340c8dc3c12566d9312215c578939efeb8b4a` retains that assembly while
  changing the conditional helper to accept a fixed polynomial point-error
  function. The helper's printed-error obligation remains open. The whole
  divergent branch was not imported.
- The scalar estimate `exists_combining_polynomial_bound` is already present
  in `Combining/ErrorBounds.lean`, following recovery in issue #275. Its
  conclusion retains the dimension factor, so it does not supply the target's
  error bound and was not reproved.

## Statement integrity

- Paper assumptions: admissible parameters, a passing projective strategy in
  the surrounding setting, and the point construction of `lem:qld-4-10`.
- Lean assumptions: the same existing quantification over `AdmissibleParams`,
  real `epsilon`, and `ProjectiveSetting P epsilon`; the point witness is
  existentially supplied with a universal polynomial point-error function.
- Paper conclusion: extended-line POVMs of degree at most `md+1`, axis degree
  at most `d`, and both displayed consistency comparisons with error
  `poly(m^2 * epsilon, md/q)` over field answers.
- Lean conclusion: the unchanged `ExtendedLinesWitness`, which uses the
  directly indexed line carrier and law and the completed `Option` answer
  alphabet. These pre-existing differences remain documented. The corrected
  sum interpretation of `IsPolyErr₂` also remains unchanged.
- Verdict: no new assumptions or conclusion changes. The target remains an
  unfinished directly indexed auxiliary, not a complete formalization of the
  source theorem. The new scalar lemma exactly matches its separate blueprint
  entry `lem:qld-combining-quarter-power-obstruction`; only that new entry
  receives proof-complete links.

## Validation

Focused Lean checks pass for `Combining/ErrorObstruction.lean` without
warnings and for `Combining/Apply.lean` with its five existing proof-hole
warnings. The new file contains no `sorry`, `admit`, or axiom declaration.
The worktree hook installation check passes, as does blueprint declaration
synchronization. `leanblueprint web` completes successfully; its bibliography
warnings concern existing entries outside the new lemma.

The axiom harness imports freshly compiled `Combining/Apply.lean`:

| Declaration | Axiom closure |
| --- | --- |
| `not_exists_combining_quarter_power_bound` | `propext`, `Classical.choice`, `Quot.sound` |
| `exists_combinedPointsWitness` | `propext`, `Classical.choice`, `Quot.sound` |
| `exists_extendedLinesWitness_ofPointsWitness` | The standard three plus `sorryAx` |
| `exists_extendedLinesWitness` | The standard three plus `sorryAx` |

## Prior costs and next gate

This is session `prover-510-20260912-01`, begun at
`2026-09-12T04:54:03Z`, with a 60-minute bound. No descendants were launched.
Its cost is additional to the prior work, not a restart of that accounting.

The saved assembly's session `opus-prover-118-s3-20260905T0812Z` records
816 seconds and 174,484 harness tokens in `results/telemetry/owner-sessions.jsonl`.
The exhausted B8 episode records ten attempts and 19,931 seconds, anchored at
`2026-09-05T19:24:00Z`, in `results/telemetry/events.md`. Subsequent terminal
records `mathfix-118-20260906-11`, `-12`, and `-13` record another
2,335 + 1,976 + 2,267 = 6,578 seconds in `results/telemetry/sessions.jsonl`.
These nonoverlapping recorded intervals give a prior lower bound of 27,325
seconds, before this packet and other historical combining work. They do not
reclassify the original exhausted ten-attempt episode. Several records resume
the same thread, so their cumulative token counters must not be summed;
timed-out zero counters are not evidence of zero usage.

The next publication gate is exact-head local CI, followed by a distinct
reviewer session. The mathematical prerequisite for closing #510 is an
extended-line estimate at the unchanged printed error scale for the constructed
point witnesses. Merely recovering the saved existential assembly, obtaining
a `GlobalPairWitness` as an assumption, or absorbing the first-route dimension
factor does not provide it. The existing `notready` source entry stays open.
