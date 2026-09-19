# QPBT theorem index

A reviewer-facing map of the quantum Pauli basis test formalization: for each
result, where the paper states it, what the Lean declaration says, where the
blueprint records it, which axioms the declaration rests on, and whether the
Lean statement departs from the printed one.

The chain this index follows is the one a reviewer needs in order to get from
the definitions to the headline theorem
[`pauli_soundness`](#1-headline-results): game and strategies → the Pauli basis
test → winning implications and the commutation/anticommutation tests →
combining the two bases → applying the classical low individual degree test →
extraction → soundness.

**Generated from commit `c6c8c2f2d34add9aebf15872f50a0f18039e4d46`** (the
`github/main` of 2026-09-19). Every row was read off that tree; nothing here is
carried over from an earlier report.

---

## How to read the columns

**Lean declaration** — fully qualified name, with the file and line it is
declared at in this commit. Permalink base:

```
https://github.com/Dengnifer/MIPStarRE-A/blob/c6c8c2f2d34add9aebf15872f50a0f18039e4d46/<file>#L<line>
```

**Paper** — file and line range under `references/qpbt-paper/`, given as the
enclosing LaTeX environment, together with the source's own theorem/lemma label
when it has one. Chapter files are abbreviated:

| short | file under `references/qpbt-paper/` |
|---|---|
| `04` | `04_preliminaries.tex` |
| `06` | `06_nonlocal_games_and_mipstar.tex` |
| `08` | `08_classical_and_quantum_low_degree_tests.tex` |
| `14` | `14_analysis_of_the_pauli_basis_test.tex` |

A dash means the source states the content as unlabelled prose with no
environment to cite; the blueprint node then carries the reference.

**Blueprint** — the node label and its location under `blueprint/src/chapter/`.
The pairing is not guessed: it is the node's own `\lean{…}` tag. `stmt`/`proof`
record whether that node carries a statement-level and a proof-level `\leanok`.

**Ax** — the axioms the declaration depends on, from `#print axioms`:

- **S** = `[propext, Classical.choice, Quot.sound]`, the three standard Lean
  axioms. No `sorryAx`, and no project axiom: the Lean tree declares none.
- **P** = `[propext]` only.

Section 8 gives the raw probe output and the command that regenerates it.

**Differs?** — whether the Lean statement departs from the printed one:

- **no** — the Lean statement is the printed statement.
- **correction: `note`** — a documented statement correction; `note` is a file
  under [`docs/paper-gaps/`](paper-gaps/), and the row is also a row of
  [`docs/paper-gaps/qpbt-gap-register.md`](paper-gaps/qpbt-gap-register.md).
- **hypothesis: …** — the Lean statement adds the named hypothesis.
- **support** — a formalization-support declaration with no separate statement
  in the paper: an intermediate step, an obstruction, or a bridge between two
  source statements.

---

## 1. Headline results

| Lean declaration | file:line | What it says | Paper | Blueprint | Ax | Differs? |
|---|---|---|---|---|---|---|
| `MIPStarRE.QPBT.pauli_soundness` | `MIPStarRE/QPBT/Test/Soundness.lean:52` | There are universal constants `a ≥ 1`, `0 < b < 1` such that every strategy for the Pauli basis test that wins with probability at least `1 - ε` admits local isometries and an auxiliary state under which the state and both players' Pauli operator families are within `deltaQld a b ε m d q` of the ideal ones. | `thm:pauli`, `08:1431-1445` | `thm:pauli`, `ch13:1581` (stmt ✓, proof —) | S | no [^route] |
| `MIPStarRE.QPBT.pauli_soundness_qubit` | `MIPStarRE/QPBT/Test/QubitForm.lean:423` | The same conclusion restated over qubit EPR pairs and qubit Pauli observables, using that the admissible field sizes are powers of two. | `cor:pauli-binary`, `08:1469-1487` | `cor:pauli-binary`, `ch13:1606` (stmt ✓, proof ✓) | S | no [^binary] |
| `MIPStarRE.QPBT.exists_spcc_value_one` | `MIPStarRE/QPBT/Test/Completeness.lean:266` | For every admissible parameter tuple the symmetrized Pauli basis test has a symmetric, projective, consistent, commuting strategy of value exactly 1. | `lem:pauli-completeness`, `08:1232-1234` | `lem:pauli-completeness`, `ch13:1553` (stmt ✓, proof ✓) | S | no |
| `MIPStarRE.QPBT.honestStrategy_isSPCC` | `MIPStarRE/QPBT/Test/Completeness.lean:220` | The honest strategy built from the ideal Pauli measurements is SPCC. | `lem:pauli-completeness`, `08:1232-1234` | `lem:pauli-completeness`, `ch13:1553` (stmt ✓, proof ✓) | S | no |
| `MIPStarRE.QPBT.exists_ld_soundness` | `MIPStarRE/QPBT/Test/LowDegreeGameTheorems.lean:82` | Quantum soundness of the simultaneous classical low individual degree test: a projective strategy of value `1 - ε` is close to one measuring simultaneous low-degree polynomials, at the source's error `deltaLd`. | `lem:ld-soundness`, `08:413-440` | `lem:ld-soundness`, `ch13:245` (stmt ✓, proof —) | S | no [^ldroute] |

[^route]: The statement is the printed one. What the proof route replaces is
    below it: the carriers of `lem:qld-sublines`, `lem:qld-4-13` and
    `lem:qld-4-7` use a **directly indexed** line space at dimension `2m+2`
    instead of the source's seed-indexed one, because the source's own side
    condition `2m+2 ∣ q` is unsatisfiable. Documented in
    [`qpbt_ld-dimension-divisibility.tex`](paper-gaps/qpbt_ld-dimension-divisibility.tex).
    One further statement-level choice, recorded in the docstring
    (`Soundness.lean:38-50`): the field identification is fixed once and for all
    per admissible size by `fixedFieldModel`, rather than existentially
    re-quantified at each use.

[^binary]: The supporting qubit-isometry lemma `lem:pauli-binary` carries a
    documented correction to the range of its inner factor index — see
    [`qpbt_pauli-binary-factor-index.tex`](paper-gaps/qpbt_pauli-binary-factor-index.tex).
    The corollary's own statement is unchanged.

[^ldroute]: The statement is unchanged and is proved for every `k`. The
    blueprint node deliberately carries no proof-level `\leanok` because the
    printed tensor-code route is not the route that was formalized; the printed
    route's own imports (the tensor-code game correspondence, and `K ≥ 12m(d+1)`
    for the printed choice `K = m³d`) remain open under issue #527. See
    [`qpbt_ld-simultaneous-sandwich.tex`](paper-gaps/qpbt_ld-simultaneous-sandwich.tex)
    and
    [`qpbt_ld-dimension-divisibility.tex`](paper-gaps/qpbt_ld-dimension-divisibility.tex).

---

## 2. The game, strategies, and the value

| Lean declaration | file:line | What it says | Paper | Blueprint | Ax | Differs? |
|---|---|---|---|---|---|---|
| `MIPStarRE.QPBT.Game` | `MIPStarRE/QPBT/Games/Defs.lean:32` | A two-player one-round game: finite question and answer alphabets, a question distribution, and a win predicate. | `def:game`, `06:10-24` | — | S | no |
| `MIPStarRE.QPBT.Strategy` | `MIPStarRE/QPBT/Games/Defs.lean:88` | A tensor-product strategy: a bipartite state together with a POVM per question for each player. | `def:tensor-product-strategy`, `06:26-38` | — | S | no |
| `MIPStarRE.QPBT.Strategy.value` | `MIPStarRE/QPBT/Games/Defs.lean:489` | The winning probability of a strategy: the question-averaged mass the win predicate assigns to the outcome distribution. | `def:tensor-product-value`, `06:40-57` | — | S | no |
| `MIPStarRE.QPBT.Game.value` | `MIPStarRE/QPBT/Games/Defs.lean:573` | The entangled value: the supremum of `Strategy.value` over all finite-dimensional strategies. | `def:tensor-product-value`, `06:40-57` | — | S | no |
| `MIPStarRE.QPBT.Strategy.value_le_one` | `MIPStarRE/QPBT/Games/Defs.lean:551` | Every strategy's value is at most 1. | `def:tensor-product-value`, `06:40-57` | — | S | support |
| `MIPStarRE.QPBT.Strategy.value_le_game_value` | `MIPStarRE/QPBT/Games/Symmetrization.lean:51` | Every strategy's value is at most the game's value. | — | — | S | support |
| `MIPStarRE.QPBT.Strategy.IsProjective` | `MIPStarRE/QPBT/Games/StrategyClasses.lean:27` | Every measurement operator of the strategy is a projection. | — | `def:projective-strategy-general`, `ch12:89` (stmt ✓) | S | no |
| `MIPStarRE.QPBT.SymmetricGame` | `MIPStarRE/QPBT/Games/StrategyClasses.lean:35` | A game with one question alphabet and a symmetric question distribution and win predicate. | — | `def:symmetric-game`, `ch12:100` (stmt ✓) | S | no |
| `MIPStarRE.QPBT.SymmetricStrategy` | `MIPStarRE/QPBT/Games/StrategyClasses.lean:67` | A strategy for a symmetric game in which both players use the same measurement family. | — | `def:symmetric-game`, `ch12:100` (stmt ✓) | S | no |
| `MIPStarRE.QPBT.Strategy.IsPCC` | `MIPStarRE/QPBT/Games/StrategyClasses.lean:139` | Projective, consistent and commuting. | `def:spcc`, `06:176-180` | `def:spcc`, `ch12:232` (stmt ✓) | S | no |
| `MIPStarRE.QPBT.SymmetricStrategy.IsSPCC` | `MIPStarRE/QPBT/Games/StrategyClasses.lean:151` | Symmetric, projective, consistent and commuting. | `def:spcc`, `06:176-180` | `def:spcc`, `ch12:232` (stmt ✓) | S | no |
| `MIPStarRE.QPBT.exists_symmetric_projective_strategy_approx` | `MIPStarRE/QPBT/Games/Symmetrization.lean:139` | For every `ε' > ε` a game of value `1 - ε` has a **symmetric projective** strategy of value at least `1 - ε'`, given a nonempty answer alphabet. | `lem:symmetric-strat`, `06:94-99` | `lem:symmetric-strat`, `ch12:121` (stmt ✓, proof ✓) | S | correction: [`qpbt_symmetrization-attainment`](paper-gaps/qpbt_symmetrization-attainment.tex); hypothesis: `Nonempty G.Answer` |
| `MIPStarRE.QPBT.exists_symmetric_projective_strategy_of_strategy` | `MIPStarRE/QPBT/Games/StrategyClasses.lean:967` | Value-preserving symmetrization of a **given** strategy. | — | `lem:symmetric-strat-given-strategy`, `ch12:179` (stmt ✓, proof ✓) | S | support |

The printed form of `lem:symmetric-strat` — that the supremum defining the value
is *attained* — is kept visible but not asserted; see section 7.

---

## 3. The Pauli basis test and its parameters

| Lean declaration | file:line | What it says | Paper | Blueprint | Ax | Differs? |
|---|---|---|---|---|---|---|
| `MIPStarRE.QPBT.AdmissibleParams` | `MIPStarRE/QPBT/Test/PauliBasisTest.lean:37` | An admissible tuple `(q, m, d)`: `q` a power of two, and the source's size conditions relating `q`, `m` and `d`. | `def:admissible`, `08:958-961` | `def:admissible`, `ch13:1390` (stmt ✓) | P | no |
| `MIPStarRE.QPBT.pauliQuestionDistribution` | `MIPStarRE/QPBT/Test/PauliBasisTest.lean:465` | The question distribution of the test: a uniformly chosen edge of the type graph, with the two endpoints' conditionally linear question components. | `08:1070-1120` | `def:pauli-question-distribution`, `ch13:1408` (stmt ✓) | S | no |
| `MIPStarRE.QPBT.pauliWinPredicate` | `MIPStarRE/QPBT/Test/PauliBasisTest.lean:676` | The acceptance predicate: answer well-formedness, the line/point and point/Pauli consistency conditions, the pair condition, and the commutation phase `γ`. | `08:1126-1225` | `def:pauli-win-predicate`, `ch13:1510` (stmt ✓) | S | no |
| `MIPStarRE.QPBT.pauliBasisTest` | `MIPStarRE/QPBT/Test/PauliBasisTest.lean:728` | The Pauli basis test game itself, assembled from the two above. | `08:964-1225` | `def:pauli-win-predicate`, `ch13:1510` (stmt ✓) | S | no |
| `MIPStarRE.QPBT.pauliBasisTestSymm` | `MIPStarRE/QPBT/Test/Completeness.lean:178` | The symmetrized form of the test, on which completeness is stated. | `08:964-1225` | `lem:pauli-completeness`, `ch13:1553` (stmt ✓, proof ✓) | — | support |
| `MIPStarRE.QPBT.LdParams` | `MIPStarRE/QPBT/Test/LowDegreeGame.lean:40` | Parameters `(q, m, d, k)` of the classical low individual degree test. | `08:31-391` | — | P | no |
| `MIPStarRE.QPBT.ldGame` | `MIPStarRE/QPBT/Test/LowDegreeGame.lean:757` | The classical simultaneous low individual degree test game. | `08:31-391` | `def:ld-game`, `ch13:17` (stmt ✓) | S | no |
| `MIPStarRE.QPBT.introParams` | `MIPStarRE/QPBT/Test/CanonicalParams.lean:105` | The canonical admissible tuple used to instantiate the test. | `def:introparams`, `08:1503-1514` | `def:introparams`, `ch13:1648` (stmt ✓) | S | no |
| `MIPStarRE.QPBT.introParamsTuple_isAdmissible` | `MIPStarRE/QPBT/Test/CanonicalParams.lean:90` | That canonical tuple really is admissible — so the soundness hypotheses are satisfiable. | `lem:delta-bound`, `08:1520-1529` | `lem:delta-bound`, `ch13:1661` (stmt ✓, proof ✓) | S | no [^deltabound] |
| `MIPStarRE.QPBT.exists_deltaQld_introParams_bound` | `MIPStarRE/QPBT/Test/CanonicalParams.lean:170` | At the canonical parameters `deltaQld` is bounded as the source's complexity estimate requires. | `lem:delta-bound`, `08:1520-1529` | `lem:delta-bound`, `ch13:1661` (stmt ✓, proof ✓) | S | no [^deltabound] |

[^deltabound]: Statement unchanged. The printed *proof* uses a false comparison
    `k ≤ m`; the formalized proof estimates `2^(-bm)` directly. See
    [`qpbt_delta-bound-exponent-comparison.tex`](paper-gaps/qpbt_delta-bound-exponent-comparison.tex).

---

## 4. The error function and the soundness conclusion

| Lean declaration | file:line | What it says | Paper | Blueprint | Ax | Differs? |
|---|---|---|---|---|---|---|
| `MIPStarRE.QPBT.deltaQld` | `MIPStarRE/QPBT/Test/SoundnessDefs.lean:35` | `deltaQld a b ε m d q = a · (m·d)^a · (ε^b + q^(-b) + 2^(-b·m·d))`, the soundness error. | `thm:pauli`, `08:1431-1445` | — | S | no [^vacuity] |
| `MIPStarRE.QPBT.deltaQld_mono` | `MIPStarRE/QPBT/Test/SoundnessDefs.lean:47` | `deltaQld` is monotone in its constant and error arguments. | `14:1402` | `lem:delta-qld-mono-support`, `ch16:1730` (stmt ✓, proof ✓) | S | support |
| `MIPStarRE.QPBT.idealState` | `MIPStarRE/QPBT/Test/SoundnessDefs.lean:85` | The target state: an auxiliary state tensored with `M = 2^m` qudit EPR pairs. | `def:EPR`, `04:946-955` | — | S | no |
| `MIPStarRE.QPBT.PauliSoundnessWitness` | `MIPStarRE/QPBT/Test/SoundnessDefs.lean:164` | The data the conclusion produces: the two local isometries and the auxiliary state. | `thm:pauli`, `08:1431-1445` | — | S | no |
| `MIPStarRE.QPBT.pauliOperatorDistanceA` | `MIPStarRE/QPBT/Test/SoundnessDefs.lean:187` | Alice's squared operator distance between her transported Pauli family and the ideal one, on the ideal state. | `def:povm-distance`, `06:258-271` | — | S | no |
| `MIPStarRE.QPBT.pauliOperatorDistanceB` | `MIPStarRE/QPBT/Test/SoundnessDefs.lean:199` | Bob's counterpart. | `def:povm-distance`, `06:258-271` | — | S | no |
| `MIPStarRE.QPBT.pauli_soundness_deltaQld_ofExtractionWitness` | `MIPStarRE/QPBT/Test/Soundness/OperatorTransfer.lean:248` | From an extraction witness, the three soundness estimates at scale `deltaQld`. | — | — | S | support |
| `MIPStarRE.QPBT.exists_projective_setting_isometry_bounds` | `MIPStarRE/QPBT/Test/Soundness/ProjectiveSetting.lean:37` | The soundness conclusion for **projective** strategies. | `thm:pauli`, `08:1431-1445`; `14:1862-1876` | `thm:pauli-projective-setting-isometry-support`, `ch16:1458` (stmt ✓, proof ✓) | S | support |
| `MIPStarRE.QPBT.exists_arbitrary_strategy_isometry_bounds` | `MIPStarRE/QPBT/Test/Soundness/NaimarkAssembly.lean:47` | The same for an **arbitrary** strategy, via Naimark dilation — this is what drops the projectivity assumption. | `thm:pauli`, `08:1431-1445` | `thm:pauli-arbitrary-strategy-isometry-support`, `ch16:1576` (stmt ✓, proof ✓) | S | support |
| `MIPStarRE.QPBT.pauli_isometry_bounds_extend_epsilon` | `MIPStarRE/QPBT/Test/Soundness/EpsReduction.lean:101` | Extension of the conclusion to every `ε ≥ 0`, including the range where the bound is vacuous. | `thm:pauli`, `08:1431-1445`; `14:1862-1876` | — | S | support |

[^vacuity]: A reviewer's fair question is whether the conclusion is ever
    non-trivial. The constants `a, b` are existentially quantified exactly as in
    the paper, and **no declaration in this tree exhibits a regime with
    `deltaQld < 1`.** The hypotheses are satisfiable — `introParams`
    (`CanonicalParams.lean:105`) is an admissible tuple and `exists_spcc_value_one`
    gives a value-1 strategy — but the strength of the conclusion is inherited
    from the source, not established here.

---

## 5. Winning implications, commutation and anticommutation

The Pauli basis test's subtests are read off the win predicate by the `win_*`
family: each says that a strategy of value `1 - ε` satisfies the corresponding
subtest up to a controlled error. All of them are covered by one documented
correction,
[`qpbt_win-implications-corrections.tex`](paper-gaps/qpbt_win-implications-corrections.tex),
which repairs the conditioning phase, a circular parameter reduction, the
zero-direction completion, reversed observable indices, and a label typo.

| Lean declaration | file:line | What it says | Paper | Blueprint | Ax | Differs? |
|---|---|---|---|---|---|---|
| `MIPStarRE.QPBT.win_cons` | `MIPStarRE/QPBT/Observables/WinImplications.lean:34` | Success implies the consistency subtest passes. | `lem:qld-win-implications`, `14:197-228` | `lem:qld-win-implications`, `ch14:667` (stmt ✓, proof ✓) | S | correction: [`qpbt_win-implications-corrections`](paper-gaps/qpbt_win-implications-corrections.tex) |
| `MIPStarRE.QPBT.win_low_degree` | `MIPStarRE/QPBT/Observables/WinImplications.lean:50` | Success implies the low individual degree subtest passes. | `lem:qld-win-implications`, `14:197-228` | `lem:qld-win-implications`, `ch14:667` (stmt ✓, proof ✓) | S | correction: same note |
| `MIPStarRE.QPBT.win_comm` | `MIPStarRE/QPBT/Observables/WinImplications.lean:79` | Success implies the **commutation** subtest passes. | `lem:qld-win-implications`, `14:197-228` | `lem:qld-win-implications`, `ch14:667` (stmt ✓, proof ✓) | S | correction: same note |
| `MIPStarRE.QPBT.win_comm_cons` | `MIPStarRE/QPBT/Observables/WinImplications.lean:93` | Success implies the commutation-consistency subtest passes. | `lem:qld-win-implications`, `14:197-228` | `lem:qld-win-implications`, `ch14:667` (stmt ✓, proof ✓) | S | correction: same note |
| `MIPStarRE.QPBT.win_magic_square` | `MIPStarRE/QPBT/Observables/WinImplications.lean:111` | Success implies the embedded **Magic Square** (anticommutation) subtest passes. | `lem:qld-win-implications`, `14:197-228` | `lem:qld-win-implications`, `ch14:667` (stmt ✓, proof ✓) | S | correction: same note |
| `MIPStarRE.QPBT.win_ms_cons` | `MIPStarRE/QPBT/Observables/WinImplications.lean:123` | Success implies the Magic-Square-consistency subtest passes. | `lem:qld-win-implications`, `14:197-228` | `lem:qld-win-implications`, `ch14:667` (stmt ✓, proof ✓) | S | correction: same note |
| `MIPStarRE.QPBT.ProjectiveSetting` | `MIPStarRE/QPBT/Observables/Defs.lean:49` | The working setting of the analysis: a projective strategy of value at least `1 - ε` for the test, with its expanded state. | — | `def:strategy-observables`, `ch14:582` (stmt ✓) | S | no |
| `MIPStarRE.QPBT.ProjectiveSetting.pointObs` | `MIPStarRE/QPBT/Observables/Defs.lean:614` | The `±1` point observables extracted from the point measurements. | — | `def:strategy-observables`, `ch14:582` (stmt ✓) | S | no |
| `MIPStarRE.QPBT.pointObs_self_consistent` | `MIPStarRE/QPBT/Observables/WinImplications.lean:275` | The point observables of the two players agree on the state up to a controlled defect. | `lem:qld-win-implications-obs`, `14:267-284` | `lem:qld-win-implications-obs`, `ch14:1049` (stmt ✓, proof ✓) | S | correction: [`qpbt_win-implications-corrections`](paper-gaps/qpbt_win-implications-corrections.tex) |
| `MIPStarRE.QPBT.pointObs_twisted_commutation` | `MIPStarRE/QPBT/Observables/WinImplications.lean:293` | The **twisted commutation** relation for the point observables, on average and up to a controlled defect. | `lem:qld-win-implications-obs`, `14:267-284` | `lem:qld-win-implications-obs`, `ch14:1049` (stmt ✓, proof ✓) | S | correction: same note |
| `MIPStarRE.QPBT.ProjectiveSetting.exists_twistedCommutator_avg_le` | `MIPStarRE/QPBT/Observables/ExpandedCommutation.lean:188` | The averaged twisted-commutator bound in the expanded picture. | — | — | S | support |
| `MIPStarRE.QPBT.IsAnticommuting` | `MIPStarRE/QPBT/Observables/Anticommuting.lean:34` | A tuple of observables pairwise anticommutes. | — | `def:anticommuting-tuple`, `ch14:132` (stmt ✓) | S | no |
| `MIPStarRE.QPBT.anticommProb_ge_of_one_le_md` | `MIPStarRE/QPBT/Observables/Anticommuting.lean:442` | The lower bound on the probability that a random pair of the sampled tuple anticommutes. | `fact:omega-anticomm-prob`, `14:70-78` | `fact:omega-anticomm-prob`, `ch14:159` (stmt ✓, proof ✓) | S | correction: [`qpbt_anticommuting-probability`](paper-gaps/qpbt_anticommuting-probability.tex); hypothesis: `1 ≤ m·d` [^md] |
| `MIPStarRE.QPBT.exists_deltaAnticom` | `MIPStarRE/QPBT/Observables/PointConsistency.lean:768` | Existence of the polynomial anticommutation-consistency error function for the point observables. | `lem:qld-comm-cons`, `14:462-486` | `lem:qld-comm-cons`, `ch14:1508` (stmt ✓, proof ✓) | S | correction: [`qpbt_polynomial-error-square-root`](paper-gaps/qpbt_polynomial-error-square-root.tex) |

[^md]: Lean's `ℕ` contains `0`, which the source's positive-integer parameter
    domain does not; the hypothesis restores the source domain rather than
    weakening the statement. The register records that both opening assertions
    of the printed proof are refuted inside that domain while the printed bounds
    themselves hold throughout it.

---

## 6. Combining the two bases, and extraction

| Lean declaration | file:line | What it says | Paper | Blueprint | Ax | Differs? |
|---|---|---|---|---|---|---|
| `MIPStarRE.QPBT.exists_combinedLinesWitness` | `MIPStarRE/QPBT/Combining/Lines.lean:141` | The X and Z line measurements can be combined into a single line measurement with a polynomially controlled consistency error. | `lem:qld-xz-lines`, `14:882-894` | `lem:qld-xz-lines`, `ch15:1724` (stmt —, proof —) | S | correction: [`qpbt_combined-lines-error-term`](paper-gaps/qpbt_combined-lines-error-term.tex), [`qpbt_pasting-product-error`](paper-gaps/qpbt_pasting-product-error.tex) [^unmarked] |
| `MIPStarRE.QPBT.restricted_lines_consistency_bound` | `MIPStarRE/QPBT/Combining/Lines.lean:274` | The consistency defect of the restricted-line mixture is bounded by the mixture of the coordinate defects. | `14:1058-1061` | `thm:conditional-restricted-lines-consistency`, `ch15:2939` (stmt ✓, proof ✓) | S | support |
| `MIPStarRE.QPBT.exists_subLineWitness` | `MIPStarRE/QPBT/Combining/Lines.lean:326` | Existence of the sub-line measurements the combining argument restricts to. | `lem:qld-sublines`, `14:1063-1069` | `lem:qld-sublines-direct`, `ch15:3235` (stmt ✓, proof ✓) | S | correction: [`qpbt_ld-dimension-divisibility`](paper-gaps/qpbt_ld-dimension-divisibility.tex) [^direct] |
| `MIPStarRE.QPBT.exists_extendedLinesWitness_established` | `MIPStarRE/QPBT/Combining/Apply.lean:237` | Extended-line measurements with the error `C·m·poly(ε, md/q)` that the source's first derivation actually delivers. | `lem:qld-4-13`, `14:1020-1034` | `lem:qld-4-13-established`, `ch15:4508` (stmt ✓, proof ✓) | S | correction: [`qpbt_combined-lines-error-term`](paper-gaps/qpbt_combined-lines-error-term.tex) [^established] |
| `MIPStarRE.QPBT.not_exists_combining_quarter_power_bound` | `MIPStarRE/QPBT/Combining/ErrorObstruction.lean:37` | The first route's `m·ε^(1/4)` term provably cannot be absorbed into the printed arguments — an obstruction to that route, not a refutation of the printed assertion. | — | `lem:qld-combining-quarter-power-obstruction`, `ch15:4372` (stmt ✓, proof ✓) | S | support |
| `MIPStarRE.QPBT.exists_globalPairWitness` | `MIPStarRE/QPBT/Combining/Apply.lean:280` | The global polynomial-pair construction: a single pair of low-degree polynomials consistent with both players' point measurements. | `lem:qld-4-7`, `14:1267-1274` | `lem:qld-4-7`, `ch15:4818` (stmt ✓, proof ✓) | S | correction: [`qpbt_ld-dimension-divisibility`](paper-gaps/qpbt_ld-dimension-divisibility.tex) [^direct] |
| `MIPStarRE.QPBT.exists_actual_rounded_global_pair_error_bound` | `MIPStarRE/QPBT/Combining/ActualErrorBounds.lean:90` | The rounded error bound actually carried by the global-pair construction. | — | `thm:qld-actual-rounded-error-bound`, `ch15:6569` (stmt ✓, proof ✓) | S | support |
| `MIPStarRE.QPBT.tildeObs` | `MIPStarRE/QPBT/Extraction/Observables.lean:158` | The extracted ideal Pauli observables `W̃` on the extraction registers. | — | `def:tilde-w-observables`, `ch16:186` (stmt ✓) | S | no |
| `MIPStarRE.QPBT.tildeObs_twisted_commutation` | `MIPStarRE/QPBT/Extraction/Observables.lean:331` | The extracted observables satisfy the twisted commutation relation, with the full trace phase. | `14:1451-1456` | `lem:tildew-product-form`, `ch16:199` (stmt ✓, proof ✓) | S | correction: [`qpbt_cross-basis-phase`](paper-gaps/qpbt_cross-basis-phase.tex) |
| `MIPStarRE.QPBT.exists_pulled_apart_consistency` | `MIPStarRE/QPBT/Extraction/Construction.lean:46` | Pulling the X and Z measurements apart: the extracted measurements are consistent with the point measurements. | `lem:qld-construct-the-paulis`, `14:1463-1481` | `lem:qld-construct-the-paulis`, `ch16:241` (stmt ✓, proof ✓) | S | correction: [`qpbt_extraction-transfer`](paper-gaps/qpbt_extraction-transfer.tex), [`qpbt_decoding-identity`](paper-gaps/qpbt_decoding-identity.tex) |
| `MIPStarRE.QPBT.exists_extraction_aux_ofGlobalPairWitness` | `MIPStarRE/QPBT/Extraction/StateExtraction.lean:109` | The auxiliary state extraction, from a global-pair witness. | — | — | S | support |
| `MIPStarRE.QPBT.exists_extractionWitness` | `MIPStarRE/QPBT/Extraction/SourceUnitary.lean:34` | **The extraction-to-soundness bridge.** For every admissible tuple, every `0 ≤ ε ≤ 1` and every projective setting: a global-pair witness together with an extraction witness — the two swap unitaries, the auxiliary state and the Pauli transport — at the nested construction/extraction scale. This is the assembly the soundness layer consumes: `exists_projective_setting_isometry_bounds` (section 4) discharges its hypotheses from exactly this theorem (`Soundness/ProjectiveSetting.lean:48`). | `lem:qld-unitary`, `14:1669-1685` | `lem:qld-unitary`, `ch16:767` (stmt ✓, proof ✓) | S | correction: [`qpbt_extraction-transfer`](paper-gaps/qpbt_extraction-transfer.tex), [`qpbt_ld-dimension-divisibility`](paper-gaps/qpbt_ld-dimension-divisibility.tex) [^direct] [^transfer] |

[^transfer]: The Lean statement is the *unitary* conclusion of the source
    lemma. The subsequent range-projection step that turns those unitaries into
    the isometries of the printed soundness theorem is not asserted here; the
    blueprint node records the same separation, and the gap note carries it.

[^unmarked]: This is the one node in the chain whose blueprint entry carries
    **neither** a statement-level nor a proof-level `\leanok`, and that is
    deliberate: the Lean carrier uses the directly indexed line space and the
    corrected two-variable error contract `IsPolyErr₂` (sum form
    `C·(x^r + y^s)` rather than the source's product form), so it is not
    advertised as the source-labelled lemma.

[^direct]: The Lean carriers realize dimension `2m+2` by direct index sampling
    rather than the source's seed indexing, because the source's condition
    `2m+2 ∣ q` is unsatisfiable. The blueprint keeps the source-shaped nodes and
    marks the blocked steps instead of adding the impossible hypothesis. The
    source's own construction proofs for `lem:qld-4-7` remain open.

[^established]: The printed error form `poly(m²ε, md/q)` is **not** proved; see
    section 7. `exists_extendedLinesWitness_established` is the form the first
    derivation really yields, and it is what the rest of the chain consumes.

---

## 7. The two printed claims recorded as non-asserted `Prop`s

Two sentences of the source could not be proved as printed and are not known to
be false as mathematics. Rather than delete them, weaken them silently, or leave
a `sorry` behind, each is recorded as a **`Prop`-valued definition**: the printed
statement stays in the Lean tree, in the source's own words, and is never
asserted. Stating a proposition is not proving it, so nothing downstream depends
on either, and neither site carries proof debt.

Both landed on 2026-09-19 and are the reason the tree now has zero `sorry`.

### 7.1 The printed form of `lem:qld-4-13`

| | |
|---|---|
| Printed claim, unasserted | `MIPStarRE.QPBT.PrintedExtendedLinesWitnessClaim`, `MIPStarRE/QPBT/Combining/Apply.lean:108` |
| Paper | `lem:qld-4-13`, `14:1020-1034` |
| Blueprint | `lem:qld-4-13`, `ch15:2768` — no statement-level `\leanok` |
| What it claims | Extended-line measurements at the error `poly(m²ε, md/q)`. |
| Why it is not proved | Neither of the two derivations printed in the source delivers that error. The first yields `C·m·poly(ε, md/q)`; the second would yield `m²·poly(ε, md/q)` and additionally relies on a distributional decomposition the cited sub-line lemma does not supply. |
| Proved corrected form | `MIPStarRE.QPBT.exists_extendedLinesWitness_established`, `MIPStarRE/QPBT/Combining/Apply.lean:237` — the first route's error form, and what the rest of the chain uses. |
| Obstruction, proved | `MIPStarRE.QPBT.not_exists_combining_quarter_power_bound`, `MIPStarRE/QPBT/Combining/ErrorObstruction.lean:37` — the `m·ε^(1/4)` term cannot be absorbed into the printed arguments. |
| Note / issue | [`qpbt_combined-lines-error-term.tex`](paper-gaps/qpbt_combined-lines-error-term.tex), issue #598; landed in PR 633. |

### 7.2 The printed form of `lem:symmetric-strat`

| | |
|---|---|
| Printed claim, unasserted | `MIPStarRE.QPBT.PrintedSymmetricProjectiveAttainmentClaim`, `MIPStarRE/QPBT/Games/StrategyClasses.lean:901` |
| Paper | `lem:symmetric-strat`, `06:94-99` |
| Blueprint | `lem:symmetric-strat-printed-claim`, `ch12:165` (stmt ✓, proof ✓) |
| What it claims | A game of value exactly `1 - ε` has a symmetric projective strategy *attaining* value `1 - ε`. |
| Why it is not proved | Two independent defects. The source's argument builds a strategy above every strict lower bound and never at the bound, so the printed sentence asserts that a supremum over unbounded finite dimension is attained — which the source does not establish. And on the Lean domain, where the answer alphabet may be empty, the printed sentence is outright **false** at `ε = 1`. |
| Proved corrected form | `MIPStarRE.QPBT.exists_symmetric_projective_strategy_approx`, `MIPStarRE/QPBT/Games/Symmetrization.lean:139` — for every `ε' > ε`, with `Nonempty G.Answer`; with the slack form `exists_symmetric_projective_strategy_of_lt_value` (`Symmetrization.lean:110`). |
| Refutation, proved | `MIPStarRE.QPBT.not_forall_printedSymmetricProjectiveAttainmentClaim`, `MIPStarRE/QPBT/Games/StrategyClasses.lean:952`, from the empty-answer game `SymmetrizationObstruction.emptyAnswerGame` (`StrategyClasses.lean:915`). |
| Note / issue | [`qpbt_symmetrization-attainment.tex`](paper-gaps/qpbt_symmetrization-attainment.tex), issue #524; landed in PR 634. |

---

## 8. Axioms

Every theorem listed above was checked with `#print axioms` against this commit.
The result is uniform: **the three standard Lean axioms and nothing else**. No
declaration depends on `sorryAx`, and the Lean tree declares no axiom of its
own: at this commit `MIPStarRE/` contains zero `axiom` declarations and zero
`sorry` occurrences outside prose.

The two `P` rows, `AdmissibleParams` and `LdParams`, are structure *types*; a
structure's type constant needs only `propext`. Their projections and every
theorem about them are `S`. `pauliBasisTestSymm` is marked `—` because it was
added to this index from the completeness node and is not in the probe list
below; it is reachable from `exists_spcc_value_one`, which is `S`.

### Regenerating this column

The probe deliberately lives **outside** the worktree, so that the index can be
checked without adding a module to the build:

```bash
# in a warm checkout of this commit
lake env lean scripts/probe/AxiomProbe.lean
```

where the probe is a file importing `MIPStarRE.QPBT` and listing the names. The
minimal form for a single declaration is:

```lean
import MIPStarRE.QPBT
#print axioms MIPStarRE.QPBT.pauli_soundness
-- 'MIPStarRE.QPBT.pauli_soundness' depends on axioms: [propext, Classical.choice, Quot.sound]
```

Two cautions, both learned while producing this index:

1. `lake env lean` **does not rebuild**. If the `.lake/build` oleans are older
   than the checkout, the probe silently reports on the stale environment. Build
   the modules first (`lake build MIPStarRE.QPBT.…`) and only then run the probe.
2. A name that is missing from the environment is a signal, not a nuisance: it
   means the module holding it was not rebuilt.

### Raw output

Produced by the probe at commit `c6c8c2f2d34add9aebf15872f50a0f18039e4d46`.
Format: `AX <requested name> <resolved name> [<axioms>]`. The final row,
`exists_extractionWitness`, was probed in a later run when that declaration was
added to the index; no `.lean` file changed between the two runs, so it reports
on the same Lean tree as the rest.

```text
AX	Game	MIPStarRE.QPBT.Game	[propext, Classical.choice, Quot.sound]
AX	Strategy	MIPStarRE.QPBT.Strategy	[propext, Classical.choice, Quot.sound]
AX	Strategy.value	MIPStarRE.QPBT.Strategy.value	[propext, Classical.choice, Quot.sound]
AX	Game.value	MIPStarRE.QPBT.Game.value	[propext, Classical.choice, Quot.sound]
AX	Strategy.value_le_one	MIPStarRE.QPBT.Strategy.value_le_one	[propext, Classical.choice, Quot.sound]
AX	Strategy.value_le_game_value	MIPStarRE.QPBT.Strategy.value_le_game_value	[propext, Classical.choice, Quot.sound]
AX	Strategy.IsProjective	MIPStarRE.QPBT.Strategy.IsProjective	[propext, Classical.choice, Quot.sound]
AX	SymmetricGame	MIPStarRE.QPBT.SymmetricGame	[propext, Classical.choice, Quot.sound]
AX	SymmetricStrategy	MIPStarRE.QPBT.SymmetricStrategy	[propext, Classical.choice, Quot.sound]
AX	Strategy.IsPCC	MIPStarRE.QPBT.Strategy.IsPCC	[propext, Classical.choice, Quot.sound]
AX	SymmetricStrategy.IsSPCC	MIPStarRE.QPBT.SymmetricStrategy.IsSPCC	[propext, Classical.choice, Quot.sound]
AX	AdmissibleParams	MIPStarRE.QPBT.AdmissibleParams	[propext]
AX	pauliQuestionDistribution	MIPStarRE.QPBT.pauliQuestionDistribution	[propext, Classical.choice, Quot.sound]
AX	pauliWinPredicate	MIPStarRE.QPBT.pauliWinPredicate	[propext, Classical.choice, Quot.sound]
AX	pauliBasisTest	MIPStarRE.QPBT.pauliBasisTest	[propext, Classical.choice, Quot.sound]
AX	LdParams	MIPStarRE.QPBT.LdParams	[propext]
AX	ldGame	MIPStarRE.QPBT.ldGame	[propext, Classical.choice, Quot.sound]
AX	deltaQld	MIPStarRE.QPBT.deltaQld	[propext, Classical.choice, Quot.sound]
AX	deltaQld_mono	MIPStarRE.QPBT.deltaQld_mono	[propext, Classical.choice, Quot.sound]
AX	idealState	MIPStarRE.QPBT.idealState	[propext, Classical.choice, Quot.sound]
AX	PauliSoundnessWitness	MIPStarRE.QPBT.PauliSoundnessWitness	[propext, Classical.choice, Quot.sound]
AX	pauliOperatorDistanceA	MIPStarRE.QPBT.pauliOperatorDistanceA	[propext, Classical.choice, Quot.sound]
AX	pauliOperatorDistanceB	MIPStarRE.QPBT.pauliOperatorDistanceB	[propext, Classical.choice, Quot.sound]
AX	introParams	MIPStarRE.QPBT.introParams	[propext, Classical.choice, Quot.sound]
AX	introParamsTuple_isAdmissible	MIPStarRE.QPBT.introParamsTuple_isAdmissible	[propext, Classical.choice, Quot.sound]
AX	exists_deltaQld_introParams_bound	MIPStarRE.QPBT.exists_deltaQld_introParams_bound	[propext, Classical.choice, Quot.sound]
AX	IsAnticommuting	MIPStarRE.QPBT.IsAnticommuting	[propext, Classical.choice, Quot.sound]
AX	IsCommuting	MIPStarRE.QPBT.IsCommuting	[propext, Classical.choice, Quot.sound]
AX	IsCommuting	MIPStarRE.QPBT.Strategy.IsCommuting	[propext, Classical.choice, Quot.sound]
AX	ProjectiveSetting	MIPStarRE.QPBT.ProjectiveSetting	[propext, Classical.choice, Quot.sound]
AX	pointObs	MIPStarRE.QPBT.ProjectiveSetting.pointObs	[propext, Classical.choice, Quot.sound]
AX	tildeObs	MIPStarRE.QPBT.tildeObs	[propext, Classical.choice, Quot.sound]
AX	pauli_soundness	MIPStarRE.QPBT.pauli_soundness	[propext, Classical.choice, Quot.sound]
AX	pauli_soundness_qubit	MIPStarRE.QPBT.pauli_soundness_qubit	[propext, Classical.choice, Quot.sound]
AX	exists_ld_soundness	MIPStarRE.QPBT.exists_ld_soundness	[propext, Classical.choice, Quot.sound]
AX	exists_spcc_value_one	MIPStarRE.QPBT.exists_spcc_value_one	[propext, Classical.choice, Quot.sound]
AX	honestStrategy_isSPCC	MIPStarRE.QPBT.honestStrategy_isSPCC	[propext, Classical.choice, Quot.sound]
AX	exists_arbitrary_strategy_isometry_bounds	MIPStarRE.QPBT.exists_arbitrary_strategy_isometry_bounds	[propext, Classical.choice, Quot.sound]
AX	exists_projective_setting_isometry_bounds	MIPStarRE.QPBT.exists_projective_setting_isometry_bounds	[propext, Classical.choice, Quot.sound]
AX	pauli_soundness_deltaQld_ofExtractionWitness	MIPStarRE.QPBT.pauli_soundness_deltaQld_ofExtractionWitness	[propext, Classical.choice, Quot.sound]
AX	pauli_isometry_bounds_extend_epsilon	MIPStarRE.QPBT.pauli_isometry_bounds_extend_epsilon	[propext, Classical.choice, Quot.sound]
AX	exists_symmetric_projective_strategy_approx	MIPStarRE.QPBT.exists_symmetric_projective_strategy_approx	[propext, Classical.choice, Quot.sound]
AX	exists_symmetric_projective_strategy_of_strategy	MIPStarRE.QPBT.exists_symmetric_projective_strategy_of_strategy	[propext, Classical.choice, Quot.sound]
AX	not_forall_printedSymmetricProjectiveAttainmentClaim	MIPStarRE.QPBT.not_forall_printedSymmetricProjectiveAttainmentClaim	[propext, Classical.choice, Quot.sound]
AX	PrintedSymmetricProjectiveAttainmentClaim	MIPStarRE.QPBT.PrintedSymmetricProjectiveAttainmentClaim	[propext, Classical.choice, Quot.sound]
AX	PrintedExtendedLinesWitnessClaim	MIPStarRE.QPBT.PrintedExtendedLinesWitnessClaim	[propext, Classical.choice, Quot.sound]
AX	exists_combinedLinesWitness	MIPStarRE.QPBT.exists_combinedLinesWitness	[propext, Classical.choice, Quot.sound]
AX	exists_subLineWitness	MIPStarRE.QPBT.exists_subLineWitness	[propext, Classical.choice, Quot.sound]
AX	restricted_lines_consistency_bound	MIPStarRE.QPBT.restricted_lines_consistency_bound	[propext, Classical.choice, Quot.sound]
AX	exists_extendedLinesWitness_established	MIPStarRE.QPBT.exists_extendedLinesWitness_established	[propext, Classical.choice, Quot.sound]
AX	exists_globalPairWitness	MIPStarRE.QPBT.exists_globalPairWitness	[propext, Classical.choice, Quot.sound]
AX	exists_actual_rounded_global_pair_error_bound	MIPStarRE.QPBT.exists_actual_rounded_global_pair_error_bound	[propext, Classical.choice, Quot.sound]
AX	not_exists_combining_quarter_power_bound	MIPStarRE.QPBT.not_exists_combining_quarter_power_bound	[propext, Classical.choice, Quot.sound]
AX	win_comm	MIPStarRE.QPBT.win_comm	[propext, Classical.choice, Quot.sound]
AX	win_comm	MIPStarRE.QPBT.WinImplications.win_comm	[propext, Classical.choice, Quot.sound]
AX	win_comm_cons	MIPStarRE.QPBT.win_comm_cons	[propext, Classical.choice, Quot.sound]
AX	win_comm_cons	MIPStarRE.QPBT.WinImplications.win_comm_cons	[propext, Classical.choice, Quot.sound]
AX	win_magic_square	MIPStarRE.QPBT.win_magic_square	[propext, Classical.choice, Quot.sound]
AX	win_magic_square	MIPStarRE.QPBT.WinImplications.win_magic_square	[propext, Classical.choice, Quot.sound]
AX	win_ms_cons	MIPStarRE.QPBT.WinImplications.win_ms_cons	[propext, Classical.choice, Quot.sound]
AX	win_ms_cons	MIPStarRE.QPBT.win_ms_cons	[propext, Classical.choice, Quot.sound]
AX	win_cons	MIPStarRE.QPBT.WinImplications.win_cons	[propext, Classical.choice, Quot.sound]
AX	win_cons	MIPStarRE.QPBT.win_cons	[propext, Classical.choice, Quot.sound]
AX	win_low_degree	MIPStarRE.QPBT.win_low_degree	[propext, Classical.choice, Quot.sound]
AX	win_low_degree	MIPStarRE.QPBT.WinImplications.win_low_degree	[propext, Classical.choice, Quot.sound]
AX	pointObs_self_consistent	MIPStarRE.QPBT.pointObs_self_consistent	[propext, Classical.choice, Quot.sound]
AX	pointObs_twisted_commutation	MIPStarRE.QPBT.pointObs_twisted_commutation	[propext, Classical.choice, Quot.sound]
AX	exists_deltaAnticom	MIPStarRE.QPBT.exists_deltaAnticom	[propext, Classical.choice, Quot.sound]
AX	exists_twistedCommutator_avg_le	MIPStarRE.QPBT.ProjectiveSetting.exists_twistedCommutator_avg_le	[propext, Classical.choice, Quot.sound]
AX	anticommProb_ge_of_one_le_md	MIPStarRE.QPBT.anticommProb_ge_of_one_le_md	[propext, Classical.choice, Quot.sound]
AX	tildeObs_twisted_commutation	MIPStarRE.QPBT.tildeObs_twisted_commutation	[propext, Classical.choice, Quot.sound]
AX	exists_pulled_apart_consistency	MIPStarRE.QPBT.exists_pulled_apart_consistency	[propext, Classical.choice, Quot.sound]
AX	exists_extraction_aux_ofGlobalPairWitness	MIPStarRE.QPBT.exists_extraction_aux_ofGlobalPairWitness	[propext, Classical.choice, Quot.sound]
AX	exists_extractionWitness	MIPStarRE.QPBT.exists_extractionWitness	[propext, Classical.choice, Quot.sound]
```

---

## 9. What this index does not cover

- The **LDT** track (`MIPStarRE/LDT/`), which QPBT imports for the classical
  low individual degree machinery, and the `MIPStarRE/Quantum/` support layer.
- The QPBT declarations not on the path from the definitions to
  `pauli_soundness` — the great majority of the tree. The full declaration ↔
  blueprint cross-reference is `blueprint/lean_decls` (1,006 entries at this
  commit).
- Non-triviality of the conclusion: see the note under `deltaQld` in section 4.
- The full deviation list. This index names the notes that touch the chain
  above; the complete register is
  [`docs/paper-gaps/qpbt-gap-register.md`](paper-gaps/qpbt-gap-register.md).
