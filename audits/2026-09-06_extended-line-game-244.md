# Extended-line game construction: packet #244

Date: 2026-09-06. Parent construction dependency: issue #119.

## Mathematical scope

The source is the first paragraph of the proof of `lem:qld-4-7`,
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1279-1288`,
within the requested passage at lines 1267–1402. Its input is the line
measurement conclusion of `lem:qld-4-13`, lines 1020–1034, together with
the joint point measurements. The active blueprint discusses this step at
`lem:qld-4-7` and `rem:qld-4-7-divisibility`.

This packet takes an **existing** `ExtendedLinesWitness` and constructs
measurements and a strategy from it. It does not construct that witness,
assert that it exists, or close issue #119. No issue lifecycle operation was
performed. There is no change to `Apply.lean`, `Lines.lean`, the scalar
construction work of issue #118, or the shared blueprint.

Write `D = P.extendedDirectLd` and `c = md + 1`. The parameter tuple is the
merged directly indexed game with dimension `2m+2` and simultaneity `1`.
No assertion `(2m+2) ∣ q` is introduced. The existing correction is documented
in `docs/paper-gaps/qpbt_ld-dimension-divisibility.tex`.

## Proved construction increments

All new Lean declarations are in the namespace
`MIPStarRE.QPBT.ExtendedLineGame`, in
`MIPStarRE/QPBT/Combining/ExtendedLineGame.lean`.

1. `directEvalOpt_eq_some_iff` characterizes successful completed evaluation
   by membership in the line and agreement at **every** presenting parameter.
   In particular, it applies to zero-direction lines without interpreting
   `none` as a field value.
2. `axisRead` truncates coefficients to degree `d`. `axisRead_eval` proves
   evaluation preservation when the omitted coefficients vanish.
   `axisRead_eval_of_effect_ne_zero` and
   `axisAnswer_win_iff_of_effect_ne_zero` discharge that support condition
   directly from `lines.axis_degree`.
3. `diagonalRead` extends the degree-`c` coefficient list by zeros to degree
   `D.m * D.d`. The inequality `c ≤ (2m+2)d` follows from admissibility.
   `diagonalRead_eval` proves exact evaluation preservation.
4. `axis_description_canonical` and `diagonal_description_canonical` show
   that reading the already canonical game question does not change the
   measured line. `axisAnswer_win_iff` and `diagonalAnswer_win_iff` identify
   the line–point verifier with the completed-evaluation check. The diagonal
   statement includes zero directions.
5. `answerMeasurement` is the concrete question-dependent measurement:
   joint-point linear coarse-graining followed by scalar-field transport,
   truncated axis answers, and extended diagonal answers. Wrong-tag effects
   vanish. Point projectivity follows from `points.projective` and the merged
   postprocessing theorem; the unfinished `extendedQ_spec` is not invoked.
6. `pairState` is the shuffle of the original bipartite state tensored with
   **one** EPR pair. It lives on the two expanded local spaces and is proved
   normalized. `strategy` uses precisely that state and `answerMeasurement`.
   It does not identify the six-register state with a vector of smaller type.
7. `mixed_branch_rejection_eq_zero` proves that both ordered mixed line-type
   branches have zero rejection. `strategy_value_eq` gives the exact value
   formula retaining all seven other branches. If `B(s,t)` denotes the
   branch rejection probability, the formula is

   ```text
   value = 1 - [B(p,p) + B(p,a) + B(p,d) + B(a,p)
                + B(a,a) + B(d,p) + B(d,d)] / 9.
   ```

   In particular, the coefficient-equality checks `B(a,a)` and `B(d,d)`
   have not been discarded or replaced by evaluated-answer agreement.
8. `completedLinePointDefect_sums_le` derives the two bounds
   `C_A(axis) + C_A(diagonal) ≤ 2 deltaL` and
   `C_B(axis) + C_B(diagonal) ≤ 2 deltaL` from the actual two consistency
   fields. Here `C_A` and `C_B` are still correlations on the six-register
   state, in placements `AA', BA''` and `BB', AB''`, respectively.
   `completedLinePointDefect_eq_half_sum` supplies the exact averaging
   identity. These bounds are not mislabeled as game-value estimates.
9. `projectiveStrategy` explicitly applies the merged public Naimark APIs.
   `projectiveStrategy_isProjective` and `projectiveStrategy_value` prove
   projectivity and **exact preservation of the constructed strategy's
   value**. Neither theorem assumes or asserts that this value is large.

## Statement-integrity audit

- **Paper assumptions:** the preceding construction supplies extended-line
  POVMs, axis degree support, the two oriented line–point consistency
  relations, and joint projective point measurements.
- **Lean assumptions:** the corresponding existing `ExtendedLinesWitness`
  and `CombinedPointsWitness`, indexed by the original admissible parameters
  and setting. No passing-game premise, witness producer, or quantitative
  assumption bundle is added. The local nonzero-effect premise in the axis
  lemma expresses support; its degree consequence is proved from the witness.
- **Paper conclusion:** a passing low-degree strategy, followed by
  projectivization and low-degree soundness, eventually producing the global
  polynomial-pair measurement of `lem:qld-4-7`.
- **Lean conclusion:** only the explicit strategy, faithful answer conversion,
  exact branch accounting, the two six-register defect-sum bounds, and exact
  Naimark value transport listed above.
- **Verdict:** faithful boundary hypotheses for these construction increments.
  This is **not** a formalization of the entire source theorem. No existing
  paper-labelled theorem is restated, and no source-labelled blueprint entry
  acquires `leanok`.

## Remaining obligations and their mathematical location

There is no introduced `sorry`, `admit`, or axiom declaration in this packet.
The following missing results are not hidden in theorem hypotheses.

1. **Register-correlation transport.** For arbitrary local operators, relate
   their tensor correlation on `pairState` to the `AA', BA''` product on
   `psiHat`, and separately to the `AB'', BB'` product. The first identity
   removes the spectator `B'B''` pair; the second removes `A'A''` and uses
   EPR symmetry. Without both identities, the two witness fields do not yet
   establish rejection bounds for `strategy`. Runtime exploration did not
   complete these matrix-placement identities; no partial proof is committed.
2. **Measurement and distribution transport.** Combine those identities with
   the proved coefficient/evaluation lemmas, finite-sum postprocessing, and
   the uniform question laws to identify all four line–point branch weights.
   Derive point–point consistency from the supplied joint-point witness,
   rather than invoking its unfinished producer or `extendedQ_spec`.
3. **Same-line coefficient agreement.** Prove the independent-parameter
   resampling law, including zero directions, and specialize the merged
   codeword-consistency estimate to bounded coefficient lists. The
   polynomial collision estimate and the consistency triangle must bound
   the two same-type branches left visible in `strategy_value_eq`.
4. **Passing value.** Assemble the seven branch bounds into a lower bound
   for `strategy.value`; then `projectiveStrategy_value` transports that
   bound without loss. No such lower bound is claimed here.

These are the construction and completed-answer transport obligations of
issue #119, also described in
`docs/paper-gaps/qpbt_ld-dimension-divisibility.tex` and
`docs/paper-gaps/qpbt_combined-lines-error-term.tex`. Soundness, compression
and fixed-space rounding, noncombined-polynomial mass, and the eventual
global-pair witness remain outside this packet's proved conclusions.

## Validation

- Hooks were installed and `scripts/install_git_hooks.sh --check` passed.
- The initial single-file check of `Combining/Points.lean` succeeded with its
  two existing proof-hole warnings; neither theorem is called by this packet.
- The new file type-checks without warnings against the worktree's imported
  objects; final rerun and axiom findings are recorded below.
- A full build was not run: the machine-wide full-build lock was held by
  another worktree's build operation. No bare full build, shared-cache write,
  `lake update`, main refresh, publication, CI, review, or merge was performed.
- The initial transitive axiom scan detected `sorryAx` in declarations using
  the witness type. It traced to **stale imported objects**: the compiled
  `ProjectiveSetting.expPointOp_nonneg` and
  `ProjectiveSetting.expPointOp_eq_convolution` printed direct proof holes,
  whereas the current `ExpandedDefs.lean` source contains proofs. The pure
  coefficient, verifier, and pair-state declarations had only `propext`,
  `Classical.choice`, and `Quot.sound`. A bounded, branch-private targeted
  recompilation was attempted rather than changing any upstream source.

### Final validation outcome

The stale-object problem was resolved within the branch-private build tree.
Single-file recompilation succeeded, in dependency order, for
`LDT/Basic/DistributionAvg.lean`, `QPBT/Algebra/Pauli.lean`,
`QPBT/Observables/Defs.lean`, `QPBT/Observables/ExpandedDefs.lean`,
`QPBT/Combining/Witnesses.lean`, and `QPBT/Combining/Points.lean` (all paths
under `MIPStarRE/`). Recompiling `Witnesses.lean` and `Points.lean` was also
necessary: their older objects retained the old expanded-point proof terms.
No source file in that list was changed, and all output files were written
only to this worktree's `.lake/build`.

The final `lake env lean MIPStarRE/QPBT/Combining/ExtendedLineGame.lean`
check succeeded without warnings. A further check with an explicit local
`.olean` output succeeded. A runtime `#print axioms` scan of **all 31 new
declarations** then reported only subsets of `propext`, `Classical.choice`,
and `Quot.sound`; there was no `sorryAx`. Thus the earlier cached proof-hole
finding is resolved, not an outstanding source obligation of this packet.

`rg -n "sorry|axiom" MIPStarRE/QPBT/Combining/ExtendedLineGame.lean`
returned no matches. The wider forbidden-token scan, 100-character Lean
line-length check, and whitespace check also returned no findings.
Runtime logs are in `~/.cache/mipstarre-dev/issue-244/`, notably
`final-axioms.log` and `recheck-ExtendedLineGame.log`.

The A1–A6 integrity check finds no conclusion-shaped hypothesis, fallback
evaluation value, default existential witness, substitute axiom, or external
statement bundle. The Naimark completion outcome is the ordinary distinguished
outcome of the merged dilation construction, not a witness for the paper's
existence conclusion. A separate reviewer should begin with the boundary
between the six-register defect bounds and `strategy_value_eq`; that boundary
is precisely where the passing-game construction remains incomplete.
