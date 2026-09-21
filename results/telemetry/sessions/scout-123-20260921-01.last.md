<!-- scout: scout-123-20260921-01 2026-09-21 -->
## Mathlib scouting report — 2026-09-21

### Mathematical source

- Audited commit `05df4b74fea7d291050909102c737e6b03d85ba6`.
- Headline source: `references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:1426-1487`.
- Proof source: `references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1666-1876`.
- The theorem says that universal `a ≥ 1` and `0 < b < 1` give state and Pauli-measurement closeness at
  `a(md)^a(ε^b + q^(-b) + 2^(-bmd))` for every admissible test and successful strategy.

### Relevant Mathlib definitions

- `Real.rpow` — real exponentiation, including its zero convention
  (`Mathlib/Analysis/SpecialFunctions/Pow/Real.lean:31-51`). All bases used by the headline theorem are nonnegative, and `q,m,d` are positive, so its arbitrary negative-base behavior is irrelevant.
- `LinearIsometry` — norm-preserving linear maps
  (`Mathlib/Analysis/Normed/Operator/LinearIsometry.lean:51`), matching the paper’s local isometries.
- `Lean.collectAxioms` — transitive axiom collection, also used by Mathlib’s `assert_no_sorry`
  (`Mathlib/Util/AssertNoSorry.lean:22-27`).

### Headline statement audit

- **BLOCKER — undocumented difference.** The source compares the direct Pauli-question effects
  `A_u^(Pauli,W)` and `B_u^(Pauli,W)` (`08:913-915,1146-1163,1438-1443`;
  `14:1678-1683,1827-1858,1872-1875`). Lean instead compares the completed measurements
  `postprocess pauliAnswerOrZero` (`SoundnessDefs.lean:187-205`;
  `QubitForm.lean:121-141`). Since `pauliAnswerOrZero` sends every wrong-form answer to zero
  (`PauliBasisTest.lean:491-496`), its zero effect is the raw `.pauliOutcome 0` effect plus every
  malformed-answer effect. Such answers are rejected by the game
  (`PauliBasisTest.lean:589-599,676-720`), but they need not have zero operator.
- This completion is disclosed only in the Naimark support node
  (`blueprint/src/chapter/ch16_qpbt_extraction.tex:1515-1524`). The source-shaped blueprint statement
  still prints the direct operators (`ch13_qpbt_test.tex:1581-1598`), and the final blueprint proof
  again reasons about direct `M_h` effects (`ch16_qpbt_extraction.tex:1697-1721`).
  No gap-register row records this as a headline statement difference, and no theorem transferring
  the completed-family estimate to the raw effects was found.
- Consequently, `\leanok` on `thm:pauli` and the theorem index’s “Differs? no”
  (`docs/QPBT-theorem-index.md:80-81,175-176`) are not currently justified. A rejected-mass transfer
  may repair this, but it must be proved and absorbed into `deltaQld`; it cannot be assumed.

- **NOTE — identical.** Apart from that operator-family issue, quantifier order, constants and
  exponents agree: paper `08:1431-1445`; Lean `Soundness.lean:52-62`. Both have universal
  `a ≥ 1`, `0 < b < 1`, all admissible `(q,m,d)`, all successful strategies, both bases, and the same
  three error terms. `deltaQld` is exactly the printed formula
  (`SoundnessDefs.lean:30-38`).

- **NOTE — presentation only.** Lean explicitly assumes `0 ≤ ε`
  (`Soundness.lean:54`, `QubitForm.lean:425`). The paper does not repeat this in the theorem display,
  but uses `ε` as a nonnegative failure probability. This is a faithful domain boundary, not a
  load-bearing extra premise.

- **NOTE — presentation only.** `AdmissibleParams` explicitly stores `1 ≤ d`
  (`PauliBasisTest.lean:37-43`) and derives `1 ≤ m` (`:45-57`). The paper has
  `q,m,d ∈ ℕ` (`08:903-905`) under its convention that `ℕ` means positive integers
  (`04_preliminaries.tex:4-7`), so this matches the source domain.

- **NOTE — presentation only.** The once-for-all `FixedFieldModel` contains the field, binary basis,
  self-duality and normality data (`Algebra/FieldBasis.lean:442-470`) and is selected from a proved
  existence theorem (`:490-548`). This implements the paper’s fixed admissible field representation
  (`04:662-680`) rather than adding a public hypothesis.

- **NOTE — identical encoding.** `Strategy`, its unit state and complete POVMs
  (`Games/Defs.lean:88-98`; `Quantum/Measurement.lean:34-48`) match the paper
  (`06:26-38`). `Strategy.value` is the finite Born-rule sum (`Games/Defs.lean:217-222,489-492`),
  matching `06:40-57`; the headline theorem does not use `Game.value` or `sSup`.

- **NOTE — identical encoding.** The question law and win predicate match the source graph sampler
  and checks (`08:964-1120,1126-1225`; `PauliBasisTest.lean:234-260,407-475,589-739`).
  The tagged common answer alphabet plus rejection of wrong constructors is a presentation device.
  Its later completion into outcome zero is the separate blocker above.

- **NOTE — identical encoding.** `PauliRegister = Cube m → F_q`
  (`PauliBasisTest.lean:121-125`), with `Cube m = Fin m → Bool`
  (`Algebra/LowDegreeCode.lean:29-35`), has one field coordinate for each of the `M=2^m` qudits.
  `PauliSoundnessWitness` contains only finite auxiliary spaces, two linear isometries and a unit
  auxiliary state (`SoundnessDefs.lean:158-177`), exactly the existential data at `08:1435-1443`.

- **NOTE — identical encoding.** `idealState` is the auxiliary state tensored with the normalized
  EPR vector (`SoundnessDefs.lean:80-95`; `Algebra/Pauli.lean:506-519`), matching
  `04:946-955`. `conjIsometry` is `U M U†`, and `isometryTensor` applies both local isometries
  (`State.lean:22-55`), matching the source’s transported state and operators.

- **NOTE — presentation only.** The paper’s `≈δ` means an `O(δ)` squared family distance
  (`06:258-270`); Lean states an exact finite sum bounded by `deltaQld`
  (`SoundnessDefs.lean:182-205`). Since the universal prefactor `a` is existential, universal
  multiplicative constants can be absorbed into it.

- **NOTE — documented proof correction.** The headline paper statement and Lean both bound the
  unsquared state norm (`08:1437`; `Soundness.lean:57-58`), while the printed proof obtains a squared
  norm (`14:1673-1676,1868-1871`). The square-root adjustment is documented at
  `ch16_qpbt_extraction.tex:1726-1728` and gap-register row
  `docs/paper-gaps/qpbt-gap-register.md:21`.

- **NOTE — presentation only.** The qubit corollary is otherwise exact
  (`08:1469-1487`; `QubitForm.lean:423-445`). Its register has `2^m · basisDim` qubits
  (`QubitForm.lean:37-55`), with `q=2^basisDim` (`FieldBasis.lean:446-453`).
  The paper’s display uses argument order `(ε,q,m,d)` but its first item reverts to `(ε,m,d,q)`;
  Lean consistently uses the latter, as documented at `ch13_qpbt_test.tex:1637-1639`.
  The supporting factor-index correction is gap-register row 28; it does not change the corollary.

### Hidden weakening and non-vacuity

- **NOTE — no hidden public bridge.** `PauliSoundnessWitness` and `QubitSoundnessWitness` carry data,
  not assumptions (`SoundnessDefs.lean:164-177`; `QubitForm.lean:60-73`). Projectivity occurs only
  in the internal `ProjectiveSetting` (`Observables/Defs.lean:44-52`) and is removed for arbitrary
  strategies by the proved Naimark assembly (`Soundness/NaimarkAssembly.lean:47-75`).

- **NOTE — no junk-value proof found.** Positivity gives `q≥2`, `m,d≥1`; `deltaQld` contains no
  division; the EPR normalization uses a nonempty finite carrier; and unit-state fields rule out
  empty local or auxiliary Hilbert spaces. `Game.value`’s empty-`sSup` totalization is not on the
  headline path. It is used only in the documented symmetrization obstruction
  (`StrategyClasses.lean:915-959`, gap-register row 31).

- **NOTE — non-vacuity is genuinely established.** `nonVacuousParams` gives
  `(q,m,d)=(2^(2n+1),1,n+1)` (`NonVacuity.lean:80-102`); every admissible test has a value-one
  strategy (`:104-124`); and `pauli_soundness` applies to it at `ε=0` (`:126-146`).
  Moreover `deltaQld → 0` along that family (`:225-247`), hence is below every prescribed
  `η>0` (`:249-258`), and the combined theorem obtains all three actual distances below `η`
  (`:270-294`). The file correctly limits its claim: it gives no fixed-parameter positive-`ε`
  threshold (`:45-56`).

### Printed claims

- **SHOULD FIX — documented mismatch, but reviewer docs overclaim.**
  `PrintedExtendedLinesWitnessClaim` (`Combining/Apply.lean:108-115`) is not verbatim
  `lem:qld-4-13` (`14:1020-1034`). It uses the directly indexed line carrier, direct line-point law,
  `Option`-completed answers, and the corrected `IsPolyErr₂` contract. Its own docstring admits this
  (`Apply.lean:87-106`), and gap-register row 17 explicitly says neither Lean declaration matches
  the source statement. No theorem asserting this Prop was found.

- **NOTE — source claim retained and refuted on the Lean domain.**
  `PrintedSymmetricProjectiveAttainmentClaim` (`StrategyClasses.lean:901-905`) matches
  `lem:symmetric-strat` (`06:94-99`) modulo formal encoding. Nothing proves it positively.
  Instead `not_forall_printedSymmetricProjectiveAttainmentClaim` refutes its unrestricted Lean
  version using the empty-answer game (`StrategyClasses.lean:915-959`), exactly as documented in
  gap-register row 31.

- Therefore the theorem index’s statement that both Props preserve the source “in the source’s own
  words” and that “nothing downstream depends on either”
  (`docs/QPBT-theorem-index.md:311-316`) is false: the first is not source-shaped, and the second is
  used by its refutation theorem. The soundness chain does not depend on either.

### Axiom audit

- **NOTE — passes.** `AxiomAudit.lean:86-103` uses transitive `Lean.collectAxioms` and checks both
  headline theorems. Focused type-checking printed exactly
  `[propext, Classical.choice, Quot.sound]`.
- **NOTE — it would fail on `sorryAx`.** The exact-set comparison and explicit `sorryAx` branch are
  at `AxiomAudit.lean:88-98`.
- **NOTE — CI coverage is real.** GitHub CI builds it at `.github/workflows/pr-ci.yml:155-156`;
  local CI builds it at `local/bin/ci.sh:867-874`.

### Reviewer-facing document findings

- **SHOULD FIX.** README says no nontrivial `deltaQld<1` regime exists
  (`README.md:31-43`), contradicted by `NonVacuity.lean:249-258,270-294`.
- **SHOULD FIX.** README says no QPBT axiom-audit module exists
  (`README.md:74-79`), contradicted by `AxiomAudit.lean:1-37,102-103` and both CI targets above.
- **SHOULD FIX.** README says the QPBT comparator challenge has not been built
  (`README.md:94-104`), while the local challenge is configured for both headline theorems
  (`scripts/comparator/README.md:9-19`; `docs/comparator.md:76-93`) and has a 2,654-line expected file.
- **SHOULD FIX.** README and theorem index claim both printed Props state the source sentence
  (`README.md:90-93`; `QPBT-theorem-index.md:311-316`), contradicted by
  `Apply.lean:87-115` and gap-register row 17.
- **SHOULD FIX.** README links nonexistent `docs/ARTIFACT.md` and `docs/DEVIATIONS.md`
  (`README.md:43,212-215`).
- **SHOULD FIX.** The theorem index still says a checked-in axiom module is merely proposed
  (`QPBT-theorem-index.md:368-372`), although it has landed and is CI-enforced.
- **SHOULD FIX.** Blueprint prose says the headline proof or arbitrary-strategy extension remains
  open (`ch13_qpbt_test.tex:6,1602`; `ch16_qpbt_extraction.tex:1480-1483`), while the arbitrary
  theorem and final assembly are proved (`NaimarkAssembly.lean:47-75`;
  `Soundness.lean:52-65`) and later blueprint text acknowledges this
  (`ch16_qpbt_extraction.tex:1584-1643`).
- **NOTE.** README’s size count is stale: it says 330 QPBT files / 105,319 lines
  (`README.md:17`); the current tree has 331 files / 105,695 lines.
- **NOTE.** README’s “exactly four” `.lean` occurrences of `sorry`
  (`README.md:56-69`) is stale. There are eight: three prose occurrences under `MIPStarRE/`, two
  comparator-header prose occurrences, and three intended comparator-footer holes. There are still
  zero active proof holes under `MIPStarRE/`.
- **NOTE.** The theorem index is pinned to old commit `838c51b...`
  (`QPBT-theorem-index.md:15-21`), not current HEAD `05df4b74...`.

### Suggested approach

Prove source-facing raw Pauli-family bounds. Define the raw family using
`(S.A (pauliQuestion P W)).effect (.pauliOutcome u)` and its Bob analogue, bound malformed-answer
mass from the rejected-answer mass of a successful strategy, transfer the completed-family estimate
to the raw family, and absorb the additional universal factor into `deltaQld`. Then expose those raw
distances in `pauli_soundness` and `pauli_soundness_qubit`. If completion-to-zero is instead intended
as the formal parsing of bit strings, state and prove that identification explicitly and register it
as a headline statement choice before retaining `\leanok`.

### Gaps to fill

- Raw-effect transfer lemma for both players, including the zero outcome.
- A gap-register row or source-equivalence proof for the current answer completion.
- Synchronization of README, theorem index and the stale blueprint proof-status paragraphs.

### Searched

- Read issue #123; no prior scouting report was present.
- Searched paper mirrors `04`, `06`, `08`, `14`; blueprint chapters `ch11`–`ch16`; the QPBT gap
  register; local game, measurement, extraction, soundness and non-vacuity APIs.
- Searched all uses of `pauliAnswerOrZero`, `postprocess pauliAnswerOrZero`, raw `.pauliOutcome`
  effects, `Printed*`, `sorry`, `axiom`, `sSup`, witness structures and field-model selectors.
- Type-checked `Soundness.lean`, `QubitForm.lean`, `NonVacuity.lean` and `AxiomAudit.lean`.
  No full build was run. Worktree remained clean.

### Verdict

The headline theorems are kernel-checked, axiom-clean, non-vacuous, and their parameters, robustness function, targets and state conclusion otherwise match the paper. However, the operator conclusion currently concerns a zero-completed answer postprocessing rather than the direct Pauli effects printed in the source, with no registered statement correction or raw-effect transfer theorem. Because the artifact advertises the theorem as unchanged and marks it `\leanok`, that is a submission blocker until proved equivalent or exposed as a documented correction. The remaining findings are reviewer-document synchronization issues and should be fixed before packaging the ITP artifact.