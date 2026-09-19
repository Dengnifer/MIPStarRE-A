# Deviations from the source paper

This page lists **every** place where the Lean development in this repository
differs from its source paper, *MIP\* = RE* (arXiv:2001.04383), whose TeX is
mirrored under `references/qpbt-paper/`. It is written for a reviewer who wants
to know, before reading any Lean, what was changed and why.

The short answer: the formalization corrects the source where the source is
wrong, restricts it where the printed domain is not the formalizable one, and
records the two printed sentences it could not establish as *unasserted
propositions* rather than quietly proving something weaker. **No headline
theorem depends on an unproved claim.** Section
[No headline theorem rests on an unproved claim](#no-headline-theorem-rests-on-an-unproved-claim)
says how to check that mechanically.

Detail for each row lives in a mathematical note under `docs/paper-gaps/`. The
machine-readable index of those notes is
[`docs/paper-gaps/qpbt-gap-register.md`](paper-gaps/qpbt-gap-register.md), which
currently indexes 18 of the 20 notes: `qpbt_subline-claims-line-marginal.tex`
(row c8) and `qpbt_combined-points-field-valued.tex` (row d1) have no register
entry yet, so for those two rows this page, not the register, is the complete
record. The policy that governs when a note must be written is
[`docs/paper-gaps/policy.tex`](paper-gaps/policy.tex). This page is a summary of
those notes, not a replacement for them.

Every row below was checked against `github/main` at commit `838c51b7`.
Line numbers are from that commit.

## How to read the table

**Printed-claim status** is the single most important column. It answers: what
happened to the sentence as the paper prints it?

| Status | Meaning |
|---|---|
| **refuted** | The printed sentence is *false*. The repository contains a counterexample, or the correction is forced by one. The paper's statement is not provable, in Lean or anywhere. |
| **unproved** | The printed sentence may well be true, but neither the source's argument nor this development establishes it. It is recorded in Lean as a `Prop`-valued definition, which *states* it without *asserting* it. |
| **restated** | The printed mathematics is correct and is what Lean proves; only its presentation, indexing, domain encoding, or proof route differs. |

Deviations are grouped by severity, (a) most severe to (d) least.

---

## (a) Printed claims the source does not establish

Two printed sentences of the paper are not established. Neither is hidden, and
neither is proved in weakened disguise. Each is carried in Lean as a
`Prop`-valued **definition** — writing `def C : Prop := …` introduces no proof
of `C`, so the sentence stays visible and quotable without being asserted. In
both cases the mathematics the source's argument *does* support is proved
separately, under its own name, and is what the rest of the development uses.

### a1. The error form of the combined-lines lemma

| | |
|---|---|
| **Paper statement** | `lem:qld-4-13`, the combined-lines consistency lemma, with error `poly(m²ε, md/q)` |
| **Locator** | `references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex`, chapter 14 lines 1020–1034 |
| **What differs** | The printed `poly(m²ε, md/q)` error form is not derived by the source's argument. What the argument gives is the weaker `m · poly(ε, md/q)`. Separately, the Lean carrier replaces the source's *seed-indexed* extended line space by a *directly indexed* one at dimension `2m+2` (see [c2](#c2-dimension-divisibility-in-the-classical-test-instantiation)), and compares `Option`-completed answers instead of summing over `a ∈ 𝔽_q`. |
| **Why** | The printed error form does not follow from the cited estimates, and the seed-indexed space is not defined for every admissible parameter tuple — the printed instantiation would require `2m+2 ∣ q`, which is impossible for the parameters the test actually uses. |
| **Lean (printed form)** | `PrintedExtendedLinesWitnessClaim`, `MIPStarRE/QPBT/Combining/Apply.lean:108` — a `Prop`, not a theorem |
| **Lean (what is proved)** | `exists_extendedLinesWitness_established`, `MIPStarRE/QPBT/Combining/Apply.lean:237`, with error `C·m·poly(ε, md/q)`; supplied-point companion `exists_extendedLinesWitness_established_ofPointsWitness`, `Apply.lean:158` |
| **Blueprint** | `lem:qld-4-13` (source shape, carries **no** formalization mark), `rem:qld-4-13-source-defects`, and the support node `lem:qld-4-13-established`, all in `blueprint/src/chapter/ch15_qpbt_combining.tex` |
| **Gap note** | [`qpbt_combined-lines-error-term.tex`](paper-gaps/qpbt_combined-lines-error-term.tex) |
| **Printed-claim status** | **unproved** — stated, not asserted, not refuted. Tracked as issue #598. |

The earlier `sorry`-bearing theorem `exists_extendedLinesWitness` is **gone**; it
was replaced by the unasserted `Prop` on 2026-09-19. `Apply.lean` now carries no
proof debt.

### a2. Attainment in the symmetrization lemma

| | |
|---|---|
| **Paper statement** | `lem:symmetric-strat`: the supremum defining `val*(G)` is *attained* by a symmetric projective strategy |
| **Locator** | `references/qpbt-paper/06_nonlocal_games_and_mipstar.tex`, chapter 6 lines 94–132 |
| **What differs** | The source's argument establishes only the *approximate* form — for every slack there is a symmetric projective strategy within it. The printed attainment statement is additionally **false** on the Lean domain, which admits a game with an empty answer alphabet: at `ε = 1` no strategy exists at all. |
| **Why** | A limit of symmetric projective strategies need not be a strategy, so the source's compactness step does not close; and the empty-answer game refutes the printed sentence outright. |
| **Lean (printed form)** | `PrintedSymmetricProjectiveAttainmentClaim`, `MIPStarRE/QPBT/Games/StrategyClasses.lean:901` — a `Prop`, not a theorem |
| **Lean (refutation)** | `not_forall_printedSymmetricProjectiveAttainmentClaim`, `MIPStarRE/QPBT/Games/StrategyClasses.lean:952`, from `SymmetrizationObstruction.emptyAnswerGame` |
| **Lean (what is proved)** | `exists_symmetric_projective_strategy_approx`, `MIPStarRE/QPBT/Games/Symmetrization.lean:139`; slack form `exists_symmetric_projective_strategy_of_lt_value`, `Symmetrization.lean:110`; support node carrier `exists_symmetric_projective_strategy_of_strategy`, `StrategyClasses.lean:967` |
| **Blueprint** | `lem:symmetric-strat` (corrected approximate form), `rem:symmetric-strat-limit`, `lem:symmetric-strat-printed-claim`, `lem:symmetric-strat-given-strategy`, in `blueprint/src/chapter/ch12_qpbt_games.tex` |
| **Gap note** | [`qpbt_symmetrization-attainment.tex`](paper-gaps/qpbt_symmetrization-attainment.tex) |
| **Printed-claim status** | **refuted** — the repository proves the printed sentence false. Tracked as issue #524. |

The earlier `sorry`-bearing theorem `exists_symmetric_projective_strategy` is
**gone**.

---

## (b) Corrected constants, error forms and numerical estimates

In each of these the paper's *theorem* survives, but a constant, an exponent, an
error form, or an intermediate estimate in its proof does not. The correction is
carried in the blueprint statement and in a remark beside it.

### b1. The probability of anticommuting Pauli tuples

| | |
|---|---|
| **Paper statement** | `fact:omega-anticomm-prob` |
| **Locator** | chapter 14 lines 64–93 |
| **What differs** | Corrected to the *exact* probability. Both opening assertions of the printed proof are refuted inside the source's own parameter domain — but the printed *bounds* hold throughout it, since the source takes `q, m, d` positive. Lean carries `m, d ≥ 1` explicitly. |
| **Why** | The two opening assertions are false as stated; the conclusion is not. The `m, d ≥ 1` hypothesis is a faithful encoding of the source domain, because Lean's naturals include zero — it is a boundary condition, not proof debt. |
| **Blueprint** | `fact:omega-anticomm-prob`, `rem:omega-anticomm-prob-correction` (`ch14_qpbt_observables.tex`) |
| **Gap note** | [`qpbt_anticommuting-probability.tex`](paper-gaps/qpbt_anticommuting-probability.tex) |
| **Printed-claim status** | **restated** (conclusion); the two intermediate assertions are **refuted**. Proofs complete. |

### b2. The exponent comparison in the canonical bound

| | |
|---|---|
| **Paper statement** | `lem:delta-bound` |
| **Locator** | chapter 8 lines 1520–1562 |
| **What differs** | The printed proof compares exponents via `k ≤ m`, which is false. The corrected proof estimates `2^(−bm)` directly. The lemma's **conclusion is unchanged**. |
| **Why** | The comparison `k ≤ m` does not hold for the parameters in play; the direct estimate does not need it. |
| **Blueprint** | `lem:delta-bound`, `rem:delta-bound-exponent-comparison` (`ch13_qpbt_test.tex`) |
| **Gap note** | [`qpbt_delta-bound-exponent-comparison.tex`](paper-gaps/qpbt_delta-bound-exponent-comparison.tex) |
| **Printed-claim status** | **restated** (statement matches and is proved); the printed proof step is **refuted**. |

### b3. Distance normalization in the quantum linearity theorem

| | |
|---|---|
| **Paper statement** | Natarajan–Vidick equation (3) and Theorem 10, as quoted by the source |
| **Locator** | chapter 14 lines 711–725; `references/nv-paper/` |
| **What differs** | The squared operator-distance conclusion is corrected from `δ` to `2δ`. |
| **Why** | The provider's exact operator bound is off by the factor two; the quotation's own `approx_δ` notation absorbs constant factors, so this is the provider's error, not a quotation slip. |
| **Lean** | `exists_exactly_linear_observables`, `MIPStarRE/QPBT/Combining/Linearity.lean:93` (`≤ 2δ` operator form); companion `exists_exactly_linear_observables_binaryObservableDistSq` (`≤ δ` measurement form) |
| **Blueprint** | `thm:linearity`, `rem:linearity-import` (`ch15_qpbt_combining.tex`) |
| **Gap note** | [`qpbt_linearity-distance-normalization.tex`](paper-gaps/qpbt_linearity-distance-normalization.tex) |
| **Printed-claim status** | **refuted** (the constant as printed); corrected statement proved. |

### b4. The product-form error in the pasting lemma

| | |
|---|---|
| **Paper statement** | `lem:pasting` |
| **Locator** | chapter 6 lines 504–525 |
| **What differs** | The source's *product-form* two-variable polynomial error contract is replaced by a *sum* bound `C(η^r + δ^s)` on the closed nonnegative quadrant. |
| **Why** | The product form is contradicted by an explicit two-dimensional strategy at every fixed positive consistency error. The sum form is what the imported proof of Fact 4.35 actually produces. |
| **Lean** | `exists_pasting_error`, `MIPStarRE/QPBT/Games/Sandwich.lean:205`, with explicit `δp η δ = (3C + 19)(η^(1/4) + δ^(1/8))`; contract `IsPolyErr₂`, `MIPStarRE/QPBT/Games/ErrorFunctions.lean:44` |
| **Blueprint** | `lem:pasting` (`ch12_qpbt_games.tex`) |
| **Gap note** | [`qpbt_pasting-product-error.tex`](paper-gaps/qpbt_pasting-product-error.tex) |
| **Printed-claim status** | **refuted** (the product form); corrected contract proved. |

This correction propagates: the printed error expressions of `lem:qld-4-13` and
`lem:qld-xz-lines` are qualified accordingly in the blueprint and in the
docstrings of six declarations.

### b5. The binary factor index in the qudit-to-qubit isomorphism

| | |
|---|---|
| **Paper statement** | `lem:pauli-binary` |
| **Locator** | chapter 4 lines 1172–1198 |
| **What differs** | The final inner factor range is corrected from `1 ≤ j ≤ q` to `1 ≤ j ≤ log₂ q`. |
| **Why** | The qubit register has `log₂ q` factors, not `q`; the printed range is a transcription error. |
| **Lean** | `exists_qubitIsometry`, `MIPStarRE/QPBT/Algebra/PauliTheorems.lean:721` |
| **Blueprint** | `lem:pauli-binary`, `rem:pauli-binary-source` (`ch11_qpbt_algebra.tex`) |
| **Gap note** | [`qpbt_pauli-binary-factor-index.tex`](paper-gaps/qpbt_pauli-binary-factor-index.tex) |
| **Printed-claim status** | **refuted** (as printed); corrected statement proved. |

### b6. Corrections to the Pauli-test winning implications

| | |
|---|---|
| **Paper statement** | `lem:qld-win-implications`, `lem:qld-win-implications-obs` |
| **Locator** | chapter 14 lines 197–362 |
| **What differs** | Five corrections: the conditioning phase, a circular parameter reduction, the zero-direction completion, reversed observable indices, and a label typo. |
| **Why** | The circular reduction cannot be formalized as printed; the remaining four are transcription errors. |
| **Blueprint** | `lem:qld-win-implications`, `lem:qld-win-implications-obs`, `rem:qld-win-implications-typos` (`ch14_qpbt_observables.tex`) |
| **Gap note** | [`qpbt_win-implications-corrections.tex`](paper-gaps/qpbt_win-implications-corrections.tex) |
| **Printed-claim status** | **refuted** (in the five listed places); the `win_*` and observable implication statements match and are proved. |

### b7. Triangle estimates and isometry transfer in Pauli extraction

| | |
|---|---|
| **Paper statement** | `lem:qld-construct-the-paulis`, `lem:qld-unitary`, and the final soundness proof |
| **Locator** | chapter 14 lines 1463–1480 and 1666–1875 |
| **What differs** | Numerical estimates corrected; a nonzero-normalization case split added; and the isometry **range projection**, omitted by the source, is supplied in the blueprint proof. |
| **Why** | A triangle-inequality step in the source loses a term, and the printed estimate does not survive the case where a normalization vanishes. The range projection is needed to transfer the extracted operators back; the source asserts the transfer without it. |
| **Lean** | `exists_extractionWitness`, `MIPStarRE/QPBT/Extraction/SourceUnitary.lean:34`; `exists_globalPairWitness`, `MIPStarRE/QPBT/Combining/Apply.lean:280`; range projection `sum_norm_leftTensor_conjIsometry_sub_sq_le` and its right companion in `MIPStarRE/QPBT/Test/Soundness/RangeProjection.lean` |
| **Blueprint** | `lem:qld-construct-the-paulis`, `lem:qld-unitary`, `lem:qld-unitary-given-global-pair`, `rem:qld-unitary-triangle-slip`, proof of `thm:pauli` (`ch16_qpbt_extraction.tex`) |
| **Gap note** | [`qpbt_extraction-transfer.tex`](paper-gaps/qpbt_extraction-transfer.tex) |
| **Printed-claim status** | **restated** (the source-facing theorems are proved at their stated form); the printed intermediate estimates are **refuted**. |

The range-projection transfer is on the dependency path of the final theorem —
it reaches `pauli_soundness` through `ExtractionWitness.isometry_transfer_bounds`
and `pauli_soundness_deltaQld_ofExtractionWitness`.

---

## (c) Added side conditions and domain restrictions

These rows change the *domain* on which a statement is read, or add a
hypothesis. The distinction that matters, and which the notes are required to
draw (`policy.tex`, §"When to Write a Note"), is between a **boundary
hypothesis** — positivity, nonemptiness, decidability, a field-model instance —
which is a faithful encoding of the domain the paper works in, and a
hypothesis that **supplies an unproved step** of the paper's argument. Rows c1
and c7 are the latter and say so.

### c1. The strategy class in Magic Square rigidity

| | |
|---|---|
| **Paper statement** | `thm:ms-rigidity`, quantified over **every** strategy of value `1 − ε` |
| **Locator** | chapter 8 lines 612–652 |
| **What differs** | An added hypothesis: the two players' `Variable₁` and `Variable₅` measurements agree on the state up to a defect `δ`. The conclusion replaces `√ε` by `√ε + √δ`. A second, non-mathematical deviation: the source reads its `approx` convention on the original state `ψ` while applying it to *transported* operators, so the blueprint and Lean read it on the extracted ideal state `Θ`. |
| **Why** | The source statement is **false**. A perfect strategy answering the two orientations of each constraint–variable edge on independent entangled copies violates the conclusion at `ε = 0`, and so does its symmetric role-flag version — so restricting to symmetric strategies does not repair it. The added consistency hypothesis does. |
| **Lean** | `exists_ms_rigidity`, `MIPStarRE/QPBT/Test/MagicSquareTheorems.lean:637`, with explicit constant `C = 2·10¹²`; defect `msVariableConsistencyDefect`, `MagicSquareTheorems/Rigidity/Consistency.lean:90`; specialization `exists_ms_rigidity_of_symmetric_consistent` is the case `δ = 0`, which is the source's display verbatim |
| **Blueprint** | `thm:ms-rigidity`, `rem:ms-rigidity-strategy-class` (`ch13_qpbt_test.tex`), statement and proof both `\leanok` |
| **Gap note** | [`qpbt_ms-rigidity-symmetric-strategies.tex`](paper-gaps/qpbt_ms-rigidity-symmetric-strategies.tex) |
| **Printed-claim status** | **refuted** as printed; corrected statement proved, and the source's display is recovered exactly at `δ = 0`. |

This hypothesis **supplies a missing condition**, not a boundary encoding. It
was adopted by owner decision B5 (archived owner inbox #26).

### c2. Dimension divisibility in the classical test instantiation

| | |
|---|---|
| **Paper statement** | `lem:qld-sublines`, `lem:qld-4-7`, and the `lem:ld-soundness` import |
| **Locator** | chapter 14 and chapter 8; the `lem:ld-soundness` import |
| **What differs** | The printed instantiation of the classical low-degree test at dimension `2m+2` requires `2m+2 ∣ q`, which is impossible for the admissible parameters. The blueprint keeps the source shape over the seed-indexed line-point distribution and **adds no divisibility hypothesis**, marking the blocked steps instead. The Lean carriers realize dimension `2m+2` by **direct index sampling**, so they are defined for every admissible tuple — but they are not the seed-indexed objects of the source-labelled nodes. |
| **Why** | Adding the impossible divisibility condition would make the theorem vacuous. The directly indexed replacement is a genuine, non-vacuous theorem; it is presented as a separate formalization-support node rather than as the source lemma. |
| **Lean** | `exists_direct_ld_soundness`, `MIPStarRE/QPBT/Combining/DirectLowDegree/Soundness.lean:65`; seed-indexed `exists_ld_soundness`, `MIPStarRE/QPBT/Test/LowDegreeGameTheorems.lean:82` (proved, unchanged statement); `exists_ld_soundness_of_k_eq_one`, `DirectLowDegree/SeedIndexedSoundness.lean:124` |
| **Blueprint** | `lem:ld-soundness`, `lem:qld-sublines`, `lem:qld-4-7`, `rem:qld-4-7-divisibility` (`ch13_qpbt_test.tex`, `ch15_qpbt_combining.tex`) |
| **Gap note** | [`qpbt_ld-dimension-divisibility.tex`](paper-gaps/qpbt_ld-dimension-divisibility.tex) |
| **Printed-claim status** | **restated** for `exists_ld_soundness`; two source imports remain **unproved** — the claimed tensor-code game correspondence, and the requirement `K ≥ 12m(d+1)` for the printed choice `K = m³d`. Tracked as issue #527. |

The direct route does not apply the tensor-code theorem, so it does not
discharge the original source-import obligations. This is the one place where a
source obligation is openly outstanding, and it does **not** sit under
`pauli_soundness` — `exists_ld_soundness` is proved at its unchanged statement.

### c3. Simultaneous polynomial measurements are not obtained coordinatewise

| | |
|---|---|
| **Paper statement** | Proof of `lem:ld-soundness`, the extension from `k = 1` to general `k` |
| **Locator** | chapter 8 lines 455–458 |
| **What differs** | The coordinatewise sandwich route planned for the formalization is replaced by the combining reduction of NEEXP Theorem 4.43. In the individual-degree formulation the degree stays `d` rather than rising to `d+1`, and the recovery cost is `(m+k)d/q`. |
| **Why** | The coordinatewise route is **refuted** by an explicit example in which all coordinate errors vanish yet no simultaneous measurement exists. |
| **Lean** | `exists_directSimultaneousPolynomialMeasurements_combinedError`; `exists_directSimultaneousPolynomialMeasurements_of_k_eq_one`; absorbed into the source error function at `a = 10²³`, `b = 1/80000` by `exists_direct_ld_soundness` |
| **Blueprint** | `lem:ld-soundness`, `rem:ld-soundness-simultaneity` (`ch13_qpbt_test.tex`) |
| **Gap note** | [`qpbt_ld-simultaneous-sandwich.tex`](paper-gaps/qpbt_ld-simultaneous-sandwich.tex) |
| **Printed-claim status** | **restated** (the source form is proved for every `k`); the planned proof route is **refuted**. |

### c4. Prime-characteristic and binary Pauli scope

| | |
|---|---|
| **Paper statement** | Generalized Pauli identities |
| **Locator** | chapter 4 lines 1056–1161 |
| **What differs** | The general shift, phase and observable matrices, and their product, power, unitarity, spectral, twisted-commutation and cancellation identities, are formalized for **arbitrary prime characteristic**. The common eigenvectors and rank-one projectors of the same definition are formalized **only in characteristic two** (`pauliVec`, `pauliProj`), with only the binary Fourier formulas proved. |
| **Why** | The source's prime-characteristic scope is preserved where the identities are used generally; QPBT itself only ever needs characteristic two for the eigenvector and projector layer, so the general versions were not built. |
| **Blueprint** | `def:generalized-pauli`, `lem:twisted-commutation`, `lem:pauli-observable-expansion` (`ch11_qpbt_algebra.tex`) |
| **Gap note** | [`qpbt_characteristic-two-pauli-scope.tex`](paper-gaps/qpbt_characteristic-two-pauli-scope.tex) |
| **Printed-claim status** | **restated**, at reduced scope. Source-general eigenvector, projector, expansion and inversion declarations are **absent** — not unproved, simply not formalized, and not needed downstream. |

### c5. The cross-basis phase in the extracted Pauli observables

| | |
|---|---|
| **Paper statement** | The cross-basis commutation assertion |
| **Locator** | chapter 14 lines 1451–1456 |
| **What differs** | Corrected to the **full trace phase** for every pair of basis indices, in place of the source's dichotomy (commute or anticommute). |
| **Why** | The printed dichotomy is false: for general basis index pairs the phase is a nontrivial character value, not `±1`. |
| **Lean** | `tildeObs_twisted_commutation`, `MIPStarRE/QPBT/Extraction/Observables.lean:331` |
| **Blueprint** | `lem:tildew-product-form`, `rem:qld-cross-phase` (`ch16_qpbt_extraction.tex`) |
| **Gap note** | [`qpbt_cross-basis-phase.tex`](paper-gaps/qpbt_cross-basis-phase.tex) |
| **Printed-claim status** | **refuted** (the dichotomy); corrected identity proved. |

### c6. The decoding identity in the Pauli extraction argument

| | |
|---|---|
| **Paper statement** | The decoder and its evaluation identity |
| **Locator** | chapter 14 lines 1419–1420, 1483–1492, 1805–1822 |
| **What differs** | Corrected to **full-field** decoding, and the evaluation identity is corrected to hold **only on encoding outcomes**; non-encoding mass is handled by separate estimates. |
| **Why** | The printed identity is asserted unconditionally, but fails off the encoding set; the mass there has to be bounded rather than ignored. |
| **Lean** | `decodeFq_lowDegreeEncoding`, `MIPStarRE/QPBT/Algebra/Decoding.lean:159`, with `decodeFq_add`, `decodeFq_smul`, `decodeFq_dotProduct_indicatorVec`; non-encoding bound `nonencodingMarginalMass_le`, `MIPStarRE/QPBT/Extraction/Consistency.lean:856` |
| **Blueprint** | `def:qld-full-field-decoder`, `lem:qld-decoder-linearity`, `lem:qld-decoder-evaluation`, `lem:qld-nonencoding-mass-bound`, `rem:qld-decoding-identity` (`ch16_qpbt_extraction.tex`) |
| **Gap note** | [`qpbt_decoding-identity.tex`](paper-gaps/qpbt_decoding-identity.tex) |
| **Printed-claim status** | **refuted** (the unconditional identity); corrected form proved, and the two specialized non-encoding estimates compose in `exists_pulled_apart_consistency`. |

### c7. Quantum linearity: quantifiers, a spurious hypothesis, and the ancilla

| | |
|---|---|
| **Paper statement** | The quotation of Natarajan–Vidick Theorem 10 |
| **Locator** | chapter 14 lines 711–725 |
| **What differs** | Pointwise closeness corrected to **averaged** closeness; the spurious hypothesis `δ ≤ 1` removed; the appended identity at `u = 0` derived rather than assumed; and a uniform optional Naimark ancillary space is fixed **before** quantifying over the Hilbert space, state, error and observable family. |
| **Why** | The quotation's quantifier order does not match the theorem it cites, and `δ ≤ 1` appears in neither. The ancilla point is the substantive one: the source's own step is *stronger* — that the uniform ancilla is already present in the fixed state as zero-state padding of the existing expanded player spaces — and **that step is not proved here**. |
| **Lean** | `exists_exactly_linear_observables_commonAncilla`, `MIPStarRE/QPBT/Combining/Linearity.lean:188` |
| **Blueprint** | `thm:linearity`, `rem:linearity-import`, `lem:linearity-common-ancilla` (`ch15_qpbt_combining.tex`) |
| **Gap note** | [`qpbt_linearity-theorem-quotation.tex`](paper-gaps/qpbt_linearity-theorem-quotation.tex) |
| **Printed-claim status** | **restated** for the corrected quantifiers; the source's zero-state-padding step is **unproved**. The combined-point conclusion is proved **independently** of that assumption, so nothing downstream rests on it. |

### c8. The constructed measurement in Subline Claim 17-2

| | |
|---|---|
| **Paper statement** | Claim 17-2: `\|A(T) − B(T)\| ≤ O(m√δ_Line(ε))` for the sandwich `T = L^X L^Z L^X` |
| **Locator** | `references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex` |
| **What differs** | The established Lean result is the **real-part** estimate on the *directly indexed* subline law, with completed evaluations: `\|Re A_dir(T) − Re B_dir(T)\| ≤ C·m√δ_Line(ε)`. It assumes no joint-point or paired-line consistency witness. This is not yet the complex estimate on the source law. |
| **Why** | Same directly indexed replacement as [c2](#c2-dimension-divisibility-in-the-classical-test-instantiation) — the seed-indexed subline law is not defined for the admissible parameters. The source distribution correspondence remains open. |
| **Lean** | `subline_replace_by_ordered_product_re_direct`, `MIPStarRE/QPBT/Combining/Claims.lean:80`; `subline_remove_X_factor_re_direct`, `Claims.lean:448`; `subline_Z_term_near_one_re_direct`, `Claims.lean:665` |
| **Blueprint** | `ch15_qpbt_combining.tex` lines 2443, 3281, 3600, 3900 — the source distribution correspondence is marked open at each |
| **Gap note** | [`qpbt_subline-claims-line-marginal.tex`](paper-gaps/qpbt_subline-claims-line-marginal.tex) |
| **Printed-claim status** | **unproved** on the source law (real part proved on the directly indexed law). The note's own verdict line reads `formalization-deviation / open-proof`. |

Note: the counterexample in this note is a mathematical calculation, not a
kernel-certified Lean instance. The note says so.

### c9. Index pairing in the low-degree sandwich

| | |
|---|---|
| **Paper statement** | `lem:ld-sandwich` |
| **Locator** | chapter 6 lines 465–501 |
| **What differs** | Corrected so each measurement receives the outcome from **its own dependent alphabet**; the empty case is made explicit. |
| **Why** | The source's pairing identifies outcome alphabets that must stay distinct — the outcome type genuinely depends on the index, so the printed pairing does not type-check as mathematics, let alone in Lean. |
| **Lean** | `sandwichProduct`, `MIPStarRE/QPBT/Games/Sandwich/Defs.lean:56`, with the corrected dependent indexing; measurement theorem and quantitative consistency estimate proved, explicit universal constant `C₀ = 8` |
| **Blueprint** | `lem:ld-sandwich`, `rem:ld-sandwich-indexing` (`ch12_qpbt_games.tex`) |
| **Gap note** | [`qpbt_ld-sandwich-indexing.tex`](paper-gaps/qpbt_ld-sandwich-indexing.tex) |
| **Printed-claim status** | **refuted** as printed (the identification); corrected statement proved. |

---

## (d) Presentation-only differences

Neither row changes any source theorem. Both are recorded because
`docs/paper-gaps/policy.tex` requires a note when the formal proof takes a
different route from the cited argument, even when the statement is untouched.

### d1. A field-valued construction of the combined point measurements

| | |
|---|---|
| **Paper statement** | `lem:qld-4-10`, with displays `eq:qld-q-self-cons`, `eq:qld-q-cons-m-hat-xz`, `eq:qld-q-cons-m-hat-zx` |
| **Locator** | chapter 14 lines 689–709 |
| **What differs** | **Proof route only.** The source combines binary refinements and then invokes quantum linearity; the formalization combines the field-valued point measurements directly. Parseval's identity prevents any loss depending on the field size, and orthonormalization produces projective measurements on the existing expanded local spaces. Resulting squared-distance error `Kε^(1/8)`. **No additional ancilla is needed** — which is what makes [c7](#c7-quantum-linearity-quantifiers-a-spurious-hypothesis-and-the-ancilla) harmless. |
| **Why** | The direct route avoids the source's unproved zero-state-padding step and gives a field-size-independent bound. |
| **Lean** | `exists_combinedPointsWitness`, `MIPStarRE/QPBT/Combining/Points.lean:67`; `exists_extendedQ`, `Points.lean:323` |
| **Blueprint** | `lem:qld-4-10` (`ch15_qpbt_combining.tex`) |
| **Gap note** | [`qpbt_combined-points-field-valued.tex`](paper-gaps/qpbt_combined-points-field-valued.tex) |
| **Printed-claim status** | **restated** — the note states in terms that this documents a change of proof, not a change of the source theorem. |

### d2. Polynomial error notation and square-root bounds

| | |
|---|---|
| **Paper statement** | The `poly(·)` error convention, and the square-root errors of chapter 14 |
| **Locator** | chapter 4 lines 23–29 |
| **What differs** | The polynomial-error convention is made precise as **independent prefactor and positive exponent witnesses**. |
| **Why** | The source's `poly(·)` is informal; a formal statement has to say what is quantified and in which order. Making the witnesses independent is the weakest reading consistent with every use in the paper. |
| **Lean** | `IsPolyErr`, `MIPStarRE/QPBT/Games/ErrorFunctions.lean:27`; two-variable `IsPolyErr₂`, `ErrorFunctions.lean:44` (see [b4](#b4-the-product-form-error-in-the-pasting-lemma) for the sum-form correction to the latter) |
| **Blueprint** | `lem:qld-comm-cons`, `lem:qld-comm-line-cons` (`ch14_qpbt_observables.tex`) |
| **Gap note** | [`qpbt_polynomial-error-square-root.tex`](paper-gaps/qpbt_polynomial-error-square-root.tex) |
| **Printed-claim status** | **restated**; the concrete square-root error witnesses are proved. |

---

## No headline theorem rests on an unproved claim

The four headline results are

| Theorem | Location |
|---|---|
| `pauli_soundness` | `MIPStarRE/QPBT/Test/Soundness.lean:52` |
| `pauli_soundness_qubit` | `MIPStarRE/QPBT/Test/QubitForm.lean:423` |
| `exists_spcc_value_one` | `MIPStarRE/QPBT/Test/Completeness.lean:266` |
| `exists_ld_soundness` | `MIPStarRE/QPBT/Test/LowDegreeGameTheorems.lean:82` |

None of them depends on either unasserted claim of section (a), and none
contains proof debt. Three independent checks establish this, and a reviewer can
run all three.

**1. The unasserted claims are definitions, not theorems.** Both
`PrintedExtendedLinesWitnessClaim` (`Combining/Apply.lean:108`) and
`PrintedSymmetricProjectiveAttainmentClaim` (`Games/StrategyClasses.lean:901`)
are introduced with `def … : Prop`. A `def` of type `Prop` produces a
*proposition*, not a *proof* of it, so no proof term anywhere can consume one
except as an explicit hypothesis. Comparator:

```
git grep -n "PrintedExtendedLinesWitnessClaim\|PrintedSymmetricProjectiveAttainmentClaim" -- "MIPStarRE/*.lean"
```

At commit `838c51b7` this returns eight lines: the two definitions, the
refutation `not_forall_printedSymmetricProjectiveAttainmentClaim`
(`StrategyClasses.lean:952–954`, whose hit is on line 954), and five
docstring or comment mentions (`Combining/ErrorObstruction.lean:20`,
`Combining/Lines/SubLineJoint.lean:124`, and `Games/Symmetrization.lean:25`,
`:108`, `:133`). **No theorem takes either as a hypothesis.**

**2. There is no proof debt.** No `sorry`, `admit`, `axiom` declaration,
`native_decide`, `unsafe`, `@[extern]`, bodyless `opaque`, `implemented_by`, or
`backward.*`/`respectTransparency` option occurs anywhere in the 670 Lean files
under `MIPStarRE/`. (The repository holds 676 `.lean` files in all; the six
outside `MIPStarRE/` are `MIPStarRE.lean`, `scripts/Checkdecls.lean`, the three
`scripts/comparator/*.lean` helpers, and one archived telemetry audit module,
none of which the development imports.) Comparator:

```
git grep -nE "\b(sorry|admit|native_decide|unsafe|implemented_by)\b" -- "MIPStarRE/*.lean"
```

At `838c51b7` this returns exactly two lines, both inside a docstring:
`MIPStarRE/LDT/Test/AxiomAudit.lean:81`, prose recording that the successor-step
theorem no longer has a direct `sorry`, and
`MIPStarRE/QPBT/Combining/Apply.lean:57`, the docstring of
`PrintedExtendedLinesWitnessClaim` recording that the former open `sorry` at
that site was replaced by the unasserted `Prop`. There are **zero** real sites.
(The regex does not match `sorryAx`. That identifier occurs at eleven sites
under `MIPStarRE/`, none of them a use in a proof: once at
`MIPStarRE/LDT/MainInductionStep/Theorems/MainTheorems/Successor.lean:187`, and
ten times in the LDT axiom-audit module `MIPStarRE/LDT/Test/AxiomAudit.lean`
(lines 40, 106, 115, 137, 166, 177, 191, 224, 248, 249). Nine of the eleven are
prose; `AxiomAudit.lean:248–249` is executable metaprogram code — the
`collectAxioms` guard that raises an error when an audited declaration depends
on `sorryAx`. Comparator:
`git grep -n "sorryAx" -- "MIPStarRE/*.lean"`.)

**3. Axiom audit.** The intended check is

```lean
#print axioms pauli_soundness
```

which must report exactly `propext`, `Classical.choice`, `Quot.sound` — the three
standard Lean axioms — and in particular **not** `sorryAx`. This was verified by
a whole-environment sweep on 2026-09-18.

> **Honest caveat.** That sweep was run from a one-off metaprogram in a
> throwaway worktree and **is not currently reproducible from this
> repository**. There are zero `#print axioms` directives in the Lean tree, and
> the only committed audit module, `MIPStarRE/LDT/Test/AxiomAudit.lean`, covers
> the LDT track and never mentions QPBT. A reviewer must run the command above
> by hand. Committing `MIPStarRE/QPBT/Test/AxiomAudit.lean` and building it in CI
> is a known outstanding task; until it lands, check 3 is a *manual* check,
> while checks 1 and 2 are fully mechanical.

**What remains genuinely open**, and where it sits: the two source imports of
[c2](#c2-dimension-divisibility-in-the-classical-test-instantiation) — the
tensor-code game correspondence and the `K ≥ 12m(d+1)` requirement — are not
discharged. They are obligations of the *source's* route to `lem:ld-soundness`.
The formalization reaches `exists_ld_soundness` by a different, complete route,
so these open items are not load-bearing for any headline theorem. They are
tracked as issue #527.

## A second question a reviewer may ask: is the conclusion non-vacuous?

Not a deviation, but adjacent, and better answered here than discovered later.

`pauli_soundness` bounds its conclusion by
`deltaQld a b ε m d q = a·(m·d)^a·(ε^b + q^(−b) + 2^(−b·m·d))`
(`MIPStarRE/QPBT/Test/SoundnessDefs.lean:35`) with `a, b` **existentially
quantified** (`1 ≤ a`, `0 < b < 1`), so no single numeric value can be read off
the statement. Both halves of the question are answered by citable declarations
in `MIPStarRE/QPBT/Test/NonVacuity.lean`, a corollary module that adds no
mathematics of the source and no hypothesis:

- **The hypotheses are satisfiable.** `AdmissibleParams` is inhabited —
  `nonVacuousParams` (`NonVacuity.lean:85`), hence
  `nonempty_admissibleParams` (`:101`) — and every admissible `P` carries a
  strategy for `pauliBasisTest P` itself of value exactly `1`
  (`exists_pauliBasisTest_strategy_value_one`, `:110`), transported from
  `exists_spcc_value_one`. `introParams`
  (`MIPStarRE/QPBT/Test/CanonicalParams.lean:105`) is a second explicit
  admissible tuple.
- **The conclusion is non-trivial.** Whatever constants the theorem produces,
  along the explicit admissible family `nonVacuousParams n` the error at
  `ε = 0` tends to `0` (`tendsto_deltaQld_nonVacuousParams`, `:231`), so for
  every `η > 0` there are admissible parameters with
  `deltaQld a b 0 P.m P.d P.q < η` — in particular below `1`
  (`exists_admissibleParams_deltaQld_lt`, `:252`). The two halves are combined
  in `pauli_soundness_nontrivial` (`:277`), which exhibits, for every `η > 0`,
  admissible parameters together with a value-one strategy for which the
  theorem's own state distance and both operator distances are strictly below
  `η`.

What this does **not** give is a uniform rate in `ε` at fixed parameters: the
non-triviality is established at `ε = 0`, with `deltaQld` continuous in `ε` from
the right there (`tendsto_deltaQld_eps_zero`, `:263`). The shape of the bound
remains faithful — the source too only asserts that such constants exist.

---

*Generated for the ITP artifact review. Corrections to this page belong with the
underlying note under `docs/paper-gaps/` and with the register, not here alone.*
