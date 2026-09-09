<!-- scout: scout-123-global-pair-game-20260906-01 2026-09-06 -->
## Mathlib scouting report — 2026-09-06

### Mathematical source

- **Primary:** `lem:qld-4-7`, especially the passage from extended lines to low-degree soundness, `references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1267`. Its proof first constructs a passing classical strategy, projectivizes it, and obtains a measurement of extended polynomials. Only afterward does it bound noncombined outcomes and restrict to polynomial pairs.
- **Input:** `lem:qld-4-13`, `references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1020`: extended-line POVMs, both line–point consistency orientations, and degree-\(d\) support on axis lines.
- **Soundness:** `lem:ld-soundness`, `references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:413`. The directly indexed \(k=1\) theorem is the relevant implemented replacement; do **not** construct a seed-indexed parameter tuple requiring \((2m+2)\mid q\).
- **Blueprint:** `blueprint/src/chapter/ch15_qpbt_combining.tex:1890` describes the transport obligations, but some listed obligations now have merged APIs.

**Statement to construct:** Given an actual `ExtendedLinesWitness S points δL`, use its measurements and the existing joint-point witness to construct—not assume—a passing strategy for `directLdGame P.extendedDirectLd`. Projectivize that strategy, apply \(k=1\) soundness, and transport the polynomial measurements and consistency conclusions back to the original expanded local spaces.

**Scope:** This report stops at that construction and transport interface. It does not construct the input witness, redo #118, prove the noncombined-mass estimates, redo error-family absorption, or modify `Apply`.

**Snapshot and prior work:** Inspected committed `main` at `b2f252a`. Both requested GitHub issue reads failed because network sockets are prohibited. The local issue snapshot identifies this as #119 prerequisite work for #123. Earlier #119 session reports identify the passing-game prerequisite but do not supply the construction below; their unmerged completion declarations are **not** treated as merged APIs.

### Relevant Mathlib definitions

- `Equiv.optionCongr` — `.lake/packages/mathlib/Mathlib/Logic/Equiv/Option.lean:38` — transports the witness’s completed scalar alphabet without identifying `none` with a field element.
- `Equiv.funUnique` — `.lake/packages/mathlib/Mathlib/Logic/Equiv/Defs.lean:567` — removes the singleton tuple index after \(k=1\) soundness.
- `MvPolynomial.map` and `MvPolynomial.eval_map` — `.lake/packages/mathlib/Mathlib/Algebra/MvPolynomial/Eval.lean:432` — coefficient-field transport and its evaluation identity.

### Relevant Mathlib lemmas and theorems

- `Matrix.PosSemidef.submatrix` — `.lake/packages/mathlib/Mathlib/LinearAlgebra/Matrix/PosDef.lean:80` — positivity of the distinguished-ancilla compression of a POVM effect.
- `Polynomial.card_roots'` — `.lake/packages/mathlib/Mathlib/Algebra/Polynomial/Roots.lean:80` — the univariate collision estimate needed to pass from evaluated line agreement to equality of coefficient answers.
- `Polynomial.ext` — `.lake/packages/mathlib/Mathlib/Algebra/Polynomial/Basic.lean:706` — proves injectivity of the coefficient-list polynomial representation.
- `MvPolynomial.degrees_map_of_injective` — `.lake/packages/mathlib/Mathlib/Algebra/MvPolynomial/Degrees.lean:196` — preserves the bounded-polynomial carrier under the scalar ring equivalence.

These are adaptable components, not a Mathlib theorem constructing this game strategy. No usable finite-POVM Naimark construction was found in Mathlib; the project already supplies it. The Gelfand–Naimark–Segal search hit is not that result.

### Relevant MIPStarRE declarations

“Implemented” below means a proof body is present in the inspected source. It does **not** assert a fresh transitive axiom check.

- **Exact input:** `MIPStarRE.QPBT.ExtendedLinesWitness` — `MIPStarRE/QPBT/Combining/Witnesses.lean:288` — complete line POVMs, axis-degree support, and both completed-answer consistency bounds. This is sufficient input for the proposed construction; do not call an existential producer.
- **Exact point measurement definition:** `MIPStarRE.QPBT.CombinedPointsWitness.extendedQ` — `MIPStarRE/QPBT/Combining/Points.lean:40` — the required \(\alpha a+\beta b\) coarse-graining. However, `MIPStarRE.QPBT.extendedQ_spec` at `MIPStarRE/QPBT/Combining/Points.lean:61` still ends in `sorry`. The passing-game proof should derive its needed projectivity/self-consistency subclaims from the supplied witness, not silently use this unfinished theorem.
- **Exact direct-game interface:** `MIPStarRE.QPBT.directLdWinPredicate` — `MIPStarRE/QPBT/Combining/DirectLowDegree/Game.lean:153` — checks answer tags, four line–point branches, point equality, and **coefficient equality on both same-line-type branches**. Merely proving line–point consistency does not prove its value bound.
- **Exact value accounting:** `MIPStarRE.QPBT.directLdBranchRejectionProbability` — `MIPStarRE/QPBT/Combining/DirectLowDegree/GameValue.lean:69`; `MIPStarRE.QPBT.directLdRejectionProbability_eq_one_sub_value` — `MIPStarRE/QPBT/Combining/DirectLowDegree/GameValue.lean:148` — use the nine-branch rejection decomposition.
- **Exact consistency tools:** `MIPStarRE.QPBT.DistanceCalculus.consistencyDefect_trans_le` — `MIPStarRE/QPBT/Games/DistanceTheorems/Calculus.lean:311`; `MIPStarRE.QPBT.DistanceCalculus.consistencyDefect_postprocess_le` — `MIPStarRE/QPBT/Games/DistanceTheorems/Calculus.lean:382` — derive evaluated line agreement and coarse-grained point agreement.
- **Especially useful near-match:** `MIPStarRE.QPBT.SandwichProduct.consistencyDefect_codewords_le_evaluated_add` — `MIPStarRE/QPBT/Games/Sandwich/Support.lean:324` — already proves full-outcome consistency from evaluated consistency plus a collision bound. Instantiate its codewords with coefficient lists; do not reprove its operator-valued argument.
- **Exact projectivity under coarse-graining:** `MIPStarRE.QPBT.SandwichProduct.postprocess_isProjective` — `MIPStarRE/QPBT/Games/Sandwich/Support.lean:528` — applies to the supplied projective joint-point measurements.
- **Exact Naimark building blocks:** `MIPStarRE.QPBT.dilatedMeasurement` — `MIPStarRE/QPBT/Games/StrategyClasses.lean:278`; `MIPStarRE.QPBT.dilatedMeasurement_isProjective` — `MIPStarRE/QPBT/Games/StrategyClasses.lean:288`; `MIPStarRE.QPBT.dilatedMeasurement_compression` — `MIPStarRE/QPBT/Games/StrategyClasses.lean:303`. The public assembly APIs are `MIPStarRE.QPBT.paddedStrategy` at `MIPStarRE/QPBT/Games/StrategyClasses.lean:360`, `MIPStarRE.QPBT.paddedStrategy_isProjective` at `MIPStarRE/QPBT/Games/StrategyClasses.lean:374`, and `MIPStarRE.QPBT.paddedStrategy_value` at `MIPStarRE/QPBT/Games/StrategyClasses.lean:387`. The convenient `projectiveDilation` wrapper in that file is **private**.
- **Exact \(k=1\) soundness:** `MIPStarRE.QPBT.exists_directSimultaneousPolynomialMeasurements_of_k_eq_one` — `MIPStarRE/QPBT/Combining/DirectLowDegree/Transport/Simultaneous.lean:206` — returns both point–polynomial relations and polynomial–polynomial consistency, without requiring positive error. `MIPStarRE.QPBT.exists_direct_ld_soundness_of_k_eq_one` — `MIPStarRE/QPBT/Combining/DirectLowDegree/Soundness.lean:244` — additionally supplies the `deltaLd` error form, with a strictly positive error argument.
- **Exact fixed-space rounding tool:** `MIPStarRE.QPBT.projective_rounding_with_explicit_constant` — `MIPStarRE/QPBT/Games/DistanceTheorems/ProjectiveRounding.lean:495` — rounds a consistent POVM on its **existing** local space, with squared-distance bound \(220\delta^{1/4}\). This is important after compression.

### Suggested approach

#### 1. Construct the raw answers on the correct local spaces

Write \(D=P.\mathrm{extendedDirectLd}\), \(c=md+1\), and \(R=\mathrm{PauliRegister}(P)\).

Use local spaces \(A\otimes R\) and \(B\otimes R\), with state
\[
\chi=\operatorname{shuffle}\bigl(\psi\otimes\mathrm{EPR}_{R,R}\bigr).
\]

Do **not** declare the six-register state itself to be a vector on these two smaller spaces. Prove its relevant correlations equal those of \(\chi\):

- the first identity removes the spectator \(B'B''\) EPR pair and identifies placements \(AA',BA''\);
- the second removes \(A'A''\) and uses EPR swap symmetry to identify placements \(AB'',BB'\).

Both identities are necessary: the two fields of the line witness initially use different register placements.

Answer each question as follows:

- **Point:** measure the supplied joint-point coarse-graining, map its scalar through the inverse canonical field equivalence, and emit `.pointVals`.
- **Axis:** measure the supplied canonical axis-line POVM, truncate to degree \(d\), and emit `.alinePolys`.
- **Diagonal:** measure the supplied canonical diagonal-line POVM, zero-pad its degree-\(c\) coefficient list to degree \(D.mD.d\), and emit `.dlinePolys`.

Truncation is justified by `axis_degree`: effects on which truncation changes the polynomial are zero. Padding is a genuine polynomial-preserving injection because \(md+1\le(2m+2)d\).

**Independently checked answer skeleton.** The following block passed `lake env lean --stdin` with exit status 0 in this session. It constructs measurements only; it makes no passing or existence claim.

```lean
import MIPStarRE.QPBT.Combining.Points

open MIPStarRE.QPBT MIPStarRE.Quantum

noncomputable section
namespace Scout123

def axisRead (params : AdmissibleParams)
    (coeffs : DirectDegPoly params.extendedDirectLd (params.m * params.d + 1)) :
    DirectDegPoly params.extendedDirectLd params.d :=
  fun index => coeffs ⟨index.val, by
    have := params.one_le_m
    have := params.hd
    have := Nat.mul_le_mul_right params.d params.one_le_m
    omega⟩

def diagonalRead (params : AdmissibleParams)
    (coeffs : DirectDegPoly params.extendedDirectLd (params.m * params.d + 1)) :
    DirectDegPoly params.extendedDirectLd
      (params.extendedDirectLd.m * params.extendedDirectLd.d) :=
  fun index => if bound : index.val < params.m * params.d + 2
    then coeffs ⟨index.val, bound⟩ else 0

def pointAnswer (params : AdmissibleParams) (answer : PauliScalar params) :
    DirectLdAnswer params.extendedDirectLd :=
  .pointVals (fun _ => (extendedDirectScalarEquiv params).symm answer)

def answerMeasurement {params : AdmissibleParams} {epsilon deltaQ deltaL : ℝ}
    {setting : ProjectiveSetting params epsilon}
    {points : CombinedPointsWitness setting deltaQ}
    (lines : ExtendedLinesWitness setting points deltaL)
    (side : PlayerSide) (question : DirectLdQuestion params.extendedDirectLd) :
    Measurement (DirectLdAnswer params.extendedDirectLd)
      (setting.ExpandedLocalSpace side) :=
  match question.1 with
  | .point =>
    let point := directPointToPauli params question.2.point
    (points.extendedQ side (projX point) (projZ point)
      (point (alphaVar params.m)) (point (betaVar params.m))).postprocess
        (pointAnswer params)
  | .aline =>
    (lines.Qline side (directALineDescOf params.extendedDirectLd question.2)).postprocess
      (fun coeffs => .alinePolys (fun _ => axisRead params coeffs))
  | .dline =>
    (lines.Qline side (directDLineDescOf params.extendedDirectLd question.2)).postprocess
      (fun coeffs => .dlinePolys (fun _ => diagonalRead params coeffs))

end Scout123
```

The state expression also elaborated:
```lean
reindexState prodShuffle
  (vecTensor setting.toStrategy.ψ (eprState (PauliRegister params)))
```

Its normalization follows from the source implementations of `MIPStarRE.QPBT.reindexState_norm_eq` at `MIPStarRE/QPBT/State.lean:86`, `MIPStarRE.QPBT.vecTensor_norm_eq` at `MIPStarRE/QPBT/State.lean:99`, and `MIPStarRE.QPBT.eprState_norm` at `MIPStarRE/QPBT/Algebra/Pauli.lean:435`.

#### 2. Prove all nine branch bounds

Let \(p\) be the derived point–point rejection bound; \(p\le\delta_Q\) is sufficient.

- Derive \(p\) directly from joint-point self-consistency, projectivity, and consistency data processing. This does not need the unfinished full `extendedQ_spec`.
- Each of the four line–point branches has rejection at most \(2\delta_L\), by extracting its half of the witness’s axis/diagonal mixture.
- The two mixed axis/diagonal branches accept: all constructed answers have the correct tags.
- The remaining two branches require a **new application of the existing codeword-consistency theorem**, not an additional hypothesis.

For those same-type branches, first express the line–point law as sampling a line from its marginal and an independent uniform parameter \(t\). Compare
\[
Q_A^\ell(t),\quad Q_B^{u(t)},\quad Q_A^{u(t)},\quad Q_B^\ell(t).
\]
The existing consistency triangle gives evaluated line agreement bounded by
\[
e=2\delta_L+2\sqrt{p+2\delta_L}.
\]
The codeword theorem then gives full coefficient agreement bounded by \(e+c/q\). On axis lines this bound is conservative; one can use \(d/q\).

Consequently a sufficient raw-game rejection bound is
\[
\rho=\frac{p+4(2\delta_L)+2(e+c/q)}9.
\]
This is branch accounting, not a replacement for the already-owned scalar absorption work.

**Zero directions:** do not discard them and do not replace `none` by zero. A successful completed evaluation certifies the scalar evaluation for **every** presenting parameter. Therefore scalar evaluation at a freshly sampled parameter has failure probability no greater than the completed-answer failure. This lets the parameterized codeword argument include zero-direction lines without an injectivity assumption on their parametrization.

#### 3. Projectivize with the existing public APIs

A question-independent ancilla `Option (DirectLdAnswer D)` is enough: every raw measurement uses the same full answer alphabet.

The following is a source-checked assembly skeleton using the public APIs listed above. It is not an additional assumption and does not assert a raw value bound.

```lean
import MIPStarRE.QPBT.Combining.DirectLowDegree.Game
import MIPStarRE.QPBT.Games.StrategyClasses

open MIPStarRE.QPBT

noncomputable section
namespace Scout123

def projectivized (params : DirectLdParams)
    (raw : Strategy (directLdGame params)) : Strategy (directLdGame params) :=
  paddedStrategy raw (none : Option (DirectLdAnswer params))
    (none : Option (DirectLdAnswer params))
    (fun question => dilatedMeasurement default (raw.A question))
    (fun question => dilatedMeasurement default (raw.B question))

example (params : DirectLdParams) (raw : Strategy (directLdGame params)) :
    (projectivized params raw).IsProjective :=
  paddedStrategy_isProjective raw none none _ _
    (fun question => dilatedMeasurement_isProjective default (raw.A question))
    (fun question => dilatedMeasurement_isProjective default (raw.B question))

example (params : DirectLdParams) (raw : Strategy (directLdGame params)) :
    (projectivized params raw).value = raw.value :=
  paddedStrategy_value raw none none _ _
    (fun question answer =>
      dilatedMeasurement_compression default answer (raw.A question))
    (fun question answer =>
      dilatedMeasurement_compression default answer (raw.B question))

end Scout123
```

Use the proved raw value bound and this exact value identity to satisfy soundness. No additional game-passing premise belongs in the eventual constructor from `lines`.

#### 4. Apply \(k=1\) soundness, then compress

Apply the singleton theorem with `D.k = 1` proved by `rfl`. Retain **all three** returned consistency relations.

For each returned measurement \(G\) on \(I\times\mathrm{Option}(\mathrm{Answer})\), construct its corner POVM:
\[
(\operatorname{corner}G)_g(i,j)=G_g((i,\mathrm{none}),(j,\mathrm{none})).
\]

Positivity follows from the Mathlib submatrix lemma; completeness follows by taking the same corner of the sum identity. Prove corner compression commutes with postprocessing.

The existing `MIPStarRE.QPBT.stateQForm_padState` — `MIPStarRE/QPBT/Games/StrategyClasses.lean:214` — supplies exact correlation preservation. Apply it to both polynomial measurements and to the strategy’s point measurements. This returns the three consistency statements to \(\chi\).

Next remove the singleton polynomial tuple and transport coefficients through the canonical scalar equivalence. Evaluation must commute with that transport; this is where `MvPolynomial.eval_map` is used.

#### 5. Restore projectivity on the original spaces

**Compression does not preserve projectivity.** Thus “Naimark, soundness, compress, mark projective” is not a valid construction of the fixed-space global witness.

Instead, use the retained polynomial–polynomial consistency to apply the existing fixed-space projective-rounding theorem to the compressed pair, on each side. Transfer the point-consistency conclusions with an explicit quantitative argument.

One robust transfer route is:

1. use full-polynomial consistency and rounding closeness to bound consistency of the rounded and opposite compressed polynomial measurements;
2. data-process that relation to evaluations;
3. combine with the opposite compressed measurement’s point relation and point–point consistency using the existing consistency triangle.

Do not assume arbitrary coarse-graining contracts squared operator-family distance.

This replaces the paper’s informal second Naimark step by dimension-preserving rounding. It incurs an explicit additional error, to be handed to existing error-absorption work, and should be documented as the mathematical replacement needed by the fixed-space Lean interface.

Finally use the two register-correlation identities from step 1 to recover the original six-register placements.

### Gaps to fill

The natural implementation location is a new #119 helper module such as `MIPStarRE/QPBT/Combining/GlobalPair/DirectStrategy.lean`, with transport separated if needed. Proposed names below are **new targets**, not existing declarations.

1. **`MIPStarRE.QPBT.directEvalOpt_eq_some_iff`** — exact characterization:
   ```lean
   ∀ (params : DirectLdParams) (degree : ℕ)
     (line : DirectLineDesc params)
     (point : Fin params.m → DirectScalarQ params)
     (coeffs : DirectDegPoly params degree) (answer : DirectScalarQ params),
     directEvalOpt line point coeffs = some answer ↔
       DirectEvaluatesTo line coeffs point answer
   ```
   Add the padding/truncation evaluation identities and on-support canonical-question identities. These are the small answer-conversion obligations.

2. **`MIPStarRE.QPBT.directALinePointDist_eq_parameter`**, and its diagonal counterpart — target:
   ```lean
   ∀ params : DirectLdParams,
     (Distribution.prod
       ((directALinePointDist params).map Prod.fst)
       (uniformDistribution (DirectScalarQ params))).map
         (fun sample =>
           (sample.1, sample.1.base + sample.2 • sample.1.direction)) =
       directALinePointDist params
   ```
   Prove by uniform translation/rebasing. Include zero directions. Existing direct geometry defines the required laws, but this resampling equality was not found.

3. **`MIPStarRE.QPBT.extendedPairState_correlation_alice` / `_bob`** — for arbitrary local operators, identify
   \[
   \langle\chi,(A\otimes B)\chi\rangle
   \]
   with the corresponding products of placements on `S.psiHat`. These give all consistency transports by finite summation. No exact public lemma for these two reductions was found.

4. **`MIPStarRE.QPBT.ExtendedLinesWitness.directStrategy_value_ge`** — takes the supplied witness, not a passing-game assumption, and proves the branch bound \(\rho\) above for its explicit raw strategy. Use the existing codeword theorem; only its coefficient-list collision specialization is needed.

5. **`MIPStarRE.QPBT.cornerMeasurement`**, its effect/postprocess identities, and two-sided consistency compression — input a POVM on `ι × κ` and a distinguished `κ`; output a POVM on `ι`. The existing correlated-ancilla compression averages blocks and is not a substitute for the distinguished Naimark corner.

6. **`MIPStarRE.QPBT.extendedDirectPolyEquiv`**, evaluation transport, and the fixed-space rounding transfer — complete the return from soundness tuples on padded spaces to extended-polynomial measurements on `S.ExpandedLocalSpace`.

**Actual remaining blockers:**

- The raw measurement construction is concrete, but the parameter-law, register-correlation, and branch proofs are not presently assembled.
- The full `extendedQ_spec` remains open; only its needed subclaims should be derived here from the supplied witness.
- Fixed-space compression/rounding transport is necessary and not yet supplied by a merged global-pair constructor.
- Even after these steps, `eq:qld-g-non-separable` and the subsequent ordered-product consistency argument remain separate quantitative obligations. This report does **not** claim that an extended-polynomial measurement already establishes `GlobalPairWitness`.

### Searched

- Read the committed scout personas, paper construction, direct-game source, active blueprint, API register, relevant preliminary/projectivization audit material, and earlier local #119 reports.
- Searched Mathlib by Naimark/Neumark/POVM terminology, PSD submatrix type shape, polynomial roots, coefficient extensionality, scalar mapping, and finite equivalences.
- Searched the project’s `Quantum`, `LDT/Basic`, Naimark, game-distance, sandwich/codeword, direct-game transport, point, witness, and extraction APIs.
- Searched specifically for completed direct evaluation lemmas, parameter-resampling laws, expanded-register correlation transport, distinguished-corner measurement compression, and an existing witness-to-direct-strategy constructor; no usable exact implementations were found.

**Validation limitation:** the answer-construction skeleton passed. Broader API probes encountered stale compiled objects: the cached direct soundness object predates the current source, and its simultaneous-transport object is absent. Cached probes also report `sorryAx` for the older rounding theorem. These observations cannot certify the current source’s transitive axioms. No cache refresh, file creation, build, mutation, or subagent was used.

**Handoff:** implement the six helper groups in dependency order, starting from the supplied `lines`. The deliverable is an explicit passing strategy and verified transport—not a new witness-existence assumption.