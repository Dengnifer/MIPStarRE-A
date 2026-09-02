# Implementation brief — stage 4.2, residual of ch11/ch12/ch13

Deliverable: Lean skeleton (all proofs `sorry`, definitions real) for **every node of
`blueprint/src/chapter/ch11_qpbt_algebra.tex`, `ch12_qpbt_games.tex`,
`ch13_qpbt_test.tex` not in the stage-4.1 statement closure**. Paper mirrors:
`references/qpbt-paper/04_preliminaries.tex` (ch11), `05_conditionally_linear_functions.tex`
+ `06_nonlocal_games_and_mipstar.tex` + `07_types.tex` (ch12),
`08_classical_and_quantum_low_degree_tests.tex` (ch13); exact per-node line ranges are
pinned in docstrings at implementation time. Baseline:
`local/briefs/0006-minimal-skeleton-brief.md` (stage 4.1) — its naming table is **FROZEN**
and reused verbatim; nothing below renames or redefines a 4.1 declaration. Conventions:
`AGENTS.md`; every statement-like docstring cites the blueprint `\label` and the
qpbt-paper file/lines, and every Lean-only auxiliary says so explicitly.

Scope arithmetic: ch11/ch12/ch13 carry 96 `def:`/`lem:`/`prop:`/`thm:`/`cor:`/`fact:`
labels; 37 are the in-track part of the 4.1 closure (39 minus its two ch03 nodes).
**49 nodes remain and are the scope of this brief**: 12 in ch11, 26 in ch12, 11 in ch13.

## (a) Residual nodes in dependency order, with env kind

Order is topological for statement-level `\uses` (proof-level excluded, per the 4.1
method). The blocks are independent in this order — ch11 residual reaches only 4.1 nodes,
ch12 residual only 4.1 + ch03 nodes, ch13 residual reaches ch11 and ch12 residual nodes.

### ch11 — 12 nodes (`04_preliminaries.tex`)

| # | label | env | residual-internal statement deps |
|---|-------|-----|---------------------------------|
| 1 | `lem:perp_perp` | lemma | — |
| 2 | `def:Lperp` | definition | — |
| 3 | `lem:L_perp_perp` | lemma | def:Lperp |
| 4 | `lem:schwartz-zippel` | lemma | — (restatement of a `\leanok` ch03 node) |
| 5 | `def:decoding-map` | definition | — |
| 6 | `def:dual-self-dual-normal-basis` | definition | — |
| 7 | `lem:downsize_field` | lemma | 6 |
| 8 | `lem:one` | lemma | 6 |
| 9 | `def:binary-representation` | definition | 6 |
| 10 | `lem:twisted-commutation` | lemma | — |
| 11 | `lem:cancellation` | lemma | — |
| 12 | `lem:pauli-binary` | lemma | 9 |

### ch12 — 26 nodes (`05_…`, `06_…`, `07_types.tex`)

| # | label | env | deps | # | label | env | deps |
|---|-------|-----|------|---|-------|-----|------|
| 13 | `def:bracket` | definition | — (already `\leanok`) | 26 | `fact:triangle` | lemma | — |
| 14 | `def:projective-strategy-general` | definition | — | 27 | `fact:triangle-for-simeq` | lemma | 20 |
| 15 | `def:symmetric-game` | definition | — | 28 | `fact:data-processing` | lemma | 13, 20 |
| 16 | `lem:symmetric-strat` | lemma | 14, 15 | 29 | `lem:commutation-analysis` | lemma | — |
| 17 | `def:comm-strategy` | definition | — | 30 | `lem:ld-sandwich` | lemma | 13, 20 |
| 18 | `def:consistent-measurement` | definition | — | 31 | `lem:pasting` | lemma | 13, 20 |
| 19 | `def:consistent-strategy` | definition | 14, 18 | 32 | `lem:close-strategies-have-close-values` | lemma | 14, 21 |
| 20 | `def:consistency` | definition | — | 33 | `lem:cl-kth` | lemma | — |
| 21 | `def:strategy-distance` | definition | — | 34 | `lem:cl-func-prod` | lemma | — |
| 22 | `def:spcc` | definition | 14, 17, 19, 15 | 35 | `lem:cl-dist-prod` | lemma | 34 |
| 23 | `fact:agreement` | lemma | 20 | 36 | `def:typed-cl-functions` | definition | — |
| 24 | `fact:add-a-proj` | lemma | — | 37 | `def:typed-cl-distributions` | definition | 36 |
| 25 | `fact:add-a-proj2` | lemma | — | | | | |
| 25b | `lem:cool-closeness-fact` | lemma | — | | | | |

### ch13 — 11 nodes (`08_classical_and_quantum_low_degree_tests.tex`)

| # | label | env | residual-internal statement deps |
|---|-------|-----|---------------------------------|
| 38 | `lem:alnf` | lemma | — |
| 39 | `lem:dlnf` | lemma | — |
| 40 | `def:line-point-dist` | definition | 38, 39 |
| 41 | `def:ld-meas` | definition | — |
| 42 | `lem:ld-soundness` | theorem (imported) | 41, 14, 20, 13 |
| 43 | `thm:ms-rigidity` | theorem (imported) | — |
| 44 | `thm:ms-from-ac` | theorem | 18, 22 |
| 45 | `lem:pauli-completeness` | lemma | 22 |
| 46 | `cor:pauli-binary` | corollary | — at statement level (see OPEN-2) |
| 47 | `def:introparams` | definition | — |
| 48 | `lem:delta-bound` | lemma | 47 |

Eleven `rem:` nodes carry no declaration and are cited in docstrings only
(`rem:schwartz-zippel-restated`, `rem:pauli-binary-source`, `rem:naimark-for-games`,
`rem:projective-strategy-relation`, `rem:symmetric-strat-limit`, `rem:asymptotic-distance`,
`rem:ld-sandwich-indexing`, `rem:ld-win-zero-direction`, `rem:ld-soundness-provider`,
`rem:delta-qld-argument-order`, `rem:delta-bound-exponent-comparison`).

## (b) Proposed files extending the 4.1 tree

Namespace `MIPStarRE.QPBT` throughout, as in 4.1. **No 4.1 file is edited**; the only
shared-file change is one re-export line per new file in `MIPStarRE/QPBT.lean` (the sole
merge point, OPEN-6). All files far below the 1000-line cap (estimates in parentheses);
real definitions are separated from `sorry` statements per the LDT `Defs`/`Theorems`
convention, so each new `*Theorems.lean` sits beside the 4.1 file it consumes.

```
MIPStarRE/QPBT/Algebra/SubspacesTheorems.lean      -- nodes 1,2,3                (~110)
MIPStarRE/QPBT/Algebra/SelfDualBasis.lean          -- nodes 6,9                  (~170)
MIPStarRE/QPBT/Algebra/SelfDualBasisTheorems.lean  -- nodes 7,8                  (~120)
MIPStarRE/QPBT/Algebra/LowDegreeCodeTheorems.lean  -- nodes 4,5                  (~100)
MIPStarRE/QPBT/Algebra/PauliTheorems.lean          -- nodes 10,11,12             (~230)
MIPStarRE/QPBT/Games/StrategyClasses.lean          -- nodes 14,15,17,18,19,22,16 (~280)
MIPStarRE/QPBT/Games/Consistency.lean              -- nodes 20,21                (~120)
MIPStarRE/QPBT/Games/DistanceTheorems.lean         -- nodes 23,24,25,25b,26,27,28,29,32 (~310)
MIPStarRE/QPBT/Games/Sandwich.lean                 -- nodes 30,31                (~230)
MIPStarRE/QPBT/Games/CondLinearTheorems.lean       -- nodes 33,34,35             (~210)
MIPStarRE/QPBT/Games/TypedCondLinear.lean          -- nodes 36,37                (~110)
MIPStarRE/QPBT/Test/LowDegreeGameTheorems.lean     -- nodes 38,39,40,41,42       (~290)
MIPStarRE/QPBT/Test/MagicSquareTheorems.lean       -- nodes 43,44                (~240)
MIPStarRE/QPBT/Test/Completeness.lean              -- node 45                    (~100)
MIPStarRE/QPBT/Test/QubitForm.lean                 -- node 46                    (~120)
MIPStarRE/QPBT/Test/CanonicalParams.lean           -- nodes 47,48                (~130)
```

Node 13 (`def:bracket`) gets no file: it is REUSE of an existing `\leanok` declaration.
Internal import DAG (new files only; each also imports the 4.1 file it extends):
`Algebra/Subspaces ← SubspacesTheorems`; `Algebra/FieldBasis ← SelfDualBasis ←
SelfDualBasisTheorems`; `Algebra/LowDegreeCode ← LowDegreeCodeTheorems`;
`{Algebra/Pauli, SelfDualBasisTheorems, Algebra/Subspaces} ← PauliTheorems`;
`{Games/Defs, Games/Distance} ← StrategyClasses`; `Games/Distance ← Games/Consistency`;
`{Games/Consistency, StrategyClasses} ← DistanceTheorems ← Sandwich`;
`Games/CondLinear ← CondLinearTheorems ← TypedCondLinear`;
`{Test/LowDegreeGame, Games/Consistency, StrategyClasses, Algebra/Lines} ←
Test/LowDegreeGameTheorems`; `{Test/MagicSquare, StrategyClasses, Games/Distance,
Algebra/Pauli} ← Test/MagicSquareTheorems`; `{Test/PauliBasisTest, StrategyClasses,
Test/MagicSquareTheorems, Test/LowDegreeGameTheorems} ← Test/Completeness`;
`{Test/Soundness, PauliTheorems, SelfDualBasis} ← Test/QubitForm`;
`Test/Soundness ← Test/CanonicalParams`. External imports as in 4.1 (b), plus
`LDT.Preliminaries.Polynomials` (node 4), `LDT.Basic.DistributionProduct` (node 35), and
Mathlib `FieldTheory.Finite.GaloisField` / `Algebra.Trace` (nodes 6–9).

## (c) Node → declaration mapping

Legend as in 4.1: R = reuse an existing declaration, N = new; signatures are sketches —
the implementer owns the final form. Ambient: `K := FieldModel.K q`,
`Cube m := Fin m → Bool`, `Op ι := Matrix ι ι ℂ`, `Point L := Fin L.m → ScalarQ L`.
4.1 frozen names used below (RECONCILE-1): `heteroKron`, `conjIsometry`, `isometryTensor`,
`reindexState`, `stateDistSq`, `opFamilyDistSq`, `eprState`, `pauliProj`, `tauObservable`,
`PauliKind`, `Game`, `Strategy`, `Measurement`, `Measurement.IsProjective`,
`canonicalProjOfKernel`, `dotOrthogonal`, `binTrace`, `kappa`, `IsAdmissibleSize`,
`indicatorVec`, `lowDegreeEnc`, `indicatorPoly`, `linePoints`, `lineRepMap`,
`IsCondLinearOn`/`IsCondLinear`, `clDistribution`, `graphDistribution`, `LdParams`,
`ldGame`, `ldPointCL`/`ldALineCL`/`ldDLineCL`, `chiIndex`, `ScalarQ`, `msGame`, `MsType`,
`AdmissibleParams`, `PauliRegister`, `pauliBasisTest`, `deltaQld`, `pauli_soundness`.

| label | Lean name | file | R/N | signature sketch |
|---|---|---|---|---|
| lem:perp_perp | `finrank_add_finrank_dotOrthogonal`, `dotOrthogonal_dotOrthogonal` | Algebra/SubspacesTheorems | N | `theorem … (W : Submodule K (ι → K)) : Module.finrank K W + Module.finrank K (dotOrthogonal W) = Fintype.card ι`; `theorem … : dotOrthogonal (dotOrthogonal W) = W` (both `sorry`) |
| def:Lperp | `canonicalProjPerp` | Algebra/SubspacesTheorems | N | `noncomputable def canonicalProjPerp (L : (Fin n → K) →ₗ[K] (Fin n → K)) : (Fin n → K) →ₗ[K] (Fin n → K) := canonicalProjOfKernel (dotOrthogonal (LinearMap.ker L))` — real; basis-independence is definitional in this encoding (4.1 (e)5), docstring records that the source's "basis `F` for `ker(L)^⊥`" is elided |
| lem:L_perp_perp | `ker_canonicalProjPerp` | Algebra/SubspacesTheorems | N | `theorem … : LinearMap.ker (canonicalProjPerp L) = dotOrthogonal (LinearMap.ker L)` (`sorry`) |
| lem:schwartz-zippel | `MIPStarRE.LDT.Preliminaries.schwartzZippel_totalDegree` | — (LDT) | R | already `\leanok`; the ch11 node is a restatement (its blueprint proof says so). No new decl; `LowDegreeCodeTheorems` carries a module-docstring pointer plus a bridge lemma `schwartzZippel_of_polyFunc` **only if** the LDT statement's index/degree packaging does not match verbatim (RECONCILE-4). `rem:schwartz-zippel-restated`'s `md/q` form is `schwartzZippel_individualDegree` (also `\leanok`) |
| def:decoding-map | `decodeAt`, `decodeBool` | Algebra/LowDegreeCodeTheorems | N | `def decodeAt (H : Finset K) (g : (Fin m → K) → K) : Cube m → K := fun y => if g (cubeEmbed y) ∈ H then g (cubeEmbed y) else 0`; `abbrev decodeBool := decodeAt {0,1}`; companion `decodeAt_lowDegreeEnc (h : ∀ y, a y ∈ H) : decodeAt H (lowDegreeEnc a) = a` (`sorry`). `cubeEmbed : Cube m → (Fin m → K)` is the `{0,1} ⊆ F_q` inclusion (RECONCILE-2) |
| def:dual-self-dual-normal-basis | `IsDualBasisPair`, `Basis.IsSelfDual`, `Basis.IsNormal`, `exists_selfDualNormalBasis` | Algebra/SelfDualBasis | N | `def IsDualBasisPair (b b' : Basis (Fin k) F K) : Prop := ∀ i j, Algebra.trace F K (b i * b' j) = if i = j then 1 else 0`; `def Basis.IsSelfDual (b) : Prop := IsDualBasisPair b b`; `def Basis.IsNormal (b) : Prop := ∃ α : K, ∀ j, b j = α ^ (q ^ (j : ℕ))`; `theorem exists_selfDualNormalBasis (k : ℕ) (hk : Odd k) : ∃ b : Basis (Fin k) (ZMod 2) K, b.IsSelfDual ∧ b.IsNormal` (`sorry`; the source's explicit construction is not reproduced) |
| def:binary-representation | `FixedFieldModel.binaryCoordinates`, `multiplicationTable`, `chi`, `binaryCoordinates_mul` | Algebra/SelfDualBasis | N | `noncomputable abbrev FixedFieldModel.binaryCoordinates (F : FixedFieldModel q) : F.K ≃ₗ[ZMod 2] (Fin F.basisDim → ZMod 2) := kappa F.basis`; multiplication tables reuse the landed generic `multiplicationTable`; `chi` uses product indices, never `Fin (s*k)`; `binaryCoordinates_mul` states eq:eq-mult (`sorry`). Keep this coordinate map distinct from the landed `binaryRepresentation : F.K ≃ Fin q`, which is serialization rather than the source's bit-coordinate map. Add no `SelfDualNormalRep` carrier |
| lem:downsize_field | `basisCoord_apply_eq_trace`, `trace_mul_eq_dotProduct_basisCoord`, `chi_mulVec_basisCoord` plus canonical specializations | Algebra/SelfDualBasisTheorems | N | state all three source results for abstract fields `F ⊆ K` and an arbitrary basis `b`, with self-duality required only by items 1 and 2; item 3 is basis-generic. Then derive named `FixedFieldModel` specializations for QPBT consumers without adding basis arguments to test-facing theorems (all proof statements `sorry`) |
| lem:one | `trace_basis_eq_one_of_selfDual_normal`, `basisCoord_one_of_selfDual_normal` plus canonical specializations | Algebra/SelfDualBasisTheorems | N | state the source theorem for an arbitrary self-dual normal basis of a binary odd-degree extension, then specialize it to `F.basis` using `F.selfDual`, `F.normal`, and `F.basisDimOdd` (all proof statements `sorry`) |
| lem:twisted-commutation | `primeTauShift`, `primeTauPhase`, `primeTauObservable`, `primeTauObservable_mul`, `primeTauObservable_pow`, `primeTauObservable_pow_char`, `primeTauObservable_X_mul_Z`; binary specializations `tauObservable_mul`, `tauObservable_sq`, `tauObservable_X_mul_Z` | Algebra/PauliTheorems | N | for `{p : ℕ} [Fact p.Prime]` and a finite field `K` with `Algebra (ZMod p) K`, define the source-general operators with `MIPStarRE.LDT.Preliminaries.ffChar`. The linked theorem states the product, prime-field power, characteristic power, and multi-qudit twisted relation with phase `ffChar (-dotProduct a b)` and `[Nonempty ι]` for the source's `n ≥ 1` (all theorem proofs `sorry`). Keep the landed characteristic-two operators and derive separately named binary specializations for QPBT consumers; never link those specializations as the unrestricted source lemma |
| lem:cancellation | `submoduleExpect`, `ffChar_dotProduct_submodule_expect_eq_zero`; binary specialization `avg_neg_one_pow_binTrace_eq_zero` | Algebra/PauliTheorems | N | for the same source-general prime/field parameters, `submoduleExpect V f := 𝔼 u : V, f u` uses `Fintype.ofFinite V`, and `ffChar_dotProduct_submodule_expect_eq_zero (hv : v ∉ dotOrthogonal V)` states the complex-valued Fourier cancellation (`sorry`). The project `avgOver` helper is real-valued and must not be used for this complex expectation. A separately named characteristic-two corollary may serve QPBT proofs |
| lem:pauli-binary | `qubitPauliProj`, `exists_qubitIsometry` | Algebra/PauliTheorems | R+N | `qubitPauliProj` reuses `pauliProj` over `ZMod 2`; `exists_qubitIsometry (F : FixedFieldModel q) (L : ℕ)` targets `Fin L × Fin F.basisDim → ZMod 2`, uses `F.binaryCoordinates`, and states the EPR and Pauli conjugation identities (`sorry`). It has no second model or basis carrier. `**Local fix:**` docstring for the source's `j ∈ {1,…,q}` index typo (rem:pauli-binary-source) |
| def:bracket | `MIPStarRE.Quantum.Measurement.postprocess` | — (Quantum) | R | already `\lean`+`\leanok` in ch12; no new decl. Marginals of def:povm-conventions are `postprocess` along `Prod.fst`/`Prod.snd` (4.1 (e)3) |
| def:projective-strategy-general | `Strategy.IsProjective` | Games/StrategyClasses | N | `def Strategy.IsProjective (S : Strategy G) : Prop := (∀ x, (S.A x).IsProjective) ∧ (∀ y, (S.B y).IsProjective)` — real; REUSE 4.1's `Measurement.IsProjective`. Docstring cites rem:projective-strategy-relation (disjoint from LDT's `ProjStrat`) |
| def:symmetric-game | `SymmetricGame`, `.toGame`, `SymmetricStrategy`, `.toStrategy` | Games/StrategyClasses | N | `structure SymmetricGame where Question Answer : Type; [Fintype/DecidableEq fields]; μ : Distribution (Question × Question); μ_prob; μ_symm : ∀ x y, μ.weight (x,y) = μ.weight (y,x); decide : Question → Question → Answer → Answer → Bool; decide_symm : ∀ x y a b, decide x y a b = decide y x b a`; `def SymmetricGame.toGame : Game`; `structure SymmetricStrategy (G : SymmetricGame) where ι : Type; [insts]; ψ : EuclideanSpace ℂ (ι × ι); ψ_norm : ‖ψ‖ = 1; ψ_swap : reindexState (Equiv.prodComm ι ι) ψ = ψ; M : G.Question → Quantum.Measurement G.Answer ι`; `def SymmetricStrategy.toStrategy : Strategy G.toGame`. All real. **Encoding decision**: the source's "`X = Y` and `A = B`" is realized by a single-alphabet carrier rather than by type equalities in a `Prop` on `Game` (which would force `HEq` transport); this is the compact notation the blueprint itself endorses |
| lem:symmetric-strat | `exists_symmetric_projective_strategy`, `exists_symmetric_projective_strategy_of_strategy` | Games/StrategyClasses | N | source form: `theorem … (G : SymmetricGame) (ε : ℝ) (hε : 0 ≤ ε) (h : Game.value G.toGame = 1 - ε) : ∃ S : SymmetricStrategy G, S.toStrategy.IsProjective ∧ 1 - ε ≤ S.toStrategy.value` (`sorry`; docstring cites `gap:qpbt_symmetrization-attainment` + rem:symmetric-strat-limit); **plus** the Lean-only established form `… (S₀ : Strategy G.toGame) (h : 1 - ε ≤ S₀.value) : ∃ S : SymmetricStrategy G, …` which is what every downstream use consumes (`sorry`). Two-statement pattern shared with ch15's OPEN-4 |
| def:comm-strategy | `IsCommutingOn`, `Strategy.IsCommuting` | Games/StrategyClasses | N | `def IsCommutingOn {G : Game} {ι} [insts] (μ : Distribution (G.QuestionA × G.QuestionB)) (A : G.QuestionA → Measurement G.AnswerA ι) (B : G.QuestionB → Measurement G.AnswerB ι) : Prop := ∀ x y, 0 < μ.weight (x,y) → ∀ a b, Commute ((A x).effect a) ((B y).effect b)` — real, primary form (shared local space is a parameter, not a propositional equality); `def Strategy.IsCommuting (S) (h : S.ιA = S.ιB)` transports it |
| def:consistent-measurement | `Measurement.IsConsistentOn` | Games/StrategyClasses | N | `def Quantum.Measurement.IsConsistentOn (M : Measurement α ι) (ψ : EuclideanSpace ℂ (ι × ι)) : Prop := ∀ a, (heteroKron (M.effect a) 1).mulVec ψ = (heteroKron 1 (M.effect a)).mulVec ψ` — real; projectivity is a use-site hypothesis, not a field |
| def:consistent-strategy | `IsConsistentStrategyOn`, `SymmetricStrategy.IsConsistent` | Games/StrategyClasses | N | `def IsConsistentStrategyOn (A) (B) (ψ) : Prop := (∀ x, (A x).IsConsistentOn ψ) ∧ (∀ y, (B y).IsConsistentOn ψ)`; `def SymmetricStrategy.IsConsistent (S) : Prop := ∀ x, (S.M x).IsConsistentOn S.ψ` — both real |
| def:spcc | `Strategy.IsPCC`, `SymmetricStrategy.IsSPCC` | Games/StrategyClasses | N | `def Strategy.IsPCC {ι} (μ) (A) (B) (ψ) : Prop := (projective) ∧ IsConsistentStrategyOn A B ψ ∧ IsCommutingOn μ A B`; `def SymmetricStrategy.IsSPCC (S) : Prop := (∀ x, (S.M x).IsProjective) ∧ S.IsConsistent ∧ IsCommutingOn G.μ S.M S.M` — real. This is the ch13 completeness/rigidity interface (nodes 44, 45) |
| def:consistency | `consistencyDefect`, `IsConsistentWithin` | Games/Consistency | N | `noncomputable def consistencyDefect {X α ι} [insts] (μ : Distribution X) (A B : X → α → Op ι) (ψ : EuclideanSpace ℂ ι) : ℝ := avgOver μ fun x => ∑ a, ∑ b, if a = b then 0 else (⟪ψ, (A x a * B x b).mulVec ψ⟫_ℂ).re`; `def IsConsistentWithin (μ A B ψ) (δ : ℝ) : Prop := consistencyDefect μ A B ψ ≤ δ` — the `≃_δ` of def:consistency, with both families **pre-placed** on the joint space via `heteroKron` (identical to ch15's proposed signature, adopted verbatim). Real; hidden `O(·)` constants absorbed per 4.1 (e)8 / rem:asymptotic-distance |
| def:strategy-distance | `AreCloseStrategies` | Games/Consistency | N | `structure AreCloseStrategies (G : Game) (S S' : Strategy G) (δ : ℝ) : Prop` first records `hA : S.ιA = S'.ιA` and `hB : S.ιB = S'.ιB`, then compares the transported states and operator families with `stateDistSq` and `opFamilyDistSq`. The equalities faithfully encode the source's common Hilbert spaces and make the relation type-correct for bundled strategies. **Encoding decision:** choose one of the source-permitted states, `S.ψ`, for both operator distances, and document it |
| fact:agreement | `opFamilyDistSq_le_two_mul_consistencyDefect`, `consistencyDefect_le_opFamilyDistSq_of_projective`, `consistencyDefect_le_sqrt_of_projective_left` | Games/DistanceTheorems | N | the three items with **explicit** constants (`≤ 2 * …`, `≤ …`, `≤ Real.sqrt (2 * …)`) rather than `O(·)`, per rem:asymptotic-distance ("any explicit quantitative version retains the constants"); all `sorry` |
| fact:add-a-proj | `opFamilyDistSq_mul_left_le` | Games/DistanceTheorems | N | `theorem … (hC : ∀ y a, ∑ c, (C y a c)ᴴ * (C y a c) ≤ 1) (h : opFamilyDistSq (μ.map Prod.fst) A B ψ ≤ δ) : opFamilyDistSq μ (fun p abc => C p.2 abc.1 abc.2.2 * A p.1 (abc.1, abc.2.1)) (… B …) ψ ≤ δ` (`sorry`) |
| fact:add-a-proj2 | `opFamilyDistSq_mul_funIndexed_le` | Games/DistanceTheorems | N | same shape with `S : X → (X → α) → Op ι`, `∑ g (S x g)ᴴ (S x g) ≤ 1`, outcome `g(x)` (`sorry`) |
| lem:cool-closeness-fact | `opDistSq_sum_sub_mul_le_of_projective` | Games/DistanceTheorems | N | Lean-only `opDistSq (μ) (M N : X → Op ι) (ψ) := avgOver μ fun x => ‖(M x - N x).mulVec ψ‖ ^ 2` (= `opFamilyDistSq` at `α := Unit`); `theorem … (hA : ∀ x, (A x).IsProjective) (h : opFamilyDistSq μ A B ψ ≤ δ) (S : Finset α) : opDistSq μ (fun x => ∑ a ∈ S, A x a) (fun x => ∑ a ∈ S, A x a * B x a) ψ ≤ δ` (`sorry`) |
| fact:triangle | `opFamilyDistSq_le_of_le_of_le` | Games/DistanceTheorems | N | `theorem … (h₁ : … ≤ δ) (h₂ : … ≤ ε) : opFamilyDistSq μ A C ψ ≤ 2 * δ + 2 * ε` (`sorry`) — explicit factor 2, exactly the constant rem:asymptotic-distance names |
| fact:triangle-for-simeq | `consistencyDefect_trans_le` | Games/DistanceTheorems | N | `theorem … : consistencyDefect μ A D ψ ≤ ε + 2 * Real.sqrt (δ + γ)` from the three hypotheses (`sorry`) |
| fact:data-processing | `consistencyDefect_postprocess_le` | Games/DistanceTheorems | N | `theorem … (f : α → β) (h : consistencyDefect μ A B ψ ≤ δ) : consistencyDefect μ (postprocessed A) (postprocessed B) ψ ≤ δ` (`sorry`); REUSE `Measurement.postprocess` |
| lem:commutation-analysis | `opDistSq_commutator_le` | Games/DistanceTheorems | N | `theorem … : ∃ C, 1 ≤ C ∧ ∀ …, (hB : projective) → (h₁ h₂ : the two bounds at δ) → opDistSq μ (fun x => ⁅A x .., C x ..⁆) 0 ψ ≤ C * δ` with the marginals written as `postprocess` (`sorry`); the universal constant precedes all data because the source conclusion is asymptotic |
| lem:close-strategies-have-close-values | `abs_value_sub_le_of_areClose` | Games/DistanceTheorems | N | `theorem … : ∃ C, 1 ≤ C ∧ ∀ (G) (S S') (δ : ℝ), 0 ≤ δ → δ ≤ 1 → (hclose : AreCloseStrategies G S S' δ) → reindexState (the product equivalence induced by hclose.hA.symm and hclose.hB.symm) S'.ψ = S.ψ → (S.IsProjective ∨ S'.IsProjective) → |S.value - S'.value| ≤ C * δ ^ (1/2 : ℝ)` (`sorry`). The exact transported state equality is the source's additional “use the same state” hypothesis at paper lines 531–538; it is not folded into general strategy closeness. The universal constant precedes the game, strategies, and error |
| lem:ld-sandwich | `sandwichProduct`, `consistencyDefect_sandwich_le` | Games/Sandwich | N | `sandwichProduct` is the real ordered product `G^k … G^1 … G^k` (empty product `1`), with the `**Local fix:**` indexing note; `consistencyDefect_sandwich_le : ∃ C, 1 ≤ C ∧ ∀ …, hsep → hproj → hcons → consistencyDefect … ≤ C * k * (δ + ε) ^ (1/2 : ℝ)` (`sorry`). The universal `C` precedes all data because the source conclusion uses asymptotic notation |
| lem:pasting | `pastedMeasurement`, `exists_pasting_error` | Games/Sandwich | N | `noncomputable def pastedMeasurement (G₁ G₂) (g₁ g₂) : Op ι := (G₂ g₂) * (G₁ g₁) * (G₂ g₂)` (eq:pasting-2a), real; `theorem exists_pasting_error : ∃ δp : ℝ → ℝ → ℝ, IsPolyErr₂ δp ∧ ∀ …, (hyps eq:pasting-1, eq:pasting-2) → consistencyDefect … ≤ δp η δ` (`sorry`) — `poly(η,δ)` with unspecified exponent is the `IsPolyErr₂` predicate coordinated with ch15 (OPEN-4) |
| lem:cl-kth | `CLData`, `isCondLinear_iff_nonempty_clData` | Games/CondLinearTheorems | N | `structure CLData (K) (ι) (ℓ : ℕ) (L : (ι → K) → ι → K) where marg : Fin ℓ → ((ι → K) → ι → K); factor : (k : Fin ℓ) → (ι → K) → Finset ι; lin : (k : Fin ℓ) → (ι → K) → ((ι → K) →ₗ[K] (ι → K)); levels : ∀ k, IsCondLinearOn Finset.univ (k+1) (marg k); directSum : ∀ x, the factor spaces at prefixes decompose `ι`; sumFormula : ∀ k x, marg k x = ∑ i ≤ k, …; top : marg ⟨ℓ-1,_⟩ = L` (real; prefixes indexed by the value `L_{<k}(x)` as in the source); `theorem isCondLinear_iff_nonempty_clData (hℓ : 1 ≤ ℓ) : IsCondLinear ℓ L ↔ Nonempty (CLData K ι ℓ L)` (`sorry`) |
| lem:cl-func-prod | `IsCondLinear.directSum` | Games/CondLinearTheorems | N | `theorem … (m ≥ 1) (V : Fin m → Finset ι) (hdisj : pairwise disjoint, union univ) (h : ∀ j, IsCondLinearOn (V j) (ℓ j) (L j)) : IsCondLinear (Finset.univ.sup ℓ) (fun x i => ∑ j, …)` (`sorry`); the source's level-0 base case is supplied (the blueprint's own local fix) |
| lem:cl-dist-prod | `clDistribution_directSum_eq_prod` | Games/CondLinearTheorems | N | `theorem … : clDistribution L R = Distribution.prod-over-`Fin m` of (clDistribution (L j) (R j))` (`sorry`); the product combinator is `MIPStarRE.LDT.Basic.DistributionProduct` — verify the exact name before use (RECONCILE-5) |
| def:typed-cl-functions | `IsTypedCondLinearFamily` | Games/TypedCondLinear | N | `def IsTypedCondLinearFamily (T) (ℓ : ℕ) (L : T → (ι → K) → ι → K) : Prop := ∀ t, IsCondLinear ℓ (L t)` — real |
| def:typed-cl-distributions | `typedCLDistribution`, `ldQuestionDistribution_eq_typedCL`, `pauliQuestionDistribution_eq_typedCL` | Games/TypedCondLinear | N | `noncomputable def typedCLDistribution (E : Finset (Sym2 T)) (hE : E.Nonempty) (L R : T → (ι → K) → ι → K) : Distribution ((T × (ι → K)) × (T × (ι → K))) := (graphDistribution E).bind-with-`clDistribution`-per-type-pair` — real; REUSE 4.1's `graphDistribution` and `clDistribution`. **Plus the two reconciliation lemmas** stating that 4.1's inlined `ldQuestionDistribution` and `pauliQuestionDistribution` equal `typedCLDistribution` at their edge sets and CL families (`sorry`). This is the honest discharge of 4.1's OPEN-3 |
| lem:alnf | `aLinePointDist_point_marginal_uniform`, `aLinePointDist_mem_line` | Test/LowDegreeGameTheorems | N | `theorem … (L : LdParams) : (aLinePointDist L).map (point component) = uniformDistribution (Point L) ∧ (aLinePointDist L).map (axis index) = uniformDistribution (Fin L.m)`; `theorem … : ∀ z ∈ (aLinePointDist L).support, z.point ∈ linePoints z.base (stdBasis (chiIndex L z.seed))` (both `sorry`); all field data come from `L.model` |
| lem:dlnf | `dLinePointDist_point_marginal_uniform`, `dLinePointDist_mem_line`, `dLinePointDist_prefix_zero` | Test/LowDegreeGameTheorems | N | same three-way split; the third records that the direction's first `i-1` coordinates vanish (all `sorry`) |
| def:line-point-dist | `LineKind`, `LineDesc`, `aLinePointDist`, `dLinePointDist`, `linePointDist` | Test/LowDegreeGameTheorems | N | `LineDesc (L : LdParams)` is a tagged axis/diagonal carrier. Both constructors store a canonical base fixed by `lineRepMap`; the axis constructor stores the seed that determines `coordinateDirection (chiIndex L seed)`, while the diagonal constructor stores the seed, prefix-projected direction, and its prefix-zero proof. `LineDesc.direction` is derived. The three distributions map the common CL seed into this carrier and a point, and `linePointDist` is their equal mixture. All are keyed to `LdParams`, with no model binder. This is the canonical nonredundant carrier consumed by ch14/ch15, never `Point × Point` |
| def:ld-meas | `PolyIndex`, `PolyMeas`, `PolyMeasFamily`, `PolyMeasTuple` | Test/LowDegreeGameTheorems | N | all aliases are noncomputable and use the actual bounded `polyFunc` subtype. `PolyMeasFamily` has outcome `(i : Fin k) → ↥polyFunc (m i) (K i) (d i)` for a finite family of finite coefficient fields, faithfully representing the source's non-constant tuple definition. `PolyMeasTuple L` is the constant-family specialization used by `lem:ld-soundness`. The generic `Fintype` instance is defined immediately before these aliases with `Module.finite_of_finite` and `Fintype.ofFinite`; reuse the inherited `DecidableEq` |
| lem:ld-soundness | `deltaLd`, `exists_ld_soundness` | Test/LowDegreeGameTheorems | N | `deltaLd` remains distinct from `deltaQld`, with prefactor `a(dmk)^a` and `0 < b ≤ 1`. `exists_ld_soundness : ∃ a b, 1 ≤ a ∧ 0 < b ∧ b ≤ 1 ∧ ∀ (L : LdParams) (ε : ℝ), 0 < ε → ∀ S : Strategy (ldGame L), S.IsProjective → 1 - ε ≤ S.value → ∃ GA GB, ...`, with the three source consistency conclusions against `PolyMeasTuple L` (`sorry`). It has no extra model binder. Its docstring cites the dimension-divisibility gap, game-correspondence and parameter-bound obligations, and `rem:ld-soundness-provider` |
| thm:ms-rigidity | `exists_ms_rigidity` | Test/MagicSquareTheorems | N | `theorem … : ∃ C : ℝ, 1 ≤ C ∧ ∀ (ε : ℝ), 0 ≤ ε → ∀ (S : Strategy msGame), 1 - ε ≤ S.value → ∃ (ιA'' ιB'' : Type) (insts) (φA : EuclideanSpace ℂ S.ιA →ₗᵢ[ℂ] EuclideanSpace ℂ ((Fin 2 → ZMod 2) × ιA'')) (φB : …) (aux : EuclideanSpace ℂ (ιA'' × ιB'')), ‖aux‖ = 1 ∧ ‖isometryTensor φA φB S.ψ - idealMsState aux‖ ≤ C * Real.sqrt ε ∧ (four `opFamilyDistSq` bounds for `Variable₁`/`Variable₅` against `qubitPauliProj .X` / `.Z` ≤ C * Real.sqrt ε) ∧ (two `opDistSq` anticommutation bounds ≤ C * Real.sqrt ε)` (`sorry`). The single universal `C` precedes `ε` and `S`. `idealMsState aux := reindexState prodShuffle (vecTensor (eprState (Fin 2 → ZMod 2)) aux)`; the `MsType.var` indices are **0 and 4** for `Variable₁`/`Variable₅` (4.1 indexes `Fin 9` from 0 — off-by-one, flagged). Docstring: imported from Coladangelo–Stark Thm 6.9, `**Local fix:**` for the trace-norm→Euclidean `O(√ε)` restatement and the local basis change |
| thm:ms-from-ac | `obsOf`, `exists_ms_perfect_strategy_of_anticommuting` | Test/MagicSquareTheorems | N | `obsOf` is real. The theorem is generic over an arbitrary finite nonempty local index `ι`: projective binary measurements `A B : Measurement (ZMod 2) ι`, consistency on `eprState ι`, and exact anticommutation produce the symmetric perfect Magic Square strategy on `eprState ι ⊗ eprState (Fin 2 → ZMod 2)`, embedding `A` and `B` at variables 0 and 4 (`sorry`). It has no field, model, or QPBT parameter. `msGameSymm` and its `toGame` equality are real/source obligations as adjudicated |
| lem:pauli-completeness | `pauliBasisTestSymm`, `exists_spcc_value_one` | Test/Completeness | N | define `pauliBasisTestSymm (P : AdmissibleParams)` and its `toGame` equality, then state `exists_spcc_value_one (P)` with no model binder; both use only `P.model` and the theorem above instantiated at `PauliRegister P` |
| cor:pauli-binary | `pauli_soundness_qubit` | Test/QubitForm | N | `theorem pauli_soundness_qubit : ∃ a b : ℝ, 1 ≤ a ∧ 0 < b ∧ b < 1 ∧ ∀ (P : AdmissibleParams) (ε : ℝ), 0 ≤ ε → ∀ S : Strategy (pauliBasisTest P), 1 - ε ≤ S.value → ∃ …`, with state and operator bounds against the qubit Pauli projectors obtained from `P.model` (`sorry`). The extracted qubit index is `Cube P.m × Fin P.model.basisDim → ZMod 2`. It reuses the frozen `deltaQld`, has no model/basis argument, and preserves the `0 ≤ ε` boundary |
| def:introparams | `introParamsC`, `introParamsTuple`, `AdmissibleParams.ofTuple`, `introParams` | Test/CanonicalParams | N | `noncomputable def introParamsC (a b : ℝ) : ℕ := 2 * ⌈(b + a) / (2 * b)⌉₊` (smallest even integer ≥ `(b+a)/b`); `def introParamsTuple (c R : ℕ) : ℕ × ℕ × ℕ := (2 ^ (c * Nat.clog 2 (Nat.clog 2 R) + 1), 2 ^ Nat.log 2 (c * Nat.clog 2 R + 1), 1)` — real, no `sorry`; `def AdmissibleParams.ofTuple (t) (h : IsAdmissibleTuple t) : AdmissibleParams` — real; `noncomputable def introParams (a b : ℝ) (R : ℕ) (hR : 4 ≤ R) : AdmissibleParams := AdmissibleParams.ofTuple _ (introParamsTuple_isAdmissible a b R hR)`, real (its only proof obligation is the `sorry`'d lemma below, so no `sorry` sits inside a definition) |
| lem:delta-bound | `introParamsTuple_isAdmissible`, `le_two_pow_introParams_m`, `exists_deltaQld_introParams_bound` | Test/CanonicalParams | N | `theorem introParamsTuple_isAdmissible (a b) (hb : 0 < b) (R) (hR : 4 ≤ R) : IsAdmissibleTuple (introParamsTuple (introParamsC a b) R)`; `theorem le_two_pow_introParams_m … : R ≤ 2 ^ (introParams a b R hR).m`; `theorem exists_deltaQld_introParams_bound (a b) (ha : 1 ≤ a) (hb : 0 < b) (hb' : b < 1) : ∃ a' b' : ℝ, 1 ≤ a' ∧ 0 < b' ∧ b' ≤ 1 ∧ ∀ (R) (hR : 4 ≤ R) (ε : ℝ), deltaQld a b ε (introParams a b R hR).m (introParams …).d (introParams …).q ≤ a' * ((Real.logb 2 R) ^ a' * ε ^ b' + (Real.logb 2 R) ^ (-b'))` (all `sorry`). REUSE frozen `deltaQld`; docstring cites rem:delta-bound-exponent-comparison (the `k ≤ m` step of the source is replaced) |

Lean-only helpers (each docstring-marked formalization-only per AGENTS.md): `kappaVec`,
`boolToScalar`, `cubeEmbed`, `submoduleFinset`, the generic bounded-`polyFunc` `Fintype`
instance, `submoduleExpect`, `opDistSq`, `placeA`/`placeB` (heteroKron ampliations),
`vecTensor`, `prodShuffle`, `idealMsState`, `msPerfectState`, `idealQubitState`, `obsOf`,
`IsAdmissibleTuple`, `Distribution.mix`, `stdBasis`, `lineDescOf`, `IsPolyErr`, and
`IsPolyErr₂`.

## (d) STATEMENTS (`sorry`) vs DEFINITIONS (real)

- **DEFINITIONS that must be real, no `sorry`** — the 18 `definition`-env nodes of (a)
  other than node 13 (REUSE), plus all Lean-only helpers. Every one is a direct,
  computable-shaped definition; the prose claims attached to them (well-definedness,
  basis-independence, level assertions, `IsProbability`) become named companion `sorry`
  lemmas beside them, per 4.1 (e)7.
- **STATEMENTS to `sorry`** — the 30 `lemma`/`theorem`/`corollary` nodes of (a), plus the
  companions named in (c): `kappa_mul`, `decodeAt_lowDegreeEnc`,
  `exists_selfDualNormalBasis`, `ldQuestionDistribution_eq_typedCL`,
  `pauliQuestionDistribution_eq_typedCL`, `msGameSymm_toGame`,
  `pauliBasisTestSymm_toGame`, `introParamsTuple_isAdmissible`, and `IsProbability` for
  `linePointDist`/`Distribution.mix`. All marker-free tracked skeleton sorries (4.1 (f));
  `**Scope restriction:**` / `**Local fix:**` markers only where (c) names them, and no
  `**Unfaithful:**` marker applies (there are no proofs).
- **Two-statement pattern** (source form + Lean-only established form): `lem:symmetric-strat`
  only, mirroring ch15's OPEN-4 convention.
- Blueprint sync after type-check: `\lean{…}` + `\leanok` on the 48 statement environments
  (node 13 is already tagged), statements only, never proofs; then `leanblueprint web` +
  `lake exe checkdecls`.

## (e) Cross-chapter dependencies — the parallel-wave interface

Measured mechanically against the statement-level `\uses` of ch14/ch15/ch16, with
proof-level `\uses` separated. **These signatures are the wave contract.**

**Exported at STATEMENT level — blocking for sibling chapters:**

1. `def:consistency` → **`consistencyDefect` / `IsConsistentWithin`**
   (`Games/Consistency.lean`). Statement level in **ch14 and ch16**, proof level in ch15.
   Contract: `μ : Distribution X`, both operator families already placed on the *joint*
   index `ι` via `heteroKron`, real-part-of-inner-product summands, `a ≠ b` off-diagonal
   only, `≃_δ` means `consistencyDefect … ≤ δ` with the source's `O(·)` constants absorbed.
   Signature adopted verbatim from ch15's proposal — **this brief takes ownership,
   resolving ch15's OPEN-3.**
2. `def:line-point-dist` → **`LineDesc` / `aLinePointDist` / `dLinePointDist` /
   `linePointDist`** (`Test/LowDegreeGameTheorems.lean`). Statement level in **ch14 and
   ch15**. Contract: **keyed to `LdParams`, dimension-generic**, so both
   `linePointDist P.toLdParams` and `linePointDist (P.extendedLd hdvd)` elaborate — ch15's
   RECONCILE-2, satisfied here. `LineDesc L` is the tagged canonical carrier described in
   (c): its constructors retain the seed, canonical-base invariant, and the diagonal
   prefix-zero invariant, while its direction is derived. Ch14/ch15 bind to it rather than
   defining their own. `linePointDist` is the blueprint's `1/2`–`1/2` mixture `D_Line`;
   the two components are exported separately because ch15 filters them.
3. `def:projective-strategy-general` → **`Strategy.IsProjective`** (`Games/StrategyClasses.lean`).
   Statement level in **ch14** (`lem:projective-strategy-setup`).
4. `def:symmetric-game` → **`SymmetricGame` / `SymmetricStrategy` / `.toGame` / `.toStrategy`**
   (`Games/StrategyClasses.lean`). Statement level in **ch14**. Contract: the single-alphabet
   carrier described in (c) — ch14 must phrase its ambient setting over `SymmetricStrategy`,
   whose local space is a *single* `ι` and whose state lives on `ι × ι`; ch15's
   `ExpandedSetting` bundle should be built on top of this rather than on bare `Strategy`.
5. `lem:twisted-commutation` → **`primeTauObservable_mul`,
   `primeTauObservable_pow`, `primeTauObservable_pow_char`, and
   `primeTauObservable_X_mul_Z`** (`Algebra/PauliTheorems.lean`). These general-prime
   declarations implement the blueprint source node. Ch14 separately consumes the
   characteristic-two specializations `tauObservable_mul`, `tauObservable_sq`, and
   `tauObservable_X_mul_Z`; those binary names are not linked to the source label.
6. `def:binary-representation` → **`FixedFieldModel.binaryCoordinates`** together with
   the existing generic `multiplicationTable` and a canonical `chi` specialization;
   `def:dual-self-dual-normal-basis` → **`Basis.IsSelfDual` / `Basis.IsNormal`**
   (`Algebra/SelfDualBasis.lean`). Both are statement level in **ch16**. Generic source
   algebra remains parameterized by an abstract basis and its hypotheses. Test-facing
   consumers use the basis already stored in `FixedFieldModel`; they take no second model
   or basis carrier.
7. `def:decoding-map` → **`decodeAt` / `decodeBool`** (`Algebra/LowDegreeCodeTheorems.lean`).
   Statement level in **ch16**. Contract: outcome type `Cube m → K`, `H : Finset K`, junk
   value `0` off `H`.
8. `def:bracket` → REUSE **`Quantum.Measurement.postprocess`** (already `\leanok`).
   Statement level in **ch16**. No new declaration.

**Exported at PROOF level** (must exist for the wave; no sibling *statement* blocks on
them): the whole distance calculus (`fact:agreement`, `fact:add-a-proj`,
`fact:add-a-proj2`, `fact:triangle`, `fact:triangle-for-simeq`, `fact:data-processing`,
`lem:commutation-analysis`) for ch14/ch16; `lem:downsize_field`, `lem:one`,
`thm:ms-rigidity` for ch14; `lem:cancellation`, `lem:pauli-completeness` for ch16;
`lem:ld-soundness` for ch15's `lem:qld-4-7` — whose error function `deltaLd` and
`PolyMeasTuple` outcome type are the parts ch15 consumes.

**Consumed by this brief:** only 4.1-frozen names and `\leanok` LDT/Quantum declarations
(`schwartzZippel_totalDegree`, `polyFunc`, `Measurement.postprocess`, `Distribution` +
`avgOver`/`uniformDistribution`/`uniformOnFinset`, `FieldModel`, `Quantum.Measurement`,
`IsProj`). **No sibling 4.2 chapter is a dependency** — these files go first in the wave.

## RECONCILE: assumptions pending the 4.1 merge

- **RECONCILE-1**: the 4.1 names listed in (c) are used verbatim before the 4.1 PR merges;
  renames are mechanical.
- **RECONCILE-2**: 4.1's `def:generalized-pauli` row names `pauliProj` but the multi-qudit
  observable `τ^W(a)` appears only implicitly, inside the lemma name
  `tauObservable_eq_sum_pauliProj`. This brief assumes **`tauObservable (W : PauliKind)
  (a : γ → K) : Op (γ → K)`** exists in `Algebra/Pauli.lean`; `lem:twisted-commutation` is
  stated entirely in terms of it. If 4.1 ships only `tauShift`/`tauPhase`, add the
  multi-qudit `tauObservable` there and this brief binds to it unchanged. Likewise
  `cubeEmbed : Cube m → (Fin m → K)` is assumed available (or trivially added) from 4.1's
  `indicatorPoly`, which already identifies `{0,1} ⊆ F_q`.
- **RECONCILE-3**: `def:ld-meas` is built on `Quantum.Measurement`, not on the ch03
  `\leanok` `LDT.SubMeas`/`LDT.Measurement`, because 4.1 (e)3/(e)4 keep the QPBT games
  layer on the vector-state `Quantum` API. The ch13 node therefore does **not** become a
  `\leanok` reuse of `def:polymeasurements`; confirm the blueprint records the distinction.
- **RECONCILE-4**: `lem:schwartz-zippel` is assumed a verbatim reuse of
  `LDT.Preliminaries.schwartzZippel_totalDegree`. If that statement's packaging
  (probability carrier, degree bundling, `Parameters` dependence) does not match the ch11
  restatement, add a thin bridge lemma in `Algebra/LowDegreeCodeTheorems.lean` and tag the
  ch11 node to the bridge instead.
- **RECONCILE-5**: LDT `Distribution` API names to verify before use — the finite product
  combinator in `LDT/Basic/DistributionProduct.lean` (`lem:cl-dist-prod`) and whether a
  convex-mixture combinator exists (`linePointDist`); otherwise both become Lean-only
  helpers in the consuming file.
- **RECONCILE-6**: 4.1 ships `msGame` and `pauliBasisTest` as `Game`. Both are symmetric,
  and nodes 44/45 are stated over `SymmetricStrategy`, so this brief adds
  `msGameSymm`/`pauliBasisTestSymm : SymmetricGame` with `sorry`'d `toGame` equations.
  If 4.1 instead lands them as `SymmetricGame` with a `toGame` coercion, delete the two
  wrappers and the two lemmas.
- **RECONCILE-7**: `MsType.var (j : Fin 9)` is 0-indexed in 4.1 while the blueprint writes
  `Variable₁`/`Variable₅`; this brief uses `MsType.var 0` and `MsType.var 4`. If 4.1's
  `msConstraintVars` uses a 1-shifted convention, all four occurrences move together.

## Items submitted for operator adjudication

This section records the questions raised by the scouting pass. It is historical input,
not an implementation contract. The binding operator adjudication below resolves every
item and supersedes this section wherever the two differ.

- **OPEN-1** (does `FieldModel` get pinned?): determine whether the source's coordinate
  map should become a second QPBT model/basis input or specialize the canonical basis
  already stored by `FixedFieldModel`. The binding decision rejects a second carrier and
  introduces `FixedFieldModel.binaryCoordinates := kappa F.basis`.
- **OPEN-2** (`\uses` omissions in ch11/ch13): `cor:pauli-binary` directly uses
  `def:binary-representation` in its displayed statement. `lem:pauli-binary` belongs only
  to the proof dependencies of the corollary. `lem:pauli-binary` directly uses
  `def:subfields-kappa` only when its displayed statement mentions that coordinate map.
- **OPEN-3** (general-`p` Pauli material): `lem:twisted-commutation` and `lem:cancellation`
  are stated in the blueprint for arbitrary prime `p`, but 4.1's Pauli layer fixes `p = 2`,
  `ω = −1`. The skeleton states the char-2 specializations under `**Scope restriction:**`.
  Confirm, or require a general-`p` `AddChar`-based `tauPhase` in `Algebra/Pauli.lean` —
  a 4.1 change, hence a reconciliation-pass decision.
- **OPEN-4** (`IsPolyErr` ownership): `lem:pasting`'s `poly(η,δ)` needs the same
  unspecified-exponent predicate ch15 proposes as `IsPolyErr₂`. Assign one owner: either
  ch15 keeps it in `Combining/Defs.lean` and `Games/Sandwich.lean` imports it, or it moves
  to `Games/Consistency.lean` here — lower in the DAG, so ch14 could use it too.
- **OPEN-5** (`Game.value` in `lem:symmetric-strat`): the source form quantifies over
  `Game.value`, which 4.1 encoded as a `csSup` and flagged as unused (4.1 OPEN-4). Stating
  this lemma makes it load-bearing for the first time, and its `sorry` is exactly the
  attainment gap `gap:qpbt_symmetrization-attainment`. Confirm the two-statement encoding
  rather than shipping only the established form.
- **OPEN-6** (`MIPStarRE/QPBT.lean` merge point): 16 new re-export lines land in the file
  4.1 creates and ch14/ch15/ch16 will also touch. Propose per-chapter sub-roots
  (`QPBT/Algebra.lean`, `QPBT/Games.lean`, `QPBT/Test.lean`) so each brief edits a
  distinct file, or serialize the root edit at merge time.
- **OPEN-7** (`lem:cl-kth` value): the structure theorem is the heaviest ch12 residual
  node (a prefix-indexed decomposition) and **nothing in ch11–ch16 uses it at statement
  level**; ch13's CL-level assertions are 4.1 companion lemmas instead. Confirm it is in
  scope, or defer it with the ch12 calculus.
- **OPEN-8** (`lem:ld-soundness` error function): `deltaLd` genuinely differs from the
  frozen `deltaQld` (prefactor `a(dmk)^a`, non-strict `0 < b ≤ 1`). Confirm two separate
  definitions rather than one parametrized family — ch15's `lem:qld-4-7` consumes
  `deltaQld` while its proof consumes `deltaLd`, so the distinction is load-bearing.

## Operator adjudication — 2026-09-02

This section is binding for stage 4.2 and supersedes incompatible sketches above. It
uses the landed stage-4.1 API and the paper mirrors named at the start of this brief.

### RECONCILE decisions

- **RECONCILE-1 — bind test-facing declarations to the landed canonical API.** Remove
  every stale `[FieldModel ...]` binder from declarations parameterized by `P` or `L`.
  Their field operations come from `P.model` or `L.model`; QPBT scalars are
  `PauliScalar P` and LDT scalars are `ScalarQ L`. Source-generic algebra declarations
  retain abstract field and basis parameters. Move `conjIsometry`, `reindexState`, and
  `isometryTensor` out of `Test/Soundness.lean` into a neutral
  `MIPStarRE/QPBT/State.lean` leaf. While relocating `isometryTensor`, generalize its
  two codomains to arbitrary finite index types `κA` and `κB`; the landed shared-tail
  parameter is too restrictive for Magic Square rigidity and qubit conversion.
- **RECONCILE-2 — reuse `tauObservable`; add only the missing cube embedding.** The
  multi-qudit observable has landed. `cubeEmbed` has not, so add a Lean-only
  field-valued coordinate map `boolToScalar : Bool → K` and its pointwise lift
  `cubeEmbed : Cube m → (Fin m → K)` in `Algebra/LowDegreeCodeTheorems.lean`. Do not edit
  the frozen stage-4.1 algebra declarations for these helpers. Define `decodeAt`,
  `decodeBool`, and their encoding identity generically over the source field; canonical
  QPBT wrappers may specialize them later.
- **RECONCILE-3 — keep the QPBT measurement carrier.** `PolyMeas` is based on
  `Quantum.Measurement`, not the LDT submeasurement layer. Its polynomial outcome is
  the actual `polyFunc` subtype. This residual wave owns its generic `Fintype` instance.
  Follow the existing construction in
  `LDT/Basic/ParametersFiniteAnswers.lean`: obtain `Finite (polyFunc m K d)` from
  `Module.finite_of_finite K`, then use `Fintype.ofFinite`. The existing subtype
  `DecidableEq` resolves from `DecidableEq K`; do not add a duplicate instance. A new
  coefficient equivalence is unnecessary. Because `polyFunc` is a `noncomputable
  abbrev`, declare `PolyIndex`, `PolyMeas`, and `PolyMeasTuple` noncomputable as well.
  Put the generic `Fintype` instance immediately before these aliases in
  `Test/LowDegreeGameTheorems.lean`. Ch15 consumes this infrastructure.
- **RECONCILE-4 — reuse the LDT Schwartz–Zippel theorem.** Bind the ch11 restatement to
  `MIPStarRE.LDT.Preliminaries.schwartzZippel_totalDegree`; add a thin packaging bridge
  only if elaboration shows one is necessary.
- **RECONCILE-5 — provide structured distribution combinators once.** The landed API
  has no suitable general product, mixture, or typed bind combinators. Implement and
  prove the required finite combinators in one shared `Games/DistributionAux.lean`, or
  use a specialized direct definition when that gives a materially simpler statement.
  Other waves import this owner and do not duplicate the constructions.
- **RECONCILE-6 — retain symmetric-game wrappers.** Add `msGameSymm` and
  `pauliBasisTestSymm` with named `toGame` equality theorems because the landed games
  are plain `Game` values.
- **RECONCILE-7 — use zero-based Magic Square indices.** `Variable₁` and `Variable₅`
  are `MsType.var 0` and `MsType.var 4`, respectively, everywhere.

### OPEN decisions

- **OPEN-1 — reject `SelfDualNormalRep` only as an extra QPBT carrier.** The landed
  `FixedFieldModel` already pins the basis used by `χ`, `γ`, qubit conversion, and
  extraction, so test-facing theorems gain no second model or basis argument. The
  source-generic definitions and lemmas for dual bases, coordinate maps, trace/dot
  products, and normal bases remain generic in an abstract basis and its hypotheses.
  Derive separate canonical specializations from `FixedFieldModel`. Add
  `FixedFieldModel.binaryCoordinates := kappa F.basis` for the source's bit-coordinate
  map; do not confuse it with the landed numeric serialization `binaryRepresentation`.
- **OPEN-2 — patch the missing direct dependencies.** Add
  `def:binary-representation` to the direct statement uses of `cor:pauli-binary`.
  Keep `lem:pauli-binary` only in the corollary proof's `\uses`, where it already
  belongs. Add `def:subfields-kappa` to the statement uses of `lem:pauli-binary` when
  its displayed statement mentions the coordinate map.
- **OPEN-3 — state the general-prime source nodes and separate binary specializations.**
  Import `MIPStarRE.LDT.Preliminaries.FiniteFields` and use `ffChar` to define the
  source-general prime-field phase and Pauli observables without changing the frozen
  binary declarations. Link `lem:twisted-commutation` and `lem:cancellation` only to the
  general-prime theorems. Characteristic-two results are separately named specializations
  for QPBT consumers and carry `**Scope restriction:**` documentation. This wave creates
  `docs/paper-gaps/qpbt_characteristic-two-pauli-scope.tex`, linked to issue #16, to
  explain the split and the remaining generalization debt in the landed Pauli layer; no
  unrestricted source node is matched to a binary-only theorem.
- **OPEN-4 — one owner for polynomial error predicates.** Define `IsPolyErr` and
  `IsPolyErr₂` in `Games/ErrorFunctions.lean`. `Games/Sandwich.lean`, ch14, and ch15
  import that leaf.
- **OPEN-5 — retain both symmetrization statements with honest status.** State the exact
  source attainment theorem over `Game.value`; it remains a tracked source obligation.
  State the available given-strategy theorem separately as an established Lean-only
  result and use only that result downstream. Cite the symmetrization-attainment gap;
  neither theorem is allowed to masquerade as the other.
- **OPEN-6 — serialize only the root re-export edit.** Worker PRs add their module files
  without inventing chapter sub-root abstractions. The final wave integration performs
  the small `MIPStarRE/QPBT.lean` import update after the worker branches are reconciled.
- **OPEN-7 — keep `lem:cl-kth` in scope.** It is a genuine source result and supplies
  reusable proof infrastructure even though no later stage-4.2 statement depends on it
  directly. State a faithful `CLData` decomposition and leave its proof open.
- **OPEN-8 — keep two distinct error functions.** `deltaLd` retains the LDT prefactor
  and `0 < b ≤ 1`; `deltaQld` retains the QPBT prefactor and strict `b < 1`. Do not hide
  this load-bearing distinction behind one parameterized family.

### Post-audit statement-integrity corrections

- `LineDesc` is the tagged canonical carrier required by ch14: axis and diagonal
  constructors store a base fixed by `lineRepMap`, a seed, and for diagonal lines a
  prefix-projected direction with its prefix-zero property. `LineDesc.direction` is
  derived. The obsolete `Point × Point` sketch is rejected.
- `AreCloseStrategies G S S' δ` records equalities of the two local index types and
  transports `S'` along them before comparing states and measurements. These are the
  source's common-Hilbert-space hypotheses, not bridge assumptions.
- `abs_value_sub_le_of_areClose` separately assumes that the transported state of `S'`
  equals the state of `S`, exactly matching the source's “use the same state” hypothesis.
- `State.lean` owns real `vecTensor` and `prodShuffle` definitions alongside the three
  relocated state helpers. `idealMsState` remains in `Test/MagicSquareTheorems.lean`.
- The unrestricted twisted-commutation and cancellation nodes use source-general
  `ffChar` declarations. Their characteristic-two corollaries are QPBT specializations,
  not implementations of the source nodes.
- `PolyMeasFamily` represents the source's general non-constant tuple of polynomial
  outcomes. `PolyMeasTuple L` is only its constant-family specialization.
- `lem:downsize_field`, `lem:one`, and `def:decoding-map` have generic source forms plus
  canonical specializations. `thm:ms-from-ac` is generic over a finite nonempty local
  index and has no field/model parameter.
- Every uncomputed source `O(·)` constant is quantified before all mathematical data.
  In particular this applies to rigidity, close-strategy value stability,
  commutation analysis, and the low-degree sandwich lemma.

### Cross-wave contract

This residual wave is the single implementation owner of `Strategy.IsProjective`,
state-dependent consistency, `linePointDist`, and `SymmetricGame`, as well as the error
and distribution leaf infrastructure, `opDistSq` with its `Unit` bridge, the neutral
state helpers (`conjIsometry`, `reindexState`, `isometryTensor`, `vecTensor`, and
`prodShuffle`) in `MIPStarRE/QPBT/State.lean`, the generic bounded-`polyFunc`
finite instances, and the remaining ch11–ch13 statements.
This acyclic ownership lets the residual PR land before ch14. It owns the generic
source forms of `def:decoding-map`, `def:dual-self-dual-normal-basis`,
`lem:downsize_field`, and `lem:one`, as well as canonical specializations and the fixed
`def:binary-representation` view consumed by ch16. QPBT/test-facing declarations use
the canonical fixed model; generic source algebra retains its stated field and basis
generality. Source-labelled results remain free of symmetry, divisibility, model, or
basis inputs that the papers do not assume. Universal constants are outermost, and
`cor:pauli-binary` retains the `0 ≤ ε` boundary and uses `P.model.basisDim`.
