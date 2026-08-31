# Implementation brief — stage 4.2, residual of ch11/ch12/ch13

Deliverable: Lean skeleton (all proofs `sorry`, definitions real) for **every node of
`blueprint/src/chapter/ch11_qpbt_algebra.tex`, `ch12_qpbt_games.tex`,
`ch13_qpbt_test.tex` not in the stage-4.1 statement closure**. Paper mirrors:
`references/qpbt-paper/04_preliminaries.tex` (ch11), `05_conditionally_linear_functions.tex`
+ `06_nonlocal_games_and_mipstar.tex` + `07_types.tex` (ch12),
`08_classical_and_quantum_low_degree_tests.tex` (ch13); exact per-node line ranges are
pinned in docstrings at implementation time. Baseline:
`issues/briefs/0006-minimal-skeleton-brief.md` (stage 4.1) — its naming table is **FROZEN**
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
| def:binary-representation | `SelfDualNormalRep`, `.kappa`, `.mulTable`, `.chi`, `kappa_mul` | Algebra/SelfDualBasis | N | `structure SelfDualNormalRep (q : ℕ) [FieldModel q] where k : ℕ; hk : Odd k; hq : q = 2 ^ k; basis : Basis (Fin k) (ZMod 2) (FieldModel.K q); selfDual : basis.IsSelfDual; normal : basis.IsNormal`; `noncomputable def kappa (R) : FieldModel.K q ≃ₗ[ZMod 2] (Fin R.k → ZMod 2) := R.basis.equivFun` (this is 4.1's `kappa` wrapper at the *pinned* basis); `noncomputable def mulTable (R) (a) : Matrix (Fin R.k) (Fin R.k) (ZMod 2) := Algebra.leftMulMatrix R.basis a`; `noncomputable def chi (R) (M : Matrix (Fin s) (Fin t) K) : Matrix (Fin s × Fin R.k) (Fin t × Fin R.k) (ZMod 2)` (block form, **product index, never `Fin (s*k)`** — mirrors 4.1 (e)6); `theorem kappa_mul (R) (a b) : R.kappa (a*b) = ∑ i, R.kappa a i • (R.mulTable (R.basis i) *ᵥ R.kappa b)` = eq:eq-mult (`sorry`). Real structure; **carried as an extra datum, not as a change to `FieldModel`** (see OPEN-1) |
| lem:downsize_field | `kappa_apply_eq_binTrace`, `binTrace_mul_eq_dotProduct`, `chi_mulVec_kappa` | Algebra/SelfDualBasisTheorems | N | the three items: `theorem … (R) (x) (i) : R.kappa x i = binTrace (x * R.basis i)`; `theorem … (R) (x y) : binTrace (x * y) = R.kappa x ⬝ᵥ R.kappa y`; `theorem … (R) (M) (v) : R.chi M *ᵥ (kappaVec R v) = kappaVec R (M *ᵥ v)` with Lean-only `kappaVec R v := fun p => R.kappa (v p.1) p.2` (all `sorry`) |
| lem:one | `binTrace_basis_eq_one`, `kappa_one` | Algebra/SelfDualBasisTheorems | N | `theorem … (R) (i) : binTrace (R.basis i) = 1`; `theorem … (R) : R.kappa 1 = fun _ => 1` (both `sorry`) |
| lem:twisted-commutation | `tauObservable_mul`, `tauObservable_sq`, `tauObservable_X_mul_Z` | Algebra/PauliTheorems | N | `theorem … (W) (a a' : γ → K) : tauObservable W a * tauObservable W a' = tauObservable W (a + a')`; `theorem … (W) (a) : tauObservable W a * tauObservable W a = 1` (the `(τ^W(a))^p = Id` item at `p = 2`); `theorem … (a b : γ → K) : tauObservable .X a * tauObservable .Z b = ((-1 : ℂ) ^ (binTrace (a ⬝ᵥ b)).val) • (tauObservable .Z b * tauObservable .X a)` (all `sorry`). **`**Scope restriction:**` docstring**: 4.1's Pauli layer fixes `p = 2`, `ω = −1` (admissible `q` only), so the source's general-`p` `σ^X/σ^Z` forms eq:pauli-fp / eq:twisted-fp are not stated (OPEN-3) |
| lem:cancellation | `avg_neg_one_pow_binTrace_eq_zero` | Algebra/PauliTheorems | N | `theorem … (V : Submodule K (Fin k → K)) (v) (hv : v ∉ dotOrthogonal V) : avgOver (Distribution.uniformOnFinset V.toFinset) (fun u => ((-1 : ℂ) ^ (binTrace (u ⬝ᵥ v)).val)) = 0` (`sorry`); same char-2 scope restriction; `V.toFinset` via `Fintype.ofFinite` on the submodule (Lean-only helper `submoduleFinset`) |
| lem:pauli-binary | `qubitPauliProj`, `exists_qubitIsometry` | Algebra/PauliTheorems | R+N | `abbrev qubitPauliProj (W : PauliKind) (b : γ → ZMod 2) : Op (γ → ZMod 2) := pauliProj W b` — REUSE `pauliProj` at the Lean-only instance `instFieldModelTwo : FieldModel 2` (`K = ZMod 2`); `theorem exists_qubitIsometry (q) [FieldModel q] (R : SelfDualNormalRep q) (L : ℕ) (hL : 1 ≤ L) : ∃ φ : EuclideanSpace ℂ (Fin L → K) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (Fin L × Fin R.k → ZMod 2), isometryTensor φ φ (eprState (Fin L → K)) = eprState (Fin L × Fin R.k → ZMod 2) ∧ ∀ (W) (u : Fin L → K), pauliProj W u = conjIsometry φ.symm (qubitPauliProj W (kappaVec R u))` (`sorry`). `**Local fix:**` docstring for the source's `j ∈ {1,…,q}` index typo (rem:pauli-binary-source) |
| def:bracket | `MIPStarRE.Quantum.Measurement.postprocess` | — (Quantum) | R | already `\lean`+`\leanok` in ch12; no new decl. Marginals of def:povm-conventions are `postprocess` along `Prod.fst`/`Prod.snd` (4.1 (e)3) |
| def:projective-strategy-general | `Strategy.IsProjective` | Games/StrategyClasses | N | `def Strategy.IsProjective (S : Strategy G) : Prop := (∀ x, (S.A x).IsProjective) ∧ (∀ y, (S.B y).IsProjective)` — real; REUSE 4.1's `Measurement.IsProjective`. Docstring cites rem:projective-strategy-relation (disjoint from LDT's `ProjStrat`) |
| def:symmetric-game | `SymmetricGame`, `.toGame`, `SymmetricStrategy`, `.toStrategy` | Games/StrategyClasses | N | `structure SymmetricGame where Question Answer : Type; [Fintype/DecidableEq fields]; μ : Distribution (Question × Question); μ_prob; μ_symm : ∀ x y, μ.weight (x,y) = μ.weight (y,x); decide : Question → Question → Answer → Answer → Bool; decide_symm : ∀ x y a b, decide x y a b = decide y x b a`; `def SymmetricGame.toGame : Game`; `structure SymmetricStrategy (G : SymmetricGame) where ι : Type; [insts]; ψ : EuclideanSpace ℂ (ι × ι); ψ_norm : ‖ψ‖ = 1; ψ_swap : reindexState (Equiv.prodComm ι ι) ψ = ψ; M : G.Question → Quantum.Measurement G.Answer ι`; `def SymmetricStrategy.toStrategy : Strategy G.toGame`. All real. **Encoding decision**: the source's "`X = Y` and `A = B`" is realized by a single-alphabet carrier rather than by type equalities in a `Prop` on `Game` (which would force `HEq` transport); this is the compact notation the blueprint itself endorses |
| lem:symmetric-strat | `exists_symmetric_projective_strategy`, `exists_symmetric_projective_strategy_of_strategy` | Games/StrategyClasses | N | source form: `theorem … (G : SymmetricGame) (ε : ℝ) (hε : 0 ≤ ε) (h : Game.value G.toGame = 1 - ε) : ∃ S : SymmetricStrategy G, S.toStrategy.IsProjective ∧ 1 - ε ≤ S.toStrategy.value` (`sorry`; docstring cites `gap:qpbt_symmetrization-attainment` + rem:symmetric-strat-limit); **plus** the Lean-only established form `… (S₀ : Strategy G.toGame) (h : 1 - ε ≤ S₀.value) : ∃ S : SymmetricStrategy G, …` which is what every downstream use consumes (`sorry`). Two-statement pattern shared with ch15's OPEN-4 |
| def:comm-strategy | `IsCommutingOn`, `Strategy.IsCommuting` | Games/StrategyClasses | N | `def IsCommutingOn {G : Game} {ι} [insts] (μ : Distribution (G.QuestionA × G.QuestionB)) (A : G.QuestionA → Measurement G.AnswerA ι) (B : G.QuestionB → Measurement G.AnswerB ι) : Prop := ∀ x y, 0 < μ.weight (x,y) → ∀ a b, Commute ((A x).effect a) ((B y).effect b)` — real, primary form (shared local space is a parameter, not a propositional equality); `def Strategy.IsCommuting (S) (h : S.ιA = S.ιB)` transports it |
| def:consistent-measurement | `Measurement.IsConsistentOn` | Games/StrategyClasses | N | `def Quantum.Measurement.IsConsistentOn (M : Measurement α ι) (ψ : EuclideanSpace ℂ (ι × ι)) : Prop := ∀ a, (heteroKron (M.effect a) 1).mulVec ψ = (heteroKron 1 (M.effect a)).mulVec ψ` — real; projectivity is a use-site hypothesis, not a field |
| def:consistent-strategy | `IsConsistentStrategyOn`, `SymmetricStrategy.IsConsistent` | Games/StrategyClasses | N | `def IsConsistentStrategyOn (A) (B) (ψ) : Prop := (∀ x, (A x).IsConsistentOn ψ) ∧ (∀ y, (B y).IsConsistentOn ψ)`; `def SymmetricStrategy.IsConsistent (S) : Prop := ∀ x, (S.M x).IsConsistentOn S.ψ` — both real |
| def:spcc | `Strategy.IsPCC`, `SymmetricStrategy.IsSPCC` | Games/StrategyClasses | N | `def Strategy.IsPCC {ι} (μ) (A) (B) (ψ) : Prop := (projective) ∧ IsConsistentStrategyOn A B ψ ∧ IsCommutingOn μ A B`; `def SymmetricStrategy.IsSPCC (S) : Prop := (∀ x, (S.M x).IsProjective) ∧ S.IsConsistent ∧ IsCommutingOn G.μ S.M S.M` — real. This is the ch13 completeness/rigidity interface (nodes 44, 45) |
| def:consistency | `consistencyDefect`, `IsConsistentWithin` | Games/Consistency | N | `noncomputable def consistencyDefect {X α ι} [insts] (μ : Distribution X) (A B : X → α → Op ι) (ψ : EuclideanSpace ℂ ι) : ℝ := avgOver μ fun x => ∑ a, ∑ b, if a = b then 0 else (⟪ψ, (A x a * B x b).mulVec ψ⟫_ℂ).re`; `def IsConsistentWithin (μ A B ψ) (δ : ℝ) : Prop := consistencyDefect μ A B ψ ≤ δ` — the `≃_δ` of def:consistency, with both families **pre-placed** on the joint space via `heteroKron` (identical to ch15's proposed signature, adopted verbatim). Real; hidden `O(·)` constants absorbed per 4.1 (e)8 / rem:asymptotic-distance |
| def:strategy-distance | `AreCloseStrategies` | Games/Consistency | N | `structure AreCloseStrategies (G : Game) {ιA ιB} [insts] (ψ ψ' : EuclideanSpace ℂ (ιA × ιB)) (A A' : …) (B B' : …) (δ : ℝ) : Prop where state : stateDistSq ψ ψ' ≤ δ; alice : opFamilyDistSq (G.μ.map Prod.fst) (placeA A) (placeA A') ψ ≤ δ; bob : opFamilyDistSq (G.μ.map Prod.snd) (placeB B) (placeB B') ψ ≤ δ` — real; REUSE 4.1 `stateDistSq`/`opFamilyDistSq`. **Encoding decision**: the source's "on either `ψ` or `ψ'`" is resolved to `ψ`, documented |
| fact:agreement | `opFamilyDistSq_le_two_mul_consistencyDefect`, `consistencyDefect_le_opFamilyDistSq_of_projective`, `consistencyDefect_le_sqrt_of_projective_left` | Games/DistanceTheorems | N | the three items with **explicit** constants (`≤ 2 * …`, `≤ …`, `≤ Real.sqrt (2 * …)`) rather than `O(·)`, per rem:asymptotic-distance ("any explicit quantitative version retains the constants"); all `sorry` |
| fact:add-a-proj | `opFamilyDistSq_mul_left_le` | Games/DistanceTheorems | N | `theorem … (hC : ∀ y a, ∑ c, (C y a c)ᴴ * (C y a c) ≤ 1) (h : opFamilyDistSq (μ.map Prod.fst) A B ψ ≤ δ) : opFamilyDistSq μ (fun p abc => C p.2 abc.1 abc.2.2 * A p.1 (abc.1, abc.2.1)) (… B …) ψ ≤ δ` (`sorry`) |
| fact:add-a-proj2 | `opFamilyDistSq_mul_funIndexed_le` | Games/DistanceTheorems | N | same shape with `S : X → (X → α) → Op ι`, `∑ g (S x g)ᴴ (S x g) ≤ 1`, outcome `g(x)` (`sorry`) |
| lem:cool-closeness-fact | `opDistSq_sum_sub_mul_le_of_projective` | Games/DistanceTheorems | N | Lean-only `opDistSq (μ) (M N : X → Op ι) (ψ) := avgOver μ fun x => ‖(M x - N x).mulVec ψ‖ ^ 2` (= `opFamilyDistSq` at `α := Unit`); `theorem … (hA : ∀ x, (A x).IsProjective) (h : opFamilyDistSq μ A B ψ ≤ δ) (S : Finset α) : opDistSq μ (fun x => ∑ a ∈ S, A x a) (fun x => ∑ a ∈ S, A x a * B x a) ψ ≤ δ` (`sorry`) |
| fact:triangle | `opFamilyDistSq_le_of_le_of_le` | Games/DistanceTheorems | N | `theorem … (h₁ : … ≤ δ) (h₂ : … ≤ ε) : opFamilyDistSq μ A C ψ ≤ 2 * δ + 2 * ε` (`sorry`) — explicit factor 2, exactly the constant rem:asymptotic-distance names |
| fact:triangle-for-simeq | `consistencyDefect_trans_le` | Games/DistanceTheorems | N | `theorem … : consistencyDefect μ A D ψ ≤ ε + 2 * Real.sqrt (δ + γ)` from the three hypotheses (`sorry`) |
| fact:data-processing | `consistencyDefect_postprocess_le` | Games/DistanceTheorems | N | `theorem … (f : α → β) (h : consistencyDefect μ A B ψ ≤ δ) : consistencyDefect μ (postprocessed A) (postprocessed B) ψ ≤ δ` (`sorry`); REUSE `Measurement.postprocess` |
| lem:commutation-analysis | `opDistSq_commutator_le` | Games/DistanceTheorems | N | `theorem … (hB : projective) (h₁ h₂ : the two `opFamilyDistSq` bounds) : opDistSq μ (fun x => ⁅A x .., C x ..⁆) 0 ψ ≤ δ` with the marginals of def:povm-conventions written as `postprocess` (`sorry`) |
| lem:close-strategies-have-close-values | `abs_value_sub_le_of_areClose` | Games/DistanceTheorems | N | `theorem … (h : AreCloseStrategies G ψ ψ A A' B B' δ) (hproj : S.IsProjective ∨ S'.IsProjective) : ∃ C, 1 ≤ C ∧ |S.value - S'.value| ≤ C * δ ^ (1/2 : ℝ)` (`sorry`) — the source's `O(δ^{1/2})` constant is an outermost `∃ C` |
| lem:ld-sandwich | `sandwichProduct`, `consistencyDefect_sandwich_le` | Games/Sandwich | N | `noncomputable def sandwichProduct (G : ∀ i : Fin k, X → (Y → R i) → Op ι) (g : ∀ i, Y → R i) : Op ι` — the ordered product `G^k … G^1 … G^k` (empty product = 1 at `k = 0`), real, per rem:ld-sandwich-indexing (the source's transposed pairing is **not** used; `**Local fix:**` docstring); `theorem consistencyDefect_sandwich_le (hsep : ∀ i, ∀ g ≠ g', Pr_y[g y = g' y] ≤ ε) (hproj) (h : ∀ i, consistencyDefect … ≤ δ) : consistencyDefect … ≤ k * (δ + ε) ^ (1/2 : ℝ)` (`sorry`) |
| lem:pasting | `pastedMeasurement`, `exists_pasting_error` | Games/Sandwich | N | `noncomputable def pastedMeasurement (G₁ G₂) (g₁ g₂) : Op ι := (G₂ g₂) * (G₁ g₁) * (G₂ g₂)` (eq:pasting-2a), real; `theorem exists_pasting_error : ∃ δp : ℝ → ℝ → ℝ, IsPolyErr₂ δp ∧ ∀ …, (hyps eq:pasting-1, eq:pasting-2) → consistencyDefect … ≤ δp η δ` (`sorry`) — `poly(η,δ)` with unspecified exponent is the `IsPolyErr₂` predicate coordinated with ch15 (OPEN-4) |
| lem:cl-kth | `CLData`, `isCondLinear_iff_nonempty_clData` | Games/CondLinearTheorems | N | `structure CLData (K) (ι) (ℓ : ℕ) (L : (ι → K) → ι → K) where marg : Fin ℓ → ((ι → K) → ι → K); factor : (k : Fin ℓ) → (ι → K) → Finset ι; lin : (k : Fin ℓ) → (ι → K) → ((ι → K) →ₗ[K] (ι → K)); levels : ∀ k, IsCondLinearOn Finset.univ (k+1) (marg k); directSum : ∀ x, the factor spaces at prefixes decompose `ι`; sumFormula : ∀ k x, marg k x = ∑ i ≤ k, …; top : marg ⟨ℓ-1,_⟩ = L` (real; prefixes indexed by the value `L_{<k}(x)` as in the source); `theorem isCondLinear_iff_nonempty_clData (hℓ : 1 ≤ ℓ) : IsCondLinear ℓ L ↔ Nonempty (CLData K ι ℓ L)` (`sorry`) |
| lem:cl-func-prod | `IsCondLinear.directSum` | Games/CondLinearTheorems | N | `theorem … (m ≥ 1) (V : Fin m → Finset ι) (hdisj : pairwise disjoint, union univ) (h : ∀ j, IsCondLinearOn (V j) (ℓ j) (L j)) : IsCondLinear (Finset.univ.sup ℓ) (fun x i => ∑ j, …)` (`sorry`); the source's level-0 base case is supplied (the blueprint's own local fix) |
| lem:cl-dist-prod | `clDistribution_directSum_eq_prod` | Games/CondLinearTheorems | N | `theorem … : clDistribution L R = Distribution.prod-over-`Fin m` of (clDistribution (L j) (R j))` (`sorry`); the product combinator is `MIPStarRE.LDT.Basic.DistributionProduct` — verify the exact name before use (RECONCILE-5) |
| def:typed-cl-functions | `IsTypedCondLinearFamily` | Games/TypedCondLinear | N | `def IsTypedCondLinearFamily (T) (ℓ : ℕ) (L : T → (ι → K) → ι → K) : Prop := ∀ t, IsCondLinear ℓ (L t)` — real |
| def:typed-cl-distributions | `typedCLDistribution`, `ldQuestionDistribution_eq_typedCL`, `pauliQuestionDistribution_eq_typedCL` | Games/TypedCondLinear | N | `noncomputable def typedCLDistribution (E : Finset (Sym2 T)) (hE : E.Nonempty) (L R : T → (ι → K) → ι → K) : Distribution ((T × (ι → K)) × (T × (ι → K))) := (graphDistribution E).bind-with-`clDistribution`-per-type-pair` — real; REUSE 4.1's `graphDistribution` and `clDistribution`. **Plus the two reconciliation lemmas** stating that 4.1's inlined `ldQuestionDistribution` and `pauliQuestionDistribution` equal `typedCLDistribution` at their edge sets and CL families (`sorry`). This is the honest discharge of 4.1's OPEN-3 |
| lem:alnf | `aLinePointDist_point_marginal_uniform`, `aLinePointDist_mem_line` | Test/LowDegreeGameTheorems | N | `theorem … (L : LdParams) [FieldModel L.q] : (aLinePointDist L).map (point component) = uniformDistribution (Point L) ∧ (aLinePointDist L).map (axis index) = uniformDistribution (Fin L.m)`; `theorem … : ∀ z ∈ (aLinePointDist L).support, z.point ∈ linePoints z.base (stdBasis (chiIndex L z.seed))` (both `sorry`) |
| lem:dlnf | `dLinePointDist_point_marginal_uniform`, `dLinePointDist_mem_line`, `dLinePointDist_prefix_zero` | Test/LowDegreeGameTheorems | N | same three-way split; the third records that the direction's first `i-1` coordinates vanish (all `sorry`) |
| def:line-point-dist | `LineDesc`, `aLinePointDist`, `dLinePointDist`, `linePointDist` | Test/LowDegreeGameTheorems | N | `abbrev LineDesc (L : LdParams) [FieldModel L.q] := Point L × Point L` (base point × direction — the presentation type ch15/ch14 need); `noncomputable def aLinePointDist (L) : Distribution (LineDesc L × Point L) := (clDistribution (ldALineCL L) (ldPointCL L)).map (fun p => (lineDescOf p.1, pointOf p.2))`; `dLinePointDist` likewise from `ldDLineCL`; `noncomputable def linePointDist (L) : Distribution (LineDesc L × Point L) := Distribution.mix (1/2) (aLinePointDist L) (dLinePointDist L)`. **All three keyed to `LdParams`, hence dimension-generic** (ch15 RECONCILE-2 is satisfied here). Real; `Distribution.mix` is a Lean-only helper if the LDT API lacks it (RECONCILE-5) |
| def:ld-meas | `PolyIndex`, `PolyMeas`, `PolyMeasTuple` | Test/LowDegreeGameTheorems | N | `abbrev PolyIndex (m q d : ℕ) [FieldModel q] : Type := MIPStarRE.LDT.Preliminaries.polyFunc-index at (m,q,d)`; `abbrev PolyMeas (m q d) (ι) := Quantum.Measurement (PolyIndex m q d) ι`; `abbrev PolyMeasTuple (L : LdParams) (ι) := Quantum.Measurement (Fin L.k → PolyIndex L.m L.q L.d) ι` (constant tuples only — the source's non-constant `PolyMeas(m,q,d,k)` is not needed and is omitted, docstring says so). REUSE the LDT representative convention (4.1 (e)1, issue #0004); **note** ch03's `def:polymeasurements` is `\leanok` on the LDT `SubMeas` layer, which the QPBT games layer does not use (4.1 (e)4) — hence a new `Quantum.Measurement`-based alias, not a reuse (RECONCILE-3) |
| lem:ld-soundness | `deltaLd`, `exists_ld_soundness` | Test/LowDegreeGameTheorems | N | `noncomputable def deltaLd (a b ε : ℝ) (q m d k : ℕ) : ℝ := a * ((d*m*k : ℕ) : ℝ) ^ a * (ε ^ b + (q : ℝ) ^ (-b) + (2 : ℝ) ^ (-(b * ((m*d : ℕ) : ℝ))))` — **a new function, distinct from the frozen `deltaQld`**: prefactor `a(dmk)^a` and `0 < b ≤ 1`, per rem:delta-qld-argument-order; `theorem exists_ld_soundness : ∃ a b : ℝ, 1 ≤ a ∧ 0 < b ∧ b ≤ 1 ∧ ∀ (L : LdParams) [FieldModel L.q] (ε : ℝ), 0 < ε → ∀ S : Strategy (ldGame L), S.IsProjective → 1 - ε ≤ S.value → ∃ (GA : PolyMeasTuple L S.ιA) (GB : PolyMeasTuple L S.ιB), (three `consistencyDefect` bounds ≤ deltaLd a b ε L.q L.m L.d L.k: point-vs-`GB`, `GA`-vs-point under `uniformDistribution (Point L)`, and `GA`-vs-`GB` under the one-point distribution)` (`sorry`). Docstring must cite `gap:qpbt_ld-dimension-divisibility`, the two enumerated import obligations (game correspondence, parameter bound), and rem:ld-soundness-provider (this is **not** derived from `LDT.Test.mainFormal`) |
| thm:ms-rigidity | `exists_ms_rigidity` | Test/MagicSquareTheorems | N | `theorem … (ε : ℝ) (hε : 0 ≤ ε) (S : Strategy msGame) (h : 1 - ε ≤ S.value) : ∃ C : ℝ, 1 ≤ C ∧ ∃ (ιA'' ιB'' : Type) (insts) (φA : EuclideanSpace ℂ S.ιA →ₗᵢ[ℂ] EuclideanSpace ℂ ((Fin 2 → ZMod 2) × ιA'')) (φB : …) (aux : EuclideanSpace ℂ (ιA'' × ιB'')), ‖aux‖ = 1 ∧ ‖isometryTensor φA φB S.ψ - idealMsState aux‖ ≤ C * Real.sqrt ε ∧ (four `opFamilyDistSq` bounds for `Variable₁`/`Variable₅` against `qubitPauliProj .X` / `.Z` ≤ C * Real.sqrt ε) ∧ (two `opDistSq` anticommutation bounds ≤ C * Real.sqrt ε)` (`sorry`). `idealMsState aux := reindexState prodShuffle (vecTensor (eprState (Fin 2 → ZMod 2)) aux)`; the `MsType.var` indices are **0 and 4** for `Variable₁`/`Variable₅` (4.1 indexes `Fin 9` from 0 — off-by-one, flagged). Docstring: imported from Coladangelo–Stark Thm 6.9, `**Local fix:**` for the trace-norm→Euclidean `O(√ε)` restatement and the local basis change |
| thm:ms-from-ac | `obsOf`, `exists_ms_perfect_strategy_of_anticommuting` | Test/MagicSquareTheorems | N | `def obsOf (M : Measurement (ZMod 2) ι) : Op ι := M.effect 0 - M.effect 1` (Lean-only helper, real); `theorem … (n : ℕ) (A B : Quantum.Measurement (ZMod 2) (Fin n → K)) (hA hB : projective) (hcA hcB : `.IsConsistentOn (eprState (Fin n → K))`) (hac : obsOf A * obsOf B = -(obsOf B * obsOf A)) : ∃ S : SymmetricStrategy msGameSymm, S.IsSPCC ∧ S.toStrategy.value = 1 ∧ S.ψ = msPerfectState n ∧ ∀ b, (S.M (MsType.var 0)).effect b = heteroKron (A.effect b) 1 ∧ (S.M (MsType.var 4)).effect b = heteroKron (B.effect b) 1` (`sorry`); `msGameSymm : SymmetricGame` + `msGameSymm_toGame : msGameSymm.toGame = msGame` (`sorry`) are new here (RECONCILE-6) |
| lem:pauli-completeness | `pauliBasisTestSymm`, `exists_spcc_value_one` | Test/Completeness | N | `noncomputable def pauliBasisTestSymm (P : AdmissibleParams) [FieldModel P.q] : SymmetricGame` + `pauliBasisTestSymm_toGame : (pauliBasisTestSymm P).toGame = pauliBasisTest P` (`sorry`, RECONCILE-6); `theorem exists_spcc_value_one (P) [FieldModel P.q] : ∃ S : SymmetricStrategy (pauliBasisTestSymm P), S.IsSPCC ∧ S.toStrategy.value = 1` (`sorry`) |
| cor:pauli-binary | `pauli_soundness_qubit` | Test/QubitForm | N | `theorem pauli_soundness_qubit : ∃ a b : ℝ, 1 ≤ a ∧ 0 < b ∧ b < 1 ∧ ∀ (P : AdmissibleParams) [FieldModel P.q] (R : SelfDualNormalRep P.q) (ε : ℝ), 0 < ε → ∀ S : Strategy (pauliBasisTest P), 1 - ε ≤ S.value → ∃ …, ‖isometryTensor φA φB S.ψ - idealQubitState P R aux‖ ≤ deltaQld a b ε P.m P.d P.q ∧ ∀ W, (the two `opFamilyDistSq` bounds against `qubitPauliProj W (kappaVec R u)`, summation over `u : PauliRegister P`) ≤ deltaQld a b ε P.m P.d P.q` (`sorry`), with `A''`/`B''` indexed by `Cube P.m × Fin R.k → ZMod 2`. REUSES the frozen `deltaQld` and 4.1's `pauli_soundness` shape verbatim; the `SelfDualNormalRep` argument is the `\uses` omission of OPEN-2 |
| def:introparams | `introParamsC`, `introParamsTuple`, `AdmissibleParams.ofTuple`, `introParams` | Test/CanonicalParams | N | `noncomputable def introParamsC (a b : ℝ) : ℕ := 2 * ⌈(b + a) / (2 * b)⌉₊` (smallest even integer ≥ `(b+a)/b`); `def introParamsTuple (c R : ℕ) : ℕ × ℕ × ℕ := (2 ^ (c * Nat.clog 2 (Nat.clog 2 R) + 1), 2 ^ Nat.log 2 (c * Nat.clog 2 R + 1), 1)` — real, no `sorry`; `def AdmissibleParams.ofTuple (t) (h : IsAdmissibleTuple t) : AdmissibleParams` — real; `noncomputable def introParams (a b : ℝ) (R : ℕ) (hR : 4 ≤ R) : AdmissibleParams := AdmissibleParams.ofTuple _ (introParamsTuple_isAdmissible a b R hR)`, real (its only proof obligation is the `sorry`'d lemma below, so no `sorry` sits inside a definition) |
| lem:delta-bound | `introParamsTuple_isAdmissible`, `le_two_pow_introParams_m`, `exists_deltaQld_introParams_bound` | Test/CanonicalParams | N | `theorem introParamsTuple_isAdmissible (a b) (hb : 0 < b) (R) (hR : 4 ≤ R) : IsAdmissibleTuple (introParamsTuple (introParamsC a b) R)`; `theorem le_two_pow_introParams_m … : R ≤ 2 ^ (introParams a b R hR).m`; `theorem exists_deltaQld_introParams_bound (a b) (ha : 1 ≤ a) (hb : 0 < b) (hb' : b < 1) : ∃ a' b' : ℝ, 1 ≤ a' ∧ 0 < b' ∧ b' ≤ 1 ∧ ∀ (R) (hR : 4 ≤ R) (ε : ℝ), deltaQld a b ε (introParams a b R hR).m (introParams …).d (introParams …).q ≤ a' * ((Real.logb 2 R) ^ a' * ε ^ b' + (Real.logb 2 R) ^ (-b'))` (all `sorry`). REUSE frozen `deltaQld`; docstring cites rem:delta-bound-exponent-comparison (the `k ≤ m` step of the source is replaced) |

Lean-only helpers (each docstring-marked formalization-only per AGENTS.md): `kappaVec`,
`cubeEmbed`, `submoduleFinset`, `instFieldModelTwo`, `opDistSq`, `placeA`/`placeB`
(heteroKron ampliations), `idealMsState`, `msPerfectState`, `idealQubitState`, `obsOf`,
`IsAdmissibleTuple`, `Distribution.mix`, `stdBasis`, `lineDescOf`, `IsPolyErr₂` (shared
with ch15 — OPEN-4).

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
   RECONCILE-2, satisfied here. `LineDesc L := Point L × Point L` (base point × direction)
   is also the presentation type ch15's RECONCILE-3 asks for; ch14/ch15 bind to it rather
   than defining their own. `linePointDist` is the blueprint's `1/2`–`1/2` mixture `D_Line`;
   the two components are exported separately because ch15 filters them.
3. `def:projective-strategy-general` → **`Strategy.IsProjective`** (`Games/StrategyClasses.lean`).
   Statement level in **ch14** (`lem:projective-strategy-setup`).
4. `def:symmetric-game` → **`SymmetricGame` / `SymmetricStrategy` / `.toGame` / `.toStrategy`**
   (`Games/StrategyClasses.lean`). Statement level in **ch14**. Contract: the single-alphabet
   carrier described in (c) — ch14 must phrase its ambient setting over `SymmetricStrategy`,
   whose local space is a *single* `ι` and whose state lives on `ι × ι`; ch15's
   `ExpandedSetting` bundle should be built on top of this rather than on bare `Strategy`.
5. `lem:twisted-commutation` → **`tauObservable_mul`, `tauObservable_sq`,
   `tauObservable_X_mul_Z`** (`Algebra/PauliTheorems.lean`). Statement level in **ch14**.
   Contract: char-2 only, phase written as `(-1 : ℂ) ^ (binTrace (a ⬝ᵥ b)).val`.
6. `def:binary-representation` → **`SelfDualNormalRep`** (+ `.kappa`, `.mulTable`, `.chi`);
   `def:dual-self-dual-normal-basis` → **`Basis.IsSelfDual` / `Basis.IsNormal`**
   (`Algebra/SelfDualBasis.lean`). Both statement level in **ch16**. Contract: an **extra
   argument carried alongside `[FieldModel q]`**, never a modification of `FieldModel`
   (4.1-frozen); every consumer needing κ takes `(R : SelfDualNormalRep q)`.
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

## OPEN: items for the orchestrator

- **OPEN-1** (does `FieldModel` get pinned?): 4.1's OPEN-6 asked whether
  `def:binary-representation` should pin `FieldModel.equiv`. This brief answers **no**:
  `SelfDualNormalRep q` is an extra bundled datum, so 4.1's games stay parametrized by an
  arbitrary `FieldModel` and only `lem:pauli-binary`, `cor:pauli-binary` and ch16's
  statement-level consumers carry `(R : SelfDualNormalRep P.q)`. This keeps 4.1 untouched
  but leaves `χ` (eq:chi-func) reading the *unpinned* `FieldModel.equiv` while `γ`
  (eq:gamma-value) reads the *pinned* trace — the mismatch 4.1's OPEN-1 flagged. Confirm,
  or direct that `pauliBasisTest` be re-parametrized at reconciliation.
- **OPEN-2** (`\uses` omissions in ch11/ch13): `cor:pauli-binary`'s statement needs
  `def:binary-representation` (it writes `κ(u_i)`) and `lem:pauli-binary`, but its `\uses`
  lists neither; `lem:pauli-binary`'s statement needs `def:subfields-kappa`. Consider
  patching those `\uses` lines.
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
