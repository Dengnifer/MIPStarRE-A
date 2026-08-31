# Implementation brief — stage 4.2, chapter ch14: strategy observables and the expanded space

Deliverable: Lean skeleton (all proofs `sorry`, all definitions real) for
`blueprint/src/chapter/ch14_qpbt_observables.tex` (`chap:qpbt-observables`; sections
`sec:qld-prelim`, `sec:commutation`, `sec:expanding`). Paper mirror:
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex` lines 47–679 (per-node
ranges in the table below; every statement-like docstring cites the blueprint `\label`
plus that file and line range). Baseline: `issues/briefs/0006-minimal-skeleton-brief.md`
(stage 4.1) — its naming table is FROZEN and reused verbatim. Conventions: `AGENTS.md`.

**Wave position.** ch14 is wave A; ch15 and ch16 (wave B) consume its signatures.
Rows marked **INTERFACE** in (c) are the parallel-wave contract and are stated in (e).
The sibling brief `issues/briefs/42-ch15-brief.md` was read; its RECONCILE-1/-2/-3 and
OPEN-2/-3 requests are answered here (see (e) and OPEN-6).

Scope check: **no ch14 node is in the 4.1 closure** (checked against the 4.1 39-node
table — that closure stops at ch13). Outside ch14 the statement `\uses` reach into
ch11/ch12/ch13 labels that are *also* not in the 4.1 closure: `def:consistency`,
`def:projective-strategy-general`, `def:symmetric-game` (ch12) and `def:line-point-dist`
(ch13). ch14 is the earliest chapter needing them, so this brief claims all four; see
OPEN-1. Everything else it needs is already in the 4.1 table (REUSE, frozen names).

## (a) Nodes of ch14 not in the 4.1 closure — dependency order, env kind

Topological for statement-level `\uses` restricted to ch14-internal edges (proof-level
`\uses` excluded, per the 4.1 method). 20 formalizable nodes + 3 documentation-only
remarks (no Lean declaration; cited in the docstrings of the nodes they correct).

| # | label | env | ch14-internal statement deps | paper lines |
|---|-------|-----|------------------------------|-------------|
| 1 | `def:ideg-deg-polynomials` | definition | — | 51–62 |
| 2 | `def:anticommuting-tuple` | definition | — | 63–68 |
| 3 | `fact:omega-anticomm-prob` | lemma | 2 | 70–93 |
| 4 | `def:approx-question-indexed-operators` | definition | — | 95–99 |
| 5 | `lem:avg-closeness` | lemma | 4 | 100–113 |
| 6 | `lem:povm-to-obs` | lemma | 4 | 114–131 |
| 7 | `lem:ortho` | lemma (imported) | — | 136–145 |
| 8 | `lem:projective-strategy-setup` | lemma | — | 160–172 |
| 9 | `def:strategy-observables` | definition | 8 | 174–190 |
| 10 | `lem:qld-win-implications` | lemma | 1, 2, 8 | 197–266 |
| 11 | `lem:qld-win-implications-obs` | lemma | 2, 4, 8, 9 | 267–363 |
| 12 | `def:expanded-state` | definition | 8 | 367–373 |
| 13 | `def:expanded-observables` | definition | 9, 12 | 374–378 |
| 14 | `def:expanded-point-measurement` | definition | 13 | 379–411 |
| 15 | `def:expanded-point-trace-projection` | definition | 13, 14 | 412–420 |
| 16 | `def:symmetric-equivalents` | definition | 12 | 434–460 |
| 17 | `lem:symmetric-equivalents-transfer` | lemma `\notready` | 8, 12, 16 | 434–460 |
| 18 | `lem:qld-comm-cons` | lemma | 4, 12, 14, 15, 16 | 462–522 |
| 19 | `def:expanded-line-measurement` | definition | 1, 8, 12, 13 | 552–556 |
| 20 | `lem:qld-comm-line-cons` | lemma | 1, 4, 12, 14, 16, 19 | 523–679 |

Documentation-only: `rem:deg-line-representatives` (cited by node 1 and 19),
`rem:omega-anticomm-prob-correction` (node 3 — records the source-proof error and the
added `m, d ≥ 1` hypothesis; a `**Local fix:**` docstring marker per AGENTS.md),
`rem:qld-win-implications-typos` (nodes 10, 11 — same marker).

External statement-level labels, by blueprint label (binding at reconciliation):

- **Claimed here** (not in 4.1, no other owner): `def:consistency`, `def:symmetric-game`,
  `def:projective-strategy-general` (ch12), `def:line-point-dist` (ch13).
- **REUSE, already `\leanok`**: `def:bracket` → `MIPStarRE.Quantum.Measurement.postprocess`,
  `def:submeasurement`, `def:polyfunc`; `thm:naimark` →
  `MIPStarRE.LDT.MakingMeasurementsProjective.naimarkTensorProductCorrelation`
  (proof-level only, for node 8).
- **REUSE, 4.1 frozen names**: `def:line`/`def:line-representative` (`linePoints`,
  `lineRepMap`), `def:polynomials-degree`, `def:low-degree-encoding`
  (`lowDegreeEncoding`, `lowDegreeEnc`), `def:indicator-vector` (`indicatorVec`),
  `def:subfield-trace` (`binTrace`), `def:admissible-size`, `def:admissible`
  (`AdmissibleParams`), `def:EPR` (`eprState`), `def:generalized-pauli`
  (`PauliKind`, `pauliProj`, `tauObservable` — RECONCILE-1),
  `lem:pauli-observable-expansion`, `def:povm-conventions`, `def:povm-distance`
  (`opFamilyDistSq`), `def:state-distance` (`stateDistSq`),
  `def:tensor-product-strategy`/`def:tensor-product-value` (`Strategy`,
  `Strategy.value`), `def:game` (`Game`), `def:ms-game` (`msGame`, `MsType`,
  `MsAnswer`, `msEdges`), `def:pauli-question-distribution`/`def:pauli-win-predicate`
  (`PauliType`, `PauliSpace`, `PauliQuestion`, `PauliAnswer`, `PauliRegister`,
  `pauliBasisTest`, `gammaValue`), `def:ld-question-distribution` (`chiIndex`,
  `LdParams`), `def:ld-win-predicate`.

## (b) Files extending the 4.1 tree

Namespace `MIPStarRE.QPBT` throughout (flat, as in 4.1). Real definitions are separated
from `sorry` statements per the LDT `Defs`/`Theorems` convention; every file is far
below the 1000-line cap (estimates in parentheses).

```
MIPStarRE/QPBT/Games/Consistency.lean            -- nodes 4 + def:consistency, IsPolyErr   (~150)
MIPStarRE/QPBT/Games/DistanceTheorems.lean       -- nodes 5, 6, 7                          (~120)
MIPStarRE/QPBT/Observables/LineDefs.lean         -- node 1 + def:line-point-dist           (~260)
MIPStarRE/QPBT/Observables/Anticommuting.lean    -- nodes 2, 3                             (~150)
MIPStarRE/QPBT/Observables/Setup.lean            -- node 8 + def:projective-strategy-general (~120)
MIPStarRE/QPBT/Observables/Defs.lean             -- ProjectiveSetting, questions, node 9   (~250)
MIPStarRE/QPBT/Observables/WinImplications.lean  -- nodes 10, 11                           (~290)
MIPStarRE/QPBT/Observables/ExpandedDefs.lean     -- nodes 12, 13, 14, 15, 16               (~270)
MIPStarRE/QPBT/Observables/Symmetry.lean         -- node 17                                (~160)
MIPStarRE/QPBT/Observables/PointConsistency.lean -- node 18 + eq:lc-22 / convolution       (~180)
MIPStarRE/QPBT/Observables/LineMeasurement.lean  -- nodes 19, 20                           (~260)
```

Internal import DAG: `Games/Distance ← Games/Consistency ← Games/DistanceTheorems`;
`{Algebra/Lines, Algebra/LowDegreeCode, Test/LowDegreeGame} ← Observables/LineDefs`;
`{Games/Defs, Test/PauliBasisTest, Algebra/Pauli} ← Observables/Anticommuting`;
`Games/Defs ← Observables/Setup ← Observables/Defs`;
`{LineDefs, Anticommuting, Games/Consistency} ← Observables/Defs`;
`Observables/Defs ← {WinImplications, ExpandedDefs}`;
`{ExpandedDefs, Algebra/Pauli} ← Symmetry`;
`{ExpandedDefs, Symmetry, Games/DistanceTheorems} ← PointConsistency`;
`{PointConsistency, LineDefs} ← LineMeasurement`. Add all files to
`MIPStarRE/QPBT.lean`. External imports as in 4.1 (b), plus
`MIPStarRE.LDT.MakingMeasurementsProjective` (node 8 docstring/proof target only).

## (c) Node → declaration mapping

Legend: R = reuse an existing declaration, N = new; **INTERFACE** = consumed by ch15/ch16
(see (e)). Signatures are sketches — the implementer owns the final form. Ambient:
`(q m d : ℕ) [FieldModel q]`, `K := FieldModel.K q`, `P : AdmissibleParams`,
`Reg := PauliRegister P`, `Point := Fin m → K`, `Op ι := Matrix ι ι ℂ`.
The line/polynomial layer is keyed to bare `(q, m, d)` rather than to a params bundle so
that ch15 can instantiate it at dimension `2m+2` (answers ch15 RECONCILE-2).

| label | Lean name | file | R/N | signature sketch |
|---|---|---|---|---|
| def:consistency (ch12) | `consistencyDefect` | Games/Consistency | N **INTERFACE** | `noncomputable def consistencyDefect (μ : Distribution X) (A B : X → α → Op ι) (ψ : EuclideanSpace ℂ ι) : ℝ := avgOver μ fun x => ∑ a, ∑ b, if a = b then 0 else (⟪ψ, (A x a * B x b).mulVec ψ⟫).re` — `≃_δ` is `consistencyDefect … ≤ δ`; `A`, `B` arrive already placed on the two parties (signature as proposed in the ch15 brief, adopted verbatim) |
| def:approx-question-indexed-operators | `opDistSq` | Games/Consistency | N **INTERFACE** | `noncomputable def opDistSq (μ : Distribution X) (A B : X → Op ι) (ψ : EuclideanSpace ℂ ι) : ℝ := avgOver μ fun x => ‖(A x - B x).mulVec ψ‖ ^ 2`; bridging lemma `opDistSq_eq_opFamilyDistSq_unit` relating it to 4.1's `opFamilyDistSq` at `α := Unit` (`sorry`) |
| lem:avg-closeness | `avg_closeness` | Games/DistanceTheorems | N | `theorem avg_closeness (μ) (A B : X → Op ι) (α : X → ℂ) (hα : ∀ x, ‖α x‖ ≤ 1) (ψ) : ‖((avgOver μ fun x => α x • (A x - B x))).mulVec ψ‖ ^ 2 ≤ opDistSq μ A B ψ` (`sorry`; the *quantitative* form of the blueprint, constant-free) |
| lem:povm-to-obs | `povm_to_obs` | Games/DistanceTheorems | N | `theorem povm_to_obs (μ) (A B : X → α → Op ι) (c : α → ℂ) (hc : ∀ a, ‖c a‖ = 1) (ψ) : opDistSq μ (fun x => ∑ a, c a • A x a) (fun x => ∑ a, c a • B x a) ψ ≤ (Fintype.card α) * opFamilyDistSq μ A B ψ` (`sorry`) |
| lem:ortho | `exists_projective_close_of_consistent` | Games/DistanceTheorems | N | `theorem … : ∃ η : ℝ → ℝ, (∃ C, 1 ≤ C ∧ ∀ δ, 0 ≤ δ → η δ ≤ C * δ ^ (1/4 : ℝ)) ∧ ∀ (ιA ιB α) [inst…] (ψ : EuclideanSpace ℂ (ιA × ιB)) (Q : Quantum.Measurement α ιA) (R : Quantum.Measurement α ιB) (δ) (hδ : 0 ≤ δ ∧ δ ≤ 1), consistencyDefect (single) (place Q) (place R) ψ ≤ δ → ∃ Pm : Quantum.Measurement α ιA, Pm.IsProjective ∧ opFamilyDistSq (single) (place Pm) (place Q) ψ ≤ η δ` (`sorry`; **imported** — docstring records KV11/[ML20], no proof planned) |
| def:ideg-deg-polynomials (classes) | `MvPolynomial.degreeOf`, `totalDegree`, `LDT.Preliminaries.polyFunc` | LineDefs | R | `ideg_{d,m}(F_q)` is `polyFunc m q d`; `deg_d` is `{p // p.totalDegree ≤ d}`; no new decl, module docstring records the bridge (4.1 (e)1 representative convention) |
| def:ideg-deg-polynomials (lines) | `LineKind`, `LineDesc`, `LineDesc.direction`, `LineDesc.pointSet` | LineDefs | N **INTERFACE** | `inductive LineKind ∣ axis ∣ diag`; `structure LineDesc (q m : ℕ) [FieldModel q] where kind : LineKind; base : Fin m → K; seed : K; dir : Fin m → K`; `def LineDesc.direction (ℓ) : Fin m → K` = `Pi.single (chiIndex q m ℓ.seed) 1` (axis) / `π_{i-1} ℓ.dir` (diag); `def LineDesc.pointSet (ℓ) : Set (Fin m → K) := linePoints ℓ.base ℓ.direction` (REUSE 4.1) — the `(u₀,s)` / `(u₀,s,v)` descriptions of def:strategy-observables, base point canonical by `lineRepMap` |
| def:ideg-deg-polynomials (answers) | `DegPoly`, `degPolyEval`, `DegPoly.padTo`, `EvaluatesTo`, `evalOpt` | LineDefs | N **INTERFACE** | `abbrev DegPoly (q c : ℕ) [FieldModel q] := Fin (c+1) → K` (coefficient list, rem:deg-line-representatives); `def degPolyEval (f : DegPoly q c) (t : K) : K := ∑ i, f i * t ^ (i : ℕ)`; `def DegPoly.padTo (h : c ≤ c') : DegPoly q c → DegPoly q c'` (zero extension, the inclusion `deg_d ⊆ deg_{md}`); `def EvaluatesTo (ℓ) (f : DegPoly q c) (u) (a : K) : Prop := (∃ t, u = ℓ.base + t • ℓ.direction) ∧ ∀ t, u = ℓ.base + t • ℓ.direction → degPolyEval f t = a`; `def evalOpt (ℓ) (u) (f : DegPoly q c) : Option K` (`some a` when `EvaluatesTo … a`, else `none` — decidable, `Finset.filter` over `K`) — the completed `F_q ∪ {⊥}` index; the bracket `N_{[eval_u(·)=a]}` is `Measurement.postprocess (evalOpt ℓ u)` (REUSE `def:bracket`, `\leanok`) |
| def:line-point-dist (ch13) | `aLinePointDist`, `dLinePointDist`, `linePointDist` | LineDefs | N **INTERFACE** | `noncomputable def linePointDist (L : LdParams) [FieldModel L.q] : Distribution (LineDesc L.q L.m × (Fin L.m → K))` — equal mixture of the two, each the image of `ldQuestionDistribution` under the pair of CL maps `(L_ALine, L_Point)` resp. `(L_DLine, L_Point)` (4.1 frozen `ldALineCL`/`ldDLineCL`/`ldPointCL`), read off as a `LineDesc`; `IsProbability` companions (`sorry`). Keyed to `LdParams` (dimension-generic) |
| def:anticommuting-tuple | `PauliTuple`, `IsAnticommuting`, `IsCommuting` | Anticommuting | R+N | `abbrev PauliTuple (q m) [FieldModel q] := (Fin m → K) × (Fin m → K) × K × K`; `def IsAnticommuting (ω : PauliTuple q m) : Prop := gammaValue ω.1 ω.2.1 ω.2.2.1 ω.2.2.2 ≠ 0` (γ REUSES 4.1's `gammaValue`, eq:gamma-value); `IsCommuting` its negation; both `DecidablePred` |
| fact:omega-anticomm-prob | `anticommProb`, `anticommProb_eq`, `commProb_ge_half`, `anticommProb_ge_of_m_le_q`, `anticommProb_ge_of_one_le_md` | Anticommuting | N | `noncomputable def anticommProb (q m : ℕ) [FieldModel q] : ℝ := ((univ.filter (IsAnticommuting (q := q) (m := m))).card : ℝ) / Fintype.card (PauliTuple q m)`; `anticommProb_eq : anticommProb q m = (1 - (q:ℝ)⁻¹) ^ (m+1) / 2` (`sorry`); the three bound lemmas `sorry`, the last with hypotheses `1 ≤ m`, `1 ≤ d` (`**Local fix:**` docstring, rem:omega-anticomm-prob-correction). Companion distributions `anticommTupleDist`, `commTupleDist` := `Distribution.uniformOnFinset` on the two filtered sets, `IsProbability` (`sorry`) |
| def:projective-strategy-general (ch12) | `Strategy.IsProjective` | Setup | N | `def Strategy.IsProjective (S : Strategy G) : Prop := (∀ x, (S.A x).IsProjective) ∧ (∀ y, (S.B y).IsProjective)` (REUSE 4.1's `Measurement.IsProjective`) |
| lem:projective-strategy-setup | `exists_projective_padded_strategy` | Setup | N | `theorem exists_projective_padded_strategy (G : Game) (S : Strategy G) : ∃ (nA nB : ℕ) (T : Strategy G) (eA : T.ιA ≃ S.ιA × (Fin nA → Bool)) (eB : T.ιB ≃ S.ιB × (Fin nB → Bool)), T.IsProjective ∧ reindexState (Equiv.prodShuffle …) T.ψ = isometryTensor (padWithZeros eA) (padWithZeros eB) S.ψ ∧ T.value = S.value` (`sorry`; proof route = `naimarkTensorProductCorrelation` + residual-projector completion, per the blueprint proof). Lean-only `padWithZeros` helper |
| — (standing convention, 14:160–172) | `ProjectiveSetting`, `.toStrategy`, `.IsSymmetric` | Defs | N **INTERFACE** | `structure ProjectiveSetting (P : AdmissibleParams) [FieldModel P.q] (ε : ℝ) where ι : Type; [Fintype ι] [DecidableEq ι]; ψ : EuclideanSpace ℂ (ι × ι); ψ_norm : ‖ψ‖ = 1; M : PauliQuestion P → Quantum.Measurement (PauliAnswer P) ι; M_proj : ∀ x, (M x).IsProjective; win : 1 - ε ≤ toStrategyAux.value`. Shared `M` for both players is forced by the statements of node 10 (same symbol on both sides) and is the compact symmetric notation of ch12; `noncomputable def toStrategy : Strategy (pauliBasisTest P)` (`ιA = ιB = ι`, `A = B = M`); `def IsSymmetric (S) : Prop := reindexState (Equiv.prodComm _ _) S.ψ = S.ψ` (`def:symmetric-game`, hypothesis of node 17 only) |
| — (question embeddings, 14:174–184) | `ProjectiveSetting.pointQuestion`, `.lineQuestion`, `.pauliQuestion`, `.pairQuestion`, `.pairWQuestion`, `.msQuestion` and the `Option`-completed families `.pointMeas`, `.lineMeas`, `.pairMeas`, `.msMeas`, `.pauliMeas` | Defs | N **INTERFACE** | `def pointQuestion (W : PauliKind) (u : Fin P.m → K) : PauliQuestion P := (PauliType.point W, contentOfPoint W u)` and analogues (contents are full `PauliSpace P` vectors with the named blocks filled, 0 elsewhere — 4.1 (e)9); `noncomputable def pointMeas (S) (W) (u) : Quantum.Measurement (Option K) S.ι := (S.M (S.pointQuestion W u)).postprocess pointAnswerOpt` where `pointAnswerOpt : PauliAnswer P → Option K` sends `.value a ↦ some a`, every other constructor ↦ `none`. **Every answer alphabet in this chapter is `Option`-completed this way**: it is exactly the "answers not of the prescribed form are rejected" convention, and it makes the `⊥` classes of def:ideg-deg-polynomials and of item 2 of node 10 uniform. `lineMeas W ℓ : Quantum.Measurement (Option (DegPoly P.q (P.m*P.d))) S.ι` uses `DegPoly.padTo` on axis-parallel lines |
| def:strategy-observables | `ProjectiveSetting.pointObs`, `pointObs_sq_eq_one` | Defs | N | `noncomputable def pointObs (S) (W : PauliKind) (r : K) (u : Fin P.m → K) : Op S.ι := ∑ a : K, negOnePow (binTrace (a * r)) • (S.pointMeas W u).effect (some a)` (eq:qld-strat-obs); companion `pointObs_sq_eq_one : S.pointObs W r u * S.pointObs W r u = 1` and `pointObs_isHermitian` (`sorry` — the prose "is an observable with eigenvalues ±1", per 4.1 (e)7) |
| lem:qld-win-implications | `win_cons`, `win_low_degree`, `win_pauli_basis_cons`, `win_comm`, `win_comm_cons`, `win_magic_square`, `win_ms_cons` | WinImplications | N | seven `sorry` theorems, one per item, each `(S : ProjectiveSetting P ε) (hε : 0 ≤ ε) : consistencyDefect … ≤ C * ε` with a chapter-level existential `∃ C, 1 ≤ C ∧ …` where the source writes `O(ε)`; distributions: `pauliQuestionDistribution` (item 1), `linePointDist P.toLdParams` (item 2), `uniformDistribution` on points (item 3), `commTupleDist` (items 4, 5), `anticommTupleDist` (items 6, 7); item 2's two families are the `evalOpt`-bracketed line family and the `Option`-completed point family, both indexed by `Option K` (rem:qld-win-implications-typos); item 6 is `|1 - avgOver anticommTupleDist (msValueAt S)| ≤ C * ε` with `noncomputable def msValueAt (S) (ω) : ℝ` the explicit `def:tensor-product-value` sum over `msGame` for the `Option`-completed MS families (Lean-only encoding note: no junk MS answer is invented). Trailing clause "also with `≈_ε` and factors interchanged" → companion `sorry` corollaries `win_*_approx` stated with `opFamilyDistSq` |
| lem:qld-win-implications-obs | `pointObs_self_consistent`, `pointObs_twisted_commutation` | WinImplications | N | `theorem pointObs_self_consistent (S) : ∃ C, 1 ≤ C ∧ ∀ W r, opDistSq (uniformDistribution _) (fun u => heteroKron (S.pointObs W r u) 1) (fun u => heteroKron 1 (S.pointObs W r u)) S.ψ ≤ C * ε` (eq:pts-obs-consistency); `theorem pointObs_twisted_commutation (S) : ∃ C, 1 ≤ C ∧ opDistSq (uniformDistribution (PauliTuple P.q P.m)) (fun ω => heteroKron (S.pointObs .X ω.2.2.1 ω.1 * S.pointObs .Z ω.2.2.2 ω.2.1) 1) (fun ω => negOnePow (gammaValue …) • heteroKron (S.pointObs .Z … * S.pointObs .X …) 1) S.ψ ≤ C * Real.sqrt ε` (eq:pts-obs-commutation); both `sorry`, plus interchanged-factor variants |
| def:expanded-state | `SixReg`, `ProjectiveSetting.psiHat` | ExpandedDefs | N **INTERFACE** | `abbrev SixReg (P) [FieldModel P.q] (ι) := (ι × PauliRegister P × PauliRegister P) × (ι × PauliRegister P × PauliRegister P)` (`AA'A''` × `BB'B''`); `noncomputable def psiHat (S) : EuclideanSpace ℂ (SixReg P S.ι) := reindexState sixRegShuffle (vecTensor (vecTensor S.ψ (eprState (PauliRegister P))) (eprState (PauliRegister P)))` (eq:def-psihat; `EPR_q^{⊗M}` is `eprState (PauliRegister P)` per 4.1's `def:EPR` row); `sixRegShuffle` a Lean-only `Equiv` |
| def:symmetric-equivalents | `Placement`, `ProjectiveSetting.place` | ExpandedDefs | N **INTERFACE** | `inductive Placement ∣ AA' ∣ BA'' ∣ BB' ∣ AB''`; `noncomputable def place (S) (p : Placement) (O : Op (S.ι × PauliRegister P)) : Op (SixReg P S.ι)` — ampliation of `O` onto the two named registers, identity elsewhere (via 4.1 `heteroKron` + `reindexOp`); a bipartite relation "`M_{AA'} ≈ N_{BA''}`" is `opFamilyDistSq μ (place .AA' ∘ M) (place .BA'' ∘ N) S.psiHat ≤ δ`, and its symmetric equivalents are the three other `Placement` pairs |
| def:expanded-observables | `ProjectiveSetting.expObs` | ExpandedDefs | N | `noncomputable def expObs (S) (W : PauliKind) (r : K) (u : Fin P.m → K) : Op (S.ι × PauliRegister P) := heteroKron (S.pointObs W r u) (tauObservable W (r • indicatorVec u))` (eq:lc-23; `tauObservable` = 4.1's generalized Pauli observable, RECONCILE-1; `indicatorVec` frozen) |
| def:expanded-point-measurement | `ProjectiveSetting.expPointOp`, `.pointMeasExp`, `expPointOp_eq_convolution`, `pointMeasExp_isProjective` | ExpandedDefs | N **INTERFACE** | `noncomputable def expPointOp (S) (W) (u) (a : K) : Op (S.ι × PauliRegister P) := avgOver (uniformDistribution K) fun r => negOnePow (binTrace (a*r)) • S.expObs W r u` (the definition line, real); `noncomputable def pointMeasExp (S) (W) (u) : Quantum.Measurement K (S.ι × PauliRegister P)` bundling `expPointOp` with `sorry` POVM proof fields; `def tauPointProj (W) (u) (a : K) : Op (PauliRegister P) := ∑ h ∈ univ.filter (fun h => h ⬝ᵥ indicatorVec u = a), pauliProj W h` (eq:qld-point-obs-def, real); `expPointOp_eq_convolution : expPointOp S W u a = ∑ p ∈ univ.filter (fun p : K × K => p.1 + p.2 = a), heteroKron ((S.pointMeas W u).effect (some p.1)) (tauPointProj W u p.2)` (`sorry`); `pointMeasExp_isProjective` (`sorry`) |
| def:expanded-point-trace-projection | `ProjectiveSetting.expPointTrace`, `expPointTrace_eq_half_add` | ExpandedDefs | R+N **INTERFACE** | `noncomputable def expPointTrace (S) (W) (u) (r : K) : Quantum.Measurement (ZMod 2) (S.ι × PauliRegister P) := (S.pointMeasExp W u).postprocess (fun a => binTrace (a * r))` — REUSE `Measurement.postprocess` (eq:qld-def-mptur); `expPointTrace_eq_half_add : (S.expPointTrace W u r).effect b = (2 : ℂ)⁻¹ • (1 + negOnePow b • S.expObs W r u)` (`sorry`, eq:lc-22) |
| lem:symmetric-equivalents-transfer | `swapUnitary`, `thetaUnitary`, `psiHat_invariant_of_symmetric`, `place_dist_eq_of_placementPerm` | Symmetry | N | `def placementPerm : Placement → Placement → Equiv.Perm (SixReg P S.ι)` (the `Π = {Id, U_σ, U_θ, U_σU_θ}` action, simply transitive on `Placement` — item 1); `psiHat_invariant_of_symmetric (h : S.IsSymmetric) (U ∈ Π) : reindexState U S.psiHat = S.psiHat` (`sorry`); `place_dist_eq_of_placementPerm : ‖(S.place p₁ Q - S.place p₂ R).mulVec S.psiHat‖ = ‖(S.place (σ p₁) Q - S.place (σ p₂) R).mulVec S.psiHat‖` and the `opFamilyDistSq` corollary (`sorry`, item 2). **`\notready` in the blueprint** — see OPEN-3 |
| lem:qld-comm-cons | `deltaAnticom`, `expPoint_self_cons`, `expPointTrace_comm`, `exists_deltaAnticom` | PointConsistency | N **INTERFACE** (`deltaAnticom`) | `noncomputable def deltaAnticom (ε : ℝ) : ℝ := Real.sqrt ε` (the value the proof yields); `expPoint_self_cons (S) (p₁ p₂ : Placement) (h : p₁ ≠ p₂) : ∃ C, 1 ≤ C ∧ ∀ W, opFamilyDistSq (uniformDistribution _) (fun u a => S.place p₁ ((S.pointMeasExp W u).effect a)) (fun u a => S.place p₂ …) S.psiHat ≤ C * ε` (item 1 + all symmetric equivalents, `sorry`); `expPointTrace_comm : … ≤ C * deltaAnticom ε` over `uniformDistribution (PauliTuple P.q P.m)`, both operator orders (item 2, `sorry`); `exists_deltaAnticom : ∃ δ, IsPolyErr δ ∧ …` the source's "there exists δ_Anticom = poly(ε)" form (`sorry`) |
| def:expanded-line-measurement | `restrictToLine`, `tauLineProj`, `ProjectiveSetting.expLineOp`, `.lineMeasExp`, `expLineOp_zero_of_not_deg_d` | LineMeasurement | N **INTERFACE** | `noncomputable def restrictToLine (ℓ : LineDesc q m) (g : MvPolynomial (Fin m) K) : DegPoly q (m*d)` — substitute `t ↦ ℓ.base + t • ℓ.direction`, extract coefficients (real; Lean-only, degree bound a `sorry` companion); `def tauLineProj (W) (ℓ) (f : DegPoly P.q (P.m*P.d)) : Op (PauliRegister P) := ∑ h ∈ univ.filter (fun h => restrictToLine ℓ (lowDegreeEncoding h) = f), pauliProj W h` (REUSE frozen `lowDegreeEncoding`); `noncomputable def expLineOp (S) (W) (ℓ) (f) : Op (S.ι × PauliRegister P) := ∑ p ∈ univ.filter (fun p => p.1 + p.2 = f), heteroKron ((S.lineMeas W ℓ).effect (some p.1)) (tauLineProj W ℓ p.2)`; `lineMeasExp` bundles it as a `Quantum.Measurement (DegPoly …)` with `sorry` fields; `expLineOp_zero_of_not_deg_d` (`sorry`, the axis-parallel degree collapse) |
| lem:qld-comm-line-cons | `deltaLine`, `expLine_self_cons`, `expLine_point_cons`, `expLine_point_cons'`, `exists_deltaLine` | LineMeasurement | N **INTERFACE** (`deltaLine`) | `noncomputable def deltaLine (ε : ℝ) : ℝ := Real.sqrt ε`; the three items as `sorry` theorems over `linePointDist P.toLdParams`, with `expLineOp`/`lineMeasExp` as the *concrete* witnesses (the blueprint says the proof exhibits them), answer summation over `DegPoly P.q (P.m*P.d)` (items 1, 2) and over `Option K` via `Measurement.postprocess (evalOpt ℓ u)` (item 3); item 2 with error `C * ε`, items 1 and 3 with `C * deltaLine ε`; all symmetric equivalents; `exists_deltaLine : ∃ δ, IsPolyErr δ ∧ ∃ N : … , N.IsProjective ∧ …` the source's existential form (`sorry`) |

Lean-only helpers (docstring-marked "formalization-only auxiliary" per AGENTS.md):
`IsPolyErr (f : ℝ → ℝ) : Prop := ∃ a b, 1 ≤ a ∧ 0 < b ∧ ∀ ε, 0 ≤ ε → f ε ≤ a * ε ^ b` and
`IsPolyErr₂` (Games/Consistency — adopted from the ch15 brief so both waves share one
predicate); `negOnePow (b : ZMod 2) : ℂ`; `vecTensor`, `reindexState`, `reindexOp`,
`sixRegShuffle`, `padWithZeros`; `contentOfPoint`/`contentOfLine`/… block fillers;
`pointAnswerOpt`/`lineAnswerOpt`/`pairAnswerOpt`/`msAnswerOpt`; `msValueAt`;
`restrictToLine`; `π_{i-1}` truncation if 4.1 does not already export it.

## (d) STATEMENTS to `sorry` vs DEFINITIONS that must be real

- **Real definitions (no `sorry` in the body)**: `consistencyDefect`, `opDistSq`,
  `IsPolyErr`/`IsPolyErr₂`, `LineKind`, `LineDesc` (+ `direction`, `pointSet`),
  `DegPoly`, `degPolyEval`, `DegPoly.padTo`, `EvaluatesTo`, `evalOpt`,
  `aLinePointDist`/`dLinePointDist`/`linePointDist`, `PauliTuple`,
  `IsAnticommuting`/`IsCommuting`, `anticommProb`, `anticommTupleDist`/`commTupleDist`,
  `Strategy.IsProjective`, `ProjectiveSetting` (+ `toStrategy`, `IsSymmetric`, all
  question embeddings and `Option`-completed families), `pointObs`, `SixReg`, `psiHat`,
  `Placement`, `place`, `expObs`, `expPointOp`, `tauPointProj`, `expPointTrace`,
  `placementPerm`, `deltaAnticom`, `deltaLine`, `restrictToLine`, `tauLineProj`,
  `expLineOp`, `msValueAt`, and every Lean-only helper above.
- **Definitions carrying `sorry` *proof fields* only**: `pointMeasExp`, `lineMeasExp`
  (the `Quantum.Measurement` POVM/completeness fields — the blueprint's "in particular
  each is a projection and the family is a projective measurement" is a claim, not a
  definitional obligation). Their `effect`s are the real operators above and are
  related to them by `rfl`-grade `simp` lemmas.
- **`sorry` statements** (the whole proposition-valued set): `avg_closeness`,
  `povm_to_obs`, `exists_projective_close_of_consistent`, the four
  `anticommProb`/`commProb` bounds, `exists_projective_padded_strategy`,
  `pointObs_sq_eq_one` + `pointObs_isHermitian`, the seven `win_*` items and their
  `win_*_approx` corollaries, `pointObs_self_consistent`,
  `pointObs_twisted_commutation`, `expPointOp_eq_convolution`,
  `pointMeasExp_isProjective`, `expPointTrace_eq_half_add`,
  `psiHat_invariant_of_symmetric`, `place_dist_eq_of_placementPerm`,
  `expPoint_self_cons`, `expPointTrace_comm`, `exists_deltaAnticom`,
  `expLineOp_zero_of_not_deg_d`, the three `expLine_*` items, `exists_deltaLine`, plus
  the well-formedness companions (`IsProbability` of the four new distributions,
  `restrictToLine` degree bound, `opDistSq_eq_opFamilyDistSq_unit`). All marker-free
  tracked skeleton sorries — no `**Unfaithful:**` markers.
- Blueprint sync after type-check: `\lean{…}` + `\leanok` on the **20 statement**
  environments only (never on proofs), then `leanblueprint web` + `lake exe checkdecls`.

## (e) Cross-chapter dependencies — the wave-A/wave-B interface

**Exported by ch14 (consumers: ch15, ch16). These are the contract.**

1. `ProjectiveSetting P ε` — the ambient bundle for chapters 14–16. Answers ch15's
   RECONCILE-1: the bundle exists, but `psiHat`, `place`, `pointMeas`, `lineMeas` are
   **defs in the `ProjectiveSetting` namespace**, not structure fields, so ch15's
   `S.psiHat` / `S.place` / `S.pointMeas` dot-notation is exactly right. Two deltas from
   the ch15 placeholder: the bundle is named `ProjectiveSetting`, not `ExpandedSetting`;
   and the error functions are **top-level** `deltaLine ε` / `deltaAnticom ε`, not
   `S.deltaLine`. ch15's claim-17-2 should read `deltaLine ε`.
2. `Placement` / `ProjectiveSetting.place` (`def:symmetric-equivalents`) — the four
   register placements `AA'`, `BA''`, `BB'`, `AB''`. Every ch15/ch16 relation "on
   registers `CC'`" is `place p` applied to an `Op (ι × PauliRegister P)`. Consumed at
   statement level by ch15 (`lem:qld-4-10`, `lem:qld-4-12`,
   `lem:restricted-line-mixture-bounds`, …) and ch16
   (`lem:qld-constructing-the-paulis-helper`).
3. `ProjectiveSetting.pointMeasExp` (and `expPointOp`, `expPointTrace`) —
   `def:expanded-point-measurement` / `def:expanded-point-trace-projection`. Contract:
   outcome type `K = FieldModel.K P.q` (**not** `Option K` — the expanded point family
   is complete), acting on `S.ι × PauliRegister P`, `effect a = expPointOp S W u a`.
   ch15 `lem:qld-4-10`/`lem:qld-4-12` and ch16 `lem:qld-construct-the-paulis` bind here.
4. `ProjectiveSetting.psiHat : EuclideanSpace ℂ (SixReg P S.ι)` (`def:expanded-state`) —
   the state every `≈`/`≃` in ch15/ch16 is evaluated on. Register order in `SixReg` is
   `(A, A', A'') × (B, B', B'')`; changing it breaks every wave-B statement.
5. `LineDesc q m`, `DegPoly q c`, `DegPoly.padTo`, `evalOpt`, `EvaluatesTo`
   (`def:ideg-deg-polynomials`) — answers ch15's request that ch14 supply the line
   *description* type. Note the two deltas from ch15's guess: `LineDesc` is a
   four-field structure (kind, base, seed, dir) rather than `Point × Point`, with the
   direction derived by `LineDesc.direction`; and it is keyed to bare `(q, m)`, so
   ch15's dimension-`2m+2` instantiation is free.
6. `linePointDist : (L : LdParams) → Distribution (LineDesc L.q L.m × (Fin L.m → K))`
   (`def:line-point-dist`, claimed here) — **dimension-generic**, satisfying ch15
   RECONCILE-2. ch15's `restrictedALineDist`/`restrictedDLineDist` build on it directly.
7. `consistencyDefect`, `opDistSq`, `IsPolyErr`, `IsPolyErr₂` — resolves ch15's OPEN-3
   in ch14's favour, in the file ch15 already imports
   (`MIPStarRE/QPBT/Games/Consistency.lean`); the `consistencyDefect` signature is
   ch15's proposal adopted verbatim, so no ch15 edit is needed.
8. `ProjectiveSetting.lineMeasExp` / `expLineOp` (`def:expanded-line-measurement`) and
   `deltaLine` — consumed by ch15 `lem:qld-xz-lines` (the `T` witness) and, at
   *statement* level, `lem:claim-17-2` (the error function only).
9. `exists_projective_padded_strategy` (`lem:projective-strategy-setup`) — ch16
   `lem:qld-construct-the-paulis`, `lem:qld-unitary` and `thm:pauli`'s own proof enter
   through it. Contract: it is a statement about 4.1's `Strategy`, producing a
   projective strategy with *equal* value and an explicitly ancilla-padded state; the
   `ProjectiveSetting` bundle is the convention paragraph that follows it.
10. Not exported at statement level but available: `pointObs` (ch16 builds its own
    `def:tilde-w-observables`), `PauliTuple`/`IsAnticommuting`, the `win_*` items
    (ch16 uses `lem:qld-win-implications` at proof level only), `povm_to_obs`,
    `avg_closeness`, `exists_projective_close_of_consistent` (all three consumed by
    ch15 `lem:qld-4-10` at proof level, and `lem:ortho` is listed there).

**Consumed by ch14 from wave-A siblings and 4.1**: the full REUSE list at the end of
(a); nothing from ch15 or ch16.

## RECONCILE: assumptions about the 4.1 skeleton (pending the 4.1 PR merge)

- RECONCILE-1: `Algebra/Pauli.lean` exports `tauObservable (W : PauliKind) (a : γ → K) :
  Op (γ → K)` (the multi-qudit `τ^W(a)`) alongside `pauliProj`. 4.1 names the lemma
  `tauObservable_eq_sum_pauliProj` but does not spell the observable's own row; the name
  is inferred from it. Nodes 13, 14, 19 depend on it.
- RECONCILE-2: `PauliAnswer` constructor names used verbatim from 4.1 —
  `.value`, `.alinePoly (Fin (d+1) → K)`, `.dlinePoly (Fin (m*d+1) → K)`, `.pairBits`,
  `.bit`, `.msTriple`, `.pauliOutcome` — and `DegPoly q d`/`DegPoly q (m*d)` are
  definitionally the `alinePoly`/`dlinePoly` payloads. If a payload is reshaped, the
  `Option`-completion maps and `lineMeas` change mechanically.
- RECONCILE-3: 4.1 exports only `pauliQuestion P W` (Soundness.lean) among the question
  embeddings. The other five (`pointQuestion`, `lineQuestion`, `pairQuestion`,
  `pairWQuestion`, `msQuestion`) are defined here against 4.1's `PauliIndex`/
  `PauliSpace` block layout (`V_X, V_Z, V_I, V_V, V_{R_X}, V_{R_Z}`). If 4.1 exports
  block accessors or its own embeddings, delete the local copies; if the block layout
  differs, only `contentOf*` changes. Companion `sorry` lemmas asserting each embedding
  lands in the support of `pauliQuestionDistribution` are included.
- RECONCILE-4: names used before merge, verbatim: `AdmissibleParams` (+ `toLdParams`),
  `LdParams`, `FieldModel`, `PauliRegister`, `Cube`, `chiIndex`, `ldPointCL`/`ldALineCL`/
  `ldDLineCL`, `ldQuestionDistribution`, `linePoints`, `lineRepMap`, `indicatorVec`,
  `lowDegreeEncoding`, `binTrace`, `gammaValue`, `pauliProj`, `eprState`, `heteroKron`,
  `reindexState`, `isometryTensor`, `opFamilyDistSq`, `stateDistSq`, `Game`, `Strategy`,
  `Strategy.value`, `msGame`, `MsType`, `MsAnswer`, `pauliBasisTest`,
  `Quantum.Measurement`, `Measurement.postprocess`, `Measurement.IsProjective`,
  `Distribution` + `avgOver`/`map`/`uniformDistribution`/`uniformOnFinset`/
  `IsProbability`. `ScalarQ P` is assumed `AdmissibleParams`-keyed; the line/polynomial
  layer therefore writes `FieldModel.K q` directly to stay dimension-generic.
- RECONCILE-5: 4.1's `Strategy` has separate `ιA`/`ιB` and `A`/`B`. `ProjectiveSetting`
  is the symmetric compact form (`ι`, shared `M`) with `toStrategy` as the bridge. If
  4.1 or a sibling adds its own `SymmStrategy`, merge into that.

## OPEN: items for the orchestrator

- **OPEN-1 (ownership of four unowned ch11–ch13 labels)**: `def:consistency`,
  `def:symmetric-game`, `def:projective-strategy-general` (ch12) and
  `def:line-point-dist` (ch13) are statement-level dependencies of ch14 but appear in no
  4.1 closure and in no 4.2 chapter assignment. This brief claims all four (files in
  (b)). Confirm, or point at the owning brief — the signatures in (c) are the interface
  either way.
- **OPEN-2 (`\uses` omissions in ch14)**: (i) `def:strategy-observables` and
  `def:expanded-point-measurement` are `\uses`-cited by node 19 and node 15 but the
  *statement* of `def:expanded-line-measurement` also needs `def:pauli-win-predicate`'s
  answer format (it is cited) and `def:polyfunc` (it is not). (ii) `def:expanded-observables`
  cites `lem:twisted-commutation` where only `def:generalized-pauli` is needed at
  statement level — the lemma is used to justify the sign cancellation in the *proof* of
  node 18. (iii) node 10 item 6 needs `def:tensor-product-value` (cited) and `def:game`
  (not cited). Consider patching the ch14 `\uses` lines; the skeleton follows the
  mathematical need, not the cited set.
- **OPEN-3 (`lem:symmetric-equivalents-transfer` is `\notready`)**: it is the only
  `\notready` node in the entire blueprint. The skeleton states it anyway (the statement
  is well-formed; the marker appears to record that register-permutation infrastructure
  is missing) and no other node depends on it at statement level — ch15/ch16 bind
  `def:symmetric-equivalents` (i.e. `Placement`/`place`), never the transfer lemma.
  Decide: keep the sorry'd statement, or drop node 17 from the 4.2 skeleton and leave
  `Symmetry.lean` with `placementPerm` alone.
- **OPEN-4 (`Option`-completed answer alphabets)**: every strategy-side family in this
  chapter is `Measurement.postprocess`-ed along a total map into `Option α`, with
  wrong-form answers going to `none`. This makes "answers not of the prescribed form are
  rejected", the `⊥` class of `def:ideg-deg-polynomials`, and item 2 of node 10 a single
  uniform mechanism, and keeps `fact:data-processing` applicable. Confirm as the
  wave-wide convention (ch15's `evalClass`-bracketing and ch16's coarse-grainings would
  inherit it).
- **OPEN-5 (`EvaluatesTo` off the line)**: the blueprint defines "f evaluates to a at u"
  only for `u ∈ ℓ`; read literally, every `a` qualifies vacuously when `u ∉ ℓ`. The
  skeleton conjoins the membership guard, so an off-line `u` has empty `some`-classes
  and lands entirely in the `⊥` class. The question distributions never produce off-line
  pairs, so nothing downstream sees the difference. Confirm.
- **OPEN-6 (constants and error shapes)**: `O(δ)`/`≈_δ` are encoded as an existentially
  quantified constant `C ≥ 1` at the head of each theorem (4.1 (e)8,
  rem:asymptotic-distance), and "there exists δ(ε) = poly(ε)" as `IsPolyErr` — the
  predicate proposed in the ch15 brief, adopted here and moved into
  `Games/Consistency.lean` so it is defined once, in wave A. Additionally each of nodes
  18 and 20 is stated **twice**: once with the concrete `Real.sqrt ε` the blueprint says
  the proof yields (`deltaAnticom`/`deltaLine`, which ch15 consumes) and once in the
  source's existential `poly(ε)` form. Confirm, or drop one of the two forms.
- **OPEN-7 (`msValueAt` in place of an MS strategy)**: node 10 item 6 speaks of "the
  value of the strategy … in `𝔊^MS`". Building a `Strategy msGame` from the Pauli-test
  measurements would require inventing an MS answer for wrong-form Pauli answers, and
  every such choice either wins or loses spuriously; the skeleton instead defines the
  scalar `msValueAt S ω` by the `def:tensor-product-value` formula over the
  `Option`-completed families (no junk answer, no spurious mass). Confirm this encoding
  rather than a completed `msGameOpt`.
- **OPEN-8 (`fact:omega-anticomm-prob` needs `d`)**: the corrected statement's last two
  bounds carry `1 ≤ m`, `1 ≤ d`, but `d` occurs in the chapter only through the ambient
  admissible tuple. The skeleton keys `anticommProb` to `(q, m)` and passes `d` as an
  explicit argument to the two conditional bounds. Confirm, or key the whole file to
  `AdmissibleParams` (which would cost ch15 the dimension-generic reuse of nothing —
  the node is not on ch15's path).
