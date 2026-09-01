# Implementation brief — stage 4.2, chapter ch16: extracting the Pauli observables

Deliverable: Lean skeleton (all proofs `sorry`, definitions real) for
`blueprint/src/chapter/ch16_qpbt_extraction.tex` (labels `chap:qpbt-extraction` /
`sec:separating`). Paper mirror:
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex`, lines 1415–1877
(per-node ranges in the table of (c); docstrings must cite them).
Baseline: `issues/briefs/0006-minimal-skeleton-brief.md` (stage 4.1) — its naming table is
FROZEN and reused verbatim. Sibling: `issues/briefs/42-ch15-brief.md` (ch16 is ch15's only
consumer). Conventions: `AGENTS.md`; every statement-like docstring cites the blueprint
`\label` and the qpbt-paper file/lines.

Scope check: **no ch16 node is in the 4.1 closure** (verified against the 4.1 39-node
table, which contains no `chap:qpbt-extraction` label). The chapter's detached proof of
`thm:pauli` is **out of scope**: `MIPStarRE.QPBT.pauli_soundness` keeps its 4.1 `sorry`;
ch16 supplies only the chapter's definitions and lemma statements.

## (a) Nodes of ch16 not in the 4.1 closure — dependency order, env kind

Topological for **statement-level** `\uses` restricted to ch16-internal edges (proof-level
`\uses` excluded, per the 4.1 method). 10 formalizable nodes.

| # | label | env | ch16-internal statement deps |
|---|-------|-----|------------------------------|
| 1 | `def:s-w-marginals` | definition | — |
| 2 | `def:tau-dot-product-projector` | definition | — |
| 3 | `def:tilde-m-measurement` | definition | 1, 2 |
| 4 | `def:tilde-w-observables` | definition | 3 |
| 5 | `lem:tildew-product-form` | lemma | 4, 1 |
| 6 | `lem:qld-constructing-the-paulis-helper` | lemma | 1 |
| 7 | `lem:qld-construct-the-paulis` | lemma | 3, 4 (proof: 6) |
| 8 | `def:v-swap-unitary` | definition | — |
| 9 | `lem:v-swap-conjugation` | lemma | 8, 4, 3 |
| 10 | `lem:qld-unitary` | lemma | 8 |

Node 6 is stated after node 7 in the blueprint but has no dependence on it (see the
blueprint's comment at ch16:167–171); the order above is the sound one for Lean.

Four remark nodes are documentation-only (no Lean declaration; quoted in docstrings):
`rem:qld-decoding-identity` (governs the whole chapter — the decoding map is taken at
`H = 𝔽_q`, and the decoder/encoder identity is invoked only for encodings),
`rem:qld-cross-phase`, `rem:qld-unitary-triangle-slip`, `rem:pauli-robustness-form`.

**Two ch11 labels that the 4.1 closure deliberately deferred re-enter here at STATEMENT
level and are therefore owned by ch16** (verified: no other 4.2 chapter uses them in a
statement `\uses`; ch14's only use of `def:binary-representation` is proof-level, at
ch14:181):

| label | why ch16 needs it | env |
|---|---|---|
| `def:decoding-map` | `def:tilde-m-measurement`, `def:v-swap-unitary`, `lem:tildew-product-form` | definition |
| `def:dual-self-dual-normal-basis` + `def:binary-representation` | `def:tilde-w-observables` (the basis `{e_j}` in `eq:def-tildewj`) | definitions |

External statement-level labels consumed (by blueprint label; binding at reconciliation):

- ch15: `lem:qld-4-7` — the sole inbound edge from the sibling brief.
- ch14: `lem:projective-strategy-setup`, `def:expanded-state`, `def:expanded-point-measurement`,
  `def:symmetric-equivalents`, `def:approx-question-indexed-operators` (see OPEN-4).
- ch12: `def:consistency`, `def:povm-distance` (4.1: `opFamilyDistSq`), `def:bracket` (REUSE,
  `\leanok` as `Quantum.Measurement.postprocess`).
- Already in 4.1 (REUSE frozen names): `def:generalized-pauli` (`PauliKind`, `pauliProj`,
  `tauShift`, `tauPhase`), `lem:pauli-observable-expansion`, `def:subfield-trace`
  (`binTrace`), `def:subfields-kappa` (`kappa`), `def:admissible-size`
  (`IsAdmissibleSize`), `def:admissible` (`AdmissibleParams`), `def:EPR` (`eprState`),
  `def:indicator-vector` (`indicatorVec`), `def:low-degree-encoding`
  (`lowDegreeEncoding`, `lowDegreeEnc`), `def:polyfunc`, `def:polynomials-degree`,
  `thm:pauli` (`deltaQld`, `pauli_soundness`), plus `Cube`, `ScalarQ`, `PauliRegister`,
  `heteroKron`, `reindexState`, `Quantum.Measurement`, `IsProj`.

## (b) Proposed files extending the 4.1 tree

Namespace `MIPStarRE.QPBT` throughout (flat, as in 4.1). Estimates in parentheses; all far
below the 1000-line cap. Definitions are separated from statements per the LDT
Defs/Theorems convention.

```
MIPStarRE/QPBT/Algebra/SelfDualBasis.lean   -- def:dual-self-dual-normal-basis,
                                            --   def:binary-representation             (~150)
MIPStarRE/QPBT/Algebra/Decoding.lean        -- def:decoding-map + encoding identities  (~140)
MIPStarRE/QPBT/Extraction/Defs.lean         -- nodes 1,2,3,4,8 + register helpers      (~320)
MIPStarRE/QPBT/Extraction/Observables.lean  -- nodes 5,9                               (~170)
MIPStarRE/QPBT/Extraction/Consistency.lean  -- nodes 6,7                               (~190)
MIPStarRE/QPBT/Extraction/Unitary.lean      -- node 10                                 (~190)
```

Internal import DAG: `Algebra/FieldBasis ← Algebra/SelfDualBasis`;
`Algebra/LowDegreeCode ← Algebra/Decoding`;
`{Algebra/SelfDualBasis, Algebra/Decoding, Algebra/Pauli, Games/Distance,
Games/Consistency, ch14 interface, ch15 Combining/Apply} ← Extraction/Defs`;
`Extraction/Defs ← {Observables, Consistency}`;
`{Observables, Consistency} ← Extraction/Unitary`. Add re-exports to `MIPStarRE/QPBT.lean`.
External imports as in 4.1 (b), plus `Mathlib.FieldTheory.Finite.GaloisField` and
`Mathlib.LinearAlgebra.Dual` for the basis file.

Skeleton pattern: the **witness-structure convention** proposed in ch15's brief (OPEN-2
there) is adopted here for node 10 (`ExtractionWitness` + `exists_extractionWitness`);
nodes 1–9 are stated against a `w : GlobalPairWitness S δS` taken as a hypothesis, never
re-skolemized. Error quantities are explicit reals, per 4.1 (e)8: the blueprint's hidden
`≈_δ`/`≃_δ` constants are absorbed into the existentially quantified constants.

## (c) Node → declaration mapping

Legend as in 4.1: R = reuse, N = new; signatures are sketches, the implementer owns the
final form. Paper lines are in `14_analysis_of_the_pauli_basis_test.tex`.

Ambient context for the whole (c) table:
`P : AdmissibleParams`, `[FieldModel P.q]`, `K := ScalarQ P`, `Reg := PauliRegister P`
(`= Cube P.m → K`, the `M = 2^m` qudits — `M` never materializes as `Fin (2^m)`, 4.1 (e)6),
`S : ExpandedSetting P ε` (ch14 bundle, RECONCILE-1) with local index `ι := S.ι`,
`Pair := ι × Reg` (a register pair `AA'`/`BB'`/`BA''`/`AB''`),
`Block := Pair × Reg` (`AA'A''`, one player after the pull-apart),
`Exp := Block × Block` (all six registers, `S.psiHat : EuclideanSpace ℂ Exp`),
`w : GlobalPairWitness S δS` (ch15) with `w.Smeas : Quantum.Measurement (PolyPair P) Pair`,
`Poly P` the `ideg_{d,m}(𝔽_q)` representative type with `PolyPair P = Poly P × Poly P`,
`e : SelfDualNormalBasis K P.tDeg`.

| label | Lean name | file | R/N | signature sketch |
|---|---|---|---|---|
| def:dual-self-dual-normal-basis | `IsDualBasis`, `IsSelfDualBasis`, `IsNormalBasis`, `SelfDualNormalBasis`, `exists_selfDualNormalBasis` | Algebra/SelfDualBasis | N | `def IsDualBasis (b b' : Basis (Fin k) F L) : Prop := ∀ i j, Algebra.trace F L (b i * b' j) = if i = j then 1 else 0`; `def IsSelfDualBasis (b) : Prop := IsDualBasis b b`; `def IsNormalBasis (b : Basis (Fin k) F L) : Prop := ∃ α : L, ∀ j : Fin k, b j = α ^ (Fintype.card F ^ (j : ℕ))`; `structure SelfDualNormalBasis (L) [Field L] [Algebra (ZMod 2) L] (k : ℕ) where toBasis : Basis (Fin k) (ZMod 2) L; self_dual : IsSelfDualBasis toBasis; normal : IsNormalBasis toBasis`; `theorem exists_selfDualNormalBasis (k : ℕ) (hk : Odd k) (L) [Field L] [Algebra (ZMod 2) L] (hcard : Fintype.card L = 2 ^ k) : Nonempty (SelfDualNormalBasis L k)` (`sorry`; paper 08:…, ch11:234–248) |
| def:binary-representation | `SelfDualNormalBasis.binaryRepr`, `binaryRepr_mul`, `binTrace_eq_dotProduct_binaryRepr` | Algebra/SelfDualBasis | R+N | `noncomputable def binaryRepr (e : SelfDualNormalBasis L k) : L ≃ₗ[ZMod 2] (Fin k → ZMod 2) := e.toBasis.equivFun` — REUSE 4.1's `kappa`; `binaryRepr_mul` states eq:eq-mult (`sorry`); `binTrace_eq_dotProduct_binaryRepr : binTrace a = ∑ i, (e.binaryRepr a) i` from `lem:downsize_field`/`lem:one` (`sorry`; ch11:298–312) |
| def:decoding-map | `decodeOn`, `decodeFq`, `decodeOn_univ`, `decodeFq_add`, `decodeFq_smul`, `decodeFq_lowDegreeEncoding`, `IsEncoding`, `decodeFq_dotProduct_indicatorVec` | Algebra/Decoding | N | `def decodeOn (H : Finset K) (g : Poly P) : Reg := fun y => if evalPoly g (cubePoint y) ∈ H then evalPoly g (cubePoint y) else 0`; `abbrev decodeFq : Poly P → Reg := decodeOn Finset.univ` (the `H = 𝔽_q` reading fixed by rem:qld-decoding-identity); `def IsEncoding (g : Poly P) : Prop := lowDegreeEncoding (decodeFq g) = g`; `theorem decodeFq_lowDegreeEncoding (h : Reg) : decodeFq (lowDegreeEncoding h) = h` and `theorem decodeFq_dotProduct_indicatorVec (hg : IsEncoding g) (x : Fin P.m → K) : decodeFq g ⬝ᵥ indicatorVec x = evalPoly g x` (both `sorry`) — the encoding hypothesis is mandatory, see rem:qld-decoding-identity and OPEN-1 |
| def:s-w-marginals | `PauliKind.selectPoly`, `GlobalPairWitness.marginalPoly`, `marginalPoly_isProjective` | Extraction/Defs | R+N | `def PauliKind.selectPoly (W : PauliKind) (gg : PolyPair P) : Poly P := match W with \| .X => gg.1 \| .Z => gg.2`; `noncomputable def GlobalPairWitness.marginalPoly (w) (W : PauliKind) : Quantum.Measurement (Poly P) Pair := w.Smeas.postprocess (PauliKind.selectPoly W)` — REUSE `Measurement.postprocess` (def:bracket, `\leanok`); `theorem marginalPoly_isProjective (w) (W) : (w.marginalPoly W).IsProjective` (`sorry`) — paper 1418–1424 |
| def:tau-dot-product-projector | `bracketOp`, `tauDotProj`, `tauDotProj_isProj`, `sum_tauDotProj_eq_one` | Extraction/Defs | N | `noncomputable def tauDotProj (W : PauliKind) (ut : Reg) (a : K) : Op Reg := bracketOp (pauliProj W) (· ⬝ᵥ ut) a` (eq:def-tauwu); `bracketOp {α β} [Fintype α] [DecidableEq β] (N : α → Op ι) (f : α → β) (b : β) : Op ι := ∑ a ∈ Finset.univ.filter (f · = b), N a` is the unbundled form of def:bracket (Lean-only, OPEN-3); both companions `sorry` — paper 1426–1429 |
| def:tilde-m-measurement | `tildeM`, `tildeM_isProj`, `sum_tildeM_eq_one` | Extraction/Defs | N | `noncomputable def tildeM (w) (W : PauliKind) (ut : Reg) (a : K) : Op Block := ∑ g : Poly P, heteroKron ((w.marginalPoly W).effect g) (tauDotProj W ut (decodeFq g ⬝ᵥ ut - a))` (eq:tilde_M; the `AA'` factor first, the `A''` factor second — this fixes `Block = Pair × Reg` for the whole chapter); companions `sorry` — paper 1429–1435 |
| def:tilde-w-observables | `signOf`, `tildeObs` | Extraction/Defs | N | `noncomputable def tildeObs (e : SelfDualNormalBasis K P.tDeg) (w) (W : PauliKind) (ut : Reg) (j : Fin P.tDeg) : Op Block := ∑ a : K, signOf (binTrace (e.toBasis j * a)) • tildeM w W ut a` (eq:def-tildewj); `signOf (b : ZMod 2) : ℂ := if b = 0 then 1 else -1` (Lean-only unless 4.1's `tauPhase` already exports a sign helper — RECONCILE-3); real definition — paper 1437–1441 |
| lem:tildew-product-form | `tildeObs_eq_heteroKron`, `tildeObs_isHermitian`, `tildeObs_mul_self`, `tildeObs_twisted_commutation` | Extraction/Observables | N | `theorem tildeObs_eq_heteroKron … : tildeObs e w W ut j = heteroKron (∑ gg : PolyPair P, signOf (binTrace (e.toBasis j * (decodeFq (W.selectPoly gg) ⬝ᵥ ut))) • w.Smeas.effect gg) (tauObservable W (e.toBasis j • ut))` (eq:tildewj-product-form); `tildeObs_mul_self : tildeObs … * tildeObs … = 1`; `tildeObs_twisted_commutation : tildeObs e w .X ut j * tildeObs e w .Z vt j' = signOf (binTrace (e.toBasis j * e.toBasis j' * (ut ⬝ᵥ vt))) • (tildeObs e w .Z vt j' * tildeObs e w .X ut j)` (eq:tildew-twisted-commutation) — all four `sorry`; paper 1442–1456. `e.toBasis j • ut : Reg` is the scalar multiple `e_j ũ` |
| lem:qld-constructing-the-paulis-helper | `sum_marginalPoly_pointMeas_approx_id`, `marginalPoly_sub_pointMeas_approx_zero` | Extraction/Consistency | N | `theorem sum_marginalPoly_pointMeas_approx_id (w) (W) (pl : SymmPlacement) : opDistSq (uniformDistribution (Fin P.m → K)) (fun u => ∑ g : Poly P, S.place pl.fst ((w.marginalPoly W).effect g) * S.place pl.snd ((S.pointMeas W u).effect (evalPoly g u))) (fun _ => (1 : Op Exp)) S.psiHat ≤ δS` (eq:qld-sg-cons); `theorem marginalPoly_sub_pointMeas_approx_zero (w) (W) (pl) : opFamilyDistSq (uniformDistribution (Fin P.m → K)) (fun u g => S.place pl.fst ((w.marginalPoly W).effect g * (1 - (S.pointMeas W u).effect (evalPoly g u)))) (fun _ _ => 0) S.psiHat ≤ δS` (eq:qld-sg-cons2, answer summation over `g : Poly P`) — both `sorry`, both quantified over `pl : SymmPlacement` for "all symmetric equivalents"; paper 1609–1664 |
| lem:qld-construct-the-paulis | `tildeM_consistent_pointMeas`, `tildeM_consistent_pointMeas'`, `tildeObs_selfConsistent` | Extraction/Consistency | N | item 1, the two displays: `theorem tildeM_consistent_pointMeas (w) (W) : consistencyDefect (uniformDistribution (Fin P.m → K)) (fun u a => placeSide .alice (onA ((S.pointMeasRaw W u).effect a))) (fun u a => placeSide .bob (tildeM w W (indicatorVec u) a)) S.psiHat ≤ δS`, and `…'` with the sides exchanged; item 2: `theorem tildeObs_selfConsistent (e) (w) (W) (j) : opDistSq (uniformDistribution Reg) (fun ut => placeSide .alice (tildeObs e w W ut j)) (fun ut => placeSide .bob (tildeObs e w W ut j)) S.psiHat ≤ δS` — all `sorry`; paper 1458–1608. `onA : Op ι → Op Block` lifts a bare register-`A` operator (`heteroKron (heteroKron · 1) 1`); the vacuous `j` of the source's item 1 is dropped, per the blueprint comment at ch16:108–109 |
| def:v-swap-unitary | `swapUnitary` | Extraction/Defs | N | `noncomputable def swapUnitary (w) : Op Block := ∑ gg : PolyPair P, heteroKron (w.Smeas.effect gg) (tauObservable .X (decodeFq gg.2) * tauObservable .Z (decodeFq gg.1))` — note the crossed arguments (`X` gets `Dec(g_Z)`, `Z` gets `Dec(g_X)`); real definition; paper 1687–1700 |
| lem:v-swap-conjugation | `swapUnitary_mul_conjTranspose`, `conjTranspose_mul_swapUnitary`, `swapUnitary_conj_tildeObs`, `swapUnitary_conj_tildeM` | Extraction/Observables | N | `theorem swapUnitary_conj_tildeObs (e) (w) (W) (ut) (j) : conjBy (swapUnitary w) (tildeObs e w W ut j) = heteroKron (1 : Op Pair) (tauObservable W (e.toBasis j • ut))` (eq:v-swap-obs-conjugation); `theorem swapUnitary_conj_tildeM (w) (W) (u : Fin P.m → K) (a : K) : conjBy (swapUnitary w) (tildeM w W (indicatorVec u) a) = heteroKron (1 : Op Pair) (bracketOp (pauliProj W) (fun h => lowDegreeEnc h u) a)` (eq:qld-unitary-6, whose right-hand side is exactly `τ^W_{[g_h(u)=a]}`) — all `sorry`; `conjBy (V N : Op ι) : Op ι := V * N * Vᴴ` (Lean-only); the two unitarity statements replace the informal "are unitaries"; paper 1687–1713 |
| lem:qld-unitary | `deltaExtract`, `ExtractionWitness`, `exists_extractionWitness`, `deltaExtract_le_deltaQld` | Extraction/Unitary | N | see (d) below; paper 1666–1685, 1715–1861 |

Lean-only helpers (each docstring-marked per AGENTS.md "Record formalization-only auxiliary
lemmas explicitly"): `bracketOp`, `signOf`, `conjBy`, `onA`, `cubePoint : Cube P.m →
(Fin P.m → K)` (Bool ↦ 0/1; reuse 4.1's if `Algebra/LowDegreeCode` already ships it),
`evalPoly : Poly P → (Fin P.m → K) → K` (the `polyFunc` representative evaluation),
`AdmissibleParams.tDeg (P) : ℕ := P.hq.choose` with `two_pow_tDeg : P.q = 2 ^ P.tDeg` and
`odd_tDeg : Odd P.tDeg` (both `sorry`; `IsAdmissibleSize q := ∃ k, Odd k ∧ q = 2 ^ k` is
frozen in 4.1, so this is safe to build now), `PlayerSide` + `placeSide : PlayerSide →
Op Block → Op Exp` + `placeRegPP : PlayerSide → Op Reg → Op Exp` (the `A''`/`B''` slot),
`opDistSq` := `opFamilyDistSq` at `α := Unit` (the answer-free closeness of
`def:approx-question-indexed-operators`, see OPEN-4), `idealExpState`, `swapBoth`.

## (d) STATEMENTS (`sorry`) vs DEFINITIONS (real)

**Real definitions, no `sorry`** — `IsDualBasis`, `IsSelfDualBasis`, `IsNormalBasis`,
`SelfDualNormalBasis`, `binaryRepr`, `decodeOn`, `decodeFq`, `IsEncoding`,
`PauliKind.selectPoly`, `marginalPoly`, `tauDotProj`, `tildeM`, `tildeObs`, `swapUnitary`,
`deltaExtract`, `ExtractionWitness`, and every Lean-only helper above. In particular
`marginalPoly` is a `postprocess` of an existing bundled measurement, so it needs no
proof fields; `tauDotProj`, `tildeM`, `swapUnitary`, `tildeObs` are unbundled `Op`-valued
sums, and their projectivity/completeness/unitarity are companion `sorry` lemmas rather
than structure fields (4.1 (e)7, and it keeps `sorry` out of definition bodies).

**`sorry` statements** — the 10 nodes' propositions (20 theorems in total: 1 for node 1,
2 for node 2, 2 for node 3, 0 for node 4, 4 for node 5, 2 for node 6, 3 for node 7, 0 for
node 8, 4 for node 9, 2 for node 10), plus `exists_selfDualNormalBasis`, the four decoding
identities, `binaryRepr_mul`, `binTrace_eq_dotProduct_binaryRepr`, `two_pow_tDeg`,
`odd_tDeg`. All marker-free tracked skeleton sorries (no `**Unfaithful:**` markers).

**Node 10 in full**, since it is the chapter's output:

```lean
/-- `δ_qld = O(δ_S^{1/4} + md/q)` of lem:qld-unitary, as an explicit functional. -/
noncomputable def deltaExtract (C deltaS : ℝ) (m d q : ℕ) : ℝ :=
  C * (deltaS ^ (1 / 4 : ℝ) + ((m * d : ℕ) : ℝ) / (q : ℝ))

/-- lem:qld-unitary (qpbt-paper 14_…tex:1666-1685): the swap unitaries of
def:v-swap-unitary extract the EPR state and the Pauli observables. -/
structure ExtractionWitness (S : ExpandedSetting P ε) (w : GlobalPairWitness S deltaS)
    (delta : ℝ) where
  aux : EuclideanSpace ℂ (Pair × Pair)                 -- registers AA'BB'
  aux_norm : ‖aux‖ = 1
  state_close : ‖swapBoth w S.psiHat - idealExpState aux‖ ^ 2 ≤ delta
  pauli_close : ∀ (side : PlayerSide) (W : PauliKind),
    opFamilyDistSq (Distribution.dirac ())
      (fun _ (h : Reg) =>
        conjBy (placeSide side (swapUnitary w))
          (placeSide side (onA ((S.pauliMeasRaw W).effect h))))
      (fun _ (h : Reg) => placeRegPP side (pauliProj W h))
      (idealExpState aux) ≤ delta

theorem exists_extractionWitness :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (P : AdmissibleParams) [FieldModel P.q] (ε deltaS : ℝ)
      (S : ExpandedSetting P ε) (w : GlobalPairWitness S deltaS),
      Nonempty (ExtractionWitness S w (deltaExtract C deltaS P.m P.d P.q)) := by
  sorry

/-- rem:pauli-robustness-form: `deltaExtract` at `δ_S = deltaQld` is again of the
`a(md)^a(ε^b + q^{-b} + 2^{-bmd})` shape, after replacing `b` by `b/4` and enlarging `a`. -/
theorem deltaExtract_le_deltaQld : … := by sorry
```

The blueprint's closing sentence "the unitaries may be taken to be `V_A` and `V_B` of
Definition~\ref{def:v-swap-unitary}" is honoured by *not* existentially quantifying over
unitaries: `ExtractionWitness` names `swapUnitary w` directly, which is the stronger and
simpler statement. `idealExpState aux` is `reindexState` applied to
`aux ⊗ eprState Reg`, placing the two EPR halves on `A''`/`B''` (4.1's `reindexState` +
`Equiv.prodProdProdComm` helper family); `swapBoth w` is the action of
`heteroKron (swapUnitary w) (swapUnitary w)` on `EuclideanSpace ℂ Exp`. The answer
summation is over `h : Reg` with **no** average over questions, hence the point-mass
distribution (RECONCILE-4).

Blueprint sync after type-check: `\lean{…}` + `\leanok` on the 10 ch16 statement
environments and on the three ch11 nodes ch16 adopts — statements only, never proofs —
then `leanblueprint web` + `lake exe checkdecls`.

## (e) Cross-chapter dependencies (the parallel-wave interface)

**Consumed by ch16 — stated most carefully, because these are what the wave must agree
on.** ch16 is terminal in the wave: it consumes ch14 and ch15 and is consumed by no one.

1. **From ch15, `lem:qld-4-7` → `GlobalPairWitness` / `exists_globalPairWitness`.** ch16
   binds exactly four things and nothing else: the field `w.Smeas : Quantum.Measurement
   (PolyPair P) (ι × Reg)`; `w.projective`; the outcome type `PolyPair P = Poly P × Poly P`
   over the `polyFunc` representative type `Poly P` of `ideg_{d,m}(𝔽_q)` **with `Poly P`
   exposed as a name in its own right** (ch15's brief names only the pair type — without a
   name for the single-polynomial type, `def:s-w-marginals` cannot be stated: RECONCILE-2);
   and the error `deltaQld a b ε m d q` with `∃ a b` outermost. ch16 does **not** consume
   `w.point_cons`: nodes 6 and 7 restate the point consistency in the forms
   eq:qld-sg-cons / eq:qld-sg-cons2 / item 1, which are separate `sorry` statements here.
   ch16 assumes, with ch15, that `lem:qld-4-7` carries **no divisibility hypothesis**
   (ch15 OPEN-5); if a `(2m+2) ∣ q` guard were added to `exists_globalPairWitness`, every
   ch16 statement that quantifies over `w` would inherit an unsatisfiable hypothesis for
   `m ≥ 2` and the chapter would become vacuous. This is the single hardest constraint
   ch16 places on ch15.
2. **From ch14, the `ExpandedSetting P ε` bundle** (ch15's RECONCILE-1, extended). ch16
   needs, beyond ch15's list: (i) the six-register index `Exp` presented so that it
   reassociates to `Block × Block` with `Block = (ι × Reg) × Reg` — the `AA'A''|BB'B''`
   bipartition, which is a **third** scheme, distinct from the two of
   `def:symmetric-equivalents`, and is the ambient split for nodes 7 and 10;
   (ii) `S.pointMeasRaw (W) (u) : Quantum.Measurement K ι` — the *unexpanded*
   `M^{(Point,W),u}_a` on register `A` alone, needed by item 1 of node 7 (ch15 needs only
   the expanded `S.pointMeas`); (iii) `S.pauliMeasRaw (W) : Quantum.Measurement Reg ι` —
   the total Pauli measurement `M^{(Pauli,W)}_h`, needed by node 10 and by the eventual
   `thm:pauli` proof; (iv) `S.place : SymmPlacement → Op Pair → Op Exp` for node 6.
   If ch14 does not export (i)–(iii), ch16 adds `placeSide`/`onA` and decodes the two raw
   measurements from `S.strat.A` at the `(Point,W,u)` and `(Pauli,W)` questions of 4.1's
   frozen `pauliBasisTest`; that fallback is mechanical but duplicates ch14 work.
3. **From ch12/ch15, `consistencyDefect`** (`def:consistency`) — ch16 uses it for item 1
   of node 7. ch15's brief offers it from `Games/Consistency.lean` (its OPEN-3); ch16
   consumes it under that signature wherever it ends up.
4. **Owned by ch16, offered to the wave**: `decodeFq` and its identities
   (`def:decoding-map`) — ch15's *proof* of `lem:qld-4-7`'s symmetry step will need the
   linearity and `Dec(g_h) = h`, so ch15 should import `Algebra/Decoding` rather than
   restate them; `SelfDualNormalBasis` + `binaryRepr` (`def:dual-self-dual-normal-basis`,
   `def:binary-representation`) — ch14's proof at ch14:181 will want `binaryRepr` and
   `binTrace_eq_dotProduct_binaryRepr`; `bracketOp` and `opDistSq` as the unbundled
   bracket and the answer-free closeness (OPEN-3, OPEN-4).

## RECONCILE: (assumptions pending the 4.1 merge and the sibling briefs)

- RECONCILE-1: the ch14 `ExpandedSetting` bundle, in the shape ch15's brief assumes, plus
  items (i)–(iv) of (e)2. All ch16 uses go through the bundle; renames are mechanical.
- RECONCILE-2: `Poly P` (single-polynomial representative type) exists alongside ch15's
  `PolyPair P`, with `evalPoly` and an additive structure carrying `decodeFq_add` /
  `decodeFq_smul`. Copy whatever `MIPStarRE.LDT.Preliminaries.polyFunc` does after merge
  (ch15's RECONCILE-4).
- RECONCILE-3: 4.1 names used before merge — `AdmissibleParams` (+ `hq`, `toLdParams`),
  `ScalarQ`, `PauliRegister`, `Cube`, `IsAdmissibleSize`, `PauliKind`, `pauliProj`,
  `binTrace`, `kappa`, `eprState`, `heteroKron`, `reindexState`, `opFamilyDistSq`,
  `indicatorVec`, `lowDegreeEncoding`, `lowDegreeEnc`, `deltaQld`,
  `Quantum.Measurement.postprocess`, `Measurement.IsProjective`, `IsProj`.
  Two of these are **assumed rather than confirmed**: (a) `tauObservable (W : PauliKind)
  (a : Reg) : Op Reg`, the `M`-qudit generalized Pauli observable `τ^W(a)` — 4.1's
  mapping row for `def:generalized-pauli` names only `tauShift`/`tauPhase`/`pauliVec`/
  `pauliProj`, but its `lem:pauli-observable-expansion` row names
  `tauObservable_eq_sum_pauliProj`, which presupposes `tauObservable`. ch16 uses it in
  nodes 5, 8, 9 and cannot be stated without it; if 4.1 ships only the single-qudit
  operators, `Extraction/Defs.lean` adds `tauObservable` as the entrywise product over
  `Cube P.m`. (b) a sign helper for `(-1)^{tr(·)}`; ch16 supplies `signOf` unless 4.1's
  `tauPhase` already exports one.
- RECONCILE-4: the LDT `Distribution` API's point-mass constructor (`Distribution.dirac`
  here) and `uniformDistribution` on `Reg` and on `Fin P.m → K`; verify the exact names in
  `LDT/Basic/DistributionUniform.lean` before use (4.1 (e)2).

## OPEN: items for the orchestrator

- **OPEN-1 (`\uses` omissions in ch16).** `def:tilde-w-observables` and
  `lem:tildew-product-form` need `def:subfields-kappa` (the basis `{e_j}` is used through
  `κ`, and `lem:downsize_field`/`lem:one` supply `tr(e_j)`), and node 7's item 2 needs
  `def:approx-question-indexed-operators` rather than `def:povm-distance`; neither appears
  in the corresponding statement `\uses`. `lem:qld-constructing-the-paulis-helper` also
  omits `def:expanded-point-measurement` from its statement `\uses` although
  `M̂^{(Point,W),u}` occurs in both displays. Consider patching ch16's `\uses` lines.
- **OPEN-2 (ownership of the three adopted ch11 nodes).** ch16 claims
  `def:decoding-map`, `def:dual-self-dual-normal-basis`, `def:binary-representation`,
  which 4.1 explicitly deferred (its OPEN-6). They are ch11 labels; if the orchestrator
  prefers a ch11-leftovers brief to own them, ch16 consumes them by label and the two
  `Algebra/` files above disappear. The signatures in (c) are the interface either way.
- **OPEN-3 (`bracketOp`, the unbundled bracket).** `def:bracket` is `\leanok` as
  `Measurement.postprocess`, which requires a bundled `Measurement`; ch16's Pauli
  projectors arrive from 4.1 as a bare family `pauliProj W : Reg → Op Reg`. Proposed
  resolution: a Lean-only `bracketOp` on families, with a `sorry` bridge lemma
  `postprocess_effect_eq_bracketOp`. Confirm, or require bundling `pauliProj` into a
  `Quantum.Measurement Reg Reg` (which puts `pos`/`sum_eq_one` `sorry`s inside a
  definition body — the reason this brief avoids it).
- **OPEN-4 (`opDistSq`).** Item 2 of node 7 and the eq:qld-sg-cons display compare single
  operators per question, i.e. `def:approx-question-indexed-operators` (ch14), not the
  answer-indexed `def:povm-distance`. ch16 proposes `abbrev opDistSq := opFamilyDistSq` at
  `α := Unit`, which is the same real number and needs no new ch14 declaration. Confirm,
  or have ch14 own `opDistSq` under its own label.
- **OPEN-5 (`SelfDualNormalBasis` as parameter, not instance).** ch16 threads
  `e : SelfDualNormalBasis K P.tDeg` as an explicit argument through nodes 4, 5, 7, 9, 10,
  rather than pinning it into `FieldModel`/`AdmissibleParams`. This keeps the frozen 4.1
  `FieldModel` untouched and makes the statements quantify over all self-dual normal bases
  — mildly stronger than the source, which fixes one once and for all
  (`def:binary-representation`). This is 4.1's OPEN-6 arriving in a chapter that cannot
  defer it. If the orchestrator instead pins the basis into the parameter bundle, drop the
  `e` argument everywhere; the change is mechanical but touches every ch16 statement, so
  decide before implementation starts.
- **OPEN-6 (rem:qld-decoding-identity as a `sorry`'d hypothesis).**
  `decodeFq_dotProduct_indicatorVec` is stated **only for encodings**, per the blueprint's
  local correction of the source. Every future proof that wants it for a general outcome
  `g` must instead route through the non-encoding mass bound eq:qld-nonencoding-mass,
  which is proof-level and not skeletonized here. Confirm that no 4.2 statement is allowed
  to assume the unrestricted identity.
- **OPEN-7 (`rem:qld-cross-phase`).** The blueprint records that the source's asserted
  commutation for `j ≠ j'` is false and that the relations are unused in the remainder.
  ch16 nonetheless states `tildeObs_twisted_commutation` in the corrected form, since it
  is part of `lem:tildew-product-form`. Confirm keeping it, or demote it to a docstring-
  only remark and drop the declaration.
- **OPEN-8 (the `thm:pauli` proof, and the four outstanding obligations).** The chapter's
  detached proof is out of 4.2 scope by construction, but its reliance disclosure
  (ch16:292) names four unproved obligations —
  `gap:qpbt_ld-dimension-divisibility` (three of them) and
  `gap:qpbt_combined-lines-error-term`. When `pauli_soundness`'s `sorry` is eventually
  attacked, `Extraction/Unitary.lean` is where the proof begins; the transfer step from
  `lem:qld-unitary`'s unitary conjugation to the isometry conjugation (the range-projection
  argument added by the blueprint at ch16:296–321) has no ch16 declaration and should be
  budgeted as a stage-5 lemma. Flagging so it is not lost between briefs.
