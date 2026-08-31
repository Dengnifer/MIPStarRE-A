# Implementation brief — stage 4.2, ch15: combining the bases and applying the classical test

Deliverable: a Lean skeleton for `blueprint/src/chapter/ch15_qpbt_combining.tex`
(`chap:qpbt-combining` / `sec:combining` / `sec:apply-ldt`) — every proposition-valued
node `sorry`, every definitional node real. Paper mirror:
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:680-1414`; per-node
line anchors are given in (c) and belong in the docstrings verbatim.
Baseline: `issues/briefs/0006-minimal-skeleton-brief.md` (stage 4.1). Its naming table
is FROZEN and reused verbatim; nothing below renames a 4.1 declaration. Anything this
brief must assume about 4.1 or about a sibling 4.2 chapter is under `RECONCILE:`.
Conventions: `AGENTS.md` (Mathlib naming, module docstrings, 100-col, explicit types);
every statement-like docstring cites the blueprint `\label` **and** the qpbt-paper
file/lines.

Scope check: **no ch15 node is in the 4.1 closure** (checked against the 39-node table).
ch15 has 18 labelled environments: 13 carry Lean declarations, 5 are remarks that carry
none. Outside ch15 its statements reach ch14 (the wave interface), ch13
(`def:line-point-dist` — ownership unresolved, see OPEN-1), ch12 (`def:consistency`,
`def:bracket`), and the frozen 4.1 names.

## (a) ch15 nodes not in the 4.1 closure — dependency order, env kind

Topological for statement-level `\uses` restricted to ch15-internal edges (proof-level
`\uses` excluded, as in 4.1). Formalize top to bottom.

| # | label | env | ch15-internal statement deps |
|---|-------|-----|------------------------------|
| 1 | `thm:linearity` | theorem (external import) | — |
| 2 | `lem:qld-4-10` | lemma | — |
| 3 | `lem:qld-xz-lines` | lemma | `lem:qld-4-10` |
| 4 | `lem:qld-4-12` | lemma | `lem:qld-4-10` |
| 5 | `def:combine-map` | definition | — |
| 6 | `def:ith-restricted-line` | definition | — |
| 7 | `lem:restricted-line-mixture-bounds` | lemma | 6, 3, 2 |
| 8 | `lem:qld-sublines` | lemma | 6 |
| 9 | `lem:claim-17-1` | lemma | 8, 3, 2 |
| 10 | `lem:claim-17-2` | lemma | 8, 3 |
| 11 | `lem:claim-17-3` | lemma | 8, 3, 2 |
| 12 | `lem:qld-4-13` | lemma | 4 (proof: 9–11, 5, 8) |
| 13 | `lem:qld-4-7` | lemma | — (proof: 12, 4, `lem:ld-soundness`, `thm:naimark`) |

Documentation-only (no declaration; each cited in the docstring of the node it
qualifies): `rem:linearity-import` (→ node 1), `rem:qld-sublines-property-three` (→ 8),
`rem:qld-4-13-source-defects` (→ 12), `rem:qld-4-7-divisibility` (→ 8, 12, 13),
`rem:qld-4-7-constants` (→ 13).

Statement-level labels consumed from outside ch15 (bound at reconciliation):

- **ch14 interface**: `lem:projective-strategy-setup`, `def:expanded-state`,
  `def:symmetric-equivalents`, `def:expanded-point-measurement`,
  `def:expanded-line-measurement`, `def:ideg-deg-polynomials`, `lem:qld-comm-line-cons`
  (its error function `δ_Line` occurs in the *statement* of node 10).
- **ch13**: `def:line-point-dist`, needed at dimension `m` (nodes 3, 6, 7, 8) *and* at
  dimension `2m+2` (nodes 8, 12).
- **ch12**: `def:consistency` (`≃_δ`), `def:bracket` (REUSE, already `\leanok`).
- **4.1 frozen (REUSE verbatim)**: `def:povm-distance` → `opFamilyDistSq`,
  `def:state-distance` → `stateDistSq`, `def:povm-conventions` →
  `Quantum.Measurement` + `Measurement.IsProjective`, `def:line` → `linePoints`,
  `def:line-representative` → `lineRepMap`, `prop:line-equiv`, `def:polyfunc` →
  `LDT.Preliminaries.polyFunc`, `def:ld-question-distribution` → `chiIndex`,
  `ldPointCL`, `ldALineCL`, `ldDLineCL`, `ldQuestionDistribution`, `def:cl-dist` →
  `clDistribution`, `def:admissible` → `AdmissibleParams` (+ `toLdParams`),
  `def:ld-game` → `LdParams`, `LdSpace`, `def:admissible-size` → `IsAdmissibleSize`,
  `def:subfield-trace` → `binTrace`, `thm:pauli` → `deltaQld`, plus `heteroKron`,
  `ScalarQ`, `PauliRegister`, `PauliKind`.
- Proof-level only, **not** built here: `thm:naimark`, `lem:ld-soundness`,
  `lem:ortho`, `lem:avg-closeness`, `lem:cancellation`, `lem:pasting`,
  `fact:add-a-proj`, `fact:add-a-proj2`, `fact:agreement`, `fact:data-processing`,
  `lem:cool-closeness-fact`, `lem:schwartz-zippel-total-degree`.

## (b) Files extending the 4.1 tree

Namespace `MIPStarRE.QPBT` throughout. Real definitions are separated from `sorry`
statements per the LDT `Defs`/`Theorems` convention; the theorem half is split by
chapter section so that no file approaches the 1000-line cap (estimates in parentheses).

```
MIPStarRE/QPBT/Games/ErrorFunctions.lean   -- IsPolyErr, IsPolyErr₂, scalar ≈      (~70)
MIPStarRE/QPBT/Games/DistributionAux.lean  -- mixture / prod / restrict            (~130)
MIPStarRE/QPBT/Games/Consistency.lean      -- def:consistency                      (~80)
MIPStarRE/QPBT/Test/LinePointDist.lean     -- def:line-point-dist (see OPEN-1)     (~150)
MIPStarRE/QPBT/Combining/Defs.lean         -- nodes 5, 6 + Lean-only helpers       (~200)
MIPStarRE/QPBT/Combining/Witnesses.lean    -- the five witness structures          (~240)
MIPStarRE/QPBT/Combining/Linearity.lean    -- node 1                               (~90)
MIPStarRE/QPBT/Combining/Points.lean       -- nodes 2, 4                           (~140)
MIPStarRE/QPBT/Combining/Lines.lean        -- nodes 3, 7, 8                        (~230)
MIPStarRE/QPBT/Combining/Claims.lean       -- nodes 9, 10, 11                      (~170)
MIPStarRE/QPBT/Combining/Apply.lean        -- nodes 12, 13                         (~180)
```

Import DAG: `ErrorFunctions` and `DistributionAux` are leaves;
`Games/Distance ← Games/Consistency`; `{DistributionAux, Test/LowDegreeGame,
Algebra/Lines} ← Test/LinePointDist`; `{Test/LinePointDist, Algebra/LowDegreeCode,
ErrorFunctions} ← Combining/Defs`; `{Combining/Defs, Games/Consistency, ch14 interface}
← Combining/Witnesses`; `Combining/Witnesses ← {Points, Lines, Claims, Apply}`;
`Combining/Linearity` needs only `Quantum/FiniteMatrix` + `Algebra/FieldBasis`, not the
expanded-state interface. Add every file to `MIPStarRE/QPBT.lean`.

**One append to a 4.1 file** (no rename): `deltaQld_mono` in `Test/Soundness.lean` —
`a ≤ a' → b' ≤ b → 0 < b' → deltaQld a b ε m d q ≤ deltaQld a' b' ε m d q` (`sorry`).
ch16 needs exactly this ("enlarged by an adjustment of the universal constants",
ch16 preamble); it belongs beside `deltaQld`, not in ch15's own files.

### Two skeleton patterns (proposed as wave-wide; OPEN-2)

**Witness structures.** Nodes 2, 3, 8, 12, 13 assert *existence* of an object whose
properties later statements quantify over (the claims consume the `T` of node 3, the
`Q̂` of node 2 and the `D` of node 8; ch16 consumes the `Ŝ` of node 13). Each is encoded
as `structure …Witness … (δ : ℝ)` — carrying the object plus its guarantees as fields,
the error explicit — together with `theorem exists_…  : ∃ δ, IsPolyErr δ ∧ ∀ …,
Nonempty (…Witness … (δ ε))` (`sorry`). Downstream statements take a witness as a
hypothesis rather than re-skolemizing, which is what makes the chapter's chain of
lemmas expressible at all. ch14's `lem:qld-comm-cons` / `lem:qld-comm-line-cons` have
the same shape and should export it identically.

**Error functions.** `≈_δ` / `≃_δ` hide universal constants (`rem:asymptotic-distance`);
per 4.1 (e)8 these are absorbed into the existentially quantified error, so witness
fields carry plain `≤ δ` inequalities. `poly(ε)` becomes
`IsPolyErr (f : ℝ → ℝ) : Prop := ∃ a b : ℝ, 0 < a ∧ 0 < b ∧ ∀ ε ∈ Set.Icc (0:ℝ) 1,
f ε ≤ a * ε ^ b`, and `poly(ε, md/q)` becomes the two-argument `IsPolyErr₂`. The
chapter's *scalar* convention "α ≈_δ β means |α − β| ≤ O(δ)" (preamble) is rendered by
hoisting one constant to the front of the whole statement:
`theorem … : ∃ C : ℝ, 0 < C ∧ ∀ (P) [FieldModel P.q] (ε) (S) (witnesses), |α − β| ≤ C * δ`.
Hoisting matters: `C` must not depend on `P`, `ε`, or the strategy.

## (c) Node → declaration mapping

Legend: R = reuse, N = new; signatures are sketches, the implementer owns the final
form. Paper anchors are line ranges in
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex`.
Ambient: `P : AdmissibleParams`, `[FieldModel P.q]`, `K := ScalarQ P`,
`Reg := PauliRegister P` (`= Cube P.m → K`), `Pt := Fin P.m → K`,
`DegPoly c := Fin (c+1) → K` (coefficient lists, per `def:ideg-deg-polynomials` and
4.1 (e)1), `Line L := (Fin L.m → ScalarQ L) × (Fin L.m → ScalarQ L)` (base point,
direction). `S : ExpandedSetting P ε` is the ch14 bundle (RECONCILE-1); its fields used
here are `S.ι` (the common local space of the symmetric strategy), `S.psiHat`,
`S.place : Placement → Op (S.ι × Reg) → Op S.Full` for the four register pairs
`AA' | BA'' | BB' | AB''`, `S.pointMeas (W : PauliKind) (u : Pt) : Measurement K (S.ι × Reg)`,
`S.lineMeas`, and `S.deltaLine : ℝ → ℝ`.

| label (paper lines) | Lean name | file | R/N | signature sketch |
|---|---|---|---|---|
| `def:consistency` (ch12) | `consistencyDefect` | Games/Consistency | N | `noncomputable def consistencyDefect (μ : Distribution X) (A B : X → α → Op ι) (ψ : EuclideanSpace ℂ ι) : ℝ := avgOver μ fun x => ∑ a, ∑ b ∈ {b \| b ≠ a}, (⟪ψ, (A x a * B x b).mulVec ψ⟫).re` — `A`, `B` arrive already placed on the two parties, so the blueprint's `A ⊗ B` is the product of commuting placed operators. **Not** `Quantum.inconsistency`, which is the normalized-trace LDT analogue |
| `def:line-point-dist` (ch13) | `aLinePointDist`, `dLinePointDist`, `linePointDist` | Test/LinePointDist | R+N | `noncomputable def aLinePointDist (L : LdParams) [FieldModel L.q] : Distribution (Line L × (Fin L.m → ScalarQ L)) := (clDistribution (ldALineCL L) (ldPointCL L)).map (fun z => (aLineOf L z.1, z.2.pt))` — direct REUSE of the frozen `clDistribution` and the three CL maps; `dLinePointDist` likewise with `dLineOf L z := (z.pt, z.dir)`; `linePointDist L := Distribution.mixture ![1/2, 1/2] ![aLinePointDist L, dLinePointDist L]`. Keyed to `LdParams`, so dimension `2m+2` is a free instance |
| `thm:linearity` (713–725) | `IsBinaryObservable`, `stateDepDistSq`, `exists_exactly_linear_observables` | Combining/Linearity | N | `def IsBinaryObservable (O : Op ι) : Prop := O.IsHermitian ∧ O * O = 1`; `noncomputable def stateDepDistSq (S T : Op ι) (ρ : Op ι) : ℝ := (Matrix.trace ((S - T)ᴴ * (S - T) * ρ)).re`; `theorem exists_exactly_linear_observables (t : ℕ) (ht : 0 < t) (δ : ℝ) (hδ : 0 ≤ δ) (ρ : Op ι) (hpsd : ρ.PosSemidef) (htr : ρ.trace = 1) (O : (Fin t → ZMod 2) → Op ι) (hO : ∀ u, IsBinaryObservable (O u)) (hcorr : 1 - δ ≤ avg over (u, u') of (Matrix.trace (O u * O u' * O (u + u') * ρ)).re) : ∃ (ι' : Type) (_ : Fintype ι') (_ : DecidableEq ι') (anc : EuclideanSpace ℂ ι'), ‖anc‖ = 1 ∧ ∃ L : (Fin t → ZMod 2) → Op (ι × ι'), (∀ u, IsBinaryObservable (L u)) ∧ (∀ u u', L u * L u' = L (u + u')) ∧ (avg over u of stateDepDistSq (L u) (heteroKron (O u) 1) (heteroKron ρ (ancProj anc))) ≤ δ` (`sorry`). Docstring must record `rem:linearity-import` in full: **no** upper bound on `δ`, closeness averaged over `u` only, `L 0 = Id` derived not assumed, and the three deviations of the source's quotation are not reproduced |
| `lem:qld-4-10` (689–709) | `CombinedPointsWitness`, `exists_combinedPointsWitness` | Witnesses + Points | N | `structure CombinedPointsWitness (S : ExpandedSetting P ε) (δ : ℝ) where Q : Pt → Pt → Measurement (K × K) (S.ι × Reg); projective : ∀ x z, (Q x z).IsProjective; self_cons : ∀ (p₁ p₂ : Placement), Symmetric p₁ p₂ → opFamilyDistSq (uniform (Pt × Pt)) (fun xz ab => S.place p₁ ((Q xz.1 xz.2).effect ab)) (fun xz ab => S.place p₂ …) S.psiHat ≤ δ; cons_XZ, cons_ZX : … the same against `S.place p₂ ((S.pointMeas .X x).effect a * (S.pointMeas .Z z).effect b)` and against the reversed product` — the two orders are separate fields, as the blueprint insists; `theorem exists_combinedPointsWitness : ∃ δQ : ℝ → ℝ, IsPolyErr δQ ∧ ∀ (P) [FieldModel P.q] (ε) (S : ExpandedSetting P ε), Nonempty (CombinedPointsWitness S (δQ ε))` (`sorry`) |
| `lem:qld-xz-lines` (882–894) | `CombinedLinesWitness`, `exists_combinedLinesWitness` | Witnesses + Lines | N | `structure CombinedLinesWitness (S) {δQ} (w : CombinedPointsWitness S δQ) (δ : ℝ) where T : Line P.toLdParams → Line P.toLdParams → (DegPoly (P.m*P.d) × DegPoly (P.m*P.d)) → Op (S.ι × Reg); povm : …; axis_degree : IsAxisParallel ℓW → f_W ∉ range (deg d ↪ deg md) → T … = 0; cons : consistencyDefect (Distribution.prod (linePointDist P.toLdParams) (linePointDist P.toLdParams)) (bracketed T placed AA') (fun _ ab => S.place BA'' ((w.Q x z).effect ab)) S.psiHat ≤ δ; plus the three symmetric equivalents`; `theorem exists_combinedLinesWitness : ∃ δP, IsPolyErr₂ δP ∧ ∀ S w, Nonempty (CombinedLinesWitness S w (δP ε ((P.m*P.d : ℝ)/P.q)))` (`sorry`) |
| `def:combine-map`, global (970–983) | `combinePoly`, `combinePoly_mem_polyFunc` | Combining/Defs | N | `noncomputable def combinePoly (f g : MvPolynomial (Fin m) K) : MvPolynomial (Fin (2*m+2)) K := X (alphaVar m) * rename (embX m) f + X (betaVar m) * rename (embZ m) g`, the embeddings via the Lean-only `finCombineEquiv m : Fin (2*m+2) ≃ (Fin m ⊕ Fin m ⊕ Fin 2)`. Real definition. Companion `combinePoly_mem_polyFunc (hd : 1 ≤ d) : f ∈ polyFunc m K d → g ∈ polyFunc m K d → combinePoly f g ∈ polyFunc (2*m+2) K d` (`sorry`) — the hypothesis `1 ≤ d` is load-bearing (the α, β factors have degree 1) and is supplied by `AdmissibleParams.hd` |
| `def:combine-map`, lines (984–989) | `combineLinePoly` | Combining/Defs | N | `def combineLinePoly (aX bX aZ bZ uα vα uβ vβ : K) (f g : DegPoly (m*d)) : DegPoly (m*d+1)` — eq:combine-lines with the two affine reparameterizations `t ↦ aX + bX*t`, `t ↦ aZ + bZ*t` **passed as arguments** rather than recovered from a compatibility proof (OPEN-6); implemented as coefficient extraction from `Polynomial.comp`. Real definition |
| `lem:qld-4-12` (993–1011) | `CombinedPointsWitness.extendedQ`, `extendedQ_spec` | Witnesses + Points | R+N | `noncomputable def extendedQ (w : CombinedPointsWitness S δ) (x z : Pt) (α β : K) : Measurement K (S.ι × Reg) := (w.Q x z).postprocess (fun ab => α * ab.1 + β * ab.2)` — REUSE of `Measurement.postprocess` (`def:bracket`, `\leanok`). The node's measurement is this concrete coarse-graining, so it is a real definition plus `theorem extendedQ_spec (w) : (∀ x z α β, (extendedQ w x z α β).IsProjective) ∧ self-consistency (eq:qld-4-12-self-cons) ∧ the two consistency displays, each over `uniform (Pt × Pt × K × K)` with the same `δ`, and the symmetric equivalents` (`sorry`) |
| `def:ith-restricted-line` (1038–1048) | `restrictedALineDist`, `restrictedDLineDist` | Combining/Defs | N | `noncomputable def restrictedALineDist (L : LdParams) [FieldModel L.q] (i : Fin L.m) : Distribution (Line L × (Fin L.m → ScalarQ L))` — `Distribution.restrict` of the *pre-decoding* CL distribution by `chiIndex L z.seed = i`, then `map`ped through the decoder; likewise `restrictedDLineDist`, whose defining condition is `chiIndex L z.seed = i` (the vanishing of direction coordinates `1 … i−1` is then automatic, since `ldDLineCL` already applies `π_{i−1}`). Restricting before decoding is required: the seed `s` is not recoverable from `Line L`. `IsProbability` companions (`sorry`) |
| `lem:restricted-line-mixture-bounds` (1049–1061, unlabelled prose) | `linePointDist_eq_mixture_restricted`, `avg_restricted_le`, `avg_restricted_prod_le`, `restricted_lines_consistency_bound` | Combining/Lines | N | (i) `aLinePointDist L = Distribution.mixture (fun _ => 1/L.m) (restrictedALineDist L)` and the DLine analogue, as `Distribution` equalities (`sorry`); (ii) inflation: `(∀ y, 0 ≤ f y) → avgOver (linePointDist L) f ≤ δ → avgOver (restrictedALineDist L i) f ≤ 2 * L.m * δ`, and the product form with `4 * L.m^2 * δ` (`sorry`); (iii) eq:qld-xz-lines-restricted as a separate theorem: `∃ C, 0 < C ∧ ∀ S w T v₁ v₂ i j, (the displayed expectation against `Id − w.Q`) ≤ C * P.m^2 * δP` (`sorry`) |
| `lem:qld-sublines` (1063–1069) | `SubLineWitness`, `exists_subLineWitness` | Witnesses + Lines | N | `structure SubLineWitness (P) (hdvd : 2 * P.m + 2 ∣ P.q) where D : Distribution (Line (P.extendedLd hdvd) × Line P.toLdParams × Line P.toLdParams); marginal : D.map Prod.fst = (linePointDist (P.extendedLd hdvd)).map Prod.fst; mem : ∀ t ∈ D.support, ∀ u ∈ linePoints t.1, (projX u ∈ linePoints t.2.1 ∧ projZ u ∈ linePoints t.2.2); mixture : the Property-2 description — the joint law of (ℓX, ℓZ, u) is a `Distribution.mixture` over components `(v : Bool) × Fin P.m × Fin P.m`, each component equal to `Distribution.prod` of the two restricted line marginals with the point conditionally uniform on its line, stated in the second (equivalent) product form of the blueprint, which is the one the claims use; axis_closure : IsAxisParallel ℓ → IsAxisParallel ℓX ∧ IsAxisParallel ℓZ` (= Property 3, `rem:qld-sublines-property-three`); `theorem exists_subLineWitness (P) [FieldModel P.q] (hdvd) : Nonempty (SubLineWitness P hdvd)` (`sorry`). No assertion about the joint conditional law of `(u_X, u_Z)` — the blueprint explicitly withholds it |
| `lem:claim-17-1` (1140–1145) | `subline_replace_by_ordered_product` | Combining/Claims | N | `theorem … : ∃ C, 0 < C ∧ ∀ (P) [FieldModel P.q] (ε δQ δP hdvd) (S) (w) (T) (Dw), \|lhs − rhs\| ≤ C * δQ ^ (1/2 : ℝ)`, where `lhs`, `rhs` are the two `avgOver Dw.D`-then-`avgOver (uniform on ℓ)` scalar expectations of `(⟪ψ̂, (place AA' (T ℓX ℓZ (fX,fZ)) * place BA'' N).mulVec ψ̂⟫).re` with `N` the `extendedQ`-free combined point operator, resp. the ordered product of `S.pointMeas` (`sorry`) |
| `lem:claim-17-2` (1168–1173) | `subline_remove_X_factor` | Combining/Claims | N | same hypothesis pattern; bound `C * P.m * (S.deltaLine ε) ^ (1/2 : ℝ)` — the only statement-level use of ch14's `δ_Line` in this chapter (`sorry`) |
| `lem:claim-17-3` (1204–1209) | `subline_Z_term_near_one` | Combining/Claims | N | same pattern; `\|scalar − 1\| ≤ C * Real.sqrt P.m * (δP ^ (1/4 : ℝ) + δQ ^ (1/4 : ℝ) + ε ^ (1/4 : ℝ))` (`sorry`) |
| `lem:qld-4-13` (1020–1034) | `ExtendedLinesWitness`, `exists_extendedLinesWitness`, `exists_extendedLinesWitness_established` | Witnesses + Apply | N | `structure ExtendedLinesWitness (S) (hdvd) (δ : ℝ) where Qline : Line (P.extendedLd hdvd) → DegPoly (P.m*P.d+1) → Op (S.ι × Reg); povm; axis_degree; cons : both displays of eq:qld-4-13 as `consistencyDefect … ≤ δ`, the bracketed evaluation classes of `Qline` against `extendedQ w`, over `linePointDist (P.extendedLd hdvd)`, on the placement pairs AA'/BA'' and BB'/AB''`. Two existence theorems, both `sorry`: the **source form** `∃ δc, IsPolyErr₂ δc ∧ … Nonempty (… (δc (P.m^2 * ε) ((P.m*P.d : ℝ)/P.q)))`, and `_established` with the bound the proof actually delivers, `C * P.m * δ ε (md/q)`. `rem:qld-4-13-source-defects` says the first is unproved along either source route; the second is what node 13 consumes (OPEN-4) |
| `lem:qld-4-7` (1267–1274) | `PolyPair`, `GlobalPairWitness`, `exists_globalPairWitness` | Witnesses + Apply | R+N | `abbrev PolyPair (P) := ↥(polyFunc P.m (ScalarQ P) P.d) × ↥(polyFunc P.m (ScalarQ P) P.d)` (REUSE `polyFunc`; needs the `Fintype`/`DecidableEq` instances of OPEN-3); `structure GlobalPairWitness (S : ExpandedSetting P ε) (δ : ℝ) where Smeas : Measurement (PolyPair P) (S.ι × Reg); projective : Smeas.IsProjective; point_cons : ∀ W : PauliKind, consistencyDefect (uniformDistribution Pt) (fun u a => S.place AA' ((Smeas.postprocess (evalAt W u)).effect a)) (fun u a => S.place BA'' ((S.pointMeas W u).effect a)) S.psiHat ≤ δ; point_cons' : the BB'/AB'' display`; `theorem exists_globalPairWitness : ∃ a b : ℝ, 1 < a ∧ 0 < b ∧ b < 1 ∧ ∀ (P) [FieldModel P.q] (ε : ℝ), 0 < ε → ∀ S : ExpandedSetting P ε, Nonempty (GlobalPairWitness S (deltaQld a b ε P.m P.d P.q))` (`sorry`) — δ_S REUSES the frozen `deltaQld`, whose shape is literally `a(md)^a(ε^b + q^{-b} + 2^{-bmd})`; `1 < a` here versus `1 ≤ a` in `thm:pauli` is harmless (`rem:qld-4-7-constants`). Carries **no** divisibility hypothesis: the statement lives at dimension `m`, and it is the *proof* that is blocked (`rem:qld-4-7-divisibility`) |

Lean-only helpers, each docstring-marked as formalization-only per AGENTS.md:
`IsPolyErr`, `IsPolyErr₂`, `Distribution.mixture / prod / restrict` (+ `IsProbability`
companions, `sorry`), `finCombineEquiv`, `embX`, `embZ`, `alphaVar`, `betaVar`,
`aLineOf`, `dLineOf`, `projX`, `projZ`, `ancProj v := Matrix.vecMulVec v (star v)`,
`stateDepDistSq`, `AdmissibleParams.extendedLd (hdvd) : LdParams` (fields
`(P.q, 2*P.m+2, P.d, 1)`), `evalAt (W : PauliKind) (u : Pt) : PolyPair P → K`,
`deltaQld_mono`.

## (d) STATEMENTS (`sorry`) vs DEFINITIONS (real)

**Real, no `sorry`** (10 + helpers): `consistencyDefect`; `aLinePointDist`,
`dLinePointDist`, `linePointDist`; `combinePoly`; `combineLinePoly`;
`restrictedALineDist`; `restrictedDLineDist`; `extendedQ`; `IsBinaryObservable`;
`stateDepDistSq`; all five witness `structure`s; every Lean-only helper above except
its companion lemmas. Definitions are direct and computable-shaped; every prose claim
inside a blueprint definition (degree bounds, probability of the restricted
distributions, well-definedness of the combining map on lines) becomes a named `sorry`
lemma beside it, per 4.1 (e)7 — never a definitional side condition.

**`sorry` statements** (13 nodes → 16 theorems): `exists_exactly_linear_observables`;
`exists_combinedPointsWitness`; `exists_combinedLinesWitness`; `extendedQ_spec`;
`linePointDist_eq_mixture_restricted`, `avg_restricted_le`, `avg_restricted_prod_le`,
`restricted_lines_consistency_bound` (node 7 splits into four);
`exists_subLineWitness`; the three claims; `exists_extendedLinesWitness` and
`exists_extendedLinesWitness_established`; `exists_globalPairWitness`. Plus companion
well-formedness lemmas: `combinePoly_mem_polyFunc`, the degree bound of
`combineLinePoly`, `IsProbability` of the restricted/mixture/product distributions,
`deltaQld_mono`. All are marker-free tracked skeleton sorries (4.1 (f)), not
`**Unfaithful:**` helpers.

Blueprint sync after the skeleton type-checks: `\lean{…}` + `\leanok` on the 13
*statement* environments only (never on proofs), then `leanblueprint web` and
`lake exe checkdecls`.

## (e) Cross-chapter dependencies — the parallel-wave interface

### Exported by ch15 (state these most carefully; consumers bind by label)

1. **`lem:qld-4-7` → `GlobalPairWitness` / `exists_globalPairWitness`.** The only ch15
   output ch16 consumes (verified: every ch15 reference in `ch16_qpbt_extraction.tex` is
   to `lem:qld-4-7`). Contract, in the order ch16 uses it:
   - outcome index `PolyPair P` = **pairs of `polyFunc` representatives** at
     `(P.m, ScalarQ P, P.d)`; ch16's `def:s-w-marginals` is then
     `Smeas.postprocess Prod.fst` / `Prod.snd` — no extra ch15 declaration needed;
   - `Smeas` is a **complete projective** `Measurement`, i.e. `∑ Smeas.effect = 1` and
     `IsProjective`; ch16's `lem:tildew-product-form` uses both, so `Measurement`
     (not `Submeasurement`) is the required carrier;
   - error `deltaQld a b ε P.m P.d P.q` with `∃ a b, 1 < a ∧ 0 < b ∧ b < 1` at the
     **outermost** level, so that ch16 can re-quantify after enlarging `a` and
     shrinking `b` (see `deltaQld_mono` in (b));
   - consistency stated as `consistencyDefect` under `uniformDistribution Pt`, against
     `S.pointMeas W`, on both placement pairs AA'/BA'' and BB'/AB'';
   - **no divisibility hypothesis** — ch16 must not assume one.
2. **`consistencyDefect` (`def:consistency`).** Needed verbatim by ch16 and by any brief
   that states `lem:ld-soundness`. Offered from `Games/Consistency.lean` unless the
   orchestrator assigns the node elsewhere (OPEN-5); the signature in (c) is the
   interface either way.
3. **`linePointDist` and the restricted line distributions.** ch14 states
   `lem:qld-comm-line-cons` over `def:line-point-dist`, so ch14 and ch15 must share one
   declaration; `Test/LinePointDist.lean` is a ch15-side proposal, not a claim of
   ownership (OPEN-1).
4. **The witness/`IsPolyErr` patterns** (OPEN-2), if adopted wave-wide.

### Consumed by ch15 (expressed as blueprint labels; bound at reconciliation)

- **ch14**, as one bundle (RECONCILE-1): `lem:projective-strategy-setup` +
  `def:expanded-state` (`psiHat`, the common local space) + `def:symmetric-equivalents`
  (the four placements, as an ampliation `Op (ι × Reg) → Op Full` per placement — ch15
  never manipulates the six-register factorization directly, only through `place`);
  `def:expanded-point-measurement` (`pointMeas`, a *projective* `Measurement K (ι × Reg)`
  for each `(W, u)`); `def:expanded-line-measurement` (used at statement level only
  inside node 3's witness construction; nodes 9–11 reach it through `T`);
  `def:ideg-deg-polynomials` (`DegPoly c` = `Fin (c+1) → K`, the evaluation classes,
  the `⊥` completion and the zero-operator convention for non-evaluating `f` — node 3's
  `axis_degree` field and every bracketed family depend on this convention);
  `lem:qld-comm-line-cons` **must export its error function `δ_Line` as a named
  declaration**, because node 10 mentions it in a statement, not a proof.
- **ch13**: `def:line-point-dist`, dimension-generic (`LdParams`-keyed). If the owner
  keys it to a fixed `AdmissibleParams` dimension, nodes 8 and 12 cannot be stated at
  all — RECONCILE-2, the single hardest external constraint in this brief.
- **ch12**: `def:bracket` → REUSE `Quantum.Measurement.postprocess` (`\leanok`);
  `def:consistency` per item 2.
- **4.1 frozen**: the (a) reuse list, verbatim.

## RECONCILE: (assumptions pending the 4.1 merge and sibling 4.2 briefs)

- **RECONCILE-1** — ch14 provides one bundle (`ExpandedSetting P ε` is a placeholder
  name) with `ι`, `Full`, `psiHat`, `place`, `pointMeas`, `lineMeas`, `deltaLine`, and
  the hypothesis that the strategy is symmetric, projective and wins with probability
  `≥ 1 − ε`. Every ch15 statement goes through this bundle, so a rename is mechanical;
  a *different shape* (e.g. placements as explicit tensor factorizations rather than a
  map) is not, and would force rewrites in all five witness structures.
- **RECONCILE-2** — `linePointDist : (L : LdParams) → [FieldModel L.q] →
  Distribution (Line L × (Fin L.m → ScalarQ L))`, dimension-generic. The construction
  in (c) is written out from frozen 4.1 pieces so that whoever owns the node can adopt
  it unchanged.
- **RECONCILE-3** — 4.1 names used before the merge: `AdmissibleParams` (+ `toLdParams`,
  `hd`), `LdParams`, `LdSpace` (+ `.pt .seed .dir`), `ScalarQ` (assumed available for
  both `AdmissibleParams` and `LdParams`), `PauliRegister`, `PauliKind`, `chiIndex`,
  `ldPointCL`, `ldALineCL`, `ldDLineCL`, `clDistribution`, `linePoints`, `lineRepMap`,
  `deltaQld`, `opFamilyDistSq`, `heteroKron`, `IsAdmissibleSize`, `binTrace`,
  `Measurement.postprocess`, `Measurement.IsProjective`. 4.1 sketches lines as a point
  set (`linePoints u v`); ch15 additionally needs the *presentation* type
  `Line L = (base point, direction)`, which `def:ideg-deg-polynomials` also requires —
  assumed supplied by ch14, otherwise added in `Test/LinePointDist.lean`.
- **RECONCILE-4** — `polyFunc` is a `Submodule`, so `PolyPair` is a product of subtypes
  (`↥`); if 4.1's `def:polyfunc` row settles on the bundled `LDT.Polynomial` structure
  instead, `PolyPair` and `evalAt` follow that choice and ch16 must be told.

## OPEN: items for the orchestrator

- **OPEN-1 (owner of `def:line-point-dist`)** — a ch13 node, in neither the 4.1 closure
  nor ch15, yet required at statement level by ch14 (`lem:qld-comm-line-cons`) and by
  four ch15 nodes. Either assign it to a ch13-remainder brief, or accept the ch15-side
  file in (b). Both chapters must not define it twice.
- **OPEN-2 (wave conventions)** — confirm the witness-structure pattern and
  `IsPolyErr`/`IsPolyErr₂` as wave-wide, and place `Games/ErrorFunctions.lean` under a
  single owner; ch14's `δ_Anticom` and `δ_Line` need the same predicate, and ch15's
  node 10 consumes `δ_Line` in a statement.
- **OPEN-3 (finiteness of the polynomial index)** — `Measurement` requires
  `Fintype`/`DecidableEq` on its outcome type, and the repository has **no** `Fintype`
  instance for `↥(polyFunc m K d)` (checked). Node 13 and all of ch16 need one. Proposal:
  a Lean-only `polyFuncCoeffEquiv : ↥(polyFunc m K d) ≃ ((Fin m → Fin (d+1)) → K)` with
  the derived instances, in `Algebra/LowDegreeCode.lean` or a shared file; the fallback
  is to index by the coefficient box directly and carry the equivalence as a lemma. This
  is an interface decision binding ch15 and ch16 together, so it should be settled once.
  (Line answers are unaffected: `DegPoly c = Fin (c+1) → K` is a `Fintype` already.)
- **OPEN-4 (`lem:qld-4-13` error form)** — the blueprint keeps the source's
  `poly(m²ε, md/q)`, which `rem:qld-4-13-source-defects` records as unproved along both
  source routes, while node 13 consumes the established `m · poly(ε, md/q)`. The
  skeleton states both (`exists_extendedLinesWitness` for fidelity,
  `_established` for use, cross-referenced to `gap:qpbt_combined-lines-error-term`).
  Confirm, or drop one.
- **OPEN-5 (owner of `def:consistency`)** — proposed here in `Games/Consistency.lean`;
  reassign to a ch12-remainder brief if one exists. Note that
  `Quantum.Measurement.inconsistency` is *not* a substitute: it is defined against
  `normalizedTrace`, whereas `≃_δ` is state-dependent in `ψ̂`.
- **OPEN-6 (`combineLinePoly` totality)** — eq:combine-lines is defined only for
  `(ℓ, ℓX, ℓZ)` compatible in the sense of `lem:qld-sublines` Property 2. The skeleton
  passes the affine reparameterizations as arguments, so the definition is total and no
  junk value arises; callers hold the compatibility witness via `SubLineWitness.mem`.
  Confirm.
- **OPEN-7 (divisibility guard placement)** — nodes 8 and 12 carry
  `hdvd : 2 * P.m + 2 ∣ P.q` (without it the dimension-`2m+2` question machinery has no
  well-defined `χ`), which for admissible parameters with `m ≥ 2` is unsatisfiable;
  node 13 carries no guard, so its `sorry` is where the real obstruction of
  `rem:qld-4-7-divisibility` / `gap:qpbt_ld-dimension-divisibility` is recorded. Confirm
  this split, since it makes two ch15 statements vacuous for `m ≥ 2` by design.
- **OPEN-8 (`\uses` omissions in ch15)** — `def:ideg-deg-polynomials` is needed at
  statement level by `lem:qld-xz-lines`, `lem:qld-4-13`, `lem:qld-4-7` and
  `def:combine-map` (the `deg_c(ℓ)` classes and the evaluation convention), and
  `def:admissible-size` by the chapter preamble's `q = 2^t`; none appears in the
  corresponding statement `\uses` lines. Nodes 9–11 likewise consume the *objects* of
  nodes 2, 3, 8, which their `\uses` lines do list. Consider patching the four `\uses`
  lines in ch15.
- **OPEN-9 (`thm:linearity` state carrier)** — stated with a raw `Op ι` plus
  `PosSemidef` and `trace = 1`, keeping 4.1 (e)4's rule that the density-matrix
  `LDT.QuantumState` layer stays out of the QPBT games layer. Switch to `QuantumState`
  if the orchestrator prefers; the only consumer is a future proof of node 2.
