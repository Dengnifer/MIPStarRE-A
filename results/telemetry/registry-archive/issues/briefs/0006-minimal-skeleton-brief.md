# Design brief — issue #0006, stage 4.1: minimal Lean skeleton for `thm:pauli`

Deliverable: the statement of `thm:pauli` (`MIPStarRE.QPBT.pauli_soundness`) and its
transitive **statement-level** definition closure under `MIPStarRE/QPBT/`, every proof
`sorry`. Sources: `blueprint/src/chapter/ch13_qpbt_test.tex` (`thm:pauli`), closure
through `ch12_qpbt_games.tex` and `ch11_qpbt_algebra.tex`; paper origin
`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:1426-1447`.
Conventions: `AGENTS.md` (naming, file structure, docstrings, paper citations in every
statement-like docstring — cite the blueprint `\label` and the qpbt-paper file/lines).

Verified: the statement `\uses` of `thm:pauli` is
`{def:pauli-question-distribution, def:pauli-win-predicate, def:admissible,
def:tensor-product-value, def:EPR, lem:pauli-observable-expansion, def:povm-distance}`.
`lem:ld-soundness` and `thm:ms-rigidity` appear only in prose about the *proof* and in
proof-level `\uses`; they are **not** in the statement closure (checked mechanically
against every statement `\uses` line, ch11–ch13).

## (a) Statement closure of `thm:pauli` — 39 nodes, dependency order

Computed as the transitive closure of statement-level `\uses` lines only (proof-level
`\uses` excluded). Valid topological order; formalize top to bottom.

| # | label | chapter | # | label | chapter |
|---|-------|---------|---|-------|---------|
| 1 | `def:admissible-size` | ch11 | 21 | `def:dot-product-orthogonal` | ch11 |
| 2 | `def:admissible` | ch13 | 22 | `def:indicator-vector` | ch11 |
| 3 | `def:game` | ch12 | 23 | `def:pauli-win-predicate` | ch13 |
| 4 | `def:ld-game` | ch13 | 24 | `def:submeasurement` | ch03 (LDT) |
| 5 | `def:register-subspace` | ch11 | 25 | `def:povm-conventions` | ch12 |
| 6 | `def:complementary` | ch11 | 26 | `def:tensor-product-strategy` | ch12 |
| 7 | `def:cl-func` | ch12 | 27 | `def:tensor-product-value` | ch12 |
| 8 | `def:cl-dist` | ch12 | 28 | `def:lin-reg` | ch11 |
| 9 | `lem:cl-concat` | ch12 | 29 | `def:EPR` | ch11 |
| 10 | `def:canonical-complement` | ch11 | 30 | `def:subfields-kappa` | ch11 |
| 11 | `lem:canonical-complement` | ch11 | 31 | `def:subfield-trace` | ch11 |
| 12 | `def:cl-canonical` | ch11 | 32 | `def:generalized-pauli` | ch11 |
| 13 | `def:line` | ch11 | 33 | `lem:pauli-observable-expansion` | ch11 |
| 14 | `prop:line-equiv` | ch11 | 34 | `def:state-distance` | ch12 |
| 15 | `def:line-representative` | ch11 | 35 | `def:povm-distance` | ch12 |
| 16 | `def:ld-question-distribution` | ch13 | 36 | `thm:pauli` | ch13 |
| 17 | `def:graph-distribution` | ch12 | 37 | `def:polynomials-degree` | ch11 |
| 18 | `def:ms-game` | ch13 | 38 | `def:low-degree-encoding` | ch11 |
| 19 | `def:pauli-question-distribution` | ch13 | 39 | `def:polyfunc` | ch03 (LDT) |
| 20 | `def:ld-win-predicate` | ch13 | | | |

(Ordering constraint, exact: 1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,
39,20,37,38,21,22,23,24,25,26,27,28,29,30,31,32,33,34,35,36 — i.e. `def:polyfunc`
before `def:ld-win-predicate`, `def:polynomials-degree`/`def:low-degree-encoding`
before `def:indicator-vector`.)

Two nodes are already formalized on the LDT track (ch03, `\leanok`): `def:polyfunc`
(`MIPStarRE.LDT.Preliminaries.polyFunc`, `MIPStarRE.LDT.Polynomial`) and
`def:submeasurement` (`MIPStarRE.LDT.SubMeas` / `MIPStarRE.Quantum.Measurement`).
So 37 nodes get new or bridging QPBT declarations; 4 of them are proposition-valued
(`lem:canonical-complement`, `prop:line-equiv`, `lem:cl-concat`,
`lem:pauli-observable-expansion`) and land with `sorry` proofs, as does
`pauli_soundness` itself.

## (b) File tree under `MIPStarRE/QPBT/`

Namespace `MIPStarRE.QPBT` throughout. All files far below the 1000-line repo cap
(estimates in parentheses). Import arrows point downward; every file also imports its
listed reuse targets.

```
MIPStarRE/QPBT.lean                        -- re-export root, added to MIPStarRE.lean (~15)
MIPStarRE/QPBT/Algebra/Subspaces.lean      -- nodes 5,6,10,11,12,21          (~120)
MIPStarRE/QPBT/Algebra/FieldBasis.lean     -- nodes 1,30,31 (+ char-2 glue)  (~100)
MIPStarRE/QPBT/Algebra/LowDegreeCode.lean  -- nodes 37,38,22 (39 reused)     (~110)
MIPStarRE/QPBT/Algebra/Lines.lean          -- nodes 13,14,15                 (~90)
MIPStarRE/QPBT/Algebra/Pauli.lean          -- nodes 28,29,32,33              (~180)
MIPStarRE/QPBT/Games/Defs.lean             -- nodes 3,25 (24 reused),26,27   (~150)
MIPStarRE/QPBT/Games/Distance.lean         -- nodes 34,35                    (~60)
MIPStarRE/QPBT/Games/CondLinear.lean       -- nodes 7,8,9,17                 (~130)
MIPStarRE/QPBT/Test/LowDegreeGame.lean     -- nodes 4,16,20                  (~220)
MIPStarRE/QPBT/Test/MagicSquare.lean       -- node 18                        (~110)
MIPStarRE/QPBT/Test/PauliBasisTest.lean    -- nodes 2,19,23                  (~250)
MIPStarRE/QPBT/Test/Soundness.lean         -- node 36 (+ deltaQld, helpers)  (~130)
```

Internal import DAG: `Subspaces ← Lines`; `FieldBasis ← Pauli`;
`{Subspaces, FieldBasis, LowDegreeCode, Lines} ← CondLinear` (CondLinear needs only
Subspaces); `Games/Defs ← Games/Distance`; `{CondLinear, Games/Defs, Lines,
FieldBasis} ← Test/LowDegreeGame`; `{Games/Defs, CondLinear} ← Test/MagicSquare`;
`{LowDegreeGame, MagicSquare, LowDegreeCode, FieldBasis} ← Test/PauliBasisTest`;
`{PauliBasisTest, Pauli, Distance} ← Test/Soundness`. External reuse imports:
`MIPStarRE.Quantum.FiniteMatrix` (`Op`, `IsProj`), `MIPStarRE.Quantum.Measurement`,
`MIPStarRE.Quantum.FiniteHilbert`, `MIPStarRE.Quantum.ProjectorONB`,
`MIPStarRE.LDT.Basic.ParametersBase` (`FieldModel`), `MIPStarRE.LDT.Basic.Distribution`
(+ `DistributionUniform`, `DistributionProduct`), `MIPStarRE.LDT.Preliminaries.Polynomials`.

## (c) Node → declaration mapping

Legend: R = reuse an existing declaration (name it, no new decl unless a thin wrapper
is listed), N = new. Signatures are *sketches* — the implementer owns the final form.
Ambient convention: linear spaces are `ι → K` for a `Fintype`/`DecidableEq` index `ι`;
`Op ι := Matrix ι ι ℂ` (`MIPStarRE.Quantum.Op`); `Cube m := Fin m → Bool`.

| label | Lean name | file | R/N | signature sketch |
|---|---|---|---|---|
| def:register-subspace | `registerSubmodule` | Algebra/Subspaces | N | `def registerSubmodule (K) (S : Finset ι) : Submodule K (ι → K)` (span of std basis in `S`) |
| def:dot-product-orthogonal | `Matrix.dotProduct` (`⬝ᵥ`) + `dotOrthogonal` | Algebra/Subspaces | R+N | `def dotOrthogonal (W : Submodule K (ι → K)) : Submodule K (ι → K)` |
| def:complementary | `IsCompl`, `Submodule.linearProjOfIsCompl` | — (Mathlib) | R | no new decl; cite in docstrings |
| def:canonical-complement | `canonicalComplement` | Algebra/Subspaces | N | `def canonicalComplement (W : Submodule K (Fin n → K)) : Finset (Fin n)` — non-pivot columns, see (e)5 |
| lem:canonical-complement | `isCompl_registerSubmodule_canonicalComplement` | Algebra/Subspaces | N | `theorem … : IsCompl W (registerSubmodule K (canonicalComplement W))` (`sorry`) |
| def:cl-canonical | `canonicalProjOfKernel` | Algebra/Subspaces | N | `noncomputable def canonicalProjOfKernel (W : Submodule K (Fin n → K)) : (Fin n → K) →ₗ[K] (Fin n → K)` (proj onto canonical complement along `W`) |
| def:admissible-size | `IsAdmissibleSize` | Algebra/FieldBasis | N | `def IsAdmissibleSize (q : ℕ) : Prop := ∃ k, Odd k ∧ q = 2 ^ k` |
| def:subfields-kappa | `Basis.equivFun`, `Algebra.leftMulMatrix` (+ wrapper `kappa`) | Algebra/FieldBasis | R | `abbrev kappa (b : Basis (Fin k) F K) : K ≃ₗ[F] (Fin k → F) := b.equivFun`; mult. table `K_a = Algebra.leftMulMatrix b a` |
| def:subfield-trace | `Algebra.trace` (+ wrapper `binTrace`) | Algebra/FieldBasis | R | `noncomputable abbrev binTrace (K) [Field K] [Algebra (ZMod 2) K] : K →ₗ[ZMod 2] ZMod 2 := Algebra.trace (ZMod 2) K`; `Algebra.trace_eq_matrix_trace` is exactly eq:def-trace |
| def:polyfunc | `MIPStarRE.LDT.Preliminaries.polyFunc` | — (LDT) | R | already `\leanok`; representative convention per issue #0004 |
| def:polynomials-degree | `MvPolynomial.degreeOf`, `MvPolynomial.totalDegree` + `polyFunc` | Algebra/LowDegreeCode | R | no new decl; module docstring records the evaluation/representative bridge (bijective iff `d ≤ q−1` — deferred lemma, not needed at statement level) |
| def:low-degree-encoding | `indicatorPoly`, `lowDegreeEncoding` | Algebra/LowDegreeCode | N | `def indicatorPoly (y : Cube m) : MvPolynomial (Fin m) K`; `def lowDegreeEncoding (a : Cube m → K) : MvPolynomial (Fin m) K`; eval shorthand `def lowDegreeEnc (a) (x : Fin m → K) : K` |
| def:indicator-vector | `indicatorVec` | Algebra/LowDegreeCode | N | `def indicatorVec (x : Fin m → K) : Cube m → K`; lemma `lowDegreeEnc_eq_dotProduct` (`sorry`) |
| def:line | `linePoints`, `IsAxisParallel`, `IsDiagonal` | Algebra/Lines | N | `def linePoints (u v : Fin m → K) : Set (Fin m → K) := {x ∣ ∃ t, x = u + t • v}` |
| prop:line-equiv | `linePoints_eq_of_mem` | Algebra/Lines | N | `theorem … (h : u' ∈ linePoints u v) : linePoints u v = linePoints u' v` (`sorry`) |
| def:line-representative | `lineRepMap`, `lineRep` | Algebra/Lines | N | `noncomputable def lineRepMap (v : Fin m → K) : (Fin m → K) →ₗ[K] (Fin m → K) := canonicalProjOfKernel (Submodule.span K {v})`; `v = 0` convention automatic (`span {0} = ⊥` ⇒ identity) |
| def:lin-reg | `EuclideanSpace ℂ V` | — (Mathlib) | R | states are unit vectors in `EuclideanSpace ℂ ι`; matrices act via `Matrix.mulVec` / `Matrix.toEuclideanLin` |
| def:EPR | `eprState` | Algebra/Pauli | N | `noncomputable def eprState (V : Type) [Fintype V] : EuclideanSpace ℂ (V × V)`; `EPR_q^{⊗M}` is `eprState (Cube m → K)` (identification `(V×V)^γ ≃ V^γ × V^γ` noted, not materialized) |
| def:generalized-pauli | `PauliKind`, `tauShift`, `tauPhase`, `pauliVec`, `pauliProj` | Algebra/Pauli | N | `inductive PauliKind ∣ X ∣ Z`; `noncomputable def tauShift (a : K) : Op K`; `tauPhase (b : K) : Op K` (phases via `AddChar`/char-p root of unity; for admissible q, `ω = −1`); `pauliProj (W : PauliKind) (e : γ → K) : Op (γ → K)` — rank-one, entrywise product over `γ` of single-qudit `Matrix.vecMulVec (pauliVec W eᵢ) (star …)` |
| lem:pauli-observable-expansion | `tauObservable_eq_sum_pauliProj`, `pauliProj_eq_avg_tauObservable` | Algebra/Pauli | N | both `sorry`; statement-level per the blueprint `\uses` of `thm:pauli`, even though `pauli_soundness` mentions only `pauliProj` (see OPEN-2) |
| def:game | `Game` | Games/Defs | N | `structure Game where QuestionA QuestionB AnswerA AnswerB : Type; [Fintype/DecidableEq instance fields]; μ : Distribution (QuestionA × QuestionB); μ_prob : μ.IsProbability; decide : QuestionA → QuestionB → AnswerA → AnswerB → Bool` |
| def:submeasurement | `MIPStarRE.Quantum.Submeasurement`, `Measurement` | — (Quantum) | R | already `\leanok` (ch03 tags the LDT twins; ch12's `def:bracket` already tags `Quantum.Measurement.postprocess`) |
| def:povm-conventions | `Quantum.Measurement` + `Measurement.postprocess` + `Measurement.IsProjective` | Games/Defs | R+N | marginals := `postprocess` along `Prod.fst`/`Prod.snd`; `def Measurement.IsProjective (M) : Prop := ∀ a, IsProj (M.effect a)` (only if not already present) |
| def:tensor-product-strategy | `Strategy` | Games/Defs | N | `structure Strategy (G : Game) where ιA ιB : Type; [Fintype/DecidableEq fields]; ψ : EuclideanSpace ℂ (ιA × ιB); ψ_norm : ‖ψ‖ = 1; A : G.QuestionA → Quantum.Measurement G.AnswerA ιA; B : G.QuestionB → Quantum.Measurement G.AnswerB ιB` |
| def:tensor-product-value | `Strategy.value`, `Game.value` | Games/Defs | N | `noncomputable def Strategy.value (S : Strategy G) : ℝ := avgOver G.μ fun (x,y) => ∑ a, ∑ b, (if G.decide x y a b then 1 else 0) * (re ⟪ψ, (Aˣₐ ⊗ₖ Bʸᵦ).mulVec ψ⟫)`; `Game.value := ⨆ S : Strategy G, S.value` (csSup; unused by `pauli_soundness`, see OPEN-4) |
| def:state-distance | `stateDistSq` | Games/Distance | N | `noncomputable def stateDistSq (ψ φ : EuclideanSpace ℂ ι) : ℝ := ‖ψ - φ‖ ^ 2` (quantitative; O(·) convention in (e)8) |
| def:povm-distance | `opFamilyDistSq` | Games/Distance | N | `noncomputable def opFamilyDistSq (μ : Distribution X) (M N : X → α → Op ι) (ψ : EuclideanSpace ℂ ι) : ℝ := avgOver μ fun x => ∑ a, ‖(M x a - N x a).mulVec ψ‖ ^ 2` |
| def:cl-func | `IsCondLinearOn`, `IsCondLinear` | Games/CondLinear | N | `inductive IsCondLinearOn (K) : Finset ι → ℕ → ((ι → K) → ι → K) → Prop` — `zero : … S 0 0`; `succ`: `∃ S₁ ⊆ S`, linear `L₁` supported on `S₁`, and `∀ v, IsCondLinearOn (S \ S₁) ℓ (rest v)` with `L x = L₁ x + rest (L₁ x) x`; `def IsCondLinear (ℓ) (L) := IsCondLinearOn Finset.univ ℓ L` |
| def:cl-dist | `clDistribution` | Games/CondLinear | N | `noncomputable def clDistribution (L R : (ι → K) → ι → K) : Distribution ((ι → K) × (ι → K)) := (uniformDistribution (ι → K)).map fun z => (L z, R z)` |
| lem:cl-concat | `IsCondLinearOn.concat` | Games/CondLinear | N | concatenation of a k-level function on `U`-coords with an `u`-indexed family of ℓ-level functions on `V`-coords is (k+ℓ)-level (`sorry`) |
| def:graph-distribution | `graphDistribution` | Games/CondLinear | N | `noncomputable def graphDistribution (E : Finset (Sym2 T)) : Distribution (T × T)` — `Distribution.uniformOnFinset` over ordered pairs `(u,v)` with `s(u,v) ∈ E` (self-loops contribute one pair); `IsProbability` lemma under `E.Nonempty` (`sorry`) |
| def:ld-game | `LdParams`, `LdType`, `LdIndex`, `LdSpace` | Test/LowDegreeGame | N | `structure LdParams where q m d k : ℕ; hm : 1 ≤ m; hd : 1 ≤ d; hk : 1 ≤ k; hq : IsAdmissibleSize q; hdvd : m ∣ q`; `inductive LdType ∣ point ∣ aline ∣ dline`; `def LdIndex (P) := Fin P.m ⊕ Unit ⊕ Fin P.m`; `abbrev LdSpace (P) [FieldModel P.q] := LdIndex P → ScalarQ P` (accessors `.pt .seed .dir`) |
| def:ld-question-distribution | `chiIndex`, `ldPointCL`, `ldALineCL`, `ldDLineCL`, `ldQuestionDistribution` | Test/LowDegreeGame | N | `def chiIndex (P) [FieldModel P.q] (s : ScalarQ P) : Fin P.m` (eq:chi-func via `FieldModel.equiv`, see (e)5); the three CL maps `LdSpace P → LdSpace P` defined concretely (`lineRepMap` for `L^Ln`); levels asserted by companion `sorry` lemmas `isCondLinear_ldALineCL : IsCondLinear 2 …` etc.; `noncomputable def ldQuestionDistribution (P) : Distribution (LdQuestion P × LdQuestion P)` with `LdQuestion P := LdType × LdSpace P` — uniform type pair × uniform seed, pushed through `fun ((tA,tB),z) => ((tA, ldCL tA z),(tB, ldCL tB z))` |
| def:ld-win-predicate | `LdAnswer`, `ldWinPredicate`, `ldGame` | Test/LowDegreeGame | N | `inductive LdAnswer (P) ∣ pointVals (a : Fin P.k → ScalarQ P) ∣ alinePolys (f : Fin P.k → Fin (P.d+1) → ScalarQ P) ∣ dlinePolys (f : Fin P.k → Fin (P.m*P.d+1) → ScalarQ P)`; `def ldWinPredicate (P) : LdQuestion P → LdQuestion P → LdAnswer P → LdAnswer P → Bool` (universal-`t` quantification of rem:ld-win-zero-direction; wrong-form answers rejected); `noncomputable def ldGame (P) [FieldModel P.q] : Game` |
| def:ms-game | `MsType`, `msConstraintVars`, `msParity`, `msEdges`, `MsAnswer`, `msWinPredicate`, `msGame` | Test/MagicSquare | N | `inductive MsType ∣ constraint (i : Fin 6) ∣ var (j : Fin 9)`; `def msConstraintVars : Fin 6 → Fin 3 → Fin 9`; `def msParity : Fin 6 → ZMod 2` (`1` iff `i = 5`); `def msEdges : Finset (Sym2 MsType)` (18 edges); `inductive MsAnswer ∣ triple (β : Fin 3 → ZMod 2) ∣ bit (γ : ZMod 2)`; `noncomputable def msGame : Game` (μ = `graphDistribution msEdges`) |
| def:admissible | `AdmissibleParams` | Test/PauliBasisTest | N | `structure AdmissibleParams where q m d : ℕ; hd : 1 ≤ d; hq : IsAdmissibleSize q; hdvd : m ∣ q`; lemma `one_le_m` (`sorry` ok); `def AdmissibleParams.toLdParams (P) : LdParams` (k := 1) |
| def:pauli-question-distribution | `PauliType`, `PauliIndex`, `PauliSpace`, `pauliCL`, `pauliEdges`, `pauliQuestionDistribution` | Test/PauliBasisTest | N | `inductive PauliType ∣ point (W) ∣ aline (W) ∣ dline (W) ∣ pauli (W) ∣ pairW (W) ∣ pair ∣ ms (t : MsType)` (`W : PauliKind`); `def PauliIndex (P) := Fin P.m ⊕ Fin P.m ⊕ Unit ⊕ Fin P.m ⊕ Unit ⊕ Unit` (registers `V_X,V_Z,V_I,V_V,V_{R_X},V_{R_Z}`); `abbrev PauliSpace (P) [FieldModel P.q] := PauliIndex P → ScalarQ P`; `def pauliCL (P) (t : PauliType) : PauliSpace P → PauliSpace P` (items 1–5, embedding the ld maps on the `W` block; `pauli W ↦ 0`); level lemmas `sorry`; `def pauliEdges : Finset (Sym2 PauliType)` (MS edges + 12 listed edges + all self-loops); `noncomputable def pauliQuestionDistribution (P) : Distribution (PauliQuestion P × PauliQuestion P)`, `PauliQuestion P := PauliType × PauliSpace P` — `graphDistribution pauliEdges` × uniform seed, pushed through `pauliCL` |
| def:pauli-win-predicate | `PauliAnswer`, `gammaValue`, `pauliWinPredicate`, `pauliBasisTest` | Test/PauliBasisTest | N | `inductive PauliAnswer (P) ∣ value (ScalarQ P) ∣ alinePoly (Fin (P.d+1) → ScalarQ P) ∣ dlinePoly (Fin (P.m*P.d+1) → ScalarQ P) ∣ pairBits (ZMod 2 × ZMod 2) ∣ bit (ZMod 2) ∣ msTriple (Fin 3 → ZMod 2) ∣ pauliOutcome (PauliRegister P)` with `abbrev PauliRegister (P) [FieldModel P.q] := Cube P.m → ScalarQ P`; `noncomputable def gammaValue (uX uZ : Fin P.m → ScalarQ P) (rX rZ : ScalarQ P) : ZMod 2 := binTrace ((indicatorVec uX ⬝ᵥ' rX-scaled) * (indicatorVec uZ ⬝ᵥ' …))` per eq:gamma-value; `def pauliWinPredicate (P) : … → Bool` (clauses 1–7; clause 2 delegates to `ldWinPredicate P.toLdParams` at `k = 1`; clause 3 uses `lowDegreeEnc`); `noncomputable def pauliBasisTest (P) [FieldModel P.q] : Game` (symmetric alphabets: `QuestionA = QuestionB = PauliQuestion P`, `AnswerA = AnswerB = PauliAnswer P`) |
| def:tensor-product-value (game side) | — | — | — | see `Game.value` row above |
| thm:pauli | `deltaQld`, `pauli_soundness` | Test/Soundness | N | see (d) |

Helper obligations (Lean-only, no blueprint label; docstring must say so per AGENTS.md
"Record formalization-only auxiliary lemmas explicitly"): `Cube` abbrev + card lemma;
`ScalarQ P := FieldModel.K P.q`; char-2 / `Algebra (ZMod 2)` instances for admissible
`FieldModel`s (FieldBasis.lean); `heteroKron : Op ιA → Op ιB → Op (ιA × ιB)` (via
`Matrix.kronecker`, cf. `opTensor` in `LDT/Basic/TensorPlacement.lean`);
`conjIsometry (φ : E →ₗᵢ[ℂ] F) : Op ι → Op ι'` (matrix conjugation `φ M φ†`);
`isometryTensor (φA φB)` acting on `ψ`; `reindexState (e : ι ≃ ι')` (via
`Equiv.prodProdProdComm` for the `(A'×A'')×(B'×B'') ≃ (A'×B')×(A''×B'')` shuffle).

## (d) Statement sketch of `MIPStarRE.QPBT.pauli_soundness`

```lean
/-- Soundness function of the Pauli basis test; argument order (ε, m, d, q)
everywhere, per rem:delta-qld-argument-order. Real rpow throughout. -/
noncomputable def deltaQld (a b ε : ℝ) (m d q : ℕ) : ℝ :=
  a * ((m * d : ℕ) : ℝ) ^ a *
    (ε ^ b + (q : ℝ) ^ (-b) + (2 : ℝ) ^ (-(b * ((m * d : ℕ) : ℝ))))

/-- thm:pauli (qpbt-paper 08_…tex:1426-1447): soundness of the Pauli basis test. -/
theorem pauli_soundness :
    ∃ a b : ℝ, 1 ≤ a ∧ 0 < b ∧ b < 1 ∧
      ∀ (P : AdmissibleParams) [FieldModel P.q] (ε : ℝ), 0 < ε →
        ∀ S : Strategy (pauliBasisTest P), 1 - ε ≤ S.value →
          ∃ (ιA' ιB' : Type) (_ : Fintype ιA') (_ : DecidableEq ιA')
            (_ : Fintype ιB') (_ : DecidableEq ιB')
            (φA : EuclideanSpace ℂ S.ιA →ₗᵢ[ℂ]
                    EuclideanSpace ℂ (ιA' × PauliRegister P))
            (φB : EuclideanSpace ℂ S.ιB →ₗᵢ[ℂ]
                    EuclideanSpace ℂ (ιB' × PauliRegister P))
            (aux : EuclideanSpace ℂ (ιA' × ιB')), ‖aux‖ = 1 ∧
            -- item 1: ‖φA ⊗ φB ψ − aux ⊗ EPR_q^{⊗M}‖ ≤ δ_qld  (squared distance,
            -- via stateDistSq and deltaQld²; or state with ‖·‖ directly — either
            -- form is acceptable, document the choice)
            ‖isometryTensor φA φB S.ψ - idealState P aux‖
                ≤ deltaQld a b ε P.m P.d P.q ∧
            -- item 2, for both players and both bases, summation over u ∈ F_q^M,
            -- w.r.t. the ideal state; O(·) constants absorbed into a (see (e)8)
            ∀ W : PauliKind,
              (∑ u : PauliRegister P,
                ‖(heteroKron
                    (conjIsometry φA ((S.A (pauliQuestion P W)).effect
                      (PauliAnswer.pauliOutcome u) ...decoded))
                    (1 : Op (ιB' × PauliRegister P))
                  - pauliProjOnA'' P W u).mulVec (idealState P aux)‖ ^ 2)
                ≤ deltaQld a b ε P.m P.d P.q ∧
              (symmetric B-side bound)
```

Supporting definitions in Soundness.lean (all NEW, Lean-only):
`idealState P aux := reindexState prodShuffle (vecTensor aux (eprState (PauliRegister P)))`;
`pauliQuestion P W : (pauliBasisTest P).QuestionA := (PauliType.pauli W, 0)` (the
`(Pauli, W)` question has content `0`, image of the 0-level CL function);
`pauliProjOnA'' P W u : Op ((ιA' × Reg) × (ιB' × Reg))` places `pauliProj W u` on the
`A''` factor, identity elsewhere (and the `B''` analogue). The A-side measurement
outcome family is the sub-family of `S.A` at outcomes `PauliAnswer.pauliOutcome u`
(other constructors carry no mass in the ideal comparison; define the family by
pattern-matching `PauliAnswer → Op` with `0` on the other constructors — this is the
faithful reading of "answer summation over `u ∈ F_q^M`").

## (e) Settled encoding decisions (do not re-derive)

1. **Polynomials — representative convention** (issue #0004, `def:polynomials-degree`):
   polynomial-valued objects are representatives, not function classes. Reuse
   `MIPStarRE.LDT.Preliminaries.polyFunc` where a polynomial *class* is quantified.
   Game *answers* are finite coefficient tuples exactly as printed in the paper
   ("given by its d+1 coefficients"): `Fin (d+1) → K`, resp. `Fin (m*d+1) → K`.
   Do not reuse `LDT.AxisLinePolynomial`/`DiagonalLineAnswer` (the LDT diagonal answer
   is function-encoded and `Parameters`-bundled; a bridge can come later).
   `def:ld-meas`/`PolyMeas` are NOT in this closure — do not build them now.
2. **Distributions — match LDT, not PMF**: the LDT question distributions use
   `MIPStarRE.LDT.Distribution` (Finset-supported, real weights, `Error := ℝ`) with
   `IsProbability`, `avgOver`, `map`, `uniformDistribution`, `uniformOnFinset`
   (`LDT/Basic/Distribution.lean`, `DistributionUniform.lean`; product combinators in
   `DistributionProduct.lean` — verify the exact name before use). All QPBT question
   distributions are `Distribution` values; `PMF` only ever via the existing
   `DistributionPMF` bridge, never in game-facing statements.
3. **Measurements**: use `MIPStarRE.Quantum.Measurement`/`Submeasurement`
   (`Quantum/Measurement.lean`) as the POVM carrier; marginals and the bracket
   notation are `Measurement.postprocess` (already `\leanok` for ch12 `def:bracket`).
   Projectivity via `MIPStarRE.Quantum.IsProj`.
4. **States**: pure states as unit vectors of `EuclideanSpace ℂ ι` (the theorem's
   conclusion needs vector norms, isometries `→ₗᵢ[ℂ]` — reuse
   `Quantum/FiniteHilbert.lean` patterns — and `eprState`). The density-matrix
   `LDT.QuantumState` layer is NOT used in the QPBT games layer.
5. **Field model**: reuse `MIPStarRE.LDT.FieldModel q` (bundled `K ≃ Fin q`). The χ
   map (eq:chi-func) interprets `s : K` as an integer through `FieldModel.equiv`;
   the finite-field trace is the basis-independent `Algebra.trace (ZMod 2) K`
   (= Tr of `Algebra.leftMulMatrix`, i.e. eq:def-trace). The self-dual normal basis
   and `def:binary-representation` are NOT in the statement closure and are deferred
   (see OPEN-6). `canonicalComplement` is defined basis-freely by the pivot
   characterization — `j` is a pivot of `W` iff restricting to coordinates `≤ j`
   increases rank — which agrees with the source's RREF construction by the
   basis-independence noted in `def:canonical-complement` (equivalence proof deferred).
6. **Qudit indexing**: the `M = 2^m` qudits and the vectors `F_q^M` are indexed by
   `Cube m := Fin m → Bool`. Never introduce `Fin (2^m)`; `M` appears only as
   `Fintype.card (Cube m)` in docstrings.
7. **Prose claims inside blueprint definitions become companion lemmas**: CL-level
   assertions ("`L_ALine` is a 2-level CL function"), uniformity of `χ(s)`,
   well-definedness remarks — each a named `sorry` lemma next to the definition, not
   a definitional obligation. Definitions themselves are direct and computable-shaped.
8. **Asymptotic `≈`/O(·) → quantitative functionals**: `def:state-distance` /
   `def:povm-distance` are encoded as explicit real error quantities (`stateDistSq`,
   `opFamilyDistSq`), mirroring how the LDT track already quantifies `≃`/`≈`
   (cf. rem:asymptotic-distance). The implicit universal constants of the blueprint's
   `≈_δ` are absorbed into the existentially quantified constant `a` of
   `pauli_soundness`; record this in the theorem docstring.
9. **Win predicates are `Bool`-valued**, answer alphabets are sum types, and
   "answers not of the prescribed form are rejected" is a predicate clause (match on
   constructor shape). Question alphabets are `Type × ambient-space` pairs — contents
   are full ambient vectors `ι → K` (images of the CL maps), not per-type refined
   types; this matches the blueprint's `(t, L_t(z))` format.
10. **`deltaQld` argument order** is `(ε, m, d, q)` with `0 < b < 1` strict and
    prefactor `a(md)^a` — per rem:delta-qld-argument-order; do not copy the classical
    `δ_ld` shape.

## (f) Out of scope for stage 4.1

- **All proofs**: every lemma/theorem body is `sorry` (marker-free; these are tracked
  skeleton sorries, not unfaithful helpers — no `**Unfaithful:**` markers needed).
- **Imported-statement nodes**: `lem:ld-soundness`, `thm:ms-rigidity` (proof-level
  only), and everything they alone need: `def:ld-meas`, `def:polymeasurements`,
  `def:projective-strategy-general`, `def:consistency`, `def:bracket` re-statement.
- **ch12 calculus**: `lem:symmetric-strat`, `fact:agreement` … `lem:pasting`,
  `lem:close-strategies-have-close-values`, `def:spcc` chain, typed-CL definitions
  (`def:typed-cl-functions`, `def:typed-cl-distributions` — see OPEN-3).
- **ch13 remainder**: `thm:ms-from-ac`, `lem:pauli-completeness`, `cor:pauli-binary`,
  `lem:pauli-binary`, `def:introparams`, `lem:delta-bound`, `def:decoding-map`.
- **ch14–ch16** (observables, combining, extraction) and all complexity material.
- Self-dual/normal basis existence, `def:binary-representation`,
  `def:dual-self-dual-normal-basis`, `lem:downsize_field`, `lem:one`,
  `lem:cancellation`, `lem:twisted-commutation`.
- Blueprint sync: after the skeleton type-checks, add `\lean{…}` + `\leanok` to the
  *statement* environments of the 37 in-track closure nodes (statements only — no
  `\leanok` on proofs), then `leanblueprint web` + `lake exe checkdecls`.

## OPEN items for the orchestrator

- **OPEN-1 (blueprint `\uses` omissions)**: `def:pauli-win-predicate` operationally
  needs the trace (`def:subfield-trace`, via eq:gamma-value) and
  `def:ld-question-distribution` needs the fixed integer identification of `F_q`
  (`def:binary-representation`, via eq:chi-func), but neither appears in those
  statement `\uses` lines; the trace enters the closure only accidentally through
  `lem:pauli-observable-expansion`. Consider patching the `\uses` lines in ch13.
- **OPEN-2 (`lem:pauli-observable-expansion` at statement level)**: `thm:pauli`'s
  `\uses` lists this lemma, yet the statement needs only the projectors of
  `def:generalized-pauli`. The skeleton keeps it (sorry'd) for closure fidelity;
  the orchestrator may instead demote it to proof-level `\uses` in the blueprint.
- **OPEN-3 (typed CL distributions)**: the prose of both question-distribution
  definitions says "typed CL distribution", but `def:typed-cl-functions`/
  `def:typed-cl-distributions` are absent from every statement `\uses` line in the
  closure. The skeleton inlines the construction (graph distribution × uniform seed,
  pushed through the CL maps). If the orchestrator prefers the shared abstraction,
  add the two nodes to the ch13 `\uses` lines and lift the helper into CondLinear.lean.
- **OPEN-4 (`Game.value` as csSup)**: the supremum over strategies of unbounded
  dimension is encoded as an `⨆` over the `Strategy` type (value bounded in `[0,1]`,
  so `Real` csSup is safe); it is carried for `def:tensor-product-value` fidelity but
  unused by `pauli_soundness` (which takes a concrete strategy). Cf. the attainment
  gap `gap:qpbt_symmetrization-attainment` before ever using `Game.value`.
- **OPEN-5 (canonical complement encoding)**: the rank-increase pivot definition
  replaces the source's Gaussian-elimination algorithm (equivalent by the
  basis-independence remark in `def:canonical-complement`); the equivalence proof is
  a deferred obligation. If exact algorithmic fidelity is required later, an RREF
  routine can be added behind the same interface.
- **OPEN-6 (which identification `F_q ≃ Fin q`)**: the skeleton parametrizes the
  game by an arbitrary `FieldModel P.q`, so `pauli_soundness` quantifies over all
  identifications — mildly stronger than the paper, whose game fixes the self-dual
  normal-basis binary representation once and for all. The analysis never uses which
  identification is fixed, but confirm this is acceptable, or require carrying
  `def:binary-representation` (+ self-dual-normal-basis existence, `sorry`) now and
  pinning `FieldModel.equiv` to it.
