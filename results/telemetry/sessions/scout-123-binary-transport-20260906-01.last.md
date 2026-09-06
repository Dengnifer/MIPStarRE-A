<!-- scout: scout-123-binary-transport-20260906-01 2026-09-06 -->
## Mathlib scouting report — 2026-09-06

**Finding:** there is a self-contained, exact transport packet from any supplied Pauli soundness witness to a qubit witness. It preserves the auxiliary state, state error, and both squared operator distances **exactly**, with no change to the soundness constants. It does not require the missing soundness existence proof.

The principal engineering gap is that the proved binary-isometry theorem uses `Fin L`, while the soundness register uses `Cube P.m`; its useful coordinate-level implementation lemmas are private. Generalizing that existing implementation to an arbitrary finite index type avoids a second formalization.

**Scope and evidence:** inspected local sources at HEAD `b2f252a`. The required `gh_common.py issue-view 123` failed because network sockets are forbidden; therefore issue comments and prior issue-posted scouting could not be checked. This report concerns only the supplied binary-transport task. No extraction construction, global-pair-game estimate, active PR, or source soundness proof was reviewed.

### Mathematical source

- **Corollary `cor:pauli-binary`** — `references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:1470`; its proof is at `references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:1490`. Starting with the qudit soundness isometries, post-compose each local map with the fixed binary-coordinate identification. This converts the EPR register and ideal Pauli projectors without changing the error.
- **Lemma `lem:pauli-binary`** — `references/qpbt-paper/04_preliminaries.tex:1173`; construction at `references/qpbt-paper/04_preliminaries.tex:1202`. The identification sends a computational basis label to its coordinates in the fixed self-dual binary basis. It preserves the paired EPR state and intertwines the generalized projectors with binary tensor-product projectors.
- **Source conditions:** use the fixed self-dual basis, not an arbitrary field bijection. The target has \(M k\) qubits, with \(M=2^m\) and \(q=2^k\). The erroneous final factor range \(j\le q\) is already corrected to \(j\le k\) in `docs/paper-gaps/qpbt_pauli-binary-factor-index.tex:52`.
- **Distance convention** — `references/qpbt-paper/06_nonlocal_games_and_mipstar.tex:258`: the operator comparison is a sum of **squared Euclidean norms on the ideal state**, not matrix operator norm. In the binary corollary, the answer sum remains over \(u\in\mathbb F_q^M\).
- **Blueprint counterparts** — `blueprint/src/chapter/ch11_qpbt_algebra.tex:749` and `blueprint/src/chapter/ch13_qpbt_test.tex:1523`.

### Relevant Mathlib definitions

- `Equiv.piCongrRight` — `.lake/packages/mathlib/Mathlib/Logic/Equiv/Basic.lean:143` — applies the field-coordinate equivalence independently at every register position.
- `Equiv.curry` — `.lake/packages/mathlib/Mathlib/Logic/Equiv/Prod.lean:118` — its inverse converts the curried coordinate array into labels indexed by `ι × Fin basisDim`.
- `Equiv.prodCongr` — `.lake/packages/mathlib/Mathlib/Logic/Equiv/Prod.lean:73` — extends the register relabeling by identity on each auxiliary index, then combines Alice and Bob.
- `LinearIsometryEquiv.piLpCongrLeft` — `.lake/packages/mathlib/Mathlib/Analysis/Normed/Lp/PiLp.lean:865` — **exact match** for the computational-basis permutation on Euclidean space. At `p = 2`, it sends a vector to its coordinates precomposed with the inverse label equivalence.
- `Matrix.reindex` — `.lake/packages/mathlib/Mathlib/LinearAlgebra/Matrix/Defs.lean:502` — forward operator transport by a label equivalence. For `e : ι ≃ κ`, use `Matrix.reindex e e` to send operators on `ι` to operators on `κ`.
- `Matrix.toEuclideanLin` — `.lake/packages/mathlib/Mathlib/Analysis/InnerProductSpace/PiL2.lean:1244` — the matrix action used by the project. Keep this Euclidean-space action; ordinary function-space norms have the wrong norm convention.
- `TensorProduct.congrIsometry` — `.lake/packages/mathlib/Mathlib/Analysis/InnerProductSpace/TensorProduct.lean:255` — **adaptable near-match**, but acts on abstract tensor products rather than the project’s product-indexed Euclidean spaces. No new abstract-tensor identification is needed for this packet.

### Relevant Mathlib lemmas and theorems

- `LinearIsometryEquiv.piLpCongrLeft_apply` — `.lake/packages/mathlib/Mathlib/Analysis/Normed/Lp/PiLp.lean:880` — exposes the coordinate permutation.
- `LinearIsometryEquiv.piLpCongrLeft_symm` — `.lake/packages/mathlib/Mathlib/Analysis/Normed/Lp/PiLp.lean:885` — identifies the inverse map with relabeling by the inverse equivalence.
- `EuclideanSpace.piLpCongrLeft_single` — `.lake/packages/mathlib/Mathlib/Analysis/InnerProductSpace/PiL2.lean:358` — computes images of computational basis vectors; already used by the project’s private permutation-matrix proof.
- `LinearIsometryEquiv.norm_map` — `.lake/packages/mathlib/Mathlib/Analysis/Normed/Operator/LinearIsometry.lean:533`; `LinearIsometryEquiv.map_sub` — `.lake/packages/mathlib/Mathlib/Analysis/Normed/Operator/LinearIsometry.lean:861` — together give exact preservation of state differences.
- `Matrix.submatrix_mulVec_equiv` — `.lake/packages/mathlib/Mathlib/Data/Matrix/Mul.lean:1184` — **exact underlying matrix identity** for transporting operator action:
  ```
  M.submatrix e₁ e₂ *ᵥ v = (M *ᵥ (v ∘ e₂.symm)) ∘ e₁
  ```
  Specialize both coordinate maps to the inverse of the forward register equivalence.
- `Fintype.card_congr` — `.lake/packages/mathlib/Mathlib/Data/Fintype/Card.lean:67` — preserves the EPR normalization coefficient under label equivalence.
- `Fintype.sum_equiv` — generated by `to_additive` at `.lake/packages/mathlib/Mathlib/Algebra/BigOperators/Group/Finset/Defs.lean:718` — transports the finite Fourier sums in the existing projector proof.

These are preferable to new proofs of finite-sum invariance, Euclidean permutation isometry, or matrix-action reindexing.

### Relevant MIPStarRE declarations

**Fixed coordinates and the existing binary theorem**

- `MIPStarRE.QPBT.FixedFieldModel.binaryCoordinates` — `MIPStarRE/QPBT/Algebra/SelfDualBasis.lean:22` — the existing linear equivalence
  ```
  F.K ≃ₗ[ZMod 2] (Fin F.basisDim → ZMod 2).
  ```
- `MIPStarRE.QPBT.kappaVec` — `MIPStarRE/QPBT/Algebra/SelfDualBasisTheorems.lean:147` — already accepts **arbitrary** register index type `ι`; returns `ι × Fin F.basisDim → ZMod 2`.
- `MIPStarRE.QPBT.binTrace_mul_eq_dotProduct` — `MIPStarRE/QPBT/Algebra/SelfDualBasisTheorems.lean:138` — proved self-dual trace-pairing identity needed by the binary projector transport.
- `MIPStarRE.QPBT.exists_qubitIsometry` — `MIPStarRE/QPBT/Algebra/PauliTheorems.lean:718` — **proved, adaptable near-match**. It produces a linear isometry equivalence between the `Fin L` qudit and binary registers, together with exact EPR transport and
  ```
  pauliProj W u =
    conjIsometry φ.symm.toLinearIsometry
      (qubitPauliProj W (kappaVec F u)).
  ```
  This is the **inverse-conjugation** orientation. The packet needs forward transport.
- `MIPStarRE.QPBT.qubitPauliProj` — `MIPStarRE/QPBT/Algebra/PauliTheorems.lean:705` — an abbreviation for the existing tensor-product Pauli projector specialized to `ZMod 2`; do not introduce a second binary projector definition.

The following existing implementation declarations are **private**, hence not downstream APIs to call by their source names:

- `MIPStarRE.QPBT.isometryTensor_piLpCongrLeft_epr` — `MIPStarRE/QPBT/Algebra/PauliTheorems.lean:520` — already proves EPR preservation for an arbitrary finite label equivalence.
- `MIPStarRE.QPBT.conjIsometry_piLpCongrLeft_symm` — `MIPStarRE/QPBT/Algebra/PauliTheorems.lean:552` — already identifies permutation conjugation with matrix reindexing.
- `MIPStarRE.QPBT.quditQubitLabelEquiv` — `MIPStarRE/QPBT/Algebra/PauliTheorems.lean:579` — the desired coordinate equivalence, presently specialized to `Fin L`.
- `MIPStarRE.QPBT.pauliProj_reindex_quditQubitLabelEquiv` — `MIPStarRE/QPBT/Algebra/PauliTheorems.lean:678` — already proves the projector identity through Fourier inversion. Its supporting argument uses finite sums, coordinate linearity, and self-duality, not special properties of `Fin`.

**Soundness carriers and comparison quantities**

- `MIPStarRE.QPBT.PauliRegister` — `MIPStarRE/QPBT/Test/PauliBasisTest.lean:125`; `MIPStarRE.QPBT.QubitRegister` — `MIPStarRE/QPBT/Test/QubitForm.lean:30` — respectively
  ```
  Cube P.m → P.model.K
  Cube P.m × Fin P.model.basisDim → ZMod 2.
  ```
  Cardinal equality with a `Fin` type is not definitional equality.
- `MIPStarRE.QPBT.PauliSoundnessWitness` — `MIPStarRE/QPBT/Test/SoundnessDefs.lean:164`; `MIPStarRE.QPBT.QubitSoundnessWitness` — `MIPStarRE/QPBT/Test/QubitForm.lean:51` — the same auxiliary-space/unit-vector data, with different extracted-register targets.
- `MIPStarRE.QPBT.idealState` — `MIPStarRE/QPBT/Test/SoundnessDefs.lean:85`; `MIPStarRE.QPBT.idealQubitState` — `MIPStarRE/QPBT/Test/QubitForm.lean:35` — both use local-player ordering
  ```
  ((auxA × register) × (auxB × register)).
  ```
- `MIPStarRE.QPBT.pauliOperatorDistanceA` — `MIPStarRE/QPBT/Test/SoundnessDefs.lean:187`; `MIPStarRE.QPBT.pauliOperatorDistanceB` — `MIPStarRE/QPBT/Test/SoundnessDefs.lean:199`.
- `MIPStarRE.QPBT.qubitOperatorDistanceA` — `MIPStarRE/QPBT/Test/QubitForm.lean:113`; `MIPStarRE.QPBT.qubitOperatorDistanceB` — `MIPStarRE/QPBT/Test/QubitForm.lean:124`.

All four distances sum over the same field-valued answer type. Only the Hilbert-space coordinates and corresponding ideal operators change.

**Reusable state and composition APIs**

- `MIPStarRE.QPBT.reindexState` — `MIPStarRE/QPBT/State.lean:31`; `MIPStarRE.QPBT.reindexState_norm_eq` — `MIPStarRE/QPBT/State.lean:86` — exact coordinate transport and norm preservation.
- `MIPStarRE.QPBT.prodShuffle` — `MIPStarRE/QPBT/State.lean:75`; `MIPStarRE.QPBT.vecTensor` — `MIPStarRE/QPBT/State.lean:60` — the existing four-factor shuffle and coordinate tensor.
- `MIPStarRE.QPBT.applyOperatorToState` — `MIPStarRE/QPBT/Games/Defs.lean:210` — exactly `Matrix.toEuclideanLin M ψ`.
- `MIPStarRE.QPBT.MagicSquareRigidity.conjIsometry_comp` — `MIPStarRE/QPBT/Test/MagicSquareTheorems/Rigidity/Dilation.lean:676` — proved, generic:
  ```
  conjIsometry (φ.comp E) M = conjIsometry φ (conjIsometry E M).
  ```
- `MIPStarRE.QPBT.MagicSquareRigidity.isometryTensor_comp` — `MIPStarRE/QPBT/Test/MagicSquareTheorems/Rigidity/Dilation.lean:702` — proved, generic:
  ```
  isometryTensor (φA.comp EA) (φB.comp EB) ψ =
    isometryTensor φA φB (isometryTensor EA EB ψ).
  ```
  These declarations have no strategy, success, or rigidity hypotheses. Their carrier parameters are `Type`, which suffices for the witness structures.
- `MIPStarRE.QPBT.MagicSquareRigidity.norm_isometryTensor` — `MIPStarRE/QPBT/Test/MagicSquareTheorems/Rigidity/GroundSlice.lean:348` — existing generic tensor-isometry norm preservation.
- `MIPStarRE.QPBT.MagicSquareRigidity.applyOperatorToState_leftTensor_conjIsometry` — `MIPStarRE/QPBT/Test/MagicSquareTheorems/Rigidity/GroundSlice.lean:361`; `MIPStarRE.QPBT.MagicSquareRigidity.applyOperatorToState_rightTensor_conjIsometry` — `MIPStarRE/QPBT/Test/MagicSquareTheorems/Rigidity/GroundSlice.lean:380` — existing operator-action intertwining for arbitrary local isometries.

**Important near-miss:** `MIPStarRE.QPBT.opFamilyDistSq_reindex` — `MIPStarRE/QPBT/Games/DistanceTheorems/TensorSupport.lean:334` — reindexes **outcomes**, not Hilbert-space coordinates. It does not establish the required transport, and outcome reindexing is unnecessary here.

### Suggested approach

**Packet boundary.** Separate the definitions currently preceding the corollary into a proposed `MIPStarRE/QPBT/Test/QubitFormDefs.lean`, importing the algebra API and `SoundnessDefs`, not `Soundness`. Put the constructor and transport equalities in a proposed `MIPStarRE/QPBT/Test/QubitFormTransport.lean`. Leave the public corollary’s statement unchanged in `QubitForm.lean`.

This makes independence visible in the import graph. The only algebra work is exposing/generalizing existing coordinate proofs; it should not change the public statement of the source-labelled binary-isometry theorem. No extraction or source-soundness file needs modification.

The following are **proposed signatures**, not implemented or elaborated declarations. Names below are in namespace `MIPStarRE.QPBT`.

**1. Generalize the existing fixed-coordinate equivalence and projector proof.**

Proposed declarations in `MIPStarRE/QPBT/Algebra/PauliTheorems.lean`:

```lean
noncomputable def kappaVecEquiv {q : ℕ} {ι : Type*}
    (F : FixedFieldModel q) :
    (ι → F.K) ≃ (ι × Fin F.basisDim → ZMod 2)

theorem pauliProj_reindex_kappaVecEquiv {q : ℕ} {ι : Type*}
    [Fintype ι] [DecidableEq ι]
    (F : FixedFieldModel q) (W : PauliKind) (u : ι → F.K) :
    Matrix.reindex (kappaVecEquiv F) (kappaVecEquiv F)
      (pauliProj W u) =
        qubitPauliProj W (kappaVec F u)
```

Construct `MIPStarRE.QPBT.kappaVecEquiv` by composing the pointwise field-coordinate equivalence with inverse currying—exactly the existing private construction, replacing `Fin L` by `ι`. Its application should reduce to the existing coordinate-vector function.

For `MIPStarRE.QPBT.pauliProj_reindex_kappaVecEquiv`, generalize the existing private proof rather than repeat the Fourier argument. Preserve the public `Fin L` theorem as a specialization.

**2. Supply the small coordinate-transport interface.**

For the following signatures, all carrier types have `Fintype` and `DecidableEq`; the EPR identity additionally requires `Nonempty` on both EPR carriers.

```lean
theorem reindexState_eprState (e : ι ≃ κ) :
    reindexState (Equiv.prodCongr e e) (eprState ι) =
      eprState κ

theorem applyOperatorToState_reindexState
    (e : ι ≃ κ) (M : Op ι) (ψ : EuclideanSpace ℂ ι) :
    applyOperatorToState (Matrix.reindex e e M) (reindexState e ψ) =
      reindexState e (applyOperatorToState M ψ)
```

Natural location: the proposed `QubitFormTransport.lean`, or a lightweight reusable state-transport module if already being introduced.

- `MIPStarRE.QPBT.reindexState_eprState` is the reindexing form of the existing private EPR result. Its coordinate proof uses equivalence injectivity and equal cardinalities.
- `MIPStarRE.QPBT.applyOperatorToState_reindexState` is a wrapper around Mathlib’s matrix-action reindexing theorem, not a new analytic lemma.
- Also expose a usable permutation-conjugation identity from the existing private proof. Applying its inverse-oriented version to `e.symm` gives the forward equation
  \[
  \operatorname{conjIsometry}(U_e,M)=\operatorname{Matrix.reindex}(e,e,M),
  \]
  where \(U_e\) is the Euclidean coordinate-permutation isometry.
- Identify the tensor of two such permutation isometries with reindexing by their product equivalence. Computational-basis images reduce both sums to single terms.

**3. Construct the binary witness by post-composition.**

For a supplied witness \(w\), set
\[
R=\mathrm{PauliRegister}(P),\qquad Q=\mathrm{QubitRegister}(P),
\]
and let \(e:R\simeq Q\) be the specialization of the coordinate equivalence to `Cube P.m`.

Define
\[
e_A=\mathrm{id}_{w.\iota_A'}\times e,\quad
e_B=\mathrm{id}_{w.\iota_B'}\times e,\quad
e_{AB}=e_A\times e_B.
\]
Let \(U_A,U_B\) be their Euclidean permutation isometries. Preserve both auxiliary types, their instances, the auxiliary vector, and its normalization proof; set
\[
\phi_A^{\mathrm{bit}}=U_A\circ w.\phi_A,\qquad
\phi_B^{\mathrm{bit}}=U_B\circ w.\phi_B.
\]

Proposed constructor:

```lean
noncomputable def PauliSoundnessWitness.toQubit
    {P : AdmissibleParams} {S : Strategy (pauliBasisTest P)}
    (w : PauliSoundnessWitness P S) :
    QubitSoundnessWitness P S
```

In Lean composition order, the new permutation isometry is on the **left**: post-compose the supplied extraction isometry, not the reverse.

**4. Prove the exact shuffled-state identity.**

The required identity is
\[
\operatorname{reindexState}(e_{AB},\operatorname{idealState}(P,w.\mathrm{aux}))
=
\operatorname{idealQubitState}(P,w.\mathrm{aux}).
\]

Both ideal-state definitions are the existing coordinate tensor of `aux` with the EPR vector, shuffled into local-player order. Equivalently, they are obtained from
\[
(\iota_A'\times\iota_B')\times(R\times R)
\]
using the existing four-factor shuffle.

Prove the identity directly at coordinates: the auxiliary factor is unchanged, equality of the two register labels is preserved, and the EPR normalization coefficient is unchanged. No flattening to `Fin (M * k)`, logarithm calculation, or tensor-product reassociation framework is needed.

**5. Transport the lifted operators, then their action.**

Prove forward matrix-reindex identities for Alice and Bob separately:

- transported lifted effect = the lifted effect built from the post-composed isometry;
- transported ideal projector = the corresponding qubit ideal projector.

Use the existing conjugation-composition theorem and permutation-conjugation identity. The old lifted effects are written with conditionals, while the qubit versions use a Kronecker product with identity; normalize this harmless presentation difference pointwise.

The projector identity from step 1 handles the extracted register. Product-equivalence injectivity handles the identity-factor equality guards. Then apply the operator-action reindexing helper to the **difference** of those operators and to the ideal state.

**6. End the packet with three unconditional equality lemmas.**

Proposed declarations in `MIPStarRE/QPBT/Test/QubitFormTransport.lean`:

```lean
theorem qubit_state_error_to_qubit
    (P : AdmissibleParams) (S : Strategy (pauliBasisTest P))
    (w : PauliSoundnessWitness P S) :
    ‖isometryTensor w.toQubit.φA w.toQubit.φB S.ψ -
        idealQubitState P w.toQubit.aux‖ =
      ‖isometryTensor w.φA w.φB S.ψ - idealState P w.aux‖

theorem qubit_operator_distance_a_to_qubit
    (P : AdmissibleParams) (S : Strategy (pauliBasisTest P))
    (w : PauliSoundnessWitness P S) (W : PauliKind) :
    qubitOperatorDistanceA P S w.toQubit W =
      pauliOperatorDistanceA P S w W

theorem qubit_operator_distance_b_to_qubit
    (P : AdmissibleParams) (S : Strategy (pauliBasisTest P))
    (w : PauliSoundnessWitness P S) (W : PauliKind) :
    qubitOperatorDistanceB P S w.toQubit W =
      pauliOperatorDistanceB P S w W
```

Thus the packet’s endpoints are the proposed full names `MIPStarRE.QPBT.qubit_state_error_to_qubit`, `MIPStarRE.QPBT.qubit_operator_distance_a_to_qubit`, and `MIPStarRE.QPBT.qubit_operator_distance_b_to_qubit`.

For the state identity, combine composition, the shuffled-state identity, linearity, and norm preservation. For each distance, prove equality termwise and sum over the unchanged field-valued answers.

**Statement-integrity conditions**

- No success assumption, error parameter, or bound is needed by these equality lemmas.
- The witness constructor consumes existing existential data; it does not assume any missing soundness conclusion.
- The fixed field model supplies its basis and self-duality internally. Do not add a newly quantified basis, field identification, or projector-intertwining hypothesis.
- The coordinate map is an **equivalence**. Do not silently use \(UU^\dagger=I\) for a merely injective isometry.
- EPR preservation here uses the computational-basis permutation. \(U\otimes U\) does **not** preserve EPR for an arbitrary complex unitary.
- Preserve the ideal reference state and squared-distance convention. No triangle inequality or error inflation is necessary.
- The eventual public-corollary adapter retains the original universal constants and all original hypotheses. It obtains the qudit witness from the source theorem and rewrites these three equalities. Adding a witness or transport hypothesis to the public corollary would be unfaithful.

### Gaps to fill

- **Missing public arbitrary-index coordinate API:** searched the coordinate-equivalence, binary-isometry, and projector-reindex declarations. The mathematical proof exists privately for `Fin L`; no usable public version for the actual cube-indexed register was found.
- **Missing witness constructor and exact comparison equalities:** searched both witness types, both ideal-state definitions, and all distance consumers. No existing conversion or the three endpoint equalities was found.
- **Missing small wrapper for simultaneous state/operator coordinate transport:** searched reindexing, matrix action, permutation conjugation, and distance APIs. Mathlib supplies the underlying matrix theorem; the project has no directly usable wrapper in its state vocabulary.
- **Not part of this packet:** `MIPStarRE.QPBT.pauli_soundness` — `MIPStarRE/QPBT/Test/Soundness.lean:38` — remains open, with `sorry` at line 49. `MIPStarRE.QPBT.pauli_soundness_qubit` — `MIPStarRE/QPBT/Test/QubitForm.lean:140` — remains open, with `sorry` at line 153. Closing the transport packet does not prove source soundness.

**Verdict:** this is an exact construction/API-exposure task, not a new analytic soundness estimate. Its remaining mathematical obligation is to generalize and connect already proved coordinate identities—not to assume a new transport package.

### Searched

- Read the prescribed committed-`main` scout prompts, repository instructions, local workflow documentation, paper passages, matching blueprint entries, and target Lean files.
- Consulted `docs/api_surface.md:1`, its transport/tensor sections, and prior separate-space and preliminaries scouting under `audits/`; these did not supply a binary-witness conversion.
- Searched Mathlib by module path, name, and type shape: `piLpCongrLeft`, `piCongrRight`, `curry`, `prodCongr`, `submatrix_mulVec_equiv`, `mulVecLin_reindex`, matrix reindexing, tensor isometries, norm preservation, finite-sum transport, and EPR/Pauli terminology.
- Searched local algebra, state, games/distance, Quantum, and LDT basic APIs for `kappaVec`, binary isometries, EPR reindexing, conjugation/tensor composition, action intertwining, witness conversion, and distance invariance.
- **Validation:** `lake env lean MIPStarRE/QPBT/State.lean` passed without producing artifacts. Read-only stdin checks confirmed the cached public algebra API; `#print axioms MIPStarRE.QPBT.exists_qubitIsometry` reported only `propext`, `Classical.choice`, and `Quot.sound`.
- **Validation limitation:** `SoundnessDefs`, `Dilation`, and `GroundSlice` compiled objects are absent, and the cached `State` object lacks the newer norm lemma present in source. Their current signatures and proofs were source-inspected; proposed signatures were not elaborated. No cache regeneration or build was attempted.
- The targeted `sorry|axiom` scans found no holes in the inspected algebra, state, soundness-definition, or generic composition/support files; the two source-facing soundness theorems remain the explicitly noted open sites. No files, branches, issue comments, or workflow state were changed.