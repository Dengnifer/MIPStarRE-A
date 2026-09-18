---
title: "Extraction register transport"
date: 2026-09-06
purpose: >
  Record the exact register, state, and operator transport identities for the
  extraction argument, their explicit hypotheses, and their validation evidence.
issue: "#245"
pr: "#253"
---

# Extraction register transport — packet #245

## Scope and source

This packet adds `MIPStarRE/QPBT/Extraction/RegisterTransport.lean`, this audit,
a formalization-support section in
`blueprint/src/chapter/ch16_qpbt_extraction.tex`, and the re-export of the new
leaf from `MIPStarRE/QPBT.lean`. The starting revision is `a61ee557b33a`. No
paper-labelled theorem and no existing definition is changed.

The mathematical source is `lem:qld-unitary` in
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1666-1858`,
read before the corresponding entry in
`blueprint/src/chapter/ch16_qpbt_extraction.tex`. The relevant identifications
are the six registers and two local blocks, the auxiliary/EPR factorization
at lines 1769–1784, and the one-side operator placements in
`eq:qld-unitary-6` through `eq:qld-unitary-9`.

These are formalization-only coordinate identities supporting that argument,
not a proof of its extraction witness or either approximation estimate.

## Register identifications

Write `V = PauliRegister params`, `A₀ = ιA × V`, and `B₀ = ιB × V`.
The existing definitions retain independent original player carriers `ιA`
and `ιB`. No equality of these spaces is introduced.

The new `extractionEprFirstEquiv` composes `sixRegExtractionEquiv` with
`Equiv.prodCongr` of the two local factor swaps. Explicitly,

```text
((a, (a', a'')), (b, (b', b''))) ↦ ((a'', (a, a')), (b'', (b, b'))).
```

Its codomain is `(V × A₀) × (V × B₀)`, exactly the carrier in the already
proved `MagicSquareRigidity.exists_unit_residual`.
`extractionEprFirstIsometry` uses Mathlib's
`LinearIsometryEquiv.piLpCongrLeft`, rather than constructing another norm
preservation proof. The general identity
`reindexState_eq_piLpCongrLeft` identifies that isometry with the project's
existing coordinate operation.

For an equivalence `equiv : dom ≃ cod`, state transport goes from `dom` to
`cod`, whereas `reindexOp equiv` transports operators from `cod` to `dom`.
`applyOperatorToState_reindexOp` proves the action identity with precisely
these directions, using `Matrix.submatrix_mulVec_equiv`:

```text
apply (reindexOp equiv operator) state
  = reindexState equiv.symm (apply operator (reindexState equiv state)).
```

Inverse cancellation, subtraction, vector distance, real quadratic forms,
and averaged operator-family distance then follow from the same isometry.
The family-distance identity is exact for arbitrary operators and states;
there is no positivity, unit-state, consistency, or answer-cardinality premise.

## Existing normalization and isometry results reused

`ProjectiveSetting.reindexState_idealExpState` proves that transporting
`setting.idealExpState aux` by the new permutation gives
`reindexState prodShuffle (vecTensor (eprState V) aux)`.
`norm_sub_idealExpState_eq` identifies the two corresponding distances for
every state and every auxiliary vector, including zero.

`extractionAuxReference` is the explicitly constructed vector
`reindexState prodShuffle (vecTensor setting.toStrategy.ψ (eprState V))`
on `A₀ × B₀`. Its norm is one by the existing tensor, reindexing, EPR, and
strategy norm identities. It is not asserted to approximate the transformed
state; it supplies the normalized reference vector required by
`MagicSquareRigidity.exists_unit_residual` in its zero-residual case.

A later construction can therefore use that existing normalization theorem
on the permuted state and its partially contracted auxiliary vector, then
rewrite the conclusion back using `norm_sub_idealExpState_eq`. This packet
neither reproves normalization nor introduces another existence theorem.
`JointState.lean`, which exports the normalization theorem, is needed only
by that consumer, not by this transport module.

`reindexState_applyBoth` gives the block-coordinate action directly.
`applyBoth_eq_isometryTensor` identifies it with the established heterogeneous
tensor-isometry action via
`MagicSquareRigidity.isometryTensor_eq_toEuclideanLin`.
`applyBoth_norm` reuses the existing rectangular matrix theorem
`MagicSquareRigidity.norm_toEuclideanLin_of_conjTranspose_mul_eq_one`.
It assumes only the explicit matrix equations `Aᴴ * A = 1` and `Bᴴ * B = 1`;
it does not assert these equations for the concrete swap operators.

## Operator placements

The new placement API proves:

- `placePlayer_eq_placeSide`: adjoining identities on the player's two
  Pauli registers gives the original-player placement.
- `placeExtractedRegister_eq_placeSide`: the existing crossed placement of
  an extracted-register operator equals block placement of `1 ⊗ operator`.
- `placeBoth_mul`, `placeBoth_conjTranspose`, and `conjBy_placeBoth`: block
  multiplication, adjoints, and conjugation respect the tensor factors.
- `conjBy_placeSide`: conjugation of two operators on the same block remains
  on that block, without a unitarity assumption.
- `conjBy_placeBoth_placeSide`: simultaneous conjugation equals conjugation
  on the selected side when the two given operators satisfy the explicit
  right-unitary equations.

The matrix reindexing and tensor multiplication steps use Mathlib's
`Matrix.submatrix_mul_equiv`, `Matrix.conjTranspose_reindex`, and
`Matrix.conjTranspose_kronecker`, together with the existing `heteroKron`
API. The concrete controlled-unitary sums are not expanded or assumed proved.

## Statement integrity

- **Paper assumptions:** the surrounding extraction argument has the fixed
  strategy, finite registers, and the concrete local swap unitaries proved
  earlier in its proof.
- **Lean assumptions:** the new general transport lemmas require finite
  coordinate carriers and an equivalence. Concrete register lemmas use the
  existing `AdmissibleParams` and `ProjectiveSetting`. Only `applyBoth_norm`
  and simultaneous one-side conjugation require explicit left-isometry or
  right-unitarity equations, respectively, for arbitrary block operators.
- **Paper conclusion:** register reassociation leaves state norms and
  operator actions unchanged; the larger source theorem additionally
  constructs a normalized approximate EPR factor and measurement estimates.
- **Lean conclusion:** exact register, action, placement, and norm identities
  only. The auxiliary reference is a unit vector, not an extraction witness.
  No approximation estimate or source-labelled existence claim is added.
- **Verdict:** exact formalization-only identities with finite-carrier
  boundary conditions. No source theorem is weakened or given new premises.

The A1–A6 self-check finds no conclusion-shaped hypothesis, replacement
definition hiding a source claim, zero-fallback construction, trivial
extraction witness, Mathlib bypass, or external statement assumption.
The definitional identification of reindexing with Mathlib's isometry connects
two independently existing operations; it does not redefine a paper claim.

## Validation and remaining obligations

- `lake env lean MIPStarRE/QPBT/Extraction/Defs.lean` succeeds with the two
  pre-existing warnings at `tauDotProj_isProj` and `sum_tauDotProj_eq_one`.
  Those obligations remain tracked by issue #47 and are not used by this API.
- `lake env lean MIPStarRE/QPBT/Extraction/RegisterTransport.lean` succeeds
  without errors or warnings. Its `.olean` is also generated and checked in
  this worktree's private build directory.
- `rg -n 'sorry|axiom' MIPStarRE/QPBT/Extraction/RegisterTransport.lean`
  has no matches. The broader forbidden-token scan also has no matches.
- A scratch import checks all 21 new declarations with `#print axioms`:
  only `propext`, `Classical.choice`, and `Quot.sound` occur. The same check
  succeeds for the existing `MagicSquareRigidity.exists_unit_residual`.
  Two compile-time examples verify the concrete bundled-isometry action
  and its ideal-state distance interface.
- The module's own project imports are exactly `Extraction.Defs`,
  `Extraction.EPRState` and `Test.MagicSquareTheorems.Rigidity.GroundSlice`, and
  the import graph has no cycle. No extraction consumer such as `Unitary.lean`
  is imported.
- `lake build MIPStarRE.QPBT.Extraction.RegisterTransport` succeeds at the exact
  head. The machine-wide full build is left to the pull-request check rather
  than run by hand.
- Hook installation and verification succeed. Runtime checks and logs are
  under `~/.cache/mipstarre-dev/scratch/prover-245-register-transport/`.

There is no remaining proof obligation or mathematical blocker in packet
#245. The EPR partial contraction and projection estimate, concrete swap
unitarity and conjugation, consistency estimates, and dimension-independent
measurement comparison remain outside this module. The source corrections
documented in `docs/paper-gaps/qpbt_extraction-transfer.tex` are not needed
for these exact coordinate identities. Downstream work should import this
leaf explicitly and discharge its concrete unitary equations using the
separately owned algebra results.

## Amendment — 2026-09-18, review round of 2026-09-14

This amendment records the state of the packet at the exact head published
after the marked review of 2026-09-14, which the statements above now describe.

- Scope. The diff touches `MIPStarRE/QPBT/Extraction/RegisterTransport.lean`,
  this audit, `blueprint/src/chapter/ch16_qpbt_extraction.tex`,
  `MIPStarRE/QPBT.lean` (one re-export line), and the append-only telemetry
  record. The earlier claim that no blueprint entry and no shared import file
  changed described the first packet only and has been corrected above.
- Declaration count. The module defines 21 declarations, 1 definition and 20
  theorems. The earlier count of 28 predates the withdrawal of the duplicated
  `psiHat_norm` and of `stateQForm_reindexState`; `ProjectiveSetting.psiHat_norm`
  now lives only in `MIPStarRE/QPBT/Observables/ExpandedPlacement.lean`.
- Reuse of `Extraction.EPRState`. Refreshing onto `main` showed that
  `MIPStarRE/QPBT/Extraction/EPRState.lean` now carries
  `extractionEprFirstEquiv`, `ProjectiveSetting.reindexState_idealExpState`,
  `ProjectiveSetting.idealExpState_norm`,
  `ProjectiveSetting.extractionAuxReference` and
  `ProjectiveSetting.extractionAuxReference_norm` with the same statements. This
  module's five copies were deleted and `Extraction.EPRState` is imported
  instead, so each of these declarations has exactly one definition in the
  project. The blueprint nodes keep their `\lean` tags, which now resolve to the
  declarations on `main`.
- Warnings. The stale transitive import of `Observables.ExpandedPlacement` and
  the unused `BigOperators` scope were removed, and the file-wide
  `open scoped Classical` was narrowed to the four declarations that need
  classical decidability, each with a declaration-scoped `open scoped Classical
  in`. The module now builds with no warning of its own; in particular the
  `style.openClassical` warning reported by the review is gone.
- Build. `lake build MIPStarRE.QPBT.Extraction.RegisterTransport` succeeds at
  the exact head.
- Blueprint. The section now carries a definition node for the block
  reassociation `sixRegExtractionEquiv` and one for the public
  `extractionAuxReference`; the placement lemma states its placement identity
  for an arbitrary operator, as the Lean statement does; and the statement and
  proof dependencies name the block reassociation, the operator-family
  distance, the EPR pair and the transport-support lemma actually used, with
  the swap-unitary definition removed from the dependencies.
