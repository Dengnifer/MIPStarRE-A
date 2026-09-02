# Task: implement the Stage 4.2 residual QPBT skeleton (issue #16)

You are the orchestrator for GitHub issue #16. Implement the residual Stage 4.2 Lean
skeleton for QPBT chapters 11--13 in the prepared worktree on branch
`issue-0016-qpbt-residual-skeleton`.

## Authority and inputs, in order

1. `local/briefs/42-residual-brief.md`, especially the binding 2026-09-02 operator
   adjudication. Earlier sketches in that file lose whenever they conflict with it.
2. The paper mirrors listed in that brief. Read the relevant source range before
   stating each declaration.
3. `blueprint/src/chapter/ch11_qpbt_algebra.tex` through
   `blueprint/src/chapter/ch13_qpbt_test.tex`.
4. The Stage 4.1 QPBT API merged by PR #5. Reuse its names and canonical fixed model.
5. `AGENTS.md` and the project proof-gap policies.

## Scope and ownership

- Implement all residual nodes and files assigned by the brief.
- This issue is the sole owner of `Strategy.IsProjective`, `SymmetricGame`,
  state-dependent `consistencyDefect`, `LineDesc`/`linePointDist`, `opDistSq`,
  `IsPolyErr`/`IsPolyErr₂`, and shared distribution helpers.
- Own a generic `Fintype` instance for the bounded `polyFunc` subtype.
  Reuse the `Module.finite_of_finite` plus `Fintype.ofFinite` construction already used
  in `LDT/Basic/ParametersFiniteAnswers.lean`; do not build a coefficient equivalence.
  The existing subtype `DecidableEq` resolves from `DecidableEq K`; do not add a
  competing instance. Declare the dependent aliases noncomputable. `PolyMeas` uses this
  actual subtype, and issue #18 consumes the infrastructure for `Poly P` and
  `PolyPair P`.
- Add `MIPStarRE/QPBT/State.lean` as a dependency-light leaf. Move
  `conjIsometry`, `reindexState`, and `isometryTensor` there from
  `Test/Soundness.lean`, preserving their public names and updating imports. Generalize
  `isometryTensor` to arbitrary finite codomain indices while preserving existing uses.
  Define the real coordinate-vector tensor `vecTensor` and the four-factor
  `prodShuffle` equivalence in the same leaf. Ch14 consumes both names.
- Own the tagged canonical `LineDesc` required by issue #17, including canonical-base
  and diagonal-prefix invariants. Do not implement it as `Point × Point`.
- Own generic ch11 decoding and basis/trace lemmas, their canonical QPBT
  specializations, and `FixedFieldModel.binaryCoordinates`. Keep the latter distinct
  from numeric `binaryRepresentation`. Do not add `SelfDualNormalRep` or another basis
  input to QPBT/test-facing theorems.
- Define the source-general `PolyMeasFamily` and its constant `PolyMeasTuple`
  specialization.
- State faithful general-prime versions of `lem:twisted-commutation` and
  `lem:cancellation` using `MIPStarRE.LDT.Preliminaries.ffChar`. Keep the landed
  characteristic-two declarations as separately named QPBT specializations; do not link
  a binary specialization to either unrestricted blueprint node.
- Do not add ch15's `DirectLineDesc` or direct-index game; issue #18 owns that repair.
- Do not touch workflow code, protocols, or unrelated LDT files.

## Implementation order

1. Neutral state, polynomial finiteness, error, distribution, distance, and strategy
   foundations.
2. Residual ch11 algebra and canonical-model bridges.
3. Residual ch12 game calculus and typed conditionally linear infrastructure.
4. Residual ch13 low-degree, Magic Square, completeness, qubit, and parameter modules.
5. Blueprint metadata and aggregate imports after every Lean module type-checks.

Helper sessions may work on independent file groups, but start them only through
`local/bin/dispatch.sh` and keep their ownership disjoint. The orchestrator integrates
and verifies every result; no session reviews its own diff.

## Proof and fidelity rules

- Definitions have real bodies. `sorry` is permitted only in the proposition-valued
  Stage 4.2 obligations named by the brief. Add no axioms or kernel bypasses.
- Remove obsolete `[FieldModel ...]` binders. Use `P.model`, `L.model`,
  `PauliScalar P`, and `ScalarQ L`.
- Implement the general-prime Pauli source statements with `ffChar`; no bridge hypothesis
  is permitted. Create and cite
  `docs/paper-gaps/qpbt_characteristic-two-pauli-scope.tex` to document the separate
  binary consumer layer and remaining landed-layer generalization debt.
- Keep the exact source and established symmetrization statements separate.
- Keep `deltaLd` distinct from `deltaQld`.
- Encode `AreCloseStrategies` on bundled strategies with explicit common-index
  equalities and transports, matching the source's common Hilbert spaces.
- Give `abs_value_sub_le_of_areClose` a separate transported state-equality hypothesis,
  matching the paper's requirement that the two strategies use the same state.
- State `exists_ms_perfect_strategy_of_anticommuting` over an arbitrary finite nonempty
  local index, without a field, model, or QPBT parameter.
- Quantify the constants in `exists_ms_rigidity` and
  `abs_value_sub_le_of_areClose`, `opDistSq_commutator_le`, and
  `consistencyDefect_sandwich_le` before every strategy and error parameter; a
  per-instance constant or unsupported constant `1` is not a faithful encoding of
  universal `O(·)`.
- Preserve `0 ≤ ε` in `pauli_soundness_qubit` and use only the model and basis stored in
  `P.model`, with bit dimension `P.model.basisDim`.
- Every significant declaration has a docstring with blueprint label, paper file and
  line range, and any required `**Local fix:**`, `**Scope restriction:**`, or gap note.

## Validation and handoff

Run `lake env lean` for each file in import order, scan every edited file for
`sorry|axiom`, then run `lake build`, `leanblueprint web`, and
`lake exe checkdecls blueprint/lean_decls`. Confirm no definition body contains
`sorry`, `git diff --check` passes, and direct `\uses` metadata matches public
statements. Commit coherent units with issue #16 in the body. Finish with declaration
and proof-hole counts, a statement-integrity audit, paper-gap inventory, test evidence,
and the exact interface handed to issue #17.
