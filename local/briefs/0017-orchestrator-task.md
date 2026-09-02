# Task: implement the Stage 4.2 QPBT observables skeleton (issue #17)

You are the orchestrator for GitHub issue #17. Implement the chapter 14 Stage 4.2 Lean
skeleton in the prepared worktree on branch `issue-0017-qpbt-observables-skeleton`.
Issue #16 must already be merged into the branch base.

## Authority and inputs, in order

1. `local/briefs/42-ch14-brief.md`, especially the binding 2026-09-02 operator
   adjudication.
2. `references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:47-679`.
3. `blueprint/src/chapter/ch14_qpbt_observables.tex`.
4. The merged Stage 4.1 API and issue #16's shared foundations.
5. `AGENTS.md` and the project proof-gap policies.

## Scope and ownership

- Implement the ch14 modules and formalizable nodes assigned by the brief.
- Consume issue #16's `Strategy.IsProjective`, `consistencyDefect`, `opDistSq`,
  `LineDesc`/`linePointDist`, error predicates, distribution helpers, and state helpers.
  Do not redeclare or wrap them under a second public name.
- Move `pauliQuestion` from `Test/Soundness.lean` to `Test/PauliBasisTest.lean` before
  importing it, avoiding an import cycle.
- `ProjectiveSetting` wraps an arbitrary heterogeneous `Strategy`; retain distinct
  player spaces and measurement families.
- Do not formalize the source-facing `\notready` symmetry-transfer node. Retain the four
  placements and state each required conclusion explicitly.
- Do not touch ch15/ch16 declarations or workflow files.

## Implementation order

1. Canonical line/evaluation extensions and anticommuting tuple data.
2. Projective strategy setup and typed question/measurement extraction.
3. Strategy observables and win implications.
4. Expanded state, placements, point measurements, and point consistency.
5. Expanded line measurements and line consistency.
6. Blueprint metadata and aggregate imports after the Lean interface stabilizes.

Use `local/bin/dispatch.sh` for disjoint helper sessions. Integrate their commits in
dependency order and reserve independent review for the main-session review gate.

## Proof and fidelity rules

- Definitions have real bodies; only named proposition-valued Stage 4.2 obligations may
  use `sorry`. Add no axioms or bypasses.
- Use `P.model`, `L.model`, `PauliScalar P`, landed `tauObservable`, and `phaseSign`.
- Use the canonical tagged `LineDesc` from issue #16.
- Fold wrong-form strategy answers into a fixed valid output for complete typed
  measurements and bound junk mass separately. Reserve `Option` for evaluation classes.
- Package a real Magic Square strategy for rigidity; a scalar value alone is not enough.
- Quantify hidden constants before parameters and strategies. Prove one concrete
  square-root theorem and derive the source existential wrapper from it.
- Every declaration carries exact blueprint/paper provenance and any required gap marker.

## Validation and handoff

Type-check files in import order, scan for `sorry|axiom`, then run `lake build`,
`leanblueprint web`, and `lake exe checkdecls blueprint/lean_decls`. Confirm the only
proof holes are the brief's tracked statements, the dropped transfer node is not linked
as complete, and `git diff --check` passes. Commit coherent units with issue #17 in the
body. Finish with declaration/proof-hole counts, statement-integrity audit, test
evidence, and the exact ch14 interface handed to issue #18.
