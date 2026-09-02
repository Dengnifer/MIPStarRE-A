# Task: implement the Stage 4.2 QPBT extraction skeleton (issue #19)

You are the orchestrator for GitHub issue #19. Implement the chapter 16 Stage 4.2 Lean
skeleton in the prepared worktree on branch `issue-0019-qpbt-extraction-skeleton`.
Issues #16, #17, and #18 must already be merged into the branch base.

## Authority and inputs, in order

1. `local/briefs/42-ch16-brief.md`, especially the binding 2026-09-02 operator
   adjudication.
2. `references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1415-1877`.
3. `blueprint/src/chapter/ch16_qpbt_extraction.tex`.
4. The merged Stage 4.1, residual, ch14, and ch15 APIs.
5. `AGENTS.md` and every QPBT paper-gap note named by the brief.

## Scope and ownership

- Implement all ten ch16 nodes and their named companion declarations.
- Consume issue #16's decoding/binary-representation views, `opDistSq`, distribution
  helpers, and neutral state helpers; consume issue #18's unguarded
  `GlobalPairWitness` with outcome `PolyPair P`.
- Use explicit player-side placements over the heterogeneous ch14 strategy.
- Use the basis and binary representation stored in `P.model`. Do not add an explicit
  basis parameter or a `SelfDualNormalBasis` carrier.
- This issue does not prove `pauli_soundness`; it must expose everything Stage 4.3 needs.
- Do not touch workflow files or unrelated LDT modules.

## Implementation order

1. Decoding-facing marginal and projector definitions.
2. `tildeM`, extracted observables, and their product/phase statements.
3. Combined-point consistency and extracted-observable consistency.
4. Swap unitary and conjugation statements.
5. `ExtractionWitness`, error comparison, and Stage 4.3 transfer interface.
6. Paper-gap notes, blueprint metadata, and aggregate imports after Lean stabilizes.

Use `local/bin/dispatch.sh` for disjoint helper sessions and integrate in dependency
order. Keep the final review in a separate reviewer session.

## Proof and fidelity rules

- Definitions have real bodies; only named proposition-valued Stage 4.2 obligations may
  use `sorry`. Add no axioms or bypasses.
- The decoding dot-product identity requires `IsEncoding`; general outcomes route
  through the non-encoding-mass obligation.
- Retain the actual cross-basis phase theorem with a `**Local fix:**` marker and a
  dedicated paper-gap note.
- Keep the source's arbitrary bipartite strategy; state all player-side conclusions.
- The extraction witness exposes only concrete derived swap unitaries, transformed-state
  data, and proved comparison conclusions. It must not contain residual, bridge,
  hypothesis, or assumed-transfer fields. Stage 4.3 proves the named
  range-projection/isometry transfer lemma from those data and conclusions.
- Every statement carries exact blueprint/paper provenance and required gap markers.

## Validation and handoff

Type-check files in import order, scan for `sorry|axiom`, then run `lake build`,
`leanblueprint web`, and `lake exe checkdecls blueprint/lean_decls`. Confirm the fixed
basis is not re-quantified, every decoding use has the right hypothesis, required gap
notes render, and `git diff --check` passes. Commit coherent units with issue #19 in the
body. Finish with declaration/proof-hole counts, statement-integrity audit, test
evidence, and the exact Stage 4.3 frontier leading to `pauli_soundness`.
