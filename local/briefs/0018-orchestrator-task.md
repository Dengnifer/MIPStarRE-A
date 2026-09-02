# Task: implement the Stage 4.2 QPBT combining skeleton (issue #18)

You are the orchestrator for GitHub issue #18. Implement the chapter 15 Stage 4.2 Lean
skeleton in the prepared worktree on branch `issue-0018-qpbt-combining-skeleton`.
Issues #16 and #17 must already be merged into the branch base.

## Authority and inputs, in order

1. `local/briefs/42-ch15-brief.md`, especially the binding 2026-09-02 operator
   adjudication.
2. `references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:680-1414`.
3. `blueprint/src/chapter/ch15_qpbt_combining.tex`.
4. The merged Stage 4.1, residual, and ch14 APIs.
5. `AGENTS.md`, `docs/paper-gaps/qpbt_ld-dimension-divisibility.tex`, and
   `docs/paper-gaps/qpbt_combined-lines-error-term.tex`.

## Scope and ownership

- Implement all ch15 modules, witness structures, and formalizable nodes in the brief.
- Expose `Poly P` and `PolyPair P` as noncomputable aliases of the actual bounded
  `polyFunc` subtype and its product. Consume issue #16's generic `Fintype` and the
  existing derived `DecidableEq`; do not replace the public outcome type or define
  competing instances.
- Consume the original seed-bearing `LineDesc` and `linePointDist` from issue #16.
- Own the separate `DirectLineDesc`, `directLinePointDist`, `directLdGame`, and directly
  indexed low-degree soundness obligation used at dimension `2 * P.m + 2`.
- Do not touch extraction declarations or workflow files.

## Implementation order

1. Polynomial aliases, direct-index line/game layer, and combining definitions.
2. Witness structures with explicit errors and no hidden proof inputs.
3. Linearity import and combined point/line constructions.
4. Restricted distributions, subline witness, and the three subline claims.
5. Source and established qld-4-13 statements, then the global-pair witness.
6. Blueprint metadata and aggregate imports after the Lean interface stabilizes.

Use `local/bin/dispatch.sh` for disjoint helper sessions. Keep direct-index work,
polynomial infrastructure, and witness statements under explicit owners.

## Proof and fidelity rules

- Definitions have real bodies; only named proposition-valued Stage 4.2 obligations may
  use `sorry`. Add no axioms or bypasses.
- Add no `(2 * P.m + 2) ∣ P.q` hypothesis to a source-labelled theorem. The direct-index
  layer is the faithful repair; `_of_dvd` bridges are Lean-only.
- Define `combineLinePoly` from explicit affine data and state its specification under
  compatibility. Do not use a junk fallback.
- Keep the paper's qld-4-13 error theorem separate from the established weaker result.
  Only the latter may feed a conditional Lean route, with the documented gap status.
- Use the heterogeneous ch14 setting and canonical fixed model throughout.
- Every statement carries exact source provenance and required faithfulness markers.

## Validation and handoff

Type-check files in import order, scan for `sorry|axiom`, then run `lake build`,
`leanblueprint web`, and `lake exe checkdecls blueprint/lean_decls`. Audit both line
carriers, verify no source theorem is vacuous through divisibility, and run
`git diff --check`. Commit coherent units with issue #18 in the body. Finish with
declaration/proof-hole counts, statement-integrity audit, paper-gap status, test
evidence, and the exact `GlobalPairWitness` interface handed to issue #19.
