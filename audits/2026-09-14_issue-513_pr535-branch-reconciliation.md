---
title: "PR535 branch reconciliation for the global polynomial-pair theorem"
date: 2026-09-14
purpose: "Receipt for the bounded reconciliation of the published PR535 branch"
issue: "#513"
pull_request: "#535"
status: complete
---

# Scope

This reconciliation preserves the published PR535 history and the completed
source construction of `exists_globalPairWitness`. It introduces no new
mathematical scope, theorem hypothesis, runtime change, publication, CI run, or
independent review.

# Git Provenance

- Published PR535 parent: `1744bd9533055b9b43af9a8d46906cbafb69afdd`.
- Completed source parent: `ac1be4b90f11edd7027f243eaa2a1a5db01da277`.
- Best merge base: `bc7d69bdd2d82cbfa325c3f81588b58999ce6f0d`.
- Reconciled merge: `e2750c925960fbfe98ff54fb157afadd0d2c9a3e`.
- Reconciled tree: `add85f4b240ad63cf8611dc2c078ad0e0605dba7`.

The merge was created normally with the published PR535 head as first parent
and the completed source as second parent. Both parent histories are ancestors
of the reconciled merge. The final branch head is the receipt commit immediately
following this merge and is recorded by Git and the session handoff.

# Path Accounting

Relative to the published first parent, the merge changes 768 paths: 60 under
`MIPStarRE/`, 9 under `audits/`, 1 blueprint chapter, 3 paper-gap documents,
2 local briefs, and 693 telemetry paths. Of the paths changed from the common
base, 764 were source-only and match the completed source blobs exactly. The
sole target-only path,
`audits/2026-09-12_issue-513_pair-completion.md`, matches the published PR535
blob exactly.

Four paths changed on both parents. Git merged
`blueprint/src/chapter/ch15_qpbt_combining.tex` and
`results/telemetry/events.md` without a textual conflict. The two manual
resolutions were:

- `MIPStarRE/QPBT/Combining/Apply.lean`: retain the completed source proof and
  its imports, together with the explicit target import and documentation for
  the independent completion estimates.
- `MIPStarRE/QPBT/Combining/PairCompletion.lean`: retain the common algebraic
  construction, source provenance, and the target-only proved evaluation and
  averaged consistency-defect estimates.

# Validation

- `lake env lean MIPStarRE/QPBT/Combining/PairCompletion.lean` passed.
- The focused target `lake build MIPStarRE.QPBT.Combining.Apply` passed.
- `lake env lean MIPStarRE/QPBT/Combining/Apply.lean` passed with only its three
  pre-existing, separate line-obligation warnings.
- The complete signature, `GlobalPairWitness` field expansion, and thirteen
  axiom queries are byte-identical to the completed source log: 153259 bytes,
  SHA-256 `8c7ed42394c055d9063d4b96efa5ec74fca951f84d7a65ec6b94abc9dc562228`.
  Every queried closure contains exactly `propext`, `Classical.choice`, and
  `Quot.sound`; no closure contains `sorryAx`.
- `git diff --check`, the pending and committed merge-loss guards, and the
  normal pre-commit and reference-transaction hooks passed.

No full build, canonical CI, independent review, push, or GitHub mutation was
performed.

# Statement Integrity

Paper assumptions: universal constants followed by admissible parameters, a
positive strategy error, and a projective strategy, as in `lem:qld-4-7` of
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1267-1404`.

Lean assumptions: unchanged `AdmissibleParams`, positive error, and
`ProjectiveSetting`, with no supplied-witness or construction premise.

Paper conclusion: projective global polynomial-pair measurements on both
expanded local spaces, with point consistency for both Pauli bases and both
players.

Lean conclusion: unchanged `GlobalPairWitness` at `deltaQld`, whose quantified
Alice and Bob consistency fields give those four conclusions.

Verdict: faithful statement with unchanged boundary hypotheses and conclusion.
