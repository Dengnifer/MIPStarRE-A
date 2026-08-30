---
id: "0002"
title: "Blueprint: QPBT chapters and dependency graph"
state: "open"
state_reason: null
parent: "0001"
children: []
labels: ["blueprint-only", "documentation", "formalization", "qpbt-test"]
pinned: false
created: "2026-08-30T03:03:48Z"
updated: "2026-08-30T03:03:48Z"
agent_session: null
---

### Precise mathematical statement

<!-- required -->
Name the theorem, lemma, definition, or construction and state its content.
For example: Lemma 5.3 (Pauli basis test soundness), with the hypotheses on the
number of qubits, the error parameter, and the strategy stated explicitly.

### Mathematical source

<!-- required: path, line, label, and a short quotation or precise paraphrase.
     Replace the placeholders with a real file under references/ (use
     `ls references/*/` for the live mirror layout) and a real blueprint
     chapter; the stale-issue audit flags citations to files that do not
     exist. -->
- Paper: `references/<paper-mirror>/<section>.tex:NNN`, label `thm:...`.
  Paraphrase: ...
- Blueprint: `blueprint/src/chapter/<chapter>.tex:NN`, label `thm:...`.

### Target Lean declaration

Expected Lean name and file path, e.g.
`MIPStarRE.Quantum.pauliBasisTest_sound` in `MIPStarRE/Quantum/PauliBasisTest.lean`.

### Mathematical dependencies

- Blueprint label `prop:...`.
- Lean declaration `MIPStarRE.Quantum....`.
- Sub-issue #NNNN, proving the estimate used in the paper proof.

### Proof plan

Explain the mathematical argument to be formalized, including any deliberate
deviation from the paper or blueprint statement.

### Statement integrity

Paper assumptions, Lean assumptions, paper conclusion, Lean conclusion, and a
verdict: exact / faithful boundary hypotheses / extra assumptions / weakened
conclusion / strengthened conclusion (docs/CONTRIBUTING.md:155-172).

## Initial classification

Applied by `local/bin/issue_new.py` (deterministic keyword pass, no model): `documentation`, `qpbt-test`

## Activity
