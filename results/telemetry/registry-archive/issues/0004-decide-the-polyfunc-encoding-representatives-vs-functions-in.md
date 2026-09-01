---
id: "0004"
title: "Decide the polyfunc encoding: representatives vs functions in ld-meas outcomes"
state: "open"
state_reason: null
parent: "0001"
children: []
labels: ["formalization", "qpbt-test"]
pinned: false
created: "2026-08-30T16:28:23Z"
updated: "2026-08-30T16:28:23Z"
agent_session: null
---

### Precise mathematical statement

Review finding (PR #0001, round 6, code-F2): `def:ld-meas` indexes outcomes
by polynomial representatives (`polyfunc`, matching the Lean encoding
`MvPolynomial.restrictDegree`), while the source indexes by polynomial
functions; the two differ for d >= q. Decide the project encoding for the
QPBT track: representative-indexed measurements with function statements
read through evaluation (status quo, explained at `def:polynomials-degree`),
or function-indexed as printed.

### Mathematical source

- Paper: `references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:397-408`
  (`def:ld-meas`).
- Blueprint: `blueprint/src/chapter/ch13_qpbt_test.tex`, label `def:ld-meas`;
  `ch11_qpbt_algebra.tex`, label `def:polynomials-degree`.

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

Applied by `local/bin/issue_new.py` (deterministic keyword pass, no model): No automatic label was clear from the title or body.

## Activity
