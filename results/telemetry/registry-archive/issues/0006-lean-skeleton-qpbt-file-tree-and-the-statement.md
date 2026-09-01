---
id: "0006"
title: "Lean skeleton: QPBT file tree and the statement of thm:pauli"
state: "open"
state_reason: null
parent: "0001"
children: []
labels: ["formalization", "qpbt-test"]
pinned: false
created: "2026-08-31T01:33:26Z"
updated: "2026-08-31T01:33:26Z"
agent_session: null
---

### Precise mathematical statement

Stage 4.1 (sub-issue of #0001): a minimal Lean skeleton under
`MIPStarRE/QPBT/` carrying the faithful statement of `thm:pauli`
(soundness/self-testing of the Pauli basis test, soundness function
$\delta_{\mathrm{qld}}(\eps,m,d,q) = a(md)^a(\eps^b+q^{-b}+2^{-bmd})$)
and every definition its statement transitively uses, with all proofs
`sorry`.

### Mathematical source

- Paper: `references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:1426-1447`,
  label `thm:pauli`.
- Blueprint: `blueprint/src/chapter/ch13_qpbt_test.tex`, label `thm:pauli`,
  statement closure through `ch12_qpbt_games.tex` and `ch11_qpbt_algebra.tex`.

### Target Lean declaration

`MIPStarRE.QPBT.pauli_soundness` (statement only, proof `sorry`) plus the
transitive definition closure; design brief at
`issues/briefs/0006-minimal-skeleton-brief.md`.

### Mathematical dependencies

- Reusable infrastructure: `MIPStarRE.Quantum` (matrices, measurements),
  selected `MIPStarRE.LDT` declarations per the brief's REUSE column.
- Encoding decisions: polynomial representatives (issue #0004 note);
  distribution encoding matched to the LDT track's.

### Proof plan

Explain the mathematical argument to be formalized, including any deliberate
deviation from the paper or blueprint statement.

### Statement integrity

Paper assumptions, Lean assumptions, paper conclusion, Lean conclusion, and a
verdict: exact / faithful boundary hypotheses / extra assumptions / weakened
conclusion / strengthened conclusion (docs/CONTRIBUTING.md:155-172).

## Initial classification

Applied by `local/bin/issue_new.py` (deterministic keyword pass, no model): `qpbt-test`

## Activity
