---
id: "0005"
title: "Split derived identities out of the expanded-measurement definitions"
state: "open"
state_reason: null
parent: "0001"
children: []
labels: ["blueprint-only", "formalization", "qpbt-test"]
pinned: false
created: "2026-08-30T16:28:23Z"
updated: "2026-08-30T16:28:23Z"
agent_session: null
---

### Precise mathematical statement

Review finding (PR #0001, round 6, prose-F4): the expanded-measurement
definitions in `ch14_qpbt_observables.tex` (around `def:expanded-point-measurement`
and its trace-projection companion) assert derived identities and
properties (completeness, projectivity, marginal formulas) inside
definition environments. Split each asserted property into its own lemma
node with a proof sketch, leaving pure object introduction in the
definitions.

### Mathematical source

- Paper: `references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:367-430`.
- Blueprint: `blueprint/src/chapter/ch14_qpbt_observables.tex`,
  labels `def:expanded-point-measurement`, `def:expanded-point-trace-projection`,
  `def:expanded-observables`.

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
