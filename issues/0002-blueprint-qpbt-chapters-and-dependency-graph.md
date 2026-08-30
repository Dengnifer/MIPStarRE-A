---
id: "0002"
title: "Blueprint: QPBT chapters and dependency graph"
state: "closed"
state_reason: "completed"
parent: "0001"
children: []
labels: ["blueprint-only", "documentation", "formalization", "qpbt-test"]
pinned: false
created: "2026-08-30T03:03:48Z"
updated: "2026-08-30T19:59:25Z"
agent_session: null
---

### Precise mathematical statement

Blueprint (not Lean) deliverable: a dependency-tracked LaTeX blueprint for
the quantum Pauli basis test — the game $\mathfrak G^{\mathrm{Pauli}}_{(q,m,d)}$,
its completeness (`lem:pauli-completeness`), the soundness/self-testing
theorem `thm:pauli` with soundness function
$\delta_{\mathrm{qld}}(\eps,m,d,q) = a(md)^a(\eps^b + q^{-b} + 2^{-bmd})$,
the qubit form `cor:pauli-binary`, canonical parameters `def:introparams`
with `lem:delta-bound`, and the full soundness analysis.

### Mathematical source

- Paper: `references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex`
  (test definition; `thm:pauli` at source lines 1426–1447) and
  `references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex`
  (the soundness analysis, six subsections).
- Secondary: `references/neexp-paper/07_a_self_test_for_the_pauli_basis.tex`.
- Blueprint: `blueprint/src/chapter/ch11_qpbt_algebra.tex` …
  `ch16_qpbt_extraction.tex` (this issue's deliverable).

### Target Lean declaration

None in this issue — the blueprint carries no `\lean` tags at this stage
(one exception: a verified statement-level tag on a restated node backed by
the existing LDT development). Lean skeletons and proofs are stage-4 issues
under this tracking parent.

### Mathematical dependencies

- The LDT track's `thm:main-formal` (quantum soundness of the classical low
  individual degree test) as the intended in-repo provider for
  `lem:ld-soundness`; the derivation is open and documented in the blueprint.
- Two source obstructions documented as paper-gap notes:
  `docs/paper-gaps/qpbt_ld-dimension-divisibility.tex` and
  `docs/paper-gaps/qpbt_symmetrization-attainment.tex`.

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

- 2026-08-30T19:46:25Z — PR #0001 (*docs(blueprint): QPBT chapters and dependency graph*) addressing this issue has been merged. See 0001-docs-blueprint-qpbt-chapters-and-dependency-graph/pr.md for what was accomplished and what remains.
- 2026-08-30T19:59:25Z — Issue closed as completed.
