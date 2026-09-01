---
id: "0001"
branch: "issue-0002-qpbt-blueprint"
issue: "0002"
base: "main"
state: "merged"
head_sha: "1d93f01dd23d0b48992b45759be3cf73170530f5"
ci_status: "success"
review_state: "ADJUDICATED"
fix_iterations: 0
auto_fix: true
labels: ["blueprint-only", "documentation", "formalization", "qpbt-test"]
created: "2026-08-30T03:06:41Z"
merged_commit: "330ef8dd238283d61f22e99e9f170a983889301e"
---

# docs(blueprint): QPBT chapters and dependency graph

### Motivation

Stage 3 of the QPBT track (#0002 under tracking issue #0001): a
dependency-tracked blueprint for the quantum Pauli basis test of
MIP\*=RE — `references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex`
(test definition, `thm:pauli`) and
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex` (the
soundness analysis) — so that stage 4 can formalize against stated,
source-verified nodes.

### Description

Six new chapters, `ch11_qpbt_algebra` … `ch16_qpbt_extraction` (244 labeled
nodes): algebraic preliminaries; games, strategies and conditionally linear
distributions; the Pauli basis test with `thm:pauli`, `cor:pauli-binary`,
`def:introparams`, `lem:delta-bound`; strategy observables and the expanded
space; combining the bases and applying the classical test; extracting the
Pauli observables with the detached proof `\proves{thm:pauli}`. Imported
results stated explicitly: `lem:ld-soundness` (proof node relates to the LDT
track's `thm:main-formal`), `thm:ms-rigidity` (Coladangelo–Stark),
`thm:linearity` (Natarajan–Vidick). Paper labels preserved verbatim; source
defects found during extraction are recorded as remark nodes. The chapters carry no `\lean`/`\leanok`
tags except one verified statement-level tag in chapter 12 on a node
restating an already-formalized LDT-track statement; formalization tags
land in stage 4. Five bibliography
entries added (a sixth, Natarajan2018LowDegree, was added and removed
unused during the audit); `content.tex` routes the chapters. Scope excludes all
Turing-machine/complexity material (win predicates are stated as
mathematical functions).

### Testing

`check_blueprint_latex.py` exit 0; `texra-blueprint bbl` +
`leanblueprint web` exit 0 with zero `^ERROR:` lines; `leanblueprint pdf`
exit 0 (`print/print.pdf`); cross-chapter audit: no dangling
`\uses`/`\ref`, no duplicate labels, no cycles, balanced environments;
`local/bin/ci.sh 0001` conclusion success at the current head (per-SHA
manifests under `ci/`).

---
Addresses #0002
