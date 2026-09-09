# Issue239: independent dot-product projectors

Owner: prover-239-20260906-01 in issue-239-independent-dot-projectors.
Source: references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1426-1429,
eq:def-tauwu; blueprint def:tau-dot-product-projector.

Prove tauDotProj_isProj and sum_tauDotProj_eq_one in Extraction/Defs.lean,
without changing their signatures. These targets do not quantify over a
global-pair witness; their Pauli algebra is independent of issue119's
construction. Start from published main a61ee55, with closed prerequisite63.

Exclusive scope is that file, the matching dot-projector blueprint node and
a packet-specific audit. Issue240 owns Extraction/Observables.lean. Preserve
source faithfulness, prove any necessary local projector orthogonality from
merged inputs, and check actual kernel axiom dependencies. No new holes,
axioms, assumptions, game changes or bypasses. Normal hooks, CI, independent
review and daemon-only merges remain mandatory. This supplies part of120,
not the global measurement construction or the whole extraction theorem.

Use the detailed GitHub issue body and initial dispatch attachment for the
validation and time-bound instructions. All work is primary/Astra-max, no
fan-out. Main owns publication and integration after the worker's report.
