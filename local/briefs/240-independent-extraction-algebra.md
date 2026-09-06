# Issue240: independent pulled-apart algebra

Owner: prover-240-20260906-01 in issue-240-independent-extraction-algebra.
Source: references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1421-1456,
eq:def-tildewj, eq:tilde_M and the product-form calculation. Read the existing
qpbt_cross-basis-phase.tex correction before the twisted-commutation target.

Prove marginalPoly_isProjective, tildeObs_eq_heteroKron, tildeObs_isHermitian,
tildeObs_mul_self and tildeObs_twisted_commutation in Extraction/Observables.lean.
The existing statements take a global-pair witness and use its projective
measurement fields, not the missing existence/consistency construction.
Preserve all signatures and the nontrivial corrected phase. Start from
published main a61ee55 with closed prerequisites63 and114.

One writer owns Observables.lean and these matching blueprint nodes; issue239
owns Defs.lean and its dot-projector node. Do not assume239's unfinished
lemmas or change Combining files. Prioritize this independent algebra;
tildeM/integration and the original120/121 lifecycle keep their real gates.
No new holes, axioms, bypasses or source-theorem bridge inputs. Validate
actual proof dependencies, targeted Lean checks, statement integrity and
normal hooks. CI, independent review and daemon-only merges remain required.

The completed source scout is in
results/telemetry/sessions/scout-120-20260906-02.last.md in the primary checkout.
It also identifies swap unitarity as independent given-witness algebra, but
does not certify a fresh kernel build or authorize another same-file writer.
Main owns publication and integration. Primary/Astra-max, fan-out off.
