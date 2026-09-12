# Direct-game rejection probability cap

Issue #333 is a formalization-only probability sub-issue of #119, stacked on
the capped scalar envelope from issue #326. The source context is the uniformly
weighted direct low-degree game described in
`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:178-186`.

Prove the two public facts missing from the caller API:

- every `Strategy` value is nonnegative;
- `directLdRejectionProbability D S <= 1`.

The first statement follows by unfolding `Strategy.value`, applying
nonnegativity of distribution averages and finite sums, and using
`outcomeWeight_nonneg`. The second follows from
`directLdRejectionProbability_eq_one_sub_value`.

These bounds justify the `min 1` cap in
`seven_branch_capped_error_le_directPassingErrorEnvelope`. They do not prove an
individual rejection-branch estimate, construct a strategy or witness, or
establish the final passing-value theorem. No source hypothesis, bridge,
residual input, or blueprint certification is introduced.

Completion requires single-file Lean validation, standard-only axiom checks,
proof-integrity scans, and normal checked publication. Canonical CI,
independent review, and merge remain with the integration coordinator.
