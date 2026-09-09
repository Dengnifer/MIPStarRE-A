# Issue243: direct-placement marginal agreement

Exclusive owner prover-243-20260906-01; published base a61ee55 and closed
prerequisite63. Own Extraction/Consistency.lean and a packet-specific audit.
Prove direct Alice/Bob agreement estimates from the existing global witness's
point_consistent_alice/bob fields, using finite postprocessing/projective
agreement APIs. Source: QPBT paper section14,1617-1662, eq:qld-sg-cons1 and
eq:qld-sg-cons2; blueprint lem:qld-constructing-the-paulis-helper.

Begin named lemmas for the two directly supplied opposite placements. Do not
call unfinished issue115 transfer proofs or duplicate issue240 projectivity.
Keep the full four-placement source theorem visible and do not claim it
complete from two cases. No new bridge assumptions or global-witness existence
claim. No shared blueprint edits, subagents, publication or merge. Targeted
checks, normal hooks and validated increments by2400 seconds; hard limit2700.
