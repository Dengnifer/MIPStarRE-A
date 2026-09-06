# Issue241: extraction error absorption

Exclusive owner prover-241-20260906-01; published base a61ee55 and closed
prerequisite63. Own only deltaExtract_le_deltaQld and local proof helpers
in Extraction/Unitary.lean, plus a packet-specific audit. Do not edit the
extraction witness construction. Source: QPBT paper section14,1855-1858 and
1868-1876; blueprint lem:qld-extraction-error-form. This real-power estimate
uses merged definitions and admissibility, not the missing witness.

Preserve the statement, prove from actual inputs, no new holes or assumptions.
No shared blueprint edits, subagents, publication, CI/review/merge or cache
writes. Targeted Lean/axiom checks and normal hooks; return validated commits
by2400 seconds before the2700-second hard limit. Normal integration gates apply.
