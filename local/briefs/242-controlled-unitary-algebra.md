# Issue242: finite controlled-unitary algebra

Exclusive owner prover-242-20260906-01; published base a61ee55 and closed
prerequisite63. Own new Quantum/ControlledUnitary.lean and a packet-specific
audit, not Extraction/Observables.lean. Derive unitarity of a finite sum of
orthogonal complete control projectors tensored with unitaries. Search
Mathlib/local APIs first; reuse rather than redeclare an existing theorem.
Source: QPBT paper section14,1687-1750, proof of lem:qld-unitary.

This is an importable generic calculation for later swap proofs, independent
of issue240's Pauli observable algebra and of any missing global witness.
No new source assumption or conclusion-shaped bridge. No shared blueprint
edits, subagents, publication or merge. Targeted checks and normal hooks;
return validated increments by2400 seconds, hard limit2700.
