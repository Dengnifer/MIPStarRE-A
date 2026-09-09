import MIPStarRE.QPBT.Combining.Points.Placement

/-!
# Compatibility import for the placement calculus

This module re-exports the canonical placement implementation in
`MIPStarRE.QPBT.Combining.Points.Placement`. It introduces no duplicate
declarations. The placed-measurement algebra and EPR-exchange identities are
both supplied by that implementation, so the two module paths can be imported
together.

## References

The placements are blueprint `def:symmetric-equivalents`, and the exchange
identities are `lem:symmetric-equivalents-transfer`; see
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:420-450`.
-/
