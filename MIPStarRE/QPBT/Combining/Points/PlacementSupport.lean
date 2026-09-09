import MIPStarRE.QPBT.Combining.Points.Placement
import MIPStarRE.QPBT.Observables.LineMeasurement

/-!
# Placement support for expanded line measurements

This compatibility module re-exports the placement calculus from
`MIPStarRE.QPBT.Combining.Points.Placement` together with the expanded line
measurement API. The placement declarations have a single definition, so both
module paths can be imported together.

## References

The placements are those of blueprint `def:symmetric-equivalents`, from
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:420-450`.
-/
