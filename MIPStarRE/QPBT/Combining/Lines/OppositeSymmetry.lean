import MIPStarRE.QPBT.Combining.Points.Placement
import MIPStarRE.QPBT.Games.Consistency

/-!
# Consistency symmetry on opposite placements

This module records that the consistency defect is unchanged when two
measurement families on opposite expanded-register placements are exchanged.
The result is a proof-only input to the joint line-measurement construction.

## References

The opposite placements are the directed symmetric equivalents in blueprint
`def:symmetric-equivalents`. The joint line-measurement conclusion using every
such placement is blueprint `lem:qld-xz-lines`, with paper source
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:882-894`.
-/

namespace MIPStarRE.QPBT

open MIPStarRE.LDT MIPStarRE.Quantum

noncomputable section

/-- Consistency is symmetric for measurements on opposite registers. The
operator commutation, rather than symmetry of the state or equality of local
dimensions, justifies exchanging the placements in `lem:qld-xz-lines`. -/
theorem consistencyDefect_opposite_symm {params : AdmissibleParams} {error : ℝ}
    {Question Outcome : Type*} [Fintype Question] [DecidableEq Question]
    [Fintype Outcome] [DecidableEq Outcome]
    (setting : ProjectiveSetting params error) (first second : Placement)
    (hopposite : first.IsOpposite second) (distribution : Distribution Question)
    (left : Question → Quantum.Measurement Outcome (setting.ExpandedLocalSpace first.side))
    (right : Question → Quantum.Measurement Outcome (setting.ExpandedLocalSpace second.side)) :
    consistencyDefect distribution
      (fun question answer => setting.place first ((left question).effect answer))
      (fun question answer => setting.place second ((right question).effect answer))
      setting.psiHat =
    consistencyDefect distribution
      (fun question answer => setting.place second ((right question).effect answer))
      (fun question answer => setting.place first ((left question).effect answer))
      setting.psiHat := by
  unfold consistencyDefect
  congr 1
  funext question
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro answer _
  apply Finset.sum_congr rfl
  intro other _
  rw [setting.place_comm first second hopposite]
  simp only [eq_comm]

end

end MIPStarRE.QPBT
