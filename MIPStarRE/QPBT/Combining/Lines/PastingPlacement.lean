import MIPStarRE.QPBT.Combining.Lines.ConsistencyPositivity
import MIPStarRE.QPBT.Combining.Points.Orthonormalization
import MIPStarRE.QPBT.Combining.Points.PlacementSupport
import MIPStarRE.QPBT.Games.Sandwich.Pasting.Heterogeneous

/-!
# Opposite-register transport for line pasting

The expanded state is reindexed into a bipartite state for each directed
opposite placement. The unused registers remain on the second side.

## References

These finite-coordinate identities support `lem:qld-xz-lines`,
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:950-963`.
The proofs are recovered from commit `f6a340c8`.
-/

namespace MIPStarRE.QPBT

open MIPStarRE.LDT MIPStarRE.Quantum
open scoped Matrix MatrixOrder

noncomputable section

/-- The fourth directed bipartition, with `BB'` first, `AB''` second, and
the unused `A'A''` pair retained on the second side. This is a coordinate
equivalence, not an identification of the two strategy-player spaces. -/
def bbAbBipartition (params : AdmissibleParams) (left right : Type*) :
    SixReg params left right ≃
      (right × PauliRegister params) ×
        ((left × PauliRegister params) × (PauliRegister params × PauliRegister params)) where
  toFun indices := ((indices.2.1, indices.2.2.1),
    ((indices.1.1, indices.2.2.2), (indices.1.2.1, indices.1.2.2)))
  invFun indices := ((indices.2.1.1, (indices.2.2.1, indices.2.2.2)),
    (indices.1.1, (indices.1.2, indices.2.1.2)))
  left_inv indices := by cases indices; rfl
  right_inv indices := by cases indices; rfl

/-- Coordinates of the `BB' | AB''(A'A'')` bipartition. -/
@[simp] theorem bbAbBipartition_apply (params : AdmissibleParams) (left right : Type*)
    (indices : SixReg params left right) :
    bbAbBipartition params left right indices =
      ((indices.2.1, indices.2.2.1),
        ((indices.1.1, indices.2.2.2), (indices.1.2.1, indices.1.2.2))) := rfl

set_option synthInstance.maxSize 400 in
/-- Every directed opposite placement has an actual heterogeneous
bipartition. The unused EPR pair is included on the right. This discharges the
register identities needed for the application of pasting in all symmetric
equivalents of `lem:qld-xz-lines`, paper
`14_analysis_of_the_pauli_basis_test.tex:959-963`. -/
theorem ProjectiveSetting.exists_opposite_bipartition {params : AdmissibleParams}
    {error : ℝ} (setting : ProjectiveSetting params error)
    (first second : Placement) (hopposite : first.IsOpposite second) :
    ∃ equivalence : SixReg params setting.toStrategy.ιA setting.toStrategy.ιB ≃
        setting.ExpandedLocalSpace first.side ×
          (setting.ExpandedLocalSpace second.side ×
            (PauliRegister params × PauliRegister params)),
      (∀ operator : Op (setting.ExpandedLocalSpace first.side),
        reindexOp equivalence (heteroKron operator 1) = setting.place first operator) ∧
      (∀ operator : Op (setting.ExpandedLocalSpace second.side),
        reindexOp equivalence (heteroKron 1 (heteroKron operator
          (1 : Op (PauliRegister params × PauliRegister params)))) =
          setting.place second operator) := by
  classical
  cases first <;> cases second <;> try exact False.elim hopposite
  · exact ⟨aaBaBipartition params _ _, setting.reindexOp_aaBaBipartition_left,
      setting.reindexOp_aaBaBipartition_right⟩
  · exact ⟨baAaBipartition params _ _, setting.reindexOp_baAaBipartition_left,
      setting.reindexOp_baAaBipartition_right⟩
  · refine ⟨bbAbBipartition params _ _, ?_, ?_⟩
    · intro operator
      ext row column
      change operator (row.2.1, row.2.2.1) (column.2.1, column.2.2.1) *
        (1 : Op ((setting.toStrategy.ιA × PauliRegister params) ×
          (PauliRegister params × PauliRegister params)))
          ((row.1.1, row.2.2.2), row.1.2) ((column.1.1, column.2.2.2), column.1.2) = _
      simp only [ProjectiveSetting.place, Matrix.one_apply, Prod.ext_iff]
      split_ifs <;> simp_all
    · intro operator
      ext row column
      change (1 : Op (setting.toStrategy.ιB × PauliRegister params))
        (row.2.1, row.2.2.1) (column.2.1, column.2.2.1) *
          (operator (row.1.1, row.2.2.2) (column.1.1, column.2.2.2) *
            (1 : Op (PauliRegister params × PauliRegister params)) row.1.2 column.1.2) = _
      simp only [ProjectiveSetting.place, Matrix.one_apply, Prod.ext_iff]
      split_ifs <;> simp_all
  · exact ⟨abBbBipartition params _ _, setting.reindexOp_abBbBipartition_left,
      setting.reindexOp_abBbBipartition_right⟩

set_option synthInstance.maxSize 400 in
open DistanceCalculus in
/-- Coordinate transport of arbitrary placed operator families through a
specified opposite bipartition. The two identities are representation data,
constructed for every opposite pair by `exists_opposite_bipartition`; no
mathematical approximation or extra assumption on the strategy is introduced. -/
theorem ProjectiveSetting.consistencyDefect_bipartition {params : AdmissibleParams}
    {error : ℝ} (setting : ProjectiveSetting params error) (first second : Placement)
    (equivalence : SixReg params setting.toStrategy.ιA setting.toStrategy.ιB ≃
      setting.ExpandedLocalSpace first.side ×
        (setting.ExpandedLocalSpace second.side × (PauliRegister params × PauliRegister params)))
    (hfirst : ∀ operator : Op (setting.ExpandedLocalSpace first.side),
      reindexOp equivalence (heteroKron operator 1) = setting.place first operator)
    (hsecond : ∀ operator : Op (setting.ExpandedLocalSpace second.side),
      reindexOp equivalence (heteroKron 1 (heteroKron operator
        (1 : Op (PauliRegister params × PauliRegister params)))) =
        setting.place second operator)
    {question answer : Type*} [Fintype question] [DecidableEq question]
    [Fintype answer] [DecidableEq answer] (law : Distribution question)
    (firstFamily : question → answer → Op (setting.ExpandedLocalSpace first.side))
    (secondFamily : question → answer → Op (setting.ExpandedLocalSpace second.side)) :
    consistencyDefect law (fun query output => heteroKron (firstFamily query output) 1)
      (fun query output => heteroKron 1 (heteroKron (secondFamily query output)
        (1 : Op (PauliRegister params × PauliRegister params))))
      (reindexState equivalence setting.psiHat) =
    consistencyDefect law (fun query output => setting.place first (firstFamily query output))
      (fun query output => setting.place second (secondFamily query output)) setting.psiHat := by
  unfold consistencyDefect
  congr 1
  funext query
  apply Finset.sum_congr rfl
  intro output _
  apply Finset.sum_congr rfl
  intro other _
  split_ifs
  · rfl
  · rw [consistency_term_eq_stateQForm, consistency_term_eq_stateQForm,
      WinImplications.stateQForm_reindexState, WinImplications.reindexOp_mul,
      hfirst, hsecond]

/-- An unused tensor factor commutes with both the ordered sandwich and its
evaluation. This identity keeps the unused EPR pair when applying the
heterogeneous pasting theorem to the expanded state. -/
theorem evaluated_pastedMeasurement_heteroKron_one
    {firstAnswer secondAnswer result carrier unused : Type*}
    [Fintype firstAnswer] [Fintype secondAnswer] [DecidableEq result]
    [Fintype carrier] [DecidableEq carrier] [Fintype unused] [DecidableEq unused]
    (first : firstAnswer → Op carrier) (second : secondAnswer → Op carrier)
    (evaluate : firstAnswer → secondAnswer → result) (output : result) :
    (∑ firstAnswer, ∑ secondAnswer, if evaluate firstAnswer secondAnswer = output then
      pastedMeasurement (fun answer => heteroKron (first answer) (1 : Op unused))
        (fun answer => heteroKron (second answer) (1 : Op unused)) firstAnswer secondAnswer
      else 0) =
    heteroKron (∑ firstAnswer, ∑ secondAnswer,
      if evaluate firstAnswer secondAnswer = output then
        pastedMeasurement first second firstAnswer secondAnswer else 0) (1 : Op unused) := by
  simp only [pastedMeasurement, heteroKron_mul, mul_one]
  ext row column
  simp [heteroKron, Matrix.kronecker, Matrix.sum_apply, Matrix.ite_apply,
    Finset.sum_mul, ite_mul]

/-- Reversing a paired postprocessing reverses the effect's answer index.
This formalization identity is valid without an injectivity assumption on the
evaluation functions, including completed evaluation at a degenerate line. -/
theorem postprocess_pair_swap_effect {answer first second carrier : Type*}
    [Fintype answer] [DecidableEq answer] [Fintype first] [DecidableEq first]
    [Fintype second] [DecidableEq second] [Fintype carrier] [DecidableEq carrier]
    (measurement : Quantum.Measurement answer carrier) (evaluate : answer → first × second)
    (output : second × first) :
    (measurement.postprocess (fun answer => (evaluate answer).swap)).effect output =
      (measurement.postprocess evaluate).effect output.swap := by
  simp only [Quantum.Measurement.postprocess_effect]
  congr 1
  ext answer
  simp [Prod.ext_iff, and_comm]

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
