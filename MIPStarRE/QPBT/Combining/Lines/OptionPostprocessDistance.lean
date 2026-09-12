import MIPStarRE.QPBT.Combining.Points.Placement
import MIPStarRE.QPBT.Games.Distance

/-!
# Distance under completion by a zero outcome

This module records that adjoining an unused `none` outcome to both answer
families preserves their placed squared distance.

## References

This is the formalization-only completion step used between the point
comparison in `eq:pasting-q1` and the completed evaluation convention of
`lem:qld-comm-line-cons`; see
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:936-941`.
-/

open scoped BigOperators

namespace MIPStarRE.QPBT

open MIPStarRE.LDT hiding Measurement
open MIPStarRE.Quantum

noncomputable section

/-- Postprocessing both answer families by `some` adds only a zero `none`
effect, so it preserves their placed squared distance. This is the
formalization-only completion step used at paper lines 936--941. -/
theorem ProjectiveSetting.opFamilyDistSq_postprocess_some
    {P : AdmissibleParams} {ε : ℝ} (S : ProjectiveSetting P ε)
    {Sample Answer : Type*} [Fintype Answer] [DecidableEq Answer]
    (law : Distribution Sample) (p1 p2 : Placement)
    (first : Sample → MIPStarRE.Quantum.Measurement Answer
      (S.ExpandedLocalSpace p1.side))
    (second : Sample → MIPStarRE.Quantum.Measurement Answer
      (S.ExpandedLocalSpace p2.side)) :
    opFamilyDistSq law
      (fun sample answer => S.place p1 (((first sample).postprocess some).effect answer))
      (fun sample answer => S.place p2 (((second sample).postprocess some).effect answer))
      S.psiHat =
    opFamilyDistSq law (fun sample answer => S.place p1 ((first sample).effect answer))
      (fun sample answer => S.place p2 ((second sample).effect answer)) S.psiHat := by
  classical
  have hplace_zero (p : Placement) :
      S.place p (0 : Op (S.ExpandedLocalSpace p.side)) = 0 := by
    ext i j
    cases p <;> simp [ProjectiveSetting.place]
  unfold opFamilyDistSq
  congr 1
  funext sample
  rw [Fintype.sum_option]
  simp [MIPStarRE.Quantum.Measurement.postprocess,
    MIPStarRE.Quantum.Submeasurement.postprocess, Finset.sum_filter,
    hplace_zero, applyOperatorToState]

end

end MIPStarRE.QPBT
