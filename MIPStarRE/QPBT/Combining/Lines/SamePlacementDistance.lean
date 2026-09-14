import MIPStarRE.QPBT.Combining.Lines.OptionPostprocessDistance
import MIPStarRE.QPBT.Combining.Lines.PointSelfConsistency
import MIPStarRE.QPBT.Observables.LineMeasurement

/-!
# Same-placement line-point distance

This module compares an evaluated expanded-line measurement with the completed
expanded-point measurement on the same placement. The proof passes through the
opposite placement, using line-point consistency and point self-consistency.

## References

This is the intermediate comparison in `eq:pasting-q1`,
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:936-941`.
-/

open scoped BigOperators

namespace MIPStarRE.QPBT

open MIPStarRE.LDT hiding Measurement
open MIPStarRE.Quantum

noncomputable section

/-- On either placement, an evaluated expanded-line measurement is close to
the completed expanded-point measurement. This is the intermediate comparison
in `eq:pasting-q1`, obtained from items 1 and 3 of the two consistency lemmas. -/
theorem exists_expLine_point_same_placement_distance_le :
    ∃ C : ℝ, 1 ≤ C ∧
      ∀ (P : AdmissibleParams) (ε : ℝ) (S : ProjectiveSetting P ε)
        (p1 p2 : Placement), p1.IsOpposite p2 → ∀ W : PauliKind,
        opFamilyDistSq (linePointDist P.toLdParams)
          (fun sample answer => S.place p2
            ((S.lineEvalMeasExp p2.side W sample.1 sample.2).effect answer))
          (fun sample answer => S.place p2
            ((S.pointMeasExpOption p2.side W sample.2).effect answer))
          S.psiHat ≤ C * (ε + deltaLine ε) := by
  obtain ⟨Cp, hCp, hp⟩ := expPoint_self_cons
  obtain ⟨Cl, hCl, hl⟩ := expLine_point_cons'
  refine ⟨2 * (Cp + Cl), by linarith, ?_⟩
  intro P ε S p1 p2 hopp W
  classical
  have hreverse : p2.IsOpposite p1 := by
    cases p1 <;> cases p2 <;> simp_all [Placement.IsOpposite]
  have hpoint : opFamilyDistSq (linePointDist P.toLdParams)
      (fun sample answer => S.place p1
        ((S.pointMeasExpOption p1.side W sample.2).effect answer))
      (fun sample answer => S.place p2
        ((S.pointMeasExpOption p2.side W sample.2).effect answer)) S.psiHat ≤ Cp * ε := by
    unfold ProjectiveSetting.pointMeasExpOption
    erw [S.opFamilyDistSq_postprocess_some]
    unfold opFamilyDistSq
    rw [avgOver_linePointDist_point P.toLdParams (fun point =>
      ∑ answer, ‖applyOperatorToState
        (S.place p1 ((S.pointMeasExp p1.side W point).effect answer) -
          S.place p2 ((S.pointMeasExp p2.side W point).effect answer)) S.psiHat‖ ^ 2)]
    exact hp P ε S p1 p2 hopp W
  have htri := opFamilyDistSq_le_of_le_of_le _ _ _ _ S.psiHat _ _
    (hl P ε S p2 p1 hreverse W) hpoint
  refine htri.trans ?_
  have hε := S.eps_nonneg
  have hline : 0 ≤ deltaLine ε := Real.sqrt_nonneg ε
  nlinarith

end

end MIPStarRE.QPBT
