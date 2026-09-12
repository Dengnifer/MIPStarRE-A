import MIPStarRE.QPBT.Combining.Lines.OptionPointMarginalTransport
import MIPStarRE.QPBT.Combining.Lines.SamePlacementDistance

/-!
# Combined point-to-line marginal distances

This module compares each completed coordinate marginal of a combined point
measurement with the corresponding evaluated expanded-line measurement. The
joint point error and the strategy error remain separate in both estimates.

## References

These are the two comparisons in `eq:pasting-q1`,
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:936-941`.
-/

namespace MIPStarRE.QPBT

open MIPStarRE.LDT hiding Measurement
open MIPStarRE.Quantum

noncomputable section

/-- Both completed combined-point marginals are close to their corresponding
evaluated expanded-line measurements. The `8 * δQ` term is kept separate from
the strategy and expanded-line errors. -/
theorem exists_combinedPoints_line_marginal_distance_le :
    ∃ C : ℝ, 1 ≤ C ∧
      ∀ (P : AdmissibleParams) (ε δQ : ℝ) (S : ProjectiveSetting P ε)
        (points : CombinedPointsWitness S δQ)
        (p1 p2 : Placement), p1.IsOpposite p2 →
        opFamilyDistSq (Distribution.prod (linePointDist P.toLdParams)
          (linePointDist P.toLdParams))
          (fun sample answer => S.place p1
            ((((points.Q p1.side sample.1.2 sample.2.2).postprocess Prod.fst).postprocess
              some).effect answer))
          (fun sample answer => S.place p2
            ((S.lineEvalMeasExp p2.side .X sample.1.1 sample.1.2).effect answer))
          S.psiHat ≤ 8 * δQ + C * (ε + deltaLine ε) ∧
        opFamilyDistSq (Distribution.prod (linePointDist P.toLdParams)
          (linePointDist P.toLdParams))
          (fun sample answer => S.place p1
            ((((points.Q p1.side sample.1.2 sample.2.2).postprocess Prod.snd).postprocess
              some).effect answer))
          (fun sample answer => S.place p2
            ((S.lineEvalMeasExp p2.side .Z sample.2.1 sample.2.2).effect answer))
          S.psiHat ≤ 8 * δQ + C * (ε + deltaLine ε) := by
  obtain ⟨C, hC, hbound⟩ := exists_expLine_point_same_placement_distance_le
  refine ⟨2 * C, by linarith, ?_⟩
  intro P ε δQ S points p1 p2 hopp
  classical
  have hX : opFamilyDistSq (Distribution.prod (linePointDist P.toLdParams)
      (linePointDist P.toLdParams))
      (fun sample answer => S.place p2
        ((S.pointMeasExpOption p2.side .X sample.1.2).effect answer))
      (fun sample answer => S.place p2
        ((S.lineEvalMeasExp p2.side .X sample.1.1 sample.1.2).effect answer))
      S.psiHat ≤ C * (ε + deltaLine ε) := by
    rw [DistanceCalculus.opFamilyDistSq_symm]
    unfold opFamilyDistSq
    rw [SandwichProduct.avgOver_distribution_prod]
    simp_rw [avgOver_const_of_isProbability _ (linePointDist_isProbability P.toLdParams)]
    exact hbound P ε S p1 p2 hopp .X
  have hZ : opFamilyDistSq (Distribution.prod (linePointDist P.toLdParams)
      (linePointDist P.toLdParams))
      (fun sample answer => S.place p2
        ((S.pointMeasExpOption p2.side .Z sample.2.2).effect answer))
      (fun sample answer => S.place p2
        ((S.lineEvalMeasExp p2.side .Z sample.2.1 sample.2.2).effect answer))
      S.psiHat ≤ C * (ε + deltaLine ε) := by
    rw [DistanceCalculus.opFamilyDistSq_symm]
    unfold opFamilyDistSq
    rw [SandwichProduct.avgOver_distribution_prod]
    erw [avgOver_const_of_isProbability _ (linePointDist_isProbability P.toLdParams)
      (opFamilyDistSq (linePointDist P.toLdParams)
        (fun sample answer => S.place p2
          ((S.lineEvalMeasExp p2.side .Z sample.1 sample.2).effect answer))
        (fun sample answer => S.place p2
          ((S.pointMeasExpOption p2.side .Z sample.2).effect answer)) S.psiHat)]
    exact hbound P ε S p1 p2 hopp .Z
  constructor
  · convert opFamilyDistSq_le_of_le_of_le _ _ _ _ S.psiHat _ _
      (points.marginal_X_option_linePoint_distance_le p1 p2 hopp) hX using 1
    ring
  · convert opFamilyDistSq_le_of_le_of_le _ _ _ _ S.psiHat _ _
      (points.marginal_Z_option_linePoint_distance_le p1 p2 hopp) hZ using 1
    ring

end

end MIPStarRE.QPBT
