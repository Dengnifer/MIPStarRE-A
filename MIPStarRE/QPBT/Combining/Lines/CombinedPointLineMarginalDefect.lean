import MIPStarRE.QPBT.Combining.Lines.CombinedPointLineMarginalDistance

/-!
# Combined point-to-line marginal defects

This module converts the squared-distance comparisons for completed
combined-point marginals into consistency-defect bounds. Projectivity is
derived from the existing point and expanded-line measurement constructors.

## References

These are the two defect comparisons in `eq:pasting-q1`,
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:936-941`.
-/

namespace MIPStarRE.QPBT

open MIPStarRE.LDT hiding Measurement
open MIPStarRE.Quantum

noncomputable section

/-- Both completed combined-point marginals have small consistency defect
against their corresponding evaluated expanded-line measurements. -/
theorem exists_combinedPoints_line_marginal_defect_le :
    ∃ C : ℝ, 1 ≤ C ∧
      ∀ (P : AdmissibleParams) (ε δQ : ℝ) (S : ProjectiveSetting P ε)
        (points : CombinedPointsWitness S δQ)
        (p1 p2 : Placement), p1.IsOpposite p2 →
        consistencyDefect (Distribution.prod (linePointDist P.toLdParams)
          (linePointDist P.toLdParams))
          (fun sample answer => S.place p1
            ((((points.Q p1.side sample.1.2 sample.2.2).postprocess
              (fun pair => (some pair.1, some pair.2))).postprocess Prod.fst).effect answer))
          (fun sample answer => S.place p2
            ((S.lineEvalMeasExp p2.side .X sample.1.1 sample.1.2).effect answer))
          S.psiHat ≤ 8 * δQ + C * (ε + deltaLine ε) ∧
        consistencyDefect (Distribution.prod (linePointDist P.toLdParams)
          (linePointDist P.toLdParams))
          (fun sample answer => S.place p1
            ((((points.Q p1.side sample.1.2 sample.2.2).postprocess
              (fun pair => (some pair.1, some pair.2))).postprocess Prod.snd).effect answer))
          (fun sample answer => S.place p2
            ((S.lineEvalMeasExp p2.side .Z sample.2.1 sample.2.2).effect answer))
          S.psiHat ≤ 8 * δQ + C * (ε + deltaLine ε) := by
  obtain ⟨C, hC, hbound⟩ := exists_combinedPoints_line_marginal_distance_le
  refine ⟨C, hC, ?_⟩
  intro P ε δQ S points p1 p2 hopp
  classical
  have hcompleted_fst (side : PlayerSide) (x z : Fin P.m → PauliScalar P)
      (answer : Option (PauliScalar P)) :
      (((points.Q side x z).postprocess (fun pair => (some pair.1, some pair.2))).postprocess
        Prod.fst).effect answer =
        (((points.Q side x z).postprocess Prod.fst).postprocess some).effect answer := by
    exact congrArg (fun meas => meas.effect answer)
      ((MIPStarRE.Quantum.Measurement.postprocess_comp (points.Q side x z)
        (fun pair => (some pair.1, some pair.2)) Prod.fst).trans
        (MIPStarRE.Quantum.Measurement.postprocess_comp
          (points.Q side x z) Prod.fst some).symm)
  have hcompleted_snd (side : PlayerSide) (x z : Fin P.m → PauliScalar P)
      (answer : Option (PauliScalar P)) :
      (((points.Q side x z).postprocess (fun pair => (some pair.1, some pair.2))).postprocess
        Prod.snd).effect answer =
        (((points.Q side x z).postprocess Prod.snd).postprocess some).effect answer := by
    exact congrArg (fun meas => meas.effect answer)
      ((MIPStarRE.Quantum.Measurement.postprocess_comp (points.Q side x z)
        (fun pair => (some pair.1, some pair.2)) Prod.snd).trans
        (MIPStarRE.Quantum.Measurement.postprocess_comp
          (points.Q side x z) Prod.snd some).symm)
  simp_rw [hcompleted_fst, hcompleted_snd]
  have hcompare (coordinate : PauliScalar P × PauliScalar P → PauliScalar P)
      (sampleLine : (LineDesc P.toLdParams × (Fin P.m → PauliScalar P)) ×
        (LineDesc P.toLdParams × (Fin P.m → PauliScalar P)) →
        LineDesc P.toLdParams × (Fin P.m → PauliScalar P)) (W : PauliKind) :=
    consistencyDefect_le_opFamilyDistSq_of_projective
      (Distribution.prod (linePointDist P.toLdParams) (linePointDist P.toLdParams))
      (fun sample => S.placedMeasurement p1
        (((points.Q p1.side sample.1.2 sample.2.2).postprocess coordinate).postprocess some))
      (fun sample => S.placedMeasurement p2
        (S.lineEvalMeasExp p2.side W (sampleLine sample).1 (sampleLine sample).2)) S.psiHat
      (fun sample => S.placedMeasurement_isProjective p1 _
        (SandwichProduct.postprocess_isProjective _
          (SandwichProduct.postprocess_isProjective _ (points.projective _ _ _) _) _))
      (fun sample => S.placedMeasurement_isProjective p2 _
        (SandwichProduct.postprocess_isProjective _ (S.lineMeasExp_isProjective _ _ _) _))
  exact ⟨(hcompare Prod.fst Prod.fst .X).trans (hbound P ε δQ S points p1 p2 hopp).1,
    (hcompare Prod.snd Prod.snd .Z).trans (hbound P ε δQ S points p1 p2 hopp).2⟩

end

end MIPStarRE.QPBT
