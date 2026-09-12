import MIPStarRE.QPBT.Combining.XEvalDeficit

/-!
# X-point subline averages

This directly indexed auxiliary construction follows the first consistency
route for combined lines. The question carrier, completed answer alphabet,
and corrected error convention retain their existing meanings.

## References

Paper `references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1118-1246`,
blueprint `lem:qld-4-13-established`. Recovered from commit
`6e8d67ef8ba22de69a0c166adcdf23ba6e7a33aa` for issue #512.
See `docs/paper-gaps/qpbt_combined-lines-error-term.tex` and
`docs/paper-gaps/qpbt_ld-dimension-divisibility.tex` for the remaining
comparison with the printed source theorem.
-/

namespace MIPStarRE.QPBT

open MIPStarRE.LDT hiding Measurement
open MIPStarRE.Quantum MIPStarRE.QPBT.DistanceCalculus
open scoped BigOperators Matrix MatrixOrder ComplexOrder

noncomputable section

variable {P : AdmissibleParams} {ε δQ δP : ℝ} {S : ProjectiveSetting P ε}
  {points : CombinedPointsWitness S δQ}

/-- The sub-line average, with a uniform affine parameter on the extended
line, of a sum over line answers of an overlap with a point family that
depends on the two evaluations of the answer, as the average against the
product of the sub-line law and the uniform parameter of the overlap of the
evaluated pair-line measurement with that family.  Blueprint
`lem:qld-4-13-established`. -/
theorem SubLineWitness.avgOver_regrouped_eq_at {P : AdmissibleParams}
    {ε δQ δP : ℝ} {S : ProjectiveSetting P ε} {points : CombinedPointsWitness S δQ}
    (sublines : SubLineWitness P) (lines : CombinedLinesWitness S points δP)
    (first second : Placement)
    (G : (Fin P.m → PauliScalar P) → (Fin P.m → PauliScalar P) →
      Option (PauliScalar P) → Option (PauliScalar P) →
      Op (S.ExpandedLocalSpace second.side)) :
    avgOver sublines.D (fun sample =>
        avgOver (uniformDistribution (DirectScalarQ P.extendedDirectLd))
          (fun t =>
            let u := directPointToPauli P
              (sample.1.base + t • sample.1.direction)
            let x := projX u
            let z := projZ u
            ∑ fX, ∑ fZ,
              (inner ℂ S.psiHat ((EuclideanSpace.equiv
                (SixReg P S.toStrategy.ιA S.toStrategy.ιB) ℂ).symm
                  ((S.place first
                      ((lines.T first.side sample.2.1 sample.2.2).effect
                        (fX, fZ)) *
                    S.place second
                      (G x z (evalOpt sample.2.1 x fX)
                        (evalOpt sample.2.2 z fZ))).mulVec
                          S.psiHat))).re)) =
      avgOver (Distribution.prod sublines.D
          (uniformDistribution (DirectScalarQ P.extendedDirectLd)))
        (fun s => ∑ o : Option (PauliScalar P) × Option (PauliScalar P),
          stateQForm S.psiHat
            ((S.placedMeasurement first
              ((lines.T first.side s.1.2.1 s.1.2.2).postprocess (fun fs =>
                (evalOpt s.1.2.1 (projX (directPointToPauli P
                    (s.1.1.base + s.2 • s.1.1.direction))) fs.1,
                  evalOpt s.1.2.2 (projZ (directPointToPauli P
                    (s.1.1.base + s.2 • s.1.1.direction))) fs.2)))).effect o *
              S.place second
                (G (projX (directPointToPauli P
                    (s.1.1.base + s.2 • s.1.1.direction)))
                  (projZ (directPointToPauli P
                    (s.1.1.base + s.2 • s.1.1.direction))) o.1 o.2))) := by
  rw [avgOver_prod]
  refine avgOver_congr _ _ _ fun sample => ?_
  refine avgOver_congr _ _ _ fun t => ?_
  exact (regroup_line_answer_sum_at lines first second sample.2.1 sample.2.2 _ _ (G _ _)).symm

/-! ## The mixture form of a one-point sub-line average -/

/-- The overlap of the paired-line measurement at two source lines with the
expanded `X`-point effect at a point, summed over the line answers.  This is
the deficit integrand in the proof of `lem:claim-17-2`, as a function of the
two source lines and the `X`-point alone. -/
def xPointOverlapAt (lines : CombinedLinesWitness S points δP)
    (first second : Placement)
    (w : (LineDesc P.toLdParams × LineDesc P.toLdParams) ×
      (Fin P.m → PauliScalar P)) : ℝ :=
  ∑ fX, ∑ fZ, stateQForm S.psiHat
    (S.place first ((lines.T first.side w.1.1 w.1.2).effect (fX, fZ)) *
      S.place second ((S.pointMeasExpOption second.side .X w.2).effect (evalOpt w.1.1 w.2 fX)))

/-- At a pair of line-point pairs, the `X`-point overlap is the overlap of the
evaluated pair-line measurement with the completed `X`-point measurement; the
`Z`-point of the second pair only labels the evaluation classes. -/
theorem xPointOverlap_eq_at (lines : CombinedLinesWitness S points δP)
    (first second : Placement)
    (w : LinePointPairSample P) :
    xPointOverlapAt lines first second ((w.1.1, w.2.1), w.1.2) =
      ∑ o : Option (PauliScalar P) × Option (PauliScalar P),
        stateQForm S.psiHat
          (S.place first
            (((lines.T first.side w.1.1 w.2.1).postprocess fun fs =>
              (evalOpt w.1.1 w.1.2 fs.1, evalOpt w.2.1 w.2.2 fs.2)).effect o) *
            S.place second ((S.pointMeasExpOption second.side .X w.1.2).effect o.1)) :=
  (regroup_line_answer_sum_at lines first second w.1.1 w.2.1 w.1.2 w.2.2
    (fun o1 _ => (S.pointMeasExpOption second.side .X w.1.2).effect o1)).symm

/-- The deficit of the sub-line average of the `X`-point overlap is bounded by
the inflated line and point consistency errors.  This is the bound on the
deficit in the proof of `lem:claim-17-2`, blueprint
`blueprint/src/chapter/ch15_qpbt_combining.tex`, paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1168-1201`. -/
theorem SubLineWitness.one_sub_avgOver_xPointOverlap_le_at
    (sublines : SubLineWitness P) (lines : CombinedLinesWitness S points δP)
    (first second : Placement) (hopposite : first.IsOpposite second) :
    1 - avgOver sublines.D (fun sample =>
      avgOver (uniformDistribution (DirectScalarQ P.extendedDirectLd))
        (fun t => xPointOverlapAt lines first second (sample.2, projX (directPointToPauli P
          (sample.1.base + t • sample.1.direction))))) ≤
      2 * Real.sqrt (4 * (P.m : ℝ) ^ 2 * δP) + 2 * Real.sqrt (4 * δQ) := by
  obtain ⟨components, hcomp, hmix⟩ :=
    SubLineWitness.exists_avgOver_X_eq_mixture P sublines (xPointOverlapAt lines first second)
  rw [hmix]
  have hsplit : avgOver components (fun c => 1 -
      avgOver (Distribution.prod (restrictedLinePointDist P c.1 c.2.1)
        (restrictedLinePointDist P c.1 c.2.2))
        (fun w => xPointOverlapAt lines first second ((w.1.1, w.2.1), w.1.2))) =
      1 - avgOver components (fun c =>
        avgOver (Distribution.prod (restrictedLinePointDist P c.1 c.2.1)
          (restrictedLinePointDist P c.1 c.2.2))
          (fun w => xPointOverlapAt lines first second ((w.1.1, w.2.1), w.1.2))) := by
    rw [avgOver_sub, avgOver_const_of_isProbability components hcomp]
  rw [← hsplit]
  calc
    _ ≤ avgOver components (fun _ =>
        2 * Real.sqrt (4 * (P.m : ℝ) ^ 2 * δP) + 2 * Real.sqrt (4 * δQ)) := by
      refine avgOver_mono _ _ _ fun c => ?_
      rw [avgOver_congr _ _ _ fun w => xPointOverlap_eq_at lines first second w]
      exact lines.one_sub_X_overlap_restricted_le_at first second hopposite c.1 c.1 c.2.1 c.2.2
    _ = _ := avgOver_const_of_isProbability components hcomp _


end

end MIPStarRE.QPBT
