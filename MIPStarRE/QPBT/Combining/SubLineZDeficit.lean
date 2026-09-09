import MIPStarRE.QPBT.Combining.ZEvalDeficit
import MIPStarRE.QPBT.Combining.UniformLinePoint

/-!
# Sub-line averages of the one-point overlaps

The two one-point overlaps of the paired-line measurement --- with the expanded
`X`-point effect at the `X`-point of the sampled extended point, and with the
expanded `Z`-point effect at its `Z`-point --- depend on the sample only through
the two source lines and one of the two source points.  Property~2 of the
sub-line lemma identifies the law of each such triple as a mixture of products
of two restricted line-point laws, with the fresh point of the other factor
unused.  Summing the line answers over the fibers of the evaluation at that
fresh point writes each overlap as the overlap of the evaluated pair-line
measurement with the retained point effect, so that the one-point deficits of
`MIPStarRE.QPBT.Combining.EvalDeficit` apply component by component.

The `_at` estimates and `xPointOverlapAt`, `zPointOverlapAt` retain arbitrary
opposite placements. The original overlap definitions and first-player
statements are unchanged. Only the one-point mixture laws are used.

## References

The statements support `lem:claim-17-2` and `lem:claim-17-3` in
`blueprint/src/chapter/ch15_qpbt_combining.tex`, paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1168-1239`; the
mixture is Property~2 of `lem:qld-sublines`.
-/

open scoped BigOperators

namespace MIPStarRE.QPBT

open MIPStarRE.LDT MIPStarRE.Quantum MIPStarRE.QPBT.DistanceCalculus

noncomputable section

/-! ## Regrouping the line answers by their evaluations -/

/-- Summing a paired-line answer against a family of point effects that
depends on the answer only through its two evaluations is summing the
evaluation classes of the paired-line measurement against that family.  This
is the fiber regrouping of the proofs of `lem:claim-17-1`, `lem:claim-17-2`,
and `lem:claim-17-3`, blueprint
`blueprint/src/chapter/ch15_qpbt_combining.tex:2651-2830`. -/
theorem regroup_line_answer_sum_at {P : AdmissibleParams} {ε δQ δP : ℝ}
    {S : ProjectiveSetting P ε} {points : CombinedPointsWitness S δQ}
    (lines : CombinedLinesWitness S points δP)
    (first second : Placement)
    (lineX lineZ : LineDesc P.toLdParams) (x z : Fin P.m → PauliScalar P)
    (G : Option (PauliScalar P) → Option (PauliScalar P) →
      Op (S.ExpandedLocalSpace second.side)) :
    (∑ o : Option (PauliScalar P) × Option (PauliScalar P),
        stateQForm S.psiHat
          ((S.placedMeasurement first
            ((lines.T first.side lineX lineZ).postprocess (fun fs =>
              (evalOpt lineX x fs.1, evalOpt lineZ z fs.2)))).effect o *
            S.place second (G o.1 o.2))) =
      ∑ fX, ∑ fZ, stateQForm S.psiHat
        (S.place first ((lines.T first.side lineX lineZ).effect (fX, fZ)) *
          S.place second (G (evalOpt lineX x fX) (evalOpt lineZ z fZ))) := by
  classical
  have hsum : ∀ (s : Finset (DegPoly P.toLdParams (P.m * P.d) ×
        DegPoly P.toLdParams (P.m * P.d)))
      (M : DegPoly P.toLdParams (P.m * P.d) ×
        DegPoly P.toLdParams (P.m * P.d) →
        Op (S.ExpandedLocalSpace first.side))
      (N : Op (SixReg P S.toStrategy.ιA S.toStrategy.ιB)),
      stateQForm S.psiHat (S.place first (∑ fs ∈ s, M fs) * N) =
        ∑ fs ∈ s, stateQForm S.psiHat (S.place first (M fs) * N) := by
    intro s M N
    rw [S.place_finsetSum]
    simp [stateQForm, applyOperatorToState, Finset.sum_mul]
  calc
    (∑ o : Option (PauliScalar P) × Option (PauliScalar P),
          stateQForm S.psiHat
            ((S.placedMeasurement first
              ((lines.T first.side lineX lineZ).postprocess (fun fs =>
                (evalOpt lineX x fs.1, evalOpt lineZ z fs.2)))).effect o *
              S.place second (G o.1 o.2))) =
        ∑ o : Option (PauliScalar P) × Option (PauliScalar P),
          ∑ fs ∈ Finset.univ.filter (fun fs =>
              (evalOpt lineX x fs.1, evalOpt lineZ z fs.2) = o),
            stateQForm S.psiHat
              (S.place first ((lines.T first.side lineX lineZ).effect fs) *
                S.place second (G o.1 o.2)) := by
      refine Finset.sum_congr rfl fun o _ => ?_
      rw [ProjectiveSetting.placedMeasurement_effect,
        MIPStarRE.Quantum.Measurement.postprocess_effect]
      exact hsum _ _ _
    _ = ∑ o : Option (PauliScalar P) × Option (PauliScalar P),
          ∑ fs ∈ Finset.univ.filter (fun fs =>
              (evalOpt lineX x fs.1, evalOpt lineZ z fs.2) = o),
            stateQForm S.psiHat
              (S.place first ((lines.T first.side lineX lineZ).effect fs) *
                S.place second
                  (G (evalOpt lineX x fs.1) (evalOpt lineZ z fs.2))) := by
      refine Finset.sum_congr rfl fun o _ =>
        Finset.sum_congr rfl fun fs hfs => ?_
      rw [← (Finset.mem_filter.mp hfs).2]
    _ = ∑ fs : DegPoly P.toLdParams (P.m * P.d) ×
          DegPoly P.toLdParams (P.m * P.d),
          stateQForm S.psiHat
            (S.place first ((lines.T first.side lineX lineZ).effect fs) *
              S.place second
                (G (evalOpt lineX x fs.1) (evalOpt lineZ z fs.2))) :=
      Finset.sum_fiberwise_of_maps_to (fun fs _ => Finset.mem_univ _) _
    _ = ∑ fX, ∑ fZ, stateQForm S.psiHat
          (S.place first ((lines.T first.side lineX lineZ).effect (fX, fZ)) *
            S.place second (G (evalOpt lineX x fX) (evalOpt lineZ z fZ))) :=
      Fintype.sum_prod_type (f := fun fs => stateQForm S.psiHat
        (S.place first ((lines.T first.side lineX lineZ).effect fs) *
          S.place second (G (evalOpt lineX x fs.1) (evalOpt lineZ z fs.2))))

theorem regroup_line_answer_sum {P : AdmissibleParams} {ε δQ δP : ℝ}
    {S : ProjectiveSetting P ε} {points : CombinedPointsWitness S δQ}
    (lines : CombinedLinesWitness S points δP)
    (lineX lineZ : LineDesc P.toLdParams) (x z : Fin P.m → PauliScalar P)
    (G : Option (PauliScalar P) → Option (PauliScalar P) →
      Op (S.ExpandedLocalSpace Placement.BA''.side)) :
    (∑ o : Option (PauliScalar P) × Option (PauliScalar P),
        stateQForm S.psiHat
          ((S.placedMeasurement .AA'
            ((lines.T .alice lineX lineZ).postprocess (fun fs =>
              (evalOpt lineX x fs.1, evalOpt lineZ z fs.2)))).effect o *
            S.place .BA'' (G o.1 o.2))) =
      ∑ fX, ∑ fZ, stateQForm S.psiHat
        (S.place .AA' ((lines.T .alice lineX lineZ).effect (fX, fZ)) *
          S.place .BA'' (G (evalOpt lineX x fX) (evalOpt lineZ z fZ))) := by
  exact regroup_line_answer_sum_at lines .AA' .BA'' lineX lineZ x z G

/-- The sub-line average of a function of the two source lines and the
`Z`-point of the sampled extended point is a mixture of averages over products
of two restricted line-point laws, the `Z`-point being the point of the second
factor.  This is the use of Property~2 of `lem:qld-sublines` in the proof of
`lem:claim-17-3`, blueprint `blueprint/src/chapter/ch15_qpbt_combining.tex`,
paper `references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1204-1239`. -/
theorem SubLineWitness.exists_avgOver_Z_eq_mixture (P : AdmissibleParams)
    (sublines : SubLineWitness P)
    (F : (LineDesc P.toLdParams × LineDesc P.toLdParams) ×
      (Fin P.m → PauliScalar P) → ℝ) :
    ∃ components : Distribution (SubLineComponent P), components.IsProbability ∧
      avgOver sublines.D (fun sample =>
          avgOver (uniformDistribution (DirectScalarQ P.extendedDirectLd))
            (fun t => F (sample.2, projZ (directPointToPauli P
              (sample.1.base + t • sample.1.direction))))) =
        avgOver components (fun c =>
          avgOver (Distribution.prod (restrictedLinePointDist P c.1 c.2.1)
              (restrictedLinePointDist P c.1 c.2.2))
            (fun w => F ((w.1.1, w.2.1), w.2.2))) := by
  obtain ⟨components, hcomp, -, hZ⟩ := sublines.source_mixture
  refine ⟨components, hcomp, ?_⟩
  have h1 : avgOver sublines.D (fun sample =>
      avgOver (uniformDistribution (DirectScalarQ P.extendedDirectLd))
        (fun t => F (sample.2, projZ (directPointToPauli P
          (sample.1.base + t • sample.1.direction))))) =
      avgOver ((subLinePointDist P sublines.D).map subLineZProjection) F := by
    rw [Distribution.avgOver_map, subLinePointDist, Distribution.avgOver_map,
      avgOver_prod]
    rfl
  rw [h1, hZ, avgOver_bind]
  refine avgOver_congr _ _ _ fun c => ?_
  rw [subLineZComponentDist, Distribution.avgOver_map, Distribution.prod_map_left,
    Distribution.avgOver_map]

/-! ## The two one-point overlaps -/

section Overlaps

variable {P : AdmissibleParams} {ε δQ δP : ℝ} {S : ProjectiveSetting P ε}
  {points : CombinedPointsWitness S δQ}

/-- The overlap of the paired-line measurement at two source lines with the
expanded `Z`-point effect at a point, summed over the line answers.  This is
the integrand of the left-hand side of `lem:claim-17-3`, as a function of the
two source lines and the `Z`-point alone. -/
def zPointOverlapAt (lines : CombinedLinesWitness S points δP)
    (first second : Placement)
    (w : (LineDesc P.toLdParams × LineDesc P.toLdParams) ×
      (Fin P.m → PauliScalar P)) : ℝ :=
  ∑ fX, ∑ fZ, stateQForm S.psiHat
    (S.place first ((lines.T first.side w.1.1 w.1.2).effect (fX, fZ)) *
      S.place second ((S.pointMeasExpOption second.side .Z w.2).effect (evalOpt w.1.2 w.2 fZ)))

/-- The original first-player specialization of the placed overlap. -/
def zPointOverlap (lines : CombinedLinesWitness S points δP)
    (w : (LineDesc P.toLdParams × LineDesc P.toLdParams) ×
      (Fin P.m → PauliScalar P)) : ℝ :=
  ∑ fX, ∑ fZ, stateQForm S.psiHat
    (S.place .AA' ((lines.T .alice w.1.1 w.1.2).effect (fX, fZ)) *
      S.place .BA'' ((S.pointMeasExpOption .bob .Z w.2).effect (evalOpt w.1.2 w.2 fZ)))

/-- At a pair of line-point pairs, the `Z`-point overlap is the overlap of the
evaluated pair-line measurement with the completed `Z`-point measurement; the
`X`-point of the first pair only labels the evaluation classes. -/
theorem zPointOverlap_eq_at (lines : CombinedLinesWitness S points δP)
    (first second : Placement)
    (w : LinePointPairSample P) :
    zPointOverlapAt lines first second ((w.1.1, w.2.1), w.2.2) =
      ∑ o : Option (PauliScalar P) × Option (PauliScalar P),
        stateQForm S.psiHat
          (S.place first
            (((lines.T first.side w.1.1 w.2.1).postprocess fun fs =>
              (evalOpt w.1.1 w.1.2 fs.1, evalOpt w.2.1 w.2.2 fs.2)).effect o) *
            S.place second ((S.pointMeasExpOption second.side .Z w.2.2).effect o.2)) :=
  (regroup_line_answer_sum_at lines first second w.1.1 w.2.1 w.1.2 w.2.2
    (fun _ o2 => (S.pointMeasExpOption second.side .Z w.2.2).effect o2)).symm

/-- The original first-player specialization of the placed estimate. -/
theorem zPointOverlap_eq (lines : CombinedLinesWitness S points δP)
    (w : LinePointPairSample P) :
    zPointOverlap lines ((w.1.1, w.2.1), w.2.2) =
      ∑ o : Option (PauliScalar P) × Option (PauliScalar P),
        stateQForm S.psiHat
          (S.place .AA'
            (((lines.T .alice w.1.1 w.2.1).postprocess fun fs =>
              (evalOpt w.1.1 w.1.2 fs.1, evalOpt w.2.1 w.2.2 fs.2)).effect o) *
            S.place .BA'' ((S.pointMeasExpOption .bob .Z w.2.2).effect o.2)) := by
  exact zPointOverlap_eq_at lines .AA' .BA'' w

/-- The `Z`-point overlap is nonnegative. -/
theorem zPointOverlap_nonneg_at (lines : CombinedLinesWitness S points δP)
    (first second : Placement) (hopposite : first.IsOpposite second)
    (w : (LineDesc P.toLdParams × LineDesc P.toLdParams) ×
      (Fin P.m → PauliScalar P)) :
    0 ≤ zPointOverlapAt lines first second w :=
  Finset.sum_nonneg fun fX _ => Finset.sum_nonneg fun fZ _ =>
    stateQForm_nonneg _ (S.place_mul_place_nonneg first second hopposite
      ((lines.T first.side w.1.1 w.1.2).pos (fX, fZ))
      ((S.pointMeasExpOption second.side .Z w.2).pos (evalOpt w.1.2 w.2 fZ)))

/-- The original first-player specialization of the placed estimate. -/
theorem zPointOverlap_nonneg (lines : CombinedLinesWitness S points δP)
    (w : (LineDesc P.toLdParams × LineDesc P.toLdParams) ×
      (Fin P.m → PauliScalar P)) :
    0 ≤ zPointOverlap lines w := by
  exact zPointOverlap_nonneg_at lines .AA' .BA'' trivial w

/-- The sub-line average of the `Z`-point overlap is at most one. -/
theorem SubLineWitness.avgOver_zPointOverlap_le_one_at (sublines : SubLineWitness P)
    (lines : CombinedLinesWitness S points δP)
    (first second : Placement) (hopposite : first.IsOpposite second) :
    avgOver sublines.D (fun sample =>
      avgOver (uniformDistribution (DirectScalarQ P.extendedDirectLd))
        (fun t => zPointOverlapAt lines first second (sample.2, projZ (directPointToPauli P
          (sample.1.base + t • sample.1.direction))))) ≤ 1 := by
  obtain ⟨components, hcomp, hmix⟩ :=
    SubLineWitness.exists_avgOver_Z_eq_mixture P sublines (zPointOverlapAt lines first second)
  rw [hmix]
  have hc : ∀ c : SubLineComponent P,
      avgOver (Distribution.prod (restrictedLinePointDist P c.1 c.2.1)
          (restrictedLinePointDist P c.1 c.2.2))
        (fun w => zPointOverlapAt lines first second ((w.1.1, w.2.1), w.2.2)) ≤ 1 := by
    intro c
    have h := avgOver_sum_stateQForm_mul_le_one
      (Distribution.prod (restrictedLinePointDist P c.1 c.2.1)
        (restrictedLinePointDist P c.1 c.2.2))
      (fun w : LinePointPairSample P => S.placedMeasurement first
        ((lines.T first.side w.1.1 w.2.1).postprocess fun fs =>
          (evalOpt w.1.1 w.1.2 fs.1, evalOpt w.2.1 w.2.2 fs.2)))
      (fun (w : LinePointPairSample P)
          (o : Option (PauliScalar P) × Option (PauliScalar P)) =>
        S.place second ((S.pointMeasExpOption second.side .Z w.2.2).effect o.2))
      S.psiHat
      (Distribution.prod_isProbability _ _
        (restrictedLinePointDist_isProbability P c.1 c.2.1)
        (restrictedLinePointDist_isProbability P c.1 c.2.2))
      S.psiHat_norm
      (fun w o => S.place_isProj _ (S.pointMeasExpOption_isProj _ _ _ _))
      (fun w o => S.place_comm first second hopposite _ _)
    simp only [ProjectiveSetting.placedMeasurement_effect] at h
    rw [avgOver_congr _ _ _ fun w => zPointOverlap_eq_at lines first second w]
    exact h
  calc
    _ ≤ avgOver components (fun _ => (1 : ℝ)) := avgOver_mono _ _ _ hc
    _ = 1 := avgOver_const_of_isProbability components hcomp 1

/-- The original first-player specialization of the placed estimate. -/
theorem SubLineWitness.avgOver_zPointOverlap_le_one (sublines : SubLineWitness P)
    (lines : CombinedLinesWitness S points δP) :
    avgOver sublines.D (fun sample =>
      avgOver (uniformDistribution (DirectScalarQ P.extendedDirectLd))
        (fun t => zPointOverlap lines (sample.2, projZ (directPointToPauli P
          (sample.1.base + t • sample.1.direction))))) ≤ 1 := by
  exact SubLineWitness.avgOver_zPointOverlap_le_one_at sublines lines .AA' .BA'' trivial

/-- The deficit of the sub-line average of the `Z`-point overlap is bounded by
the inflated line and point consistency errors.  This is the bound on the
deficit in the proof of `lem:claim-17-3`, blueprint
`blueprint/src/chapter/ch15_qpbt_combining.tex`, paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1204-1239`. -/
theorem SubLineWitness.one_sub_avgOver_zPointOverlap_le_at
    (sublines : SubLineWitness P) (lines : CombinedLinesWitness S points δP)
    (first second : Placement) (hopposite : first.IsOpposite second) :
    1 - avgOver sublines.D (fun sample =>
      avgOver (uniformDistribution (DirectScalarQ P.extendedDirectLd))
        (fun t => zPointOverlapAt lines first second (sample.2, projZ (directPointToPauli P
          (sample.1.base + t • sample.1.direction))))) ≤
      2 * Real.sqrt (4 * (P.m : ℝ) ^ 2 * δP) + 2 * Real.sqrt (4 * δQ) := by
  obtain ⟨components, hcomp, hmix⟩ :=
    SubLineWitness.exists_avgOver_Z_eq_mixture P sublines (zPointOverlapAt lines first second)
  rw [hmix]
  have hsplit : avgOver components (fun c => 1 -
      avgOver (Distribution.prod (restrictedLinePointDist P c.1 c.2.1)
        (restrictedLinePointDist P c.1 c.2.2))
        (fun w => zPointOverlapAt lines first second ((w.1.1, w.2.1), w.2.2))) =
      1 - avgOver components (fun c =>
        avgOver (Distribution.prod (restrictedLinePointDist P c.1 c.2.1)
          (restrictedLinePointDist P c.1 c.2.2))
          (fun w => zPointOverlapAt lines first second ((w.1.1, w.2.1), w.2.2))) := by
    rw [avgOver_sub, avgOver_const_of_isProbability components hcomp]
  rw [← hsplit]
  calc
    _ ≤ avgOver components (fun _ =>
        2 * Real.sqrt (4 * (P.m : ℝ) ^ 2 * δP) + 2 * Real.sqrt (4 * δQ)) := by
      refine avgOver_mono _ _ _ fun c => ?_
      rw [avgOver_congr _ _ _ fun w => zPointOverlap_eq_at lines first second w]
      exact lines.one_sub_Z_overlap_restricted_le_at first second hopposite c.1 c.1 c.2.1 c.2.2
    _ = _ := avgOver_const_of_isProbability components hcomp _

/-- The original first-player specialization of the placed estimate. -/
theorem SubLineWitness.one_sub_avgOver_zPointOverlap_le
    (sublines : SubLineWitness P) (lines : CombinedLinesWitness S points δP) :
    1 - avgOver sublines.D (fun sample =>
      avgOver (uniformDistribution (DirectScalarQ P.extendedDirectLd))
        (fun t => zPointOverlap lines (sample.2, projZ (directPointToPauli P
          (sample.1.base + t • sample.1.direction))))) ≤
      2 * Real.sqrt (4 * (P.m : ℝ) ^ 2 * δP) + 2 * Real.sqrt (4 * δQ) := by
  exact SubLineWitness.one_sub_avgOver_zPointOverlap_le_at sublines lines .AA' .BA'' trivial


end Overlaps

end

end MIPStarRE.QPBT
