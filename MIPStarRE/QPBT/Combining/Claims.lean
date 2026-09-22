import MIPStarRE.QPBT.Combining.ErrorBounds
import MIPStarRE.QPBT.Combining.OrderedPoints
import MIPStarRE.QPBT.Combining.OverlapGap
import MIPStarRE.QPBT.Combining.ComplexOverlapGap
import MIPStarRE.QPBT.Combining.Lines.CombinedMeasurement
import MIPStarRE.QPBT.Combining.Lines.ConcreteXDeficit
import MIPStarRE.QPBT.Combining.Lines.Construction
import MIPStarRE.QPBT.Combining.SubLineZDeficit
import MIPStarRE.QPBT.Combining.SubLineComplex
import MIPStarRE.QPBT.Combining.UniformLinePoint
import MIPStarRE.QPBT.Combining.Witnesses
import MIPStarRE.QPBT.Games.DistanceTheorems.TensorSupport

/-!
# Scalar claims for combining the Pauli bases

This module records auxiliary real-part and complex-modulus estimates for the
directly indexed subline law. The complex Claim 17-1 estimate is imported from
`SubLineComplex`; Claim 17-2 uses the concrete X-Z-X measurement, and Claim 17-3
uses the proved reality of the Z overlap. The source claims remain separate,
uncertified blueprint statements until the distribution and evaluation transport
obligations are discharged. Line-polynomial evaluation uses the
existing `Option` completion, so no field value is substituted when an evaluation
is undefined.

## References

The source comparisons are blueprint `lem:claim-17-1`, `lem:claim-17-2`, and
`lem:claim-17-3`, with paper origin
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1140-1239`.
-/

open scoped BigOperators

namespace MIPStarRE.QPBT

open MIPStarRE.LDT hiding Measurement
open MIPStarRE.Quantum MIPStarRE.QPBT.DistanceCalculus

noncomputable section

set_option synthInstance.maxSize 400

/-- Regroup paired-line answers by their two optional evaluations. -/
private theorem regroup_placed_line_answer_sum {P : AdmissibleParams} {ε δQ δP : ℝ}
    {S : ProjectiveSetting P ε} {points : CombinedPointsWitness S δQ}
    (lines : CombinedLinesWitness S points δP)
    (lineX lineZ : LineDesc P.toLdParams) (x z : Fin P.m → PauliScalar P)
    (G : Option (PauliScalar P) → Option (PauliScalar P) →
      Op (S.ExpandedLocalSpace Placement.BA''.side)) :
    (∑ o : Option (PauliScalar P) × Option (PauliScalar P),
        stateQForm S.psiHat
          (((S.placedMeasurement .AA' (lines.T .alice lineX lineZ)).postprocess
            (fun fs => (evalOpt lineX x fs.1, evalOpt lineZ z fs.2))).effect o *
            S.place .BA'' (G o.1 o.2))) =
      ∑ fX, ∑ fZ, stateQForm S.psiHat
        (S.place .AA' ((lines.T .alice lineX lineZ).effect (fX, fZ)) *
          S.place .BA'' (G (evalOpt lineX x fX) (evalOpt lineZ z fZ))) := by
  classical
  refine Eq.trans ?_ (regroup_line_answer_sum lines lineX lineZ x z G)
  refine Finset.sum_congr rfl fun o _ => ?_
  apply congrArg (fun M => stateQForm S.psiHat (M * S.place .BA'' (G o.1 o.2)))
  rw [ProjectiveSetting.placedMeasurement_effect,
    MIPStarRE.Quantum.Measurement.postprocess_effect,
    MIPStarRE.Quantum.Measurement.postprocess_effect]
  refine Eq.trans (Finset.sum_congr rfl fun fs _ =>
    S.placedMeasurement_effect .AA' _ fs) ?_
  exact (S.place_finsetSum .AA' _ _).symm

set_option maxHeartbeats 400000 in
-- The nested polynomial and completed-outcome sums require extra elaboration steps.
/-- Formalization-only real-part estimate for the directly indexed subline law.

**Scope restriction:** The conclusion bounds the absolute difference of real parts
by `2 * sqrt δQ`. Paper `claim:17-1`, at
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1140-1166`,
bounds the complex modulus over the source law. Neither the imaginary-part bound
nor transport from `SubLineWitness` is asserted here. See issue #474 and
`docs/paper-gaps/qpbt_subline-claims-line-marginal.tex`; distribution transport is
recorded in `docs/paper-gaps/qpbt_ld-dimension-divisibility.tex`.
The source statement remains blueprint `lem:claim-17-1`, without certification. -/
theorem subline_replace_by_ordered_product_re_direct :
    ∃ C : ℝ, 0 < C ∧
      ∀ (P : AdmissibleParams) (ε δQ δP : ℝ)
        (S : ProjectiveSetting P ε) (points : CombinedPointsWitness S δQ)
        (lines : CombinedLinesWitness S points δP) (sublines : SubLineWitness P),
        |avgOver sublines.D (fun sample =>
            avgOver (uniformDistribution (DirectScalarQ P.extendedDirectLd)) (fun t =>
              let u := directPointToPauli P
                (sample.1.base + t • sample.1.direction)
              let x := projX u
              let z := projZ u
              ∑ fX, ∑ fZ,
                (inner ℂ S.psiHat ((EuclideanSpace.equiv
                  (SixReg P S.toStrategy.ιA S.toStrategy.ιB) ℂ).symm
                    ((S.place .AA'
                        ((lines.T .alice sample.2.1 sample.2.2).effect (fX, fZ)) *
                      S.place .BA''
                        (((points.Q .bob x z).postprocess fun ab =>
                          (some ab.1, some ab.2)).effect
                            (evalOpt sample.2.1 x fX,
                              evalOpt sample.2.2 z fZ))).mulVec S.psiHat))).re)) -
          avgOver sublines.D (fun sample =>
            avgOver (uniformDistribution (DirectScalarQ P.extendedDirectLd)) (fun t =>
              let u := directPointToPauli P
                (sample.1.base + t • sample.1.direction)
              let x := projX u
              let z := projZ u
              ∑ fX, ∑ fZ,
                (inner ℂ S.psiHat ((EuclideanSpace.equiv
                  (SixReg P S.toStrategy.ιA S.toStrategy.ιB) ℂ).symm
                    ((S.place .AA'
                        ((lines.T .alice sample.2.1 sample.2.2).effect (fX, fZ)) *
                      S.place .BA''
                        (S.expPointEffectAtLineAnswer .bob .Z sample.2.2 z fZ *
                          S.expPointEffectAtLineAnswer .bob .X sample.2.1 x fX)).mulVec
                            S.psiHat))).re))| ≤
          C * Real.rpow δQ (1 / 2 : ℝ) := by
  refine ⟨2, by norm_num, ?_⟩
  intro P ε δQ δP S points lines sublines
  classical
  have hside : ∀ G : (Fin P.m → PauliScalar P) → (Fin P.m → PauliScalar P) →
      Option (PauliScalar P) → Option (PauliScalar P) →
      Op (S.ExpandedLocalSpace Placement.BA''.side),
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
                    ((S.place .AA'
                        ((lines.T .alice sample.2.1 sample.2.2).effect
                          (fX, fZ)) *
                      S.place .BA''
                        (G x z (evalOpt sample.2.1 x fX)
                          (evalOpt sample.2.2 z fZ))).mulVec
                            S.psiHat))).re)) =
        avgOver (Distribution.prod sublines.D
            (uniformDistribution (DirectScalarQ P.extendedDirectLd)))
          (fun s => ∑ o : Option (PauliScalar P) × Option (PauliScalar P),
            stateQForm S.psiHat
              (((S.placedMeasurement .AA'
                (lines.T .alice s.1.2.1 s.1.2.2)).postprocess (fun fs =>
                  (evalOpt s.1.2.1 (projX (directPointToPauli P
                      (s.1.1.base + s.2 • s.1.1.direction))) fs.1,
                    evalOpt s.1.2.2 (projZ (directPointToPauli P
                      (s.1.1.base + s.2 • s.1.1.direction))) fs.2))).effect o *
                S.place .BA''
                  (G (projX (directPointToPauli P
                      (s.1.1.base + s.2 • s.1.1.direction)))
                    (projZ (directPointToPauli P
                      (s.1.1.base + s.2 • s.1.1.direction))) o.1 o.2))) := by
    intro G
    rw [SandwichProduct.avgOver_distribution_prod]
    refine avgOver_congr _ _ _ fun sample => ?_
    refine avgOver_congr _ _ _ fun t => ?_
    exact (regroup_placed_line_answer_sum lines sample.2.1 sample.2.2 _ _ (G _ _)).symm
  have hprob : (Distribution.prod sublines.D
      (uniformDistribution (DirectScalarQ P.extendedDirectLd))).IsProbability :=
    Distribution.prod_isProbability _ _ sublines.isProbability
      (uniformDistribution_isProbability _)
  have hdist : opFamilyDistSq
      (Distribution.prod sublines.D
        (uniformDistribution (DirectScalarQ P.extendedDirectLd)))
      (fun (s : SubLineTriple P × DirectScalarQ P.extendedDirectLd)
          (o : Option (PauliScalar P) × Option (PauliScalar P)) =>
        S.place .BA''
        (((points.Q .bob
            (projX (directPointToPauli P
              (s.1.1.base + s.2 • s.1.1.direction)))
            (projZ (directPointToPauli P
              (s.1.1.base + s.2 • s.1.1.direction)))).postprocess fun ab =>
          (some ab.1, some ab.2)).effect (o.1, o.2)))
      (fun (s : SubLineTriple P × DirectScalarQ P.extendedDirectLd)
          (o : Option (PauliScalar P) × Option (PauliScalar P)) =>
        S.place .BA''
        ((S.pointMeasExpOption .bob .Z
            (projZ (directPointToPauli P
              (s.1.1.base + s.2 • s.1.1.direction)))).effect o.2 *
          (S.pointMeasExpOption .bob .X
            (projX (directPointToPauli P
              (s.1.1.base + s.2 • s.1.1.direction)))).effect o.1))
      S.psiHat ≤ 4 * δQ := by
    calc
      opFamilyDistSq
          (Distribution.prod sublines.D
            (uniformDistribution (DirectScalarQ P.extendedDirectLd))) _ _
          S.psiHat =
        avgOver (Distribution.prod sublines.D
            (uniformDistribution (DirectScalarQ P.extendedDirectLd)))
          (fun s => ∑ ab : PauliScalar P × PauliScalar P,
            ‖applyOperatorToState
              (S.place .BA'' ((points.Q .bob
                  (projX (directPointToPauli P
                    (s.1.1.base + s.2 • s.1.1.direction)))
                  (projZ (directPointToPauli P
                    (s.1.1.base + s.2 • s.1.1.direction)))).effect ab) -
                S.place .BA''
                  ((S.pointMeasExp .bob .Z
                      (projZ (directPointToPauli P
                        (s.1.1.base + s.2 • s.1.1.direction)))).effect ab.2 *
                    (S.pointMeasExp .bob .X
                      (projX (directPointToPauli P
                        (s.1.1.base + s.2 • s.1.1.direction)))).effect ab.1))
              S.psiHat‖ ^ 2) :=
        avgOver_congr _ _ _ fun s => S.completedPair_norm_sq_sum_ZX points .BA'' _ _
      _ = avgOver sublines.D (fun sample =>
            avgOver (uniformDistribution (DirectScalarQ P.extendedDirectLd))
              (fun t => ∑ ab : PauliScalar P × PauliScalar P,
                ‖applyOperatorToState
                  (S.place .BA'' ((points.Q .bob
                      (projX (directPointToPauli P
                        (sample.1.base + t • sample.1.direction)))
                      (projZ (directPointToPauli P
                        (sample.1.base + t • sample.1.direction)))).effect ab) -
                    S.place .BA''
                      ((S.pointMeasExp .bob .Z
                          (projZ (directPointToPauli P
                            (sample.1.base + t • sample.1.direction)))).effect ab.2 *
                        (S.pointMeasExp .bob .X
                          (projX (directPointToPauli P
                            (sample.1.base + t • sample.1.direction)))).effect ab.1))
                  S.psiHat‖ ^ 2)) :=
        SandwichProduct.avgOver_distribution_prod _ _ _
      _ = avgOver (uniformDistribution
            ((Fin P.m → PauliScalar P) × (Fin P.m → PauliScalar P)))
          (fun xz => ∑ ab : PauliScalar P × PauliScalar P,
            ‖applyOperatorToState
              (S.place .BA'' ((points.Q .bob xz.1 xz.2).effect ab) -
                S.place .BA''
                  ((S.pointMeasExp .bob .Z xz.2).effect ab.2 *
                    (S.pointMeasExp .bob .X xz.1).effect ab.1))
              S.psiHat‖ ^ 2) :=
        SubLineWitness.avgOver_projX_projZ P sublines
          (fun xz => ∑ ab : PauliScalar P × PauliScalar P,
            ‖applyOperatorToState
              (S.place .BA'' ((points.Q .bob xz.1 xz.2).effect ab) -
                S.place .BA''
                  ((S.pointMeasExp .bob .Z xz.2).effect ab.2 *
                    (S.pointMeasExp .bob .X xz.1).effect ab.1))
              S.psiHat‖ ^ 2)
      _ ≤ 4 * δQ := points.orderedZX_dist_le .BA''
  have hgap := abs_overlap_gap_le_sqrt_of_opFamilyDistSq
    (Distribution.prod sublines.D
      (uniformDistribution (DirectScalarQ P.extendedDirectLd)))
    (fun s => (S.placedMeasurement .AA'
      (lines.T .alice s.1.2.1 s.1.2.2)).postprocess (fun fs =>
        (evalOpt s.1.2.1 (projX (directPointToPauli P
            (s.1.1.base + s.2 • s.1.1.direction))) fs.1,
          evalOpt s.1.2.2 (projZ (directPointToPauli P
            (s.1.1.base + s.2 • s.1.1.direction))) fs.2)))
    (fun (s : SubLineTriple P × DirectScalarQ P.extendedDirectLd)
        (o : Option (PauliScalar P) × Option (PauliScalar P)) =>
      S.place .BA''
      (((points.Q .bob
          (projX (directPointToPauli P
            (s.1.1.base + s.2 • s.1.1.direction)))
          (projZ (directPointToPauli P
            (s.1.1.base + s.2 • s.1.1.direction)))).postprocess fun ab =>
        (some ab.1, some ab.2)).effect (o.1, o.2)))
    (fun (s : SubLineTriple P × DirectScalarQ P.extendedDirectLd)
        (o : Option (PauliScalar P) × Option (PauliScalar P)) =>
      S.place .BA''
      ((S.pointMeasExpOption .bob .Z
          (projZ (directPointToPauli P
            (s.1.1.base + s.2 • s.1.1.direction)))).effect o.2 *
        (S.pointMeasExpOption .bob .X
          (projX (directPointToPauli P
            (s.1.1.base + s.2 • s.1.1.direction)))).effect o.1))
    S.psiHat hprob S.psiHat_norm (4 * δQ) hdist
  simp only [← ProjectiveSetting.pointMeasExpOption_effect_evalOpt]
  rw [hside (fun x z o1 o2 => ((points.Q .bob x z).postprocess fun ab =>
      (some ab.1, some ab.2)).effect (o1, o2)),
    hside (fun x z o1 o2 => (S.pointMeasExpOption .bob .Z z).effect o2 *
      (S.pointMeasExpOption .bob .X x).effect o1)]
  refine hgap.trans ?_
  have h4 : Real.sqrt 4 = 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num,
      Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 2)]
  rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 4), h4, Real.sqrt_eq_rpow]
  exact le_rfl

/-! ### Shared data of the two `X`-factor removal estimates

The real-part estimate and the complex-modulus estimate below compare the same
two averages, over the same sampling law, with the same placed X-Z-X line
measurement and the same two placed point factors, and both reduce to the same
X-overlap deficit. Only the Cauchy--Schwarz estimate applied at the end differs.
The common families and the common deficit bound are therefore recorded once
here and used by both theorems. -/

/-- The sampling law of the `X`-factor removal estimates: a sub-line triple
together with an independent uniform affine parameter. -/
private def removeXLaw (P : AdmissibleParams) (sublines : SubLineWitness P) :
    Distribution (SubLineTriple P × DirectScalarQ P.extendedDirectLd) :=
  Distribution.prod sublines.D
    (uniformDistribution (DirectScalarQ P.extendedDirectLd))

/-- The placed X-Z-X line measurement of the `X`-factor removal estimates. -/
private def removeXLine {P : AdmissibleParams} {ε : ℝ} (S : ProjectiveSetting P ε)
    (s : SubLineTriple P × DirectScalarQ P.extendedDirectLd) :
    Measurement (DegPoly P.toLdParams (P.m * P.d) ×
      DegPoly P.toLdParams (P.m * P.d))
      (SixReg P S.toStrategy.ιA S.toStrategy.ιB) :=
  S.placedMeasurement .AA' (S.combinedLineMeasurement .alice s.1.2.1 s.1.2.2)

/-- The placed `X` point factor that the removal estimates drop. -/
private def removeXPointX {P : AdmissibleParams} {ε : ℝ} (S : ProjectiveSetting P ε)
    (s : SubLineTriple P × DirectScalarQ P.extendedDirectLd)
    (fs : DegPoly P.toLdParams (P.m * P.d) ×
      DegPoly P.toLdParams (P.m * P.d)) :
    Op (SixReg P S.toStrategy.ιA S.toStrategy.ιB) :=
  S.place .BA'' (S.expPointEffectAtLineAnswer .bob .X s.1.2.1
    (projX (directPointToPauli P (s.1.1.base + s.2 • s.1.1.direction))) fs.1)

/-- The placed `Z` point factor that the removal estimates keep. -/
private def removeXPointZ {P : AdmissibleParams} {ε : ℝ} (S : ProjectiveSetting P ε)
    (s : SubLineTriple P × DirectScalarQ P.extendedDirectLd)
    (fs : DegPoly P.toLdParams (P.m * P.d) ×
      DegPoly P.toLdParams (P.m * P.d)) :
    Op (SixReg P S.toStrategy.ιA S.toStrategy.ιB) :=
  S.place .BA'' (S.expPointEffectAtLineAnswer .bob .Z s.1.2.2
    (projZ (directPointToPauli P (s.1.1.base + s.2 • s.1.1.direction))) fs.2)

/-- The placed ordered `Z`-`X` point product of the removal estimates. -/
private def removeXPointZX {P : AdmissibleParams} {ε : ℝ} (S : ProjectiveSetting P ε)
    (s : SubLineTriple P × DirectScalarQ P.extendedDirectLd)
    (fs : DegPoly P.toLdParams (P.m * P.d) ×
      DegPoly P.toLdParams (P.m * P.d)) :
    Op (SixReg P S.toStrategy.ιA S.toStrategy.ιB) :=
  S.place .BA''
    (S.expPointEffectAtLineAnswer .bob .Z s.1.2.2
        (projZ (directPointToPauli P
          (s.1.1.base + s.2 • s.1.1.direction))) fs.2 *
      S.expPointEffectAtLineAnswer .bob .X s.1.2.1
        (projX (directPointToPauli P
          (s.1.1.base + s.2 • s.1.1.direction))) fs.1)

private theorem removeXLaw_isProbability {P : AdmissibleParams}
    (sublines : SubLineWitness P) : (removeXLaw P sublines).IsProbability :=
  Distribution.prod_isProbability _ _ sublines.isProbability
    (uniformDistribution_isProbability _)

/-- A placed point effect read off a line answer is a projection. -/
private theorem place_expPointEffectAtLineAnswer_isProj {P : AdmissibleParams}
    {ε : ℝ} (S : ProjectiveSetting P ε) (W : PauliKind)
    (line : LineDesc P.toLdParams) (u : Fin P.m → PauliScalar P)
    (f : DegPoly P.toLdParams (P.m * P.d)) :
    IsProj (S.place .BA'' (S.expPointEffectAtLineAnswer .bob W line u f)) := by
  rw [← S.pointMeasExpOption_effect_evalOpt]
  exact S.place_isProj .BA'' (S.pointMeasExpOption_isProj .bob W _ _)

/-- The placed line effects commute with every operator placed on the opposite
register pair. -/
private theorem removeXLine_commute_place {P : AdmissibleParams} {ε : ℝ}
    (S : ProjectiveSetting P ε)
    (s : SubLineTriple P × DirectScalarQ P.extendedDirectLd)
    (fs : DegPoly P.toLdParams (P.m * P.d) ×
      DegPoly P.toLdParams (P.m * P.d))
    (T : Op (S.ExpandedLocalSpace Placement.BA''.side)) :
    Commute ((removeXLine S s).effect fs) (S.place .BA'' T) := by
  change Commute
    (S.place .AA'
      ((S.combinedLineMeasurement .alice s.1.2.1 s.1.2.2).effect fs))
    (S.place .BA'' T)
  exact S.place_comm .AA' .BA'' trivial _ _

/-- The common deficit estimate of the two `X`-factor removal theorems: the
square root of the X-overlap deficit of the constructed X-Z-X measurement is at
most `C * m * deltaLine ε ^ (1/2)`. This is the sole quantitative input of both
estimates; it uses `exists_concreteXPointOverlap_deficit_le` and assumes no
marginal identity. -/
private theorem exists_removeX_sqrt_deficit_le :
    ∃ C : ℝ, 0 < C ∧
      ∀ (P : AdmissibleParams) (ε : ℝ)
        (S : ProjectiveSetting P ε) (sublines : SubLineWitness P),
        Real.sqrt (1 - avgOver (removeXLaw P sublines) (fun s => ∑ fs,
            stateQForm S.psiHat
              ((removeXLine S s).effect fs * removeXPointX S s fs))) ≤
          C * (P.m : ℝ) * Real.rpow (deltaLine ε) (1 / 2 : ℝ) := by
  obtain ⟨K, hK, hdeficit⟩ := exists_concreteXPointOverlap_deficit_le
  refine ⟨Real.sqrt K, Real.sqrt_pos.2 hK, ?_⟩
  intro P ε S sublines
  classical
  have hoverlap : avgOver (removeXLaw P sublines) (fun s => ∑ fs,
        stateQForm S.psiHat
          ((removeXLine S s).effect fs * removeXPointX S s fs)) =
      avgOver sublines.D (fun sample =>
        avgOver (uniformDistribution (DirectScalarQ P.extendedDirectLd))
          (fun t => concreteXPointOverlap S
            (sample.2, projX (directPointToPauli P
              (sample.1.base + t • sample.1.direction))))) := by
    rw [removeXLaw, SandwichProduct.avgOver_distribution_prod]
    refine avgOver_congr _ _ _ fun sample => ?_
    refine avgOver_congr _ _ _ fun t => ?_
    simp only [removeXLine, removeXPointX, concreteXPointOverlap,
      Placement.side, ProjectiveSetting.placedMeasurement_effect,
      Fintype.sum_prod_type]
  have hm : 0 ≤ (P.m : ℝ) := by positivity
  calc
    _ ≤ Real.sqrt (K * (P.m : ℝ) ^ 2 * deltaLine ε) := by
      apply Real.sqrt_le_sqrt
      rw [hoverlap]
      exact hdeficit P ε S sublines
    _ = Real.sqrt K * Real.sqrt ((P.m : ℝ) ^ 2 * deltaLine ε) := by
      rw [show K * (P.m : ℝ) ^ 2 * deltaLine ε =
          K * ((P.m : ℝ) ^ 2 * deltaLine ε) by ring,
        Real.sqrt_mul (le_of_lt hK)]
    _ = Real.sqrt K *
        (Real.sqrt ((P.m : ℝ) ^ 2) * Real.sqrt (deltaLine ε)) := by
      rw [Real.sqrt_mul (sq_nonneg (P.m : ℝ))]
    _ = Real.sqrt K * (P.m : ℝ) * Real.sqrt (deltaLine ε) := by
      rw [Real.sqrt_sq hm]
      ring
    _ = Real.sqrt K * (P.m : ℝ) *
        Real.rpow (deltaLine ε) (1 / 2 : ℝ) := by
      have hsqrt : Real.sqrt (deltaLine ε) =
          Real.rpow (deltaLine ε) (1 / 2 : ℝ) :=
        Real.sqrt_eq_rpow (deltaLine ε)
      rw [hsqrt]

/-- Removing the trailing `X`-point factor from the constructed X-Z-X line
measurement costs the square root of the line-consistency error, with the
source factor `m`. This is auxiliary blueprint `lem:claim-17-2-direct-real`,
supporting paper `claim:17-2`,
`14_analysis_of_the_pauli_basis_test.tex:1168-1201`; the measurement is defined
at paper lines 942--949.

**Source realignment (issue #414):** The former quantification over arbitrary
`CombinedLinesWitness` was false. The constant-polynomial counterexample and
the restored construction domain are documented in
`docs/paper-gaps/qpbt_subline-claims-line-marginal.tex`.

The proof uses the concrete X-marginal identity, expanded line-point
consistency, and the restricted X-point marginal of `SubLineWitness` to bound
the X-overlap deficit, then applies Cauchy--Schwarz. No marginal identity is
assumed in this theorem. The right-hand point is the corrected lowercase `z`
recorded in the blueprint.

**Scope restriction:** This proved estimate compares real parts on the
directly indexed `SubLineWitness` law. The source complex estimate and
seed-indexed distribution transport remain open, as recorded in the same
paper-gap note; the scalar proof is no longer a retained obligation.
The deprecated name `subline_remove_X_factor` abbreviates the complex-modulus
`subline_remove_X_factor_direct` instead. -/
theorem subline_remove_X_factor_re_direct :
    ∃ C : ℝ, 0 < C ∧
      ∀ (P : AdmissibleParams) (ε : ℝ)
        (S : ProjectiveSetting P ε) (sublines : SubLineWitness P),
        |avgOver sublines.D (fun sample =>
            avgOver (uniformDistribution (DirectScalarQ P.extendedDirectLd)) (fun t =>
              let u := directPointToPauli P
                (sample.1.base + t • sample.1.direction)
              let x := projX u
              let z := projZ u
              ∑ fX, ∑ fZ,
                (inner ℂ S.psiHat ((EuclideanSpace.equiv
                  (SixReg P S.toStrategy.ιA S.toStrategy.ιB) ℂ).symm
                    ((S.place .AA'
                        ((S.combinedLineMeasurement .alice sample.2.1
                          sample.2.2).effect (fX, fZ)) *
                      S.place .BA''
                        (S.expPointEffectAtLineAnswer .bob .Z sample.2.2 z fZ *
                          S.expPointEffectAtLineAnswer .bob .X sample.2.1 x fX)).mulVec
                            S.psiHat))).re)) -
          avgOver sublines.D (fun sample =>
            avgOver (uniformDistribution (DirectScalarQ P.extendedDirectLd)) (fun t =>
              let u := directPointToPauli P
                (sample.1.base + t • sample.1.direction)
              let z := projZ u
              ∑ fX, ∑ fZ,
                (inner ℂ S.psiHat ((EuclideanSpace.equiv
                  (SixReg P S.toStrategy.ιA S.toStrategy.ιB) ℂ).symm
                    ((S.place .AA'
                        ((S.combinedLineMeasurement .alice sample.2.1
                          sample.2.2).effect (fX, fZ)) *
                      S.place .BA''
                        (S.expPointEffectAtLineAnswer .bob .Z sample.2.2 z fZ)).mulVec
                          S.psiHat))).re))| ≤
          C * (P.m : ℝ) * Real.rpow (deltaLine ε) (1 / 2 : ℝ) := by
  obtain ⟨C, hC, hdeficit⟩ := exists_removeX_sqrt_deficit_le
  refine ⟨C, hC, ?_⟩
  intro P ε S sublines
  classical
  have hcs := abs_overlap_gap_le_sqrt_one_sub_of_isProj'
    (removeXLaw P sublines) (removeXLine S) (removeXPointX S) (removeXPointZ S)
    (removeXPointZX S) S.psiHat (removeXLaw_isProbability sublines) S.psiHat_norm
    (fun s fs => by
      dsimp only [removeXPointX]
      exact place_expPointEffectAtLineAnswer_isProj S .X _ _ _)
    (fun s fs => by
      dsimp only [removeXPointZ]
      exact place_expPointEffectAtLineAnswer_isProj S .Z _ _ _)
    (fun s fs => removeXLine_commute_place S s fs _)
    (fun s fs => removeXLine_commute_place S s fs _)
    (fun s fs => by
      dsimp only [removeXPointZX, removeXPointZ, removeXPointX]
      exact S.place_mul .BA'' _ _)
  have hfirst : avgOver sublines.D (fun sample =>
      avgOver (uniformDistribution (DirectScalarQ P.extendedDirectLd)) (fun t =>
        let u := directPointToPauli P
          (sample.1.base + t • sample.1.direction)
        let x := projX u
        let z := projZ u
        ∑ fX, ∑ fZ,
          (inner ℂ S.psiHat ((EuclideanSpace.equiv
            (SixReg P S.toStrategy.ιA S.toStrategy.ιB) ℂ).symm
              ((S.place .AA'
                  ((S.combinedLineMeasurement .alice sample.2.1
                    sample.2.2).effect (fX, fZ)) *
                S.place .BA''
                  (S.expPointEffectAtLineAnswer .bob .Z sample.2.2 z fZ *
                    S.expPointEffectAtLineAnswer .bob .X sample.2.1 x fX)).mulVec
                      S.psiHat))).re)) =
      avgOver (removeXLaw P sublines) (fun s => ∑ fs, stateQForm S.psiHat
        ((removeXLine S s).effect fs * removeXPointZX S s fs)) := by
    rw [removeXLaw, SandwichProduct.avgOver_distribution_prod]
    refine avgOver_congr _ _ _ fun sample => ?_
    refine avgOver_congr _ _ _ fun t => ?_
    change (∑ fX, ∑ fZ, stateQForm S.psiHat
        (S.place .AA'
            ((S.combinedLineMeasurement .alice sample.2.1 sample.2.2).effect
              (fX, fZ)) *
          S.place .BA''
            (S.expPointEffectAtLineAnswer .bob .Z sample.2.2
                (projZ (directPointToPauli P
                  (sample.1.base + t • sample.1.direction))) fZ *
              S.expPointEffectAtLineAnswer .bob .X sample.2.1
                (projX (directPointToPauli P
                  (sample.1.base + t • sample.1.direction))) fX))) = _
    simp only [removeXLine, removeXPointZX,
      ProjectiveSetting.placedMeasurement_effect, Fintype.sum_prod_type]
  have hsecond : avgOver sublines.D (fun sample =>
      avgOver (uniformDistribution (DirectScalarQ P.extendedDirectLd)) (fun t =>
        let u := directPointToPauli P
          (sample.1.base + t • sample.1.direction)
        let z := projZ u
        ∑ fX, ∑ fZ,
          (inner ℂ S.psiHat ((EuclideanSpace.equiv
            (SixReg P S.toStrategy.ιA S.toStrategy.ιB) ℂ).symm
              ((S.place .AA'
                  ((S.combinedLineMeasurement .alice sample.2.1
                    sample.2.2).effect (fX, fZ)) *
                S.place .BA''
                  (S.expPointEffectAtLineAnswer .bob .Z sample.2.2 z fZ)).mulVec
                    S.psiHat))).re)) =
      avgOver (removeXLaw P sublines) (fun s => ∑ fs, stateQForm S.psiHat
        ((removeXLine S s).effect fs * removeXPointZ S s fs)) := by
    rw [removeXLaw, SandwichProduct.avgOver_distribution_prod]
    refine avgOver_congr _ _ _ fun sample => ?_
    refine avgOver_congr _ _ _ fun t => ?_
    change (∑ fX, ∑ fZ, stateQForm S.psiHat
        (S.place .AA'
            ((S.combinedLineMeasurement .alice sample.2.1 sample.2.2).effect
              (fX, fZ)) *
          S.place .BA''
            (S.expPointEffectAtLineAnswer .bob .Z sample.2.2
              (projZ (directPointToPauli P
                (sample.1.base + t • sample.1.direction))) fZ))) = _
    simp only [removeXLine, removeXPointZ,
      ProjectiveSetting.placedMeasurement_effect, Fintype.sum_prod_type]
  rw [hfirst, hsecond]
  exact hcs.trans (hdeficit P ε S sublines)

/-- Complex-modulus removal of the X factor for the directly indexed subline law.

**Scope restriction:** This is a formalization-only analogue of paper `claim:17-2`,
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1168-1201`,
using the concrete X-Z-X measurement defined at paper lines 942--949.
The source-law statement remains blueprint `lem:claim-17-2`.

The complex weighted Cauchy--Schwarz inequality and
`exists_concreteXPointOverlap_deficit_le` prove the bound without a reality
assumption. The deficit theorem uses `combinedLineMeasurement_sum_Z`.
Transport of `SubLineWitness` to the source law remains separate, as recorded
in `docs/paper-gaps/qpbt_subline-claims-line-marginal.tex` (issues #414, #474,
and #480) and `docs/paper-gaps/qpbt_ld-dimension-divisibility.tex`.
No deficit or transport is assumed.
The finite weighted sums below are complex expectations, without taking real parts. -/
theorem subline_remove_X_factor_direct :
    ∃ C : ℝ, 0 < C ∧
      ∀ (P : AdmissibleParams) (ε : ℝ)
        (S : ProjectiveSetting P ε) (sublines : SubLineWitness P),
        ‖(∑ sample ∈ sublines.D.support,
            (sublines.D.weight sample : ℂ) *
              (Fintype.card (DirectScalarQ P.extendedDirectLd) : ℂ)⁻¹ *
                ∑ t : DirectScalarQ P.extendedDirectLd,
              let u := directPointToPauli P
                (sample.1.base + t • sample.1.direction)
              let x := projX u
              let z := projZ u
              ∑ fX, ∑ fZ,
                (inner ℂ S.psiHat ((EuclideanSpace.equiv
                  (SixReg P S.toStrategy.ιA S.toStrategy.ιB) ℂ).symm
                    ((S.place .AA'
                        ((S.combinedLineMeasurement .alice sample.2.1
                          sample.2.2).effect (fX, fZ)) *
                      S.place .BA''
                        (S.expPointEffectAtLineAnswer .bob .Z sample.2.2 z fZ *
                          S.expPointEffectAtLineAnswer .bob .X sample.2.1 x fX)).mulVec
                            S.psiHat)))) -
          (∑ sample ∈ sublines.D.support,
            (sublines.D.weight sample : ℂ) *
              (Fintype.card (DirectScalarQ P.extendedDirectLd) : ℂ)⁻¹ *
                ∑ t : DirectScalarQ P.extendedDirectLd,
              let u := directPointToPauli P
                (sample.1.base + t • sample.1.direction)
              let z := projZ u
              ∑ fX, ∑ fZ,
                (inner ℂ S.psiHat ((EuclideanSpace.equiv
                  (SixReg P S.toStrategy.ιA S.toStrategy.ιB) ℂ).symm
                    ((S.place .AA'
                        ((S.combinedLineMeasurement .alice sample.2.1
                          sample.2.2).effect (fX, fZ)) *
                      S.place .BA''
                        (S.expPointEffectAtLineAnswer .bob .Z sample.2.2 z fZ)).mulVec
                          S.psiHat))))‖ ≤
          C * (P.m : ℝ) * Real.rpow (deltaLine ε) (1 / 2 : ℝ) := by
  obtain ⟨C, hC, hdeficit⟩ := exists_removeX_sqrt_deficit_le
  refine ⟨C, hC, ?_⟩
  intro P ε S sublines
  classical
  have hcs := norm_overlap_gap_le_sqrt_one_sub_of_isProj
    (removeXLaw P sublines) (removeXLine S) (removeXPointX S) (removeXPointZ S)
    (removeXPointZX S) S.psiHat (removeXLaw_isProbability sublines) S.psiHat_norm
    (fun s fs => by
      dsimp only [removeXPointX]
      exact place_expPointEffectAtLineAnswer_isProj S .X _ _ _)
    (fun s fs => by
      dsimp only [removeXPointZ]
      exact place_expPointEffectAtLineAnswer_isProj S .Z _ _ _)
    (fun s fs => removeXLine_commute_place S s fs _)
    (fun s fs => removeXLine_commute_place S s fs _)
    (fun s fs => by
      dsimp only [removeXPointZX, removeXPointZ, removeXPointX]
      exact S.place_mul .BA'' _ _)
  have hbound :
      ‖(∑ s ∈ (removeXLaw P sublines).support,
          ((removeXLaw P sublines).weight s : ℂ) * ∑ fs,
            inner ℂ S.psiHat (applyOperatorToState
              ((removeXLine S s).effect fs * removeXPointZX S s fs) S.psiHat)) -
        (∑ s ∈ (removeXLaw P sublines).support,
          ((removeXLaw P sublines).weight s : ℂ) * ∑ fs,
            inner ℂ S.psiHat (applyOperatorToState
              ((removeXLine S s).effect fs * removeXPointZ S s fs) S.psiHat))‖ ≤
        C * (P.m : ℝ) * Real.rpow (deltaLine ε) (1 / 2 : ℝ) :=
    hcs.trans (hdeficit P ε S sublines)
  convert hbound using 1
  simp [removeXLaw, Distribution.prod, uniformDistribution, Finset.sum_product,
    removeXLine, removeXPointZX, removeXPointZ,
    ProjectiveSetting.placedMeasurement_effect, Fintype.sum_prod_type,
    applyOperatorToState, mul_assoc, Finset.mul_sum,
    Matrix.toLpLin_apply, Matrix.mulVec_mulVec]

/-- Formalization-only real-part Z-correlation bound for the directly indexed law.

**Scope restriction:** This uses `SubLineWitness` and compares the real part with one.
It supports, but does not certify, blueprint `lem:claim-17-3`, paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1204-1239`.
The complex scalar comparison is proved below; source-law transport remains
separate, as recorded in
`docs/paper-gaps/qpbt_subline-claims-line-marginal.tex` (issue #474) and
`docs/paper-gaps/qpbt_ld-dimension-divisibility.tex`. -/
theorem subline_Z_term_near_one_re_direct :
    ∃ C : ℝ, 0 < C ∧
      ∀ (P : AdmissibleParams) (ε δQ δP : ℝ)
        (S : ProjectiveSetting P ε) (points : CombinedPointsWitness S δQ)
        (lines : CombinedLinesWitness S points δP) (sublines : SubLineWitness P),
        |avgOver sublines.D (fun sample =>
            avgOver (uniformDistribution (DirectScalarQ P.extendedDirectLd)) (fun t =>
              let u := directPointToPauli P
                (sample.1.base + t • sample.1.direction)
              let z := projZ u
              ∑ fX, ∑ fZ,
                (inner ℂ S.psiHat ((EuclideanSpace.equiv
                  (SixReg P S.toStrategy.ιA S.toStrategy.ιB) ℂ).symm
                    ((S.place .AA'
                        ((lines.T .alice sample.2.1 sample.2.2).effect (fX, fZ)) *
                      S.place .BA''
                        (S.expPointEffectAtLineAnswer .bob .Z sample.2.2 z fZ)).mulVec
                          S.psiHat))).re)) - 1| ≤
          C * Real.sqrt (P.m : ℝ) *
            (Real.rpow δP (1 / 4 : ℝ) + Real.rpow δQ (1 / 4 : ℝ) +
              Real.rpow ε (1 / 4 : ℝ)) := by
  refine ⟨2, by norm_num, ?_⟩
  intro P ε δQ δP S points lines sublines
  classical
  have hδP : 0 ≤ δP := by
    refine le_trans ?_ (lines.consistent .AA' .BA'' trivial)
    unfold consistencyDefect
    exact avgOver_nonneg _ _ fun s =>
      consistencyDefect_integrand_nonneg S .AA' .BA'' trivial
        ((lines.T .alice s.1.1 s.2.1).postprocess fun fs =>
          (evalOpt s.1.1 s.1.2 fs.1, evalOpt s.2.1 s.2.2 fs.2))
        ((points.Q .bob s.1.2 s.2.2).postprocess fun ab => (some ab.1, some ab.2))
  have hδQ : 0 ≤ δQ :=
    le_trans (opFamilyDistSq_nonneg _ _ _ _) (points.self_consistent .AA' .BA'' trivial)
  have hm : (1 : ℝ) ≤ (P.m : ℝ) := by exact_mod_cast P.one_le_m
  have hLHS : avgOver sublines.D (fun sample =>
      avgOver (uniformDistribution (DirectScalarQ P.extendedDirectLd)) (fun t =>
        let u := directPointToPauli P
          (sample.1.base + t • sample.1.direction)
        let z := projZ u
        ∑ fX, ∑ fZ,
          (inner ℂ S.psiHat ((EuclideanSpace.equiv
            (SixReg P S.toStrategy.ιA S.toStrategy.ιB) ℂ).symm
              ((S.place .AA'
                  ((lines.T .alice sample.2.1 sample.2.2).effect (fX, fZ)) *
                S.place .BA''
                  (S.expPointEffectAtLineAnswer .bob .Z sample.2.2 z fZ)).mulVec
                    S.psiHat))).re)) =
      avgOver sublines.D (fun sample =>
        avgOver (uniformDistribution (DirectScalarQ P.extendedDirectLd))
          (fun t => zPointOverlap lines (sample.2, projZ (directPointToPauli P
            (sample.1.base + t • sample.1.direction))))) := by
    refine avgOver_congr _ _ _ fun sample => avgOver_congr _ _ _ fun t => ?_
    simp only [zPointOverlap, ← ProjectiveSetting.pointMeasExpOption_effect_evalOpt]
    rfl
  rw [hLHS]
  set L := avgOver sublines.D (fun sample =>
    avgOver (uniformDistribution (DirectScalarQ P.extendedDirectLd))
      (fun t => zPointOverlap lines (sample.2, projZ (directPointToPauli P
        (sample.1.base + t • sample.1.direction))))) with hL
  have hdef := sublines.one_sub_avgOver_zPointOverlap_le lines
  have hle := sublines.avgOver_zPointOverlap_le_one lines
  have hnonneg : 0 ≤ L :=
    avgOver_nonneg _ _ fun sample => avgOver_nonneg _ _ fun t =>
      zPointOverlap_nonneg lines _
  rw [← hL] at hdef hle
  have h0 : 0 ≤ 1 - L := by linarith
  have hsq : (1 - L) ^ 2 ≤ 1 - L := by nlinarith
  calc
    |L - 1| = 1 - L := by rw [abs_sub_comm, abs_of_nonneg h0]
    _ = Real.sqrt ((1 - L) ^ 2) := (Real.sqrt_sq h0).symm
    _ ≤ Real.sqrt (2 * Real.sqrt (4 * (P.m : ℝ) ^ 2 * δP) +
          2 * Real.sqrt (4 * δQ)) := Real.sqrt_le_sqrt (hsq.trans hdef)
    _ ≤ 2 * Real.sqrt (P.m : ℝ) *
          (Real.rpow δP (1 / 4 : ℝ) + Real.rpow δQ (1 / 4 : ℝ)) :=
      sqrt_deficit_bound_le _ _ _ hm hδP hδQ
    _ ≤ _ := by
      have hε := rpow_quarter_nonneg ε
      have hsm : 0 ≤ 2 * Real.sqrt (P.m : ℝ) :=
        mul_nonneg (by norm_num) (Real.sqrt_nonneg _)
      nlinarith [mul_nonneg hsm hε]

/-- Complex-modulus Z-correlation bound on the same domain as the real-part bound.

**Scope restriction:** This is the directly indexed analogue of paper
`claim:17-3`, lines 1204--1239. Positivity on opposite registers proves that the
overlap is real, so the existing real bound gives exactly the same error in
complex modulus. Its line witness is used only for that consistency estimate;
the concrete specialization below constructs this witness internally. See
`docs/paper-gaps/qpbt_subline-claims-line-marginal.tex` (issue #689). -/
theorem subline_Z_term_near_one_direct :
    ∃ C : ℝ, 0 < C ∧
      ∀ (P : AdmissibleParams) (ε δQ δP : ℝ)
        (S : ProjectiveSetting P ε) (points : CombinedPointsWitness S δQ)
        (lines : CombinedLinesWitness S points δP) (sublines : SubLineWitness P),
        ‖(∑ sample ∈ sublines.D.support,
          (sublines.D.weight sample : ℂ) *
            (Fintype.card (DirectScalarQ P.extendedDirectLd) : ℂ)⁻¹ *
              ∑ t : DirectScalarQ P.extendedDirectLd,
          let z := projZ (directPointToPauli P (sample.1.base + t • sample.1.direction))
          ∑ fX, ∑ fZ, inner ℂ S.psiHat (applyOperatorToState
            (S.place .AA' ((lines.T .alice sample.2.1 sample.2.2).effect (fX, fZ)) *
              S.place .BA'' (S.expPointEffectAtLineAnswer .bob .Z sample.2.2 z fZ))
            S.psiHat)) - 1‖ ≤
          C * Real.sqrt (P.m : ℝ) *
            (Real.rpow δP (1 / 4 : ℝ) + Real.rpow δQ (1 / 4 : ℝ) +
              Real.rpow ε (1 / 4 : ℝ)) := by
  obtain ⟨C, hC, hbound⟩ := subline_Z_term_near_one_re_direct
  refine ⟨C, hC, ?_⟩
  intro P ε δQ δP S points lines sublines
  rw [subline_Z_overlap_eq_real_direct S sublines (lines.T .alice),
    ← Complex.ofReal_one, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
  exact hbound P ε δQ δP S points lines sublines

/-- The complex Z estimate for the actual X-Z-X measurement, with its line error
produced by the existing pasting theorem.

**Scope restriction:** For a polynomially controlled joint point family, the
line error is obtained from `combined_line_measurement_consistency`, so no
line witness, equality with the construction, or reality premise is assumed.
The error scale is that of paper `claim:17-3`, lines 1204--1239, on the directly
indexed law with completed evaluations. This does not resolve source-law
transport; see `docs/paper-gaps/qpbt_subline-claims-line-marginal.tex`. -/
theorem subline_concrete_Z_term_near_one_direct (deltaQ : ℝ → ℝ)
    (hdeltaQ : IsPolyErr deltaQ) :
    ∃ deltaP : ℝ → ℝ → ℝ, IsPolyErr₂ deltaP ∧ ∃ C : ℝ, 0 < C ∧
      ∀ (P : AdmissibleParams) (ε : ℝ) (S : ProjectiveSetting P ε)
        (_points : CombinedPointsWitness S (deltaQ ε)) (sublines : SubLineWitness P),
        ‖(∑ sample ∈ sublines.D.support,
          (sublines.D.weight sample : ℂ) *
            (Fintype.card (DirectScalarQ P.extendedDirectLd) : ℂ)⁻¹ *
              ∑ t : DirectScalarQ P.extendedDirectLd,
          let z := projZ (directPointToPauli P (sample.1.base + t • sample.1.direction))
          ∑ fX, ∑ fZ, inner ℂ S.psiHat (applyOperatorToState
            (S.place .AA' ((S.combinedLineMeasurement .alice sample.2.1 sample.2.2).effect
                (fX, fZ)) *
              S.place .BA'' (S.expPointEffectAtLineAnswer .bob .Z sample.2.2 z fZ))
            S.psiHat)) - 1‖ ≤
          C * Real.sqrt (P.m : ℝ) *
            (Real.rpow (deltaP ε (((P.m * P.d : ℕ) : ℝ) / (P.q : ℝ))) (1 / 4 : ℝ) +
              Real.rpow (deltaQ ε) (1 / 4 : ℝ) + Real.rpow ε (1 / 4 : ℝ)) := by
  obtain ⟨deltaP, hdeltaP, hconsistent⟩ := combined_line_measurement_consistency deltaQ hdeltaQ
  obtain ⟨C, hC, hbound⟩ := subline_Z_term_near_one_direct
  refine ⟨deltaP, hdeltaP, C, hC, ?_⟩
  intro P ε S points sublines
  let lines : CombinedLinesWitness S points
      (deltaP ε (((P.m * P.d : ℕ) : ℝ) / (P.q : ℝ))) :=
    { T := S.combinedLineMeasurement
      axis_degree_X := S.combinedLineMeasurement_axis_degree_X
      axis_degree_Z := S.combinedLineMeasurement_axis_degree_Z
      consistent := hconsistent P ε S points }
  exact hbound P ε _ _ S points lines sublines

/-- Compatibility name for the proved real-part ordered-product estimate.

**Scope restriction:** This is `subline_replace_by_ordered_product_re_direct`,
with its unchanged directly indexed law and real-part conclusion. It does not
certify paper `claim:17-1`; see issue #474 and
`docs/paper-gaps/qpbt_subline-claims-line-marginal.tex`. -/
@[deprecated (since := "2026-09-12")]
alias subline_replace_by_ordered_product := subline_replace_by_ordered_product_re_direct

/-- Compatibility name for the corrected concrete-measurement X-factor obligation.

**Scope restriction:** The domain and complex-modulus conclusion are those of
`subline_remove_X_factor_direct`, following paper `claim:17-2` at
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1168-1201`.
The former quantification over arbitrary line witnesses is false, as documented
in `docs/paper-gaps/qpbt_subline-claims-line-marginal.tex` (issue #414).

The complex Cauchy--Schwarz estimate of `subline_remove_X_factor_direct` is
proved, from `norm_overlap_gap_le_sqrt_one_sub_of_isProj` and
`exists_concreteXPointOverlap_deficit_le`. Its source-law transport remains
open under issues #414 and #474, as recorded in the same paper-gap note.
The real-part analogue on the same law is
`subline_remove_X_factor_re_direct`. -/
@[deprecated (since := "2026-09-12")]
alias subline_remove_X_factor := subline_remove_X_factor_direct

/-- Compatibility name for the proved real-part Z-correlation estimate.

**Scope restriction:** This is `subline_Z_term_near_one_re_direct`, with its
unchanged directly indexed law and real-part conclusion. It does not certify
paper `claim:17-3`; see issue #474 and
`docs/paper-gaps/qpbt_subline-claims-line-marginal.tex`. -/
@[deprecated (since := "2026-09-12")]
alias subline_Z_term_near_one := subline_Z_term_near_one_re_direct

end

end MIPStarRE.QPBT
