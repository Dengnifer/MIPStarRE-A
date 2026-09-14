import MIPStarRE.QPBT.Combining.ErrorBounds
import MIPStarRE.QPBT.Combining.OrderedPoints
import MIPStarRE.QPBT.Combining.OverlapGap
import MIPStarRE.QPBT.Combining.Lines.CombinedMeasurement
import MIPStarRE.QPBT.Combining.Lines.ConcreteXDeficit
import MIPStarRE.QPBT.Combining.SubLineZDeficit
import MIPStarRE.QPBT.Combining.UniformLinePoint
import MIPStarRE.QPBT.Combining.Witnesses
import MIPStarRE.QPBT.Games.DistanceTheorems.TensorSupport

/-!
# Scalar claims for combining the Pauli bases

This module records auxiliary scalar estimates for the directly indexed subline
law. The proved estimates compare real parts; they do not establish the complex
modulus comparisons over the source distribution in Claims 17-1 and 17-3.
The pending Claim 17-2 analogue retains the complex modulus. The source claims
remain separate, uncertified blueprint statements until the distribution and
scalar transport obligations are discharged. Line-polynomial evaluation uses the
existing `Option` completion, so no field value is substituted when an evaluation
is undefined.

## References

The source comparisons are blueprint `lem:claim-17-1`, `lem:claim-17-2`, and
`lem:claim-17-3`, with paper origin
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1140-1209`.
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
    rw [avgOver_prod]
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
        avgOver_prod _ _ _
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

/-- Complex-modulus removal of the X factor for the directly indexed subline law.

**Scope restriction:** This is a formalization-only analogue of paper `claim:17-2`,
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1168-1201`,
using the concrete X-Z-X measurement defined at paper lines 942--949.
The source-law statement remains blueprint `lem:claim-17-2`.

**Unfaithful:** The complex Cauchy--Schwarz estimate is still unproved, and
`SubLineWitness` has not been transported to the source law. Issues #414 and
#474 and `docs/paper-gaps/qpbt_subline-claims-line-marginal.tex` track the scalar
obligation; `docs/paper-gaps/qpbt_ld-dimension-divisibility.tex` tracks transport.
Discharge this retained hole by the complex weighted Cauchy--Schwarz inequality
and `exists_concreteXPointOverlap_deficit_le`, which already uses
`combinedLineMeasurement_sum_Z`. No deficit or transport is assumed.
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
  sorry

/-- Formalization-only real-part Z-correlation bound for the directly indexed law.

**Scope restriction:** This uses `SubLineWitness` and compares the real part with one.
It supports, but does not certify, blueprint `lem:claim-17-3`, paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1204-1239`.
The source-law and scalar comparison remain separate obligations, recorded in
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

end

end MIPStarRE.QPBT
