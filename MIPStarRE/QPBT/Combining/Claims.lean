import MIPStarRE.QPBT.Combining.OrderedPoints
import MIPStarRE.QPBT.Combining.OverlapGap
import MIPStarRE.QPBT.Combining.UniformLinePoint
import MIPStarRE.QPBT.Combining.Witnesses
import MIPStarRE.QPBT.Games.DistanceTheorems.TensorSupport

/-!
# Scalar claims for combining the Pauli bases

This module states the three scalar estimates used to compare the paired line
measurement with the joint and ordered point measurements.  The expectations
retain the subline law and the uniform affine parameter on each extended line
explicitly.  Line-polynomial evaluation uses the existing `Option` completion,
so no field value is substituted when an evaluation is undefined.

## References

The claims are blueprint `lem:claim-17-1`, `lem:claim-17-2`, and
`lem:claim-17-3`, with paper origin
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1140-1209`.
-/

open scoped BigOperators

namespace MIPStarRE.QPBT

open MIPStarRE.LDT hiding Measurement
open MIPStarRE.Quantum MIPStarRE.QPBT.DistanceCalculus

noncomputable section

set_option synthInstance.maxSize 400

/-- Place an Alice-side measurement on `AA'` by the current tensor
bipartition API. -/
private noncomputable def placedAAMeasurement {P : AdmissibleParams} {ε : ℝ}
    (S : ProjectiveSetting P ε) {α : Type*} [Fintype α]
    (M : Measurement α (S.ExpandedLocalSpace .alice)) :
    Measurement α (SixReg P S.toStrategy.ιA S.toStrategy.ιB) :=
  reindexMeasurement
    (ProjectiveSetting.aaBaBipartition P S.toStrategy.ιA S.toStrategy.ιB)
    (leftPlacedMeasurement M)

/-- The effects of `placedAAMeasurement` are the `AA'` placements of the
original effects. -/
private theorem placedAAMeasurement_effect {P : AdmissibleParams} {ε : ℝ}
    (S : ProjectiveSetting P ε) {α : Type*} [Fintype α]
    (M : Measurement α (S.ExpandedLocalSpace .alice)) (a : α) :
    (placedAAMeasurement S M).effect a = S.place .AA' (M.effect a) := by
  change reindexOp
    (ProjectiveSetting.aaBaBipartition P S.toStrategy.ιA S.toStrategy.ιB)
      (heteroKron (M.effect a) 1) = S.place .AA' (M.effect a)
  exact ProjectiveSetting.reindexOp_aaBaBipartition_left S (M.effect a)

/-- A product-distribution average is the corresponding iterated average. -/
private theorem avgOver_prod_current {α β : Type*}
    [DecidableEq α] [DecidableEq β]
    (μ : Distribution α) (ν : Distribution β) (f : α × β → ℝ) :
    avgOver (Distribution.prod μ ν) f =
      avgOver μ (fun a => avgOver ν (fun b => f (a, b))) := by
  classical
  unfold avgOver
  change (∑ p ∈ μ.support ×ˢ ν.support,
    μ.weight p.1 * ν.weight p.2 * f p) = _
  rw [Finset.sum_product]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun b _ => by ring

/-- The completed point measurement has zero effect at `none`. -/
private theorem pointMeasExpOption_effect_none_current
    {P : AdmissibleParams} {ε : ℝ} (S : ProjectiveSetting P ε)
    (side : PlayerSide) (W : PauliKind) (u : Fin P.m → PauliScalar P) :
    (S.pointMeasExpOption side W u).effect none = 0 := by
  classical
  unfold ProjectiveSetting.pointMeasExpOption
  rw [MIPStarRE.Quantum.Measurement.postprocess_effect]
  apply Finset.sum_eq_zero
  intro a ha
  exact absurd (Finset.mem_filter.mp ha).2 (by simp)

/-- The completed point measurement agrees with the original measurement at
a `some` outcome. -/
private theorem pointMeasExpOption_effect_some_current
    {P : AdmissibleParams} {ε : ℝ} (S : ProjectiveSetting P ε)
    (side : PlayerSide) (W : PauliKind) (u : Fin P.m → PauliScalar P)
    (a : PauliScalar P) :
    (S.pointMeasExpOption side W u).effect (some a) =
      (S.pointMeasExp side W u).effect a := by
  classical
  unfold ProjectiveSetting.pointMeasExpOption
  rw [MIPStarRE.Quantum.Measurement.postprocess_effect]
  simp [Finset.filter_eq']

/-- Evaluating a completed point effect through a line answer gives the
explicit zero-completed effect used in the claim statements. -/
private theorem pointMeasExpOption_effect_evalOpt_current
    {P : AdmissibleParams} {ε : ℝ} (S : ProjectiveSetting P ε)
    (side : PlayerSide) (W : PauliKind) (line : LineDesc P.toLdParams)
    (u : Fin P.m → PauliScalar P)
    (f : DegPoly P.toLdParams (P.m * P.d)) :
    (S.pointMeasExpOption side W u).effect (evalOpt line u f) =
      S.expPointEffectAtLineAnswer side W line u f := by
  unfold ProjectiveSetting.expPointEffectAtLineAnswer
  cases evalOpt line u f with
  | none => exact pointMeasExpOption_effect_none_current S side W u
  | some a => exact pointMeasExpOption_effect_some_current S side W u a

/-- Regroup paired-line answers by their two optional evaluations. -/
private theorem regroup_line_answer_sum {P : AdmissibleParams} {ε δQ δP : ℝ}
    {S : ProjectiveSetting P ε} {points : CombinedPointsWitness S δQ}
    (lines : CombinedLinesWitness S points δP)
    (lineX lineZ : LineDesc P.toLdParams) (x z : Fin P.m → PauliScalar P)
    (G : Option (PauliScalar P) → Option (PauliScalar P) →
      Op (S.ExpandedLocalSpace Placement.BA''.side)) :
    (∑ o : Option (PauliScalar P) × Option (PauliScalar P),
        stateQForm S.psiHat
          (((placedAAMeasurement S (lines.T .alice lineX lineZ)).postprocess
            (fun fs => (evalOpt lineX x fs.1, evalOpt lineZ z fs.2))).effect o *
            S.place .BA'' (G o.1 o.2))) =
      ∑ fX, ∑ fZ, stateQForm S.psiHat
        (S.place .AA' ((lines.T .alice lineX lineZ).effect (fX, fZ)) *
          S.place .BA'' (G (evalOpt lineX x fX) (evalOpt lineZ z fZ))) := by
  classical
  have hsum : ∀ (s : Finset (DegPoly P.toLdParams (P.m * P.d) ×
        DegPoly P.toLdParams (P.m * P.d)))
      (M : DegPoly P.toLdParams (P.m * P.d) ×
        DegPoly P.toLdParams (P.m * P.d) →
        Op (SixReg P S.toStrategy.ιA S.toStrategy.ιB))
      (N : Op (SixReg P S.toStrategy.ιA S.toStrategy.ιB)),
      stateQForm S.psiHat ((∑ fs ∈ s, M fs) * N) =
        ∑ fs ∈ s, stateQForm S.psiHat (M fs * N) := by
    intro s M N
    simp [stateQForm, applyOperatorToState, Finset.sum_mul]
  calc
    (∑ o : Option (PauliScalar P) × Option (PauliScalar P),
          stateQForm S.psiHat
            (((placedAAMeasurement S
              (lines.T .alice lineX lineZ)).postprocess (fun fs =>
                (evalOpt lineX x fs.1, evalOpt lineZ z fs.2))).effect o *
              S.place .BA'' (G o.1 o.2))) =
        ∑ o : Option (PauliScalar P) × Option (PauliScalar P),
          ∑ fs ∈ Finset.univ.filter (fun fs =>
              (evalOpt lineX x fs.1, evalOpt lineZ z fs.2) = o),
            stateQForm S.psiHat
              (S.place .AA' ((lines.T .alice lineX lineZ).effect fs) *
                S.place .BA'' (G o.1 o.2)) := by
      refine Finset.sum_congr rfl fun o _ => ?_
      rw [MIPStarRE.Quantum.Measurement.postprocess_effect]
      refine (hsum _ _ _).trans ?_
      exact Finset.sum_congr rfl fun fs _ => by
        rw [placedAAMeasurement_effect]
    _ = ∑ o : Option (PauliScalar P) × Option (PauliScalar P),
          ∑ fs ∈ Finset.univ.filter (fun fs =>
              (evalOpt lineX x fs.1, evalOpt lineZ z fs.2) = o),
            stateQForm S.psiHat
              (S.place .AA' ((lines.T .alice lineX lineZ).effect fs) *
                S.place .BA''
                  (G (evalOpt lineX x fs.1) (evalOpt lineZ z fs.2))) := by
      refine Finset.sum_congr rfl fun o _ =>
        Finset.sum_congr rfl fun fs hfs => ?_
      rw [← (Finset.mem_filter.mp hfs).2]
    _ = ∑ fs : DegPoly P.toLdParams (P.m * P.d) ×
          DegPoly P.toLdParams (P.m * P.d),
          stateQForm S.psiHat
            (S.place .AA' ((lines.T .alice lineX lineZ).effect fs) *
              S.place .BA''
                (G (evalOpt lineX x fs.1) (evalOpt lineZ z fs.2))) :=
      Finset.sum_fiberwise_of_maps_to (fun fs _ => Finset.mem_univ _) _
    _ = ∑ fX, ∑ fZ, stateQForm S.psiHat
          (S.place .AA' ((lines.T .alice lineX lineZ).effect (fX, fZ)) *
            S.place .BA'' (G (evalOpt lineX x fX) (evalOpt lineZ z fZ))) :=
      Fintype.sum_prod_type (f := fun fs => stateQForm S.psiHat
        (S.place .AA' ((lines.T .alice lineX lineZ).effect fs) *
          S.place .BA'' (G (evalOpt lineX x fs.1) (evalOpt lineZ z fs.2))))

/-- Completing both outcome coordinates with `none` does not change the
squared distance sum between the joint and ordered point families. -/
private theorem completed_pair_norm_sq_sum {P : AdmissibleParams} {ε δQ : ℝ}
    {S : ProjectiveSetting P ε} (points : CombinedPointsWitness S δQ)
    (x z : Fin P.m → PauliScalar P) :
    (∑ o : Option (PauliScalar P) × Option (PauliScalar P),
        ‖applyOperatorToState
          (S.place .BA'' (((points.Q .bob x z).postprocess (fun ab =>
              (some ab.1, some ab.2))).effect (o.1, o.2)) -
            S.place .BA''
              ((S.pointMeasExpOption .bob .Z z).effect o.2 *
                (S.pointMeasExpOption .bob .X x).effect o.1))
          S.psiHat‖ ^ 2) =
      ∑ ab : PauliScalar P × PauliScalar P,
        ‖applyOperatorToState
          (S.place .BA'' ((points.Q .bob x z).effect ab) -
            S.place .BA''
              ((S.pointMeasExp .bob .Z z).effect ab.2 *
                (S.pointMeasExp .bob .X x).effect ab.1))
          S.psiHat‖ ^ 2 := by
  classical
  have hXnone : ((S.pointMeasExpOption .bob .X x).effect
      (none : Option (PauliScalar P)) :
        Op (S.ExpandedLocalSpace Placement.BA''.side)) = 0 :=
    pointMeasExpOption_effect_none_current S .bob .X x
  have hZnone : ((S.pointMeasExpOption .bob .Z z).effect
      (none : Option (PauliScalar P)) :
        Op (S.ExpandedLocalSpace Placement.BA''.side)) = 0 :=
    pointMeasExpOption_effect_none_current S .bob .Z z
  have hXsome : ∀ a : PauliScalar P,
      ((S.pointMeasExpOption .bob .X x).effect (some a) :
        Op (S.ExpandedLocalSpace Placement.BA''.side)) =
        (S.pointMeasExp .bob .X x).effect a :=
    fun a => pointMeasExpOption_effect_some_current S .bob .X x a
  have hZsome : ∀ b : PauliScalar P,
      ((S.pointMeasExpOption .bob .Z z).effect (some b) :
        Op (S.ExpandedLocalSpace Placement.BA''.side)) =
        (S.pointMeasExp .bob .Z z).effect b :=
    fun b => pointMeasExpOption_effect_some_current S .bob .Z z b
  have hQnone : ∀ o : Option (PauliScalar P) × Option (PauliScalar P),
      (∀ ab : PauliScalar P × PauliScalar P, (some ab.1, some ab.2) ≠ o) →
      ((((points.Q .bob x z).postprocess fun ab =>
          (some ab.1, some ab.2)).effect o) :
        Op (S.ExpandedLocalSpace Placement.BA''.side)) = 0 := by
    intro o ho
    rw [MIPStarRE.Quantum.Measurement.postprocess_effect]
    exact Finset.sum_eq_zero fun ab hab =>
      absurd (Finset.mem_filter.mp hab).2 (ho ab)
  have hQsome : ∀ ab : PauliScalar P × PauliScalar P,
      ((((points.Q .bob x z).postprocess fun cd =>
          (some cd.1, some cd.2)).effect (some ab.1, some ab.2)) :
        Op (S.ExpandedLocalSpace Placement.BA''.side)) =
        (points.Q .bob x z).effect ab := by
    intro ab
    rw [MIPStarRE.Quantum.Measurement.postprocess_effect,
      show (Finset.univ.filter fun cd : PauliScalar P × PauliScalar P =>
          (some cd.1, some cd.2) = (some ab.1, some ab.2)) = {ab} by
        ext cd
        simp [Prod.ext_iff, eq_comm]]
    simp
  have hkey : ∀ (F : Option (PauliScalar P) × Option (PauliScalar P) → ℝ),
      (∀ o2, F (none, o2) = 0) → (∀ o1, F (o1, none) = 0) →
      (∑ o, F o) =
        ∑ ab : PauliScalar P × PauliScalar P, F (some ab.1, some ab.2) := by
    intro F h1 h2
    calc
      (∑ o : Option (PauliScalar P) × Option (PauliScalar P), F o) =
          ∑ o1 : Option (PauliScalar P), ∑ o2 : Option (PauliScalar P),
            F (o1, o2) := Fintype.sum_prod_type (f := F)
      _ = (∑ o2 : Option (PauliScalar P), F (none, o2)) +
            ∑ a : PauliScalar P, ∑ o2 : Option (PauliScalar P),
              F (some a, o2) := Fintype.sum_option _
      _ = ∑ a : PauliScalar P, ∑ o2 : Option (PauliScalar P),
            F (some a, o2) := by
          rw [Finset.sum_eq_zero fun o2 _ => h1 o2, zero_add]
      _ = ∑ a : PauliScalar P,
            (F (some a, none) + ∑ b : PauliScalar P, F (some a, some b)) :=
          Finset.sum_congr rfl fun a _ => Fintype.sum_option _
      _ = ∑ a : PauliScalar P, ∑ b : PauliScalar P, F (some a, some b) := by
          refine Finset.sum_congr rfl fun a _ => ?_
          rw [h2 (some a), zero_add]
      _ = ∑ ab : PauliScalar P × PauliScalar P,
            F (some ab.1, some ab.2) :=
          (Fintype.sum_prod_type (f := fun ab : PauliScalar P × PauliScalar P =>
            F (some ab.1, some ab.2))).symm
  refine Eq.trans (hkey _ ?_ ?_) ?_
  · intro o2
    dsimp only
    rw [hQnone (none, o2) (fun ab => by simp), hXnone, mul_zero, sub_self]
    simp [applyOperatorToState]
  · intro o1
    dsimp only
    rw [hQnone (o1, none) (fun ab => by simp), hZnone, zero_mul, sub_self]
    simp [applyOperatorToState]
  · refine Finset.sum_congr rfl fun ab _ => ?_
    dsimp only
    rw [hQsome ab, hZsome ab.2, hXsome ab.1]

/-- Replacing the combined point measurement by the ordered `Z`-then-`X`
point product costs a square-root joint-point error.  This is
`lem:claim-17-1`, paper lines 1140--1145. -/
theorem subline_replace_by_ordered_product :
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
              (((placedAAMeasurement S
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
    rw [avgOver_prod_current]
    refine avgOver_congr _ _ _ fun sample => ?_
    refine avgOver_congr _ _ _ fun t => ?_
    exact (regroup_line_answer_sum lines sample.2.1 sample.2.2 _ _ (G _ _)).symm
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
        avgOver_congr _ _ _ fun s => completed_pair_norm_sq_sum points _ _
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
        avgOver_prod_current _ _ _
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
    (fun s => (placedAAMeasurement S
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
  simp only [← pointMeasExpOption_effect_evalOpt_current]
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

/-- Removing the trailing `X`-point factor costs the square root of the
line-consistency error, with the source factor `m`.  This is
`lem:claim-17-2`, paper lines 1168--1173; the right-hand point is the corrected
lowercase `z` recorded in the blueprint. -/
theorem subline_remove_X_factor :
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
                        ((lines.T .alice sample.2.1 sample.2.2).effect (fX, fZ)) *
                      S.place .BA''
                        (S.expPointEffectAtLineAnswer .bob .Z sample.2.2 z fZ)).mulVec
                          S.psiHat))).re))| ≤
          C * (P.m : ℝ) * Real.rpow (deltaLine ε) (1 / 2 : ℝ) := by
  sorry

/-- The remaining `Z`-point correlation is close to one with the fourth-root
error from the point and line constructions.  This is `lem:claim-17-3`, paper
lines 1204--1209. -/
theorem subline_Z_term_near_one :
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
  sorry

end

end MIPStarRE.QPBT
