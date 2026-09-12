import MIPStarRE.QPBT.Combining.ExtendedLines.Overlap
import MIPStarRE.QPBT.Combining.Claims


/-!
# Estimates for the extended-line construction

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

/-- Removing the X factor for arbitrary opposite register placements, including
Bob at `BBprime` and Alice at `ABdoubleprime`. The proof uses only the
one-point X mixture from paper `lem:qld-sublines`, lines 1168--1201. -/
theorem subline_remove_X_factor_at :
    ∃ C : ℝ, 0 < C ∧
      ∀ (P : AdmissibleParams) (ε δQ δP : ℝ)
        (S : ProjectiveSetting P ε) (points : CombinedPointsWitness S δQ)
        (lines : CombinedLinesWitness S points δP) (sublines : SubLineWitness P)
        (first second : Placement) (_hopposite : first.IsOpposite second),
        |avgOver sublines.D (fun sample =>
            avgOver (uniformDistribution (DirectScalarQ P.extendedDirectLd)) (fun t =>
              let u := directPointToPauli P
                (sample.1.base + t • sample.1.direction)
              let x := projX u
              let z := projZ u
              ∑ fX, ∑ fZ,
                (inner ℂ S.psiHat ((EuclideanSpace.equiv
                  (SixReg P S.toStrategy.ιA S.toStrategy.ιB) ℂ).symm
                    ((S.place first
                        ((lines.T first.side sample.2.1 sample.2.2).effect (fX, fZ)) *
                      S.place second
                        (S.expPointEffectAtLineAnswer second.side .Z sample.2.2 z fZ *
                          S.expPointEffectAtLineAnswer second.side .X sample.2.1 x fX)).mulVec
                            S.psiHat))).re)) -
          avgOver sublines.D (fun sample =>
            avgOver (uniformDistribution (DirectScalarQ P.extendedDirectLd)) (fun t =>
              let u := directPointToPauli P
                (sample.1.base + t • sample.1.direction)
              let z := projZ u
              ∑ fX, ∑ fZ,
                (inner ℂ S.psiHat ((EuclideanSpace.equiv
                  (SixReg P S.toStrategy.ιA S.toStrategy.ιB) ℂ).symm
                    ((S.place first
                        ((lines.T first.side sample.2.1 sample.2.2).effect (fX, fZ)) *
                      S.place second
                        (S.expPointEffectAtLineAnswer second.side .Z sample.2.2 z fZ)).mulVec
                          S.psiHat))).re))| ≤
          C * Real.sqrt (P.m : ℝ) *
            (Real.rpow δP (1 / 4 : ℝ) + Real.rpow δQ (1 / 4 : ℝ)) := by
  refine ⟨2, by norm_num, ?_⟩
  intro P ε δQ δP S points lines sublines first second hopposite
  classical
  have hside := sublines.avgOver_regrouped_eq_at lines first second
  have hprob : (Distribution.prod sublines.D
      (uniformDistribution (DirectScalarQ P.extendedDirectLd))).IsProbability :=
    Distribution.prod_isProbability _ _ sublines.isProbability
      (uniformDistribution_isProbability _)
  have hδP : 0 ≤ δP := by
    refine le_trans ?_ (lines.consistent first second hopposite)
    unfold consistencyDefect
    exact avgOver_nonneg _ _ fun s =>
      consistencyDefect_integrand_nonneg S first second hopposite
        ((lines.T first.side s.1.1 s.2.1).postprocess fun fs =>
          (evalOpt s.1.1 s.1.2 fs.1, evalOpt s.2.1 s.2.2 fs.2))
        ((points.Q second.side s.1.2 s.2.2).postprocess fun ab => (some ab.1, some ab.2))
  have hδQ : 0 ≤ δQ :=
    le_trans (opFamilyDistSq_nonneg _ _ _ _) (points.self_consistent first second hopposite)
  have hm : (1 : ℝ) ≤ (P.m : ℝ) := by exact_mod_cast P.one_le_m
  simp only [← ProjectiveSetting.pointMeasExpOption_effect_evalOpt]
  rw [hside (fun x z o1 o2 => (S.pointMeasExpOption second.side .Z z).effect o2 *
      (S.pointMeasExpOption second.side .X x).effect o1),
    hside (fun x z o1 o2 => (S.pointMeasExpOption second.side .Z z).effect o2)]
  have hcs := abs_overlap_gap_le_sqrt_one_sub_of_isProj'
    (Distribution.prod sublines.D
      (uniformDistribution (DirectScalarQ P.extendedDirectLd)))
    (fun s => S.placedMeasurement first
      ((lines.T first.side s.1.2.1 s.1.2.2).postprocess (fun fs =>
        (evalOpt s.1.2.1 (projX (directPointToPauli P
            (s.1.1.base + s.2 • s.1.1.direction))) fs.1,
          evalOpt s.1.2.2 (projZ (directPointToPauli P
            (s.1.1.base + s.2 • s.1.1.direction))) fs.2))))
    (fun (s : SubLineTriple P × DirectScalarQ P.extendedDirectLd)
        (o : Option (PauliScalar P) × Option (PauliScalar P)) =>
      S.place second ((S.pointMeasExpOption second.side .X
        (projX (directPointToPauli P
          (s.1.1.base + s.2 • s.1.1.direction)))).effect o.1))
    (fun (s : SubLineTriple P × DirectScalarQ P.extendedDirectLd)
        (o : Option (PauliScalar P) × Option (PauliScalar P)) =>
      S.place second ((S.pointMeasExpOption second.side .Z
        (projZ (directPointToPauli P
          (s.1.1.base + s.2 • s.1.1.direction)))).effect o.2))
    (fun (s : SubLineTriple P × DirectScalarQ P.extendedDirectLd)
        (o : Option (PauliScalar P) × Option (PauliScalar P)) =>
      S.place second
        ((S.pointMeasExpOption second.side .Z
            (projZ (directPointToPauli P
              (s.1.1.base + s.2 • s.1.1.direction)))).effect o.2 *
          (S.pointMeasExpOption second.side .X
            (projX (directPointToPauli P
              (s.1.1.base + s.2 • s.1.1.direction)))).effect o.1))
    S.psiHat hprob S.psiHat_norm
    (fun s o => S.place_isProj _ (S.pointMeasExpOption_isProj _ _ _ _))
    (fun s o => S.place_isProj _ (S.pointMeasExpOption_isProj _ _ _ _))
    (fun s o => S.place_comm first second hopposite _ _)
    (fun s o => S.place_comm first second hopposite _ _)
    (fun s o => ProjectiveSetting.place_mul S second _ _)
  refine hcs.trans ?_
  have hrew : avgOver (Distribution.prod sublines.D
      (uniformDistribution (DirectScalarQ P.extendedDirectLd)))
      (fun s => ∑ o : Option (PauliScalar P) × Option (PauliScalar P),
        stateQForm S.psiHat
          ((S.placedMeasurement first
            ((lines.T first.side s.1.2.1 s.1.2.2).postprocess (fun fs =>
              (evalOpt s.1.2.1 (projX (directPointToPauli P
                  (s.1.1.base + s.2 • s.1.1.direction))) fs.1,
                evalOpt s.1.2.2 (projZ (directPointToPauli P
                  (s.1.1.base + s.2 • s.1.1.direction))) fs.2)))).effect o *
            S.place second ((S.pointMeasExpOption second.side .X
              (projX (directPointToPauli P
                (s.1.1.base + s.2 • s.1.1.direction)))).effect o.1))) =
      avgOver sublines.D (fun sample =>
        avgOver (uniformDistribution (DirectScalarQ P.extendedDirectLd))
          (fun t => xPointOverlapAt lines first second (sample.2, projX (directPointToPauli P
            (sample.1.base + t • sample.1.direction))))) := by
    rw [avgOver_prod]
    refine avgOver_congr _ _ _ fun sample => avgOver_congr _ _ _ fun t => ?_
    exact regroup_line_answer_sum_at lines first second sample.2.1 sample.2.2 _ _
      (fun o1 _ => (S.pointMeasExpOption second.side .X (projX (directPointToPauli P
        (sample.1.base + t • sample.1.direction)))).effect o1)
  refine (Real.sqrt_le_sqrt ?_).trans (sqrt_deficit_bound_le _ _ _ hm hδP hδQ)
  have hX := sublines.one_sub_avgOver_xPointOverlap_le_at lines first second hopposite
  rw [← hrew] at hX
  exact hX

/-- The remaining Z overlap for arbitrary opposite register placements.
The one-point Z mixture and positivity prove this counterpart of paper
`claim:17-3`, lines 1204--1239, without a joint restricted-product law. -/
theorem subline_Z_term_near_one_at :
    ∃ C : ℝ, 0 < C ∧
      ∀ (P : AdmissibleParams) (ε δQ δP : ℝ)
        (S : ProjectiveSetting P ε) (points : CombinedPointsWitness S δQ)
        (lines : CombinedLinesWitness S points δP) (sublines : SubLineWitness P)
        (first second : Placement) (_hopposite : first.IsOpposite second),
        |avgOver sublines.D (fun sample =>
            avgOver (uniformDistribution (DirectScalarQ P.extendedDirectLd)) (fun t =>
              let u := directPointToPauli P
                (sample.1.base + t • sample.1.direction)
              let z := projZ u
              ∑ fX, ∑ fZ,
                (inner ℂ S.psiHat ((EuclideanSpace.equiv
                  (SixReg P S.toStrategy.ιA S.toStrategy.ιB) ℂ).symm
                    ((S.place first
                        ((lines.T first.side sample.2.1 sample.2.2).effect (fX, fZ)) *
                      S.place second
                        (S.expPointEffectAtLineAnswer second.side .Z sample.2.2 z fZ)).mulVec
                          S.psiHat))).re)) - 1| ≤
          C * Real.sqrt (P.m : ℝ) *
            (Real.rpow δP (1 / 4 : ℝ) + Real.rpow δQ (1 / 4 : ℝ) +
              Real.rpow ε (1 / 4 : ℝ)) := by
  refine ⟨2, by norm_num, ?_⟩
  intro P ε δQ δP S points lines sublines first second hopposite
  classical
  have hδP : 0 ≤ δP := by
    refine le_trans ?_ (lines.consistent first second hopposite)
    unfold consistencyDefect
    exact avgOver_nonneg _ _ fun s =>
      consistencyDefect_integrand_nonneg S first second hopposite
        ((lines.T first.side s.1.1 s.2.1).postprocess fun fs =>
          (evalOpt s.1.1 s.1.2 fs.1, evalOpt s.2.1 s.2.2 fs.2))
        ((points.Q second.side s.1.2 s.2.2).postprocess fun ab => (some ab.1, some ab.2))
  have hδQ : 0 ≤ δQ :=
    le_trans (opFamilyDistSq_nonneg _ _ _ _) (points.self_consistent first second hopposite)
  have hm : (1 : ℝ) ≤ (P.m : ℝ) := by exact_mod_cast P.one_le_m
  have hLHS : avgOver sublines.D (fun sample =>
      avgOver (uniformDistribution (DirectScalarQ P.extendedDirectLd)) (fun t =>
        let u := directPointToPauli P
          (sample.1.base + t • sample.1.direction)
        let z := projZ u
        ∑ fX, ∑ fZ,
          (inner ℂ S.psiHat ((EuclideanSpace.equiv
            (SixReg P S.toStrategy.ιA S.toStrategy.ιB) ℂ).symm
              ((S.place first
                  ((lines.T first.side sample.2.1 sample.2.2).effect (fX, fZ)) *
                S.place second
                  (S.expPointEffectAtLineAnswer second.side .Z sample.2.2 z fZ)).mulVec
                    S.psiHat))).re)) =
      avgOver sublines.D (fun sample =>
        avgOver (uniformDistribution (DirectScalarQ P.extendedDirectLd))
          (fun t => zPointOverlapAt lines first second (sample.2, projZ (directPointToPauli P
            (sample.1.base + t • sample.1.direction))))) := by
    refine avgOver_congr _ _ _ fun sample => avgOver_congr _ _ _ fun t => ?_
    simp only [zPointOverlapAt, ← ProjectiveSetting.pointMeasExpOption_effect_evalOpt]
    rfl
  rw [hLHS]
  set L := avgOver sublines.D (fun sample =>
    avgOver (uniformDistribution (DirectScalarQ P.extendedDirectLd))
      (fun t => zPointOverlapAt lines first second (sample.2, projZ (directPointToPauli P
        (sample.1.base + t • sample.1.direction))))) with hL
  have hdef := sublines.one_sub_avgOver_zPointOverlap_le_at lines first second hopposite
  have hle := sublines.avgOver_zPointOverlap_le_one_at lines first second hopposite
  have hnonneg : 0 ≤ L :=
    avgOver_nonneg _ _ fun sample => avgOver_nonneg _ _ fun t =>
      zPointOverlap_nonneg_at lines first second hopposite _
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

/-- Expand the state quadratic form before specializing the register carrier. -/
private theorem stateQForm_eq_inner_mulVec {Carrier : Type*}
    [Fintype Carrier] [DecidableEq Carrier]
    (state : EuclideanSpace ℂ Carrier) (operator : Op Carrier) :
    stateQForm state operator = (inner ℂ state
      ((EuclideanSpace.equiv Carrier ℂ).symm (operator.mulVec state))).re := rfl

set_option maxHeartbeats 800000 in
/-- The first-route paired overlap estimate holds for every opposite placement.
This includes the second relation of paper `lem:qld-4-13` at lines 1020--1034,
with the established first-route error, not the stronger printed polynomial. -/
theorem subline_joint_overlap_near_one_at :
    ∃ constant : ℝ, 0 < constant ∧
      ∀ (params : AdmissibleParams) (error pointError lineError : ℝ)
        (setting : ProjectiveSetting params error)
        (points : CombinedPointsWitness setting pointError)
        (lines : CombinedLinesWitness setting points lineError) (sublines : SubLineWitness params)
        (first second : Placement), first.IsOpposite second →
        |avgOver sublines.D (pairedSublineOverlap setting points lines first second) - 1| ≤
          constant * (pointError ^ (1 / 2 : ℝ) + Real.sqrt (params.m : ℝ) *
            (lineError ^ (1 / 4 : ℝ) + pointError ^ (1 / 4 : ℝ) +
              error ^ (1 / 4 : ℝ))) := by
  obtain ⟨removeConstant, hremoveConstant, hremove⟩ := subline_remove_X_factor_at
  obtain ⟨nearConstant, hnearConstant, hnear⟩ := subline_Z_term_near_one_at
  refine ⟨2 + removeConstant + nearConstant, by positivity, ?_⟩
  intro params error pointError lineError setting points lines sublines first second hopposite
  let zOverlap := avgOver sublines.D (fun sample =>
    avgOver (uniformDistribution (DirectScalarQ params.extendedDirectLd)) (fun parameter =>
      zPointOverlapAt lines first second (sample.2, projZ (directPointToPauli params
        (sample.1.base + parameter • sample.1.direction)))))
  have hfirst : |avgOver sublines.D
      (pairedSublineOverlap setting points lines first second) - avgOver sublines.D
        (orderedSublineOverlap setting points lines first second)| ≤
      2 * pointError ^ (1 / 2 : ℝ) := by
    have heq : Real.sqrt (4 * pointError) = 2 * pointError ^ (1 / 2 : ℝ) := by
      rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 4)]
      norm_num [Real.sqrt_eq_rpow]
    exact (sublines.paired_ordered_overlap_gap_le lines first second).trans_eq heq
  have hsecond : |avgOver sublines.D
      (orderedSublineOverlap setting points lines first second) - zOverlap| ≤
      removeConstant * Real.sqrt (params.m : ℝ) *
        (lineError ^ (1 / 4 : ℝ) + pointError ^ (1 / 4 : ℝ)) := by
    have hbound := hremove params error pointError lineError setting points lines sublines
      first second hopposite
    simp only [← ProjectiveSetting.pointMeasExpOption_effect_evalOpt] at hbound
    unfold orderedSublineOverlap zOverlap zPointOverlapAt
    simp only [Fintype.sum_prod_type, stateQForm_eq_inner_mulVec]
    with_unfolding_all exact hbound
  have hthird : |zOverlap - 1| ≤ nearConstant * Real.sqrt (params.m : ℝ) *
      (lineError ^ (1 / 4 : ℝ) + pointError ^ (1 / 4 : ℝ) + error ^ (1 / 4 : ℝ)) := by
    have hbound := hnear params error pointError lineError setting points lines sublines
      first second hopposite
    simp only [← ProjectiveSetting.pointMeasExpOption_effect_evalOpt] at hbound
    unfold zOverlap zPointOverlapAt
    simp only [stateQForm_eq_inner_mulVec]
    with_unfolding_all exact hbound
  have hchain := (abs_sub_le _ _ (1 : ℝ)).trans
    (add_le_add hfirst ((abs_sub_le _ zOverlap (1 : ℝ)).trans (add_le_add hsecond hthird)))
  have hhalf : 0 ≤ pointError ^ (1 / 2 : ℝ) := by
    rw [← Real.sqrt_eq_rpow]
    exact Real.sqrt_nonneg _
  have hsum : 0 ≤ lineError ^ (1 / 4 : ℝ) + pointError ^ (1 / 4 : ℝ) :=
    add_nonneg (rpow_quarter_nonneg _) (rpow_quarter_nonneg _)
  have hquarter := rpow_quarter_nonneg error
  simp only [Real.rpow_eq_pow] at hquarter
  have hdimension := Real.sqrt_nonneg (params.m : ℝ)
  refine hchain.trans ?_
  nlinarith [mul_nonneg hremoveConstant.le hhalf, mul_nonneg hnearConstant.le hhalf,
    mul_nonneg hdimension hsum, mul_nonneg hdimension hquarter,
    mul_nonneg (mul_nonneg hremoveConstant.le hdimension) hquarter]


end

end MIPStarRE.QPBT
