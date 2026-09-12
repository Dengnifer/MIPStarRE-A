import MIPStarRE.QPBT.Combining.Lines.Marginal
import MIPStarRE.QPBT.Combining.SubLineZDeficit

/-!
# Concrete X-overlap deficit on sub-line samples

This module bounds the deficit of the overlap between the constructed X-Z-X
line measurement and the expanded X-point effect. The exact X marginal of the
constructed measurement reduces the overlap to expanded line-point
consistency, and the sub-line mixture law transfers that estimate to the
restricted line-point components.

## References

This is the deficit estimate in the proof of `lem:claim-17-2`, paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1168-1201`.
-/

open scoped BigOperators

namespace MIPStarRE.QPBT

open MIPStarRE.LDT hiding Measurement
open MIPStarRE.Quantum MIPStarRE.QPBT.DistanceCalculus

noncomputable section

private theorem opFamilyDistSq_self_mul_eq_one_sub_overlap
    {X α ι : Type*} [Fintype α] [Fintype ι] [DecidableEq ι]
    (μ : Distribution X) (A : X → Measurement α ι) (B : X → α → Op ι)
    (ψ : EuclideanSpace ℂ ι) (hμ : μ.IsProbability) (hψ : ‖ψ‖ = 1)
    (hA : ∀ x, MIPStarRE.QPBT.Measurement.IsProjective (A x))
    (hB : ∀ x a, IsProj (B x a))
    (hAB : ∀ x a, Commute ((A x).effect a) (B x a)) :
    opFamilyDistSq μ (fun x a => (A x).effect a)
        (fun x a => (A x).effect a * B x a) ψ =
      1 - avgOver μ (fun x =>
        ∑ a, stateQForm ψ ((A x).effect a * B x a)) := by
  unfold opFamilyDistSq
  calc
    avgOver μ (fun x => ∑ a,
        ‖applyOperatorToState ((A x).effect a - (A x).effect a * B x a) ψ‖ ^ 2) =
        avgOver μ (fun x => 1 -
          ∑ a, stateQForm ψ ((A x).effect a * B x a)) := by
      refine avgOver_congr _ _ _ fun x => ?_
      rw [← sum_stateQForm_effect_eq_one (A x) ψ hψ,
        ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun a _ => ?_
      have hcomm : Commute ((A x).effect a) (1 - B x a) :=
        (Commute.one_right _).sub_right (hAB x a)
      have hprod : IsProj ((A x).effect a * (1 - B x a)) :=
        (hA x a).mul (hB x a).one_sub hcomm
      rw [show (A x).effect a - (A x).effect a * B x a =
          (A x).effect a * (1 - B x a) by rw [mul_sub, mul_one]]
      rw [norm_applyOperatorToState_sq_eq_stateQForm,
        hprod.isSelfAdjoint.isHermitian.eq, hprod.isIdempotentElem.eq]
      simp [stateQForm, applyOperatorToState, mul_sub]
    _ = _ := by
      rw [avgOver_sub, avgOver_const_of_isProbability μ hμ]

/-- The overlap of the constructed X-Z-X line measurement with the expanded
X-point effect selected by the X-line answer. -/
def concreteXPointOverlap {P : AdmissibleParams} {ε : ℝ}
    (S : ProjectiveSetting P ε)
    (w : (LineDesc P.toLdParams × LineDesc P.toLdParams) ×
      (Fin P.m → PauliScalar P)) : ℝ :=
  ∑ fX, ∑ fZ, stateQForm S.psiHat
    (S.place .AA'
        ((S.combinedLineMeasurement Placement.AA'.side w.1.1 w.1.2).effect
          (fX, fZ)) *
      S.place .BA''
        (S.expPointEffectAtLineAnswer Placement.BA''.side .X w.1.1 w.2 fX))

private theorem concreteXPointOverlap_eq_linePointOverlap
    {P : AdmissibleParams} {ε : ℝ} (S : ProjectiveSetting P ε)
    (lineX lineZ : LineDesc P.toLdParams) (x : Fin P.m → PauliScalar P) :
    concreteXPointOverlap S ((lineX, lineZ), x) =
      ∑ fX, stateQForm S.psiHat
        (S.place .AA'
            ((S.lineMeasExp Placement.AA'.side .X lineX).effect fX) *
          S.place .BA''
            (S.expPointEffectAtLineAnswer Placement.BA''.side .X lineX x fX)) := by
  classical
  unfold concreteXPointOverlap
  refine Finset.sum_congr rfl fun fX _ => ?_
  rw [← DistanceCalculus.stateQForm_finset_sum, ← Finset.sum_mul,
    ← S.place_finset_sum, S.combinedLineMeasurement_sum_Z]

private theorem concreteXPointOverlap_restricted_deficit_le
    (C : ℝ)
    (hC : 0 ≤ C)
    (hline : ∀ (P : AdmissibleParams) (ε : ℝ) (S : ProjectiveSetting P ε)
      (p₁ p₂ : Placement), p₁.IsOpposite p₂ → ∀ W : PauliKind,
      opFamilyDistSq (linePointDist P.toLdParams)
        (fun sample f => S.place p₁
          ((S.lineMeasExp p₁.side W sample.1).effect f))
        (fun sample f =>
          S.place p₁ ((S.lineMeasExp p₁.side W sample.1).effect f) *
            S.place p₂ (S.expPointEffectAtLineAnswer p₂.side W
              sample.1 sample.2 f))
        S.psiHat ≤ C * deltaLine ε)
    (P : AdmissibleParams) (ε : ℝ) (S : ProjectiveSetting P ε)
    (kind : LineKind) (i j : Fin P.m) :
    1 - avgOver (Distribution.prod (restrictedLinePointDist P kind i)
        (restrictedLinePointDist P kind j))
      (fun w => concreteXPointOverlap S ((w.1.1, w.2.1), w.1.2)) ≤
      2 * C * (P.m : ℝ) ^ 2 * deltaLine ε := by
  classical
  let μX := restrictedLinePointDist P kind i
  let μZ := restrictedLinePointDist P kind j
  have hμX : μX.IsProbability := restrictedLinePointDist_isProbability P kind i
  have hμZ : μZ.IsProbability := restrictedLinePointDist_isProbability P kind j
  have hcollapse : avgOver (Distribution.prod μX μZ)
      (fun w => concreteXPointOverlap S ((w.1.1, w.2.1), w.1.2)) =
      avgOver μX (fun w => ∑ fX, stateQForm S.psiHat
        (S.place .AA'
            ((S.lineMeasExp Placement.AA'.side .X w.1).effect fX) *
          S.place .BA''
            (S.expPointEffectAtLineAnswer Placement.BA''.side .X w.1 w.2 fX))) := by
    rw [SandwichProduct.avgOver_distribution_prod]
    refine avgOver_congr _ _ _ fun wX => ?_
    calc
      avgOver μZ (fun wZ =>
          concreteXPointOverlap S ((wX.1, wZ.1), wX.2)) =
          avgOver μZ (fun _ => ∑ fX, stateQForm S.psiHat
            (S.place .AA'
                ((S.lineMeasExp Placement.AA'.side .X wX.1).effect fX) *
              S.place .BA'' (S.expPointEffectAtLineAnswer
                Placement.BA''.side .X wX.1 wX.2 fX))) := by
        refine avgOver_congr _ _ _ fun wZ => ?_
        exact concreteXPointOverlap_eq_linePointOverlap S wX.1 wZ.1 wX.2
      _ = _ := avgOver_const_of_isProbability μZ hμZ _
  rw [hcollapse]
  let A : (LineDesc P.toLdParams × (Fin P.m → PauliScalar P)) →
      Measurement (DegPoly P.toLdParams (P.m * P.d))
        (SixReg P S.toStrategy.ιA S.toStrategy.ιB) := fun w =>
    S.placedMeasurement .AA' (S.lineMeasExp Placement.AA'.side .X w.1)
  let B : (LineDesc P.toLdParams × (Fin P.m → PauliScalar P)) →
      DegPoly P.toLdParams (P.m * P.d) →
        Op (SixReg P S.toStrategy.ιA S.toStrategy.ιB) := fun w f =>
    S.place .BA'' (S.expPointEffectAtLineAnswer Placement.BA''.side .X w.1 w.2 f)
  change 1 - avgOver μX (fun w => ∑ f,
      stateQForm S.psiHat ((A w).effect f * B w f)) ≤ _
  rw [← opFamilyDistSq_self_mul_eq_one_sub_overlap μX A B S.psiHat hμX
    S.psiHat_norm]
  · calc
      opFamilyDistSq μX (fun w f => (A w).effect f)
          (fun w f => (A w).effect f * B w f) S.psiHat ≤
          2 * (P.m : ℝ) * opFamilyDistSq (linePointDist P.toLdParams)
            (fun w f => (A w).effect f)
            (fun w f => (A w).effect f * B w f) S.psiHat := by
        exact avgOver_restrictedLinePointDist_le _
          (fun w => Finset.sum_nonneg fun f _ => sq_nonneg _) kind i
      _ ≤ 2 * (P.m : ℝ) * (C * deltaLine ε) := by
        exact mul_le_mul_of_nonneg_left (hline P ε S .AA' .BA'' trivial .X)
          (by positivity)
      _ ≤ 2 * C * (P.m : ℝ) ^ 2 * deltaLine ε := by
        have hm : (1 : ℝ) ≤ (P.m : ℝ) := by exact_mod_cast P.one_le_m
        have hCδ : 0 ≤ C * deltaLine ε := by
          exact mul_nonneg hC (Real.sqrt_nonneg _)
        have hstep := mul_nonneg (sub_nonneg.mpr hm) hCδ
        nlinarith
  · intro w
    exact S.placedMeasurement_isProjective .AA' _
      (S.lineMeasExp_isProjective .alice .X w.1)
  · intro w f
    dsimp only [B]
    rw [← S.pointMeasExpOption_effect_evalOpt]
    exact S.place_isProj .BA''
      (S.pointMeasExpOption_isProj Placement.BA''.side .X w.2 _)
  · intro w f
    exact S.place_comm .AA' .BA'' trivial _ _

/-- The concrete X overlap over the directly indexed subline law has deficit at most a
universal constant times `m² * deltaLine ε`. This is the restricted-line
estimate used after Cauchy--Schwarz in `lem:claim-17-2`, paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1168-1201`.

**Scope restriction:** `SubLineWitness` describes the directly indexed law.
Transport to the source law remains open as recorded in
`docs/paper-gaps/qpbt_ld-dimension-divisibility.tex`. This real deficit estimate
does not itself prove the complex scalar comparison; see issue #474 and
`docs/paper-gaps/qpbt_subline-claims-line-marginal.tex`. -/
theorem exists_concreteXPointOverlap_deficit_le :
    ∃ C : ℝ, 0 < C ∧
      ∀ (P : AdmissibleParams) (ε : ℝ)
        (S : ProjectiveSetting P ε) (sublines : SubLineWitness P),
        1 - avgOver sublines.D (fun sample =>
          avgOver (uniformDistribution (DirectScalarQ P.extendedDirectLd))
            (fun t => concreteXPointOverlap S
              (sample.2, projX (directPointToPauli P
                (sample.1.base + t • sample.1.direction))))) ≤
          C * (P.m : ℝ) ^ 2 * deltaLine ε := by
  obtain ⟨C, hC, hline⟩ := expLine_point_cons
  refine ⟨2 * C, by positivity, ?_⟩
  intro P ε S sublines
  obtain ⟨components, hcomp, hmix⟩ :=
    sublines.exists_avgOver_X_eq_mixture P (concreteXPointOverlap S)
  rw [hmix]
  have hsplit : avgOver components (fun c => 1 -
      avgOver (Distribution.prod (restrictedLinePointDist P c.1 c.2.1)
        (restrictedLinePointDist P c.1 c.2.2))
        (fun w => concreteXPointOverlap S ((w.1.1, w.2.1), w.1.2))) =
      1 - avgOver components (fun c =>
        avgOver (Distribution.prod (restrictedLinePointDist P c.1 c.2.1)
          (restrictedLinePointDist P c.1 c.2.2))
          (fun w => concreteXPointOverlap S ((w.1.1, w.2.1), w.1.2))) := by
    rw [avgOver_sub, avgOver_const_of_isProbability components hcomp]
  rw [← hsplit]
  calc
    _ ≤ avgOver components (fun _ =>
        2 * C * (P.m : ℝ) ^ 2 * deltaLine ε) := by
      refine avgOver_mono _ _ _ fun c => ?_
      exact concreteXPointOverlap_restricted_deficit_le C (by linarith) hline P ε S
        c.1 c.2.1 c.2.2
    _ = _ := avgOver_const_of_isProbability components hcomp _

end

end MIPStarRE.QPBT
