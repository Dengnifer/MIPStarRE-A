import MIPStarRE.QPBT.Combining.ComplexOverlapGap
import MIPStarRE.QPBT.Combining.Lines.CombinedMeasurement
import MIPStarRE.QPBT.Combining.OrderedPoints
import MIPStarRE.QPBT.Combining.UniformLinePoint
import MIPStarRE.QPBT.Combining.ZEvalDeficit

/-!
# Complex overlaps for the directly indexed subline law

The ordered-product replacement uses complex Cauchy--Schwarz with a positive
measurement weight. The remaining Z overlap is real because its positive factors
act on opposite registers. Neither argument identifies the directly indexed law
with the source law, or changes the completed evaluation alphabet.

## References

Paper `claim:17-1` and `claim:17-3`,
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1140-1239`;
the X-Z-X construction is at lines 942--949. See issue #689 and
`docs/paper-gaps/qpbt_subline-claims-line-marginal.tex`.
-/

open scoped BigOperators Matrix MatrixOrder ComplexOrder

namespace MIPStarRE.QPBT

open MIPStarRE.LDT hiding Measurement
open MIPStarRE.Quantum MIPStarRE.QPBT.DistanceCalculus

noncomputable section

/-- Complex counterpart of the real overlap-distance estimate. Positivity and
completeness of the left measurement suffice; neither right family is assumed
Hermitian. This is the Cauchy--Schwarz step of paper `claim:17-1`, using
`Wᴴ * W` as the squared-norm operator for `W = B - C`. -/
theorem norm_overlap_gap_le_sqrt_of_opFamilyDistSq {X α ι : Type*}
    [Fintype α] [Fintype ι] [DecidableEq ι]
    (μ : Distribution X) (A : X → Measurement α ι) (B C : X → α → Op ι)
    (ψ : EuclideanSpace ℂ ι) (hμ : μ.IsProbability) (hψ : ‖ψ‖ = 1)
    (ζ : ℝ) (hBC : opFamilyDistSq μ B C ψ ≤ ζ) :
    ‖(∑ x ∈ μ.support, (μ.weight x : ℂ) * ∑ a,
        inner ℂ ψ (applyOperatorToState ((A x).effect a * B x a) ψ)) -
      (∑ x ∈ μ.support, (μ.weight x : ℂ) * ∑ a,
        inner ℂ ψ (applyOperatorToState ((A x).effect a * C x a) ψ))‖ ≤
      Real.sqrt ζ := by
  classical
  have hdiff :
      (∑ x ∈ μ.support, (μ.weight x : ℂ) * ∑ a,
        inner ℂ ψ (applyOperatorToState ((A x).effect a * B x a) ψ)) -
      (∑ x ∈ μ.support, (μ.weight x : ℂ) * ∑ a,
        inner ℂ ψ (applyOperatorToState ((A x).effect a * C x a) ψ)) =
      ∑ x ∈ μ.support, (μ.weight x : ℂ) * ∑ a,
        inner ℂ ψ (applyOperatorToState ((A x).effect a)
          (applyOperatorToState (B x a - C x a) ψ)) := by
    simp [applyOperatorToState, Finset.sum_sub_distrib, mul_sub]
  rw [hdiff]
  have hcs := norm_weighted_sum_inner_le_sqrt_mul_sqrt μ
    (fun x a => (A x).effect a) (fun x a => (A x).pos a)
    (fun _ _ => ψ) (fun x a => applyOperatorToState (B x a - C x a) ψ)
  have hleft : avgOver μ (fun x => ∑ a, stateQForm ψ ((A x).effect a)) = 1 := by
    simp only [sum_stateQForm_effect_eq_one _ ψ hψ]
    exact avgOver_const_of_isProbability μ hμ 1
  have hright : avgOver μ (fun x => ∑ a,
      stateQForm (applyOperatorToState (B x a - C x a) ψ) ((A x).effect a)) ≤ ζ := by
    refine le_trans (avgOver_mono _ _ _ fun x => Finset.sum_le_sum fun a _ =>
      stateQForm_le_norm_sq_of_le_one _ (measurement_effect_le_one (A x) a)) hBC
  rw [hleft, Real.sqrt_one, one_mul] at hcs
  exact hcs.trans (Real.sqrt_le_sqrt hright)

/-- Regroup a complex overlap along the fibers of a measurement postprocessing.
This is the finite-sum step in paper `claim:17-1`. -/
private theorem sum_inner_postprocess {α β ι : Type*}
    [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    [Fintype ι] [DecidableEq ι] (A : Measurement α ι) (f : α → β)
    (B : β → Op ι) (ψ : EuclideanSpace ℂ ι) :
    (∑ b, inner ℂ ψ (applyOperatorToState ((A.postprocess f).effect b * B b) ψ)) =
      ∑ a, inner ℂ ψ (applyOperatorToState (A.effect a * B (f a)) ψ) := by
  simp only [Measurement.postprocess_effect, Finset.sum_mul, applyOperatorToState,
    map_sum, LinearMap.sum_apply, inner_sum]
  calc
    (∑ b, ∑ a ∈ Finset.univ.filter (fun a => f a = b),
        inner ℂ ψ (Matrix.toEuclideanLin (A.effect a * B b) ψ)) =
      ∑ b, ∑ a ∈ Finset.univ.filter (fun a => f a = b),
        inner ℂ ψ (Matrix.toEuclideanLin (A.effect a * B (f a)) ψ) := by
      refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun a ha => ?_
      rw [(Finset.mem_filter.mp ha).2]
    _ = _ := Finset.sum_fiberwise _ _ _

/-- Complex-modulus ordered-product replacement for the actual X-Z-X measurement.

**Scope restriction:** This proves the directly indexed, completed-evaluation
analogue of paper `claim:17-1` (lines 1140--1166), with constant `2` from the
same-placement squared-distance bound `4 * δQ`. No line-consistency witness or
reality hypothesis is needed. Source-law transport remains open under issue #118;
see `docs/paper-gaps/qpbt_subline-claims-line-marginal.tex`. -/
theorem subline_replace_by_ordered_product_direct {P : AdmissibleParams} {ε δQ : ℝ}
    (S : ProjectiveSetting P ε) (points : CombinedPointsWitness S δQ)
    (sublines : SubLineWitness P) :
    ‖(∑ sample ∈ sublines.D.support,
        (sublines.D.weight sample : ℂ) *
          (Fintype.card (DirectScalarQ P.extendedDirectLd) : ℂ)⁻¹ *
            ∑ t : DirectScalarQ P.extendedDirectLd,
        let u := directPointToPauli P (sample.1.base + t • sample.1.direction)
        ∑ fX, ∑ fZ, inner ℂ S.psiHat (applyOperatorToState
          (S.place .AA' ((S.combinedLineMeasurement .alice sample.2.1 sample.2.2).effect
              (fX, fZ)) *
            S.place .BA'' (((points.Q .bob (projX u) (projZ u)).postprocess
              (fun ab => (some ab.1, some ab.2))).effect
                (evalOpt sample.2.1 (projX u) fX, evalOpt sample.2.2 (projZ u) fZ)))
          S.psiHat)) -
      (∑ sample ∈ sublines.D.support,
        (sublines.D.weight sample : ℂ) *
          (Fintype.card (DirectScalarQ P.extendedDirectLd) : ℂ)⁻¹ *
            ∑ t : DirectScalarQ P.extendedDirectLd,
        let u := directPointToPauli P (sample.1.base + t • sample.1.direction)
        ∑ fX, ∑ fZ, inner ℂ S.psiHat (applyOperatorToState
          (S.place .AA' ((S.combinedLineMeasurement .alice sample.2.1 sample.2.2).effect
              (fX, fZ)) *
            S.place .BA'' (S.expPointEffectAtLineAnswer .bob .Z sample.2.2 (projZ u) fZ *
              S.expPointEffectAtLineAnswer .bob .X sample.2.1 (projX u) fX)) S.psiHat))‖ ≤
      2 * Real.rpow δQ (1 / 2 : ℝ) := by
  classical
  let law := Distribution.prod sublines.D
    (uniformDistribution (DirectScalarQ P.extendedDirectLd))
  let point (s : SubLineTriple P × DirectScalarQ P.extendedDirectLd) :=
    directPointToPauli P (s.1.1.base + s.2 • s.1.1.direction)
  let evaluation (s : SubLineTriple P × DirectScalarQ P.extendedDirectLd)
      (fs : DegPoly P.toLdParams (P.m * P.d) × DegPoly P.toLdParams (P.m * P.d)) :=
    (evalOpt s.1.2.1 (projX (point s)) fs.1, evalOpt s.1.2.2 (projZ (point s)) fs.2)
  let line (s : SubLineTriple P × DirectScalarQ P.extendedDirectLd) :=
    S.placedMeasurement .AA' (S.combinedLineMeasurement .alice s.1.2.1 s.1.2.2)
  let joint (s : SubLineTriple P × DirectScalarQ P.extendedDirectLd)
      (o : Option (PauliScalar P) × Option (PauliScalar P)) :=
    S.place .BA'' (((points.Q .bob (projX (point s)) (projZ (point s))).postprocess
      (fun ab => (some ab.1, some ab.2))).effect o)
  let ordered (s : SubLineTriple P × DirectScalarQ P.extendedDirectLd)
      (o : Option (PauliScalar P) × Option (PauliScalar P)) :=
    S.place .BA'' ((S.pointMeasExpOption .bob .Z (projZ (point s))).effect o.2 *
      (S.pointMeasExpOption .bob .X (projX (point s))).effect o.1)
  have hprob : law.IsProbability := Distribution.prod_isProbability _ _
    sublines.isProbability (uniformDistribution_isProbability _)
  have hdist : opFamilyDistSq law joint ordered S.psiHat ≤ 4 * δQ := by
    unfold opFamilyDistSq
    have hcompleted := avgOver_congr law _ _ (fun s =>
      S.completedPair_norm_sq_sum_ZX points .BA'' (projX (point s)) (projZ (point s)))
    dsimp only [joint, ordered]
    erw [hcompleted]
    rw [show law = Distribution.prod sublines.D
      (uniformDistribution (DirectScalarQ P.extendedDirectLd)) from rfl,
      SandwichProduct.avgOver_distribution_prod]
    dsimp only [point]
    erw [SubLineWitness.avgOver_projX_projZ P sublines
      (fun xz => ∑ ab : PauliScalar P × PauliScalar P,
        ‖applyOperatorToState
          (S.place .BA'' ((points.Q .bob xz.1 xz.2).effect ab) -
            S.place .BA'' ((S.pointMeasExp .bob .Z xz.2).effect ab.2 *
              (S.pointMeasExp .bob .X xz.1).effect ab.1)) S.psiHat‖ ^ 2)]
    exact points.orderedZX_dist_le .BA''
  have hgap := norm_overlap_gap_le_sqrt_of_opFamilyDistSq law
    (fun s => (line s).postprocess (evaluation s)) joint ordered S.psiHat
    hprob S.psiHat_norm (4 * δQ) hdist
  simp only [sum_inner_postprocess] at hgap
  have h4 : Real.sqrt 4 = 2 := by norm_num
  rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 4), h4, Real.sqrt_eq_rpow] at hgap
  convert hgap using 1 <;>
    simp [law, Distribution.prod, uniformDistribution, Finset.sum_product,
      line, joint, ordered, evaluation, point, ProjectiveSetting.placedMeasurement_effect,
      Fintype.sum_prod_type, mul_assoc, Finset.mul_sum]
  simp only [← ProjectiveSetting.pointMeasExpOption_effect_evalOpt]
  rfl

/-- An opposite-register overlap of positive effects is its real part, embedded
in the complex numbers. Positivity of the tensor product proves reality. -/
private theorem placed_positive_overlap_eq_real {P : AdmissibleParams} {ε : ℝ}
    (S : ProjectiveSetting P ε) (A : Op (S.ExpandedLocalSpace .alice))
    (B : Op (S.ExpandedLocalSpace .bob)) (hA : 0 ≤ A) (hB : 0 ≤ B) :
    inner ℂ S.psiHat (applyOperatorToState (S.place .AA' A * S.place .BA'' B) S.psiHat) =
      (stateQForm S.psiHat (S.place .AA' A * S.place .BA'' B) : ℂ) := by
  have hpos := Matrix.nonneg_iff_posSemidef.mp
    (S.place_mul_place_nonneg .AA' .BA'' trivial hA hB)
  have him : (inner ℂ S.psiHat
      (applyOperatorToState (S.place .AA' A * S.place .BA'' B) S.psiHat)).im = 0 := by
    simpa only [applyOperatorToState, Matrix.toEuclideanLin, Matrix.toLpLin_apply,
      EuclideanSpace.inner_eq_star_dotProduct, dotProduct_comm] using
      (Complex.nonneg_iff.mp (hpos.dotProduct_mulVec_nonneg S.psiHat)).2.symm
  apply Complex.ext
  · rfl
  · simpa using him

/-- The Z overlap in paper `claim:17-3` is real for the directly indexed law.
This identity uses only positivity of the supplied line POVMs and opposite
placement of the point effects. In particular it applies to
`S.combinedLineMeasurement .alice`, without a reality assumption or any
consistency premise. See issue #689 and
`docs/paper-gaps/qpbt_subline-claims-line-marginal.tex`. -/
theorem subline_Z_overlap_eq_real_direct {P : AdmissibleParams} {ε : ℝ}
    (S : ProjectiveSetting P ε) (sublines : SubLineWitness P)
    (T : LineDesc P.toLdParams → LineDesc P.toLdParams →
      Measurement (DegPoly P.toLdParams (P.m * P.d) × DegPoly P.toLdParams (P.m * P.d))
        (S.ExpandedLocalSpace .alice)) :
    (∑ sample ∈ sublines.D.support,
      (sublines.D.weight sample : ℂ) *
        (Fintype.card (DirectScalarQ P.extendedDirectLd) : ℂ)⁻¹ *
          ∑ t : DirectScalarQ P.extendedDirectLd,
      let z := projZ (directPointToPauli P (sample.1.base + t • sample.1.direction))
      ∑ fX, ∑ fZ, inner ℂ S.psiHat (applyOperatorToState
        (S.place .AA' ((T sample.2.1 sample.2.2).effect (fX, fZ)) *
          S.place .BA'' (S.expPointEffectAtLineAnswer .bob .Z sample.2.2 z fZ)) S.psiHat)) =
      (avgOver sublines.D (fun sample =>
        avgOver (uniformDistribution (DirectScalarQ P.extendedDirectLd)) (fun t =>
          let z := projZ (directPointToPauli P (sample.1.base + t • sample.1.direction))
          ∑ fX, ∑ fZ, stateQForm S.psiHat
            (S.place .AA' ((T sample.2.1 sample.2.2).effect (fX, fZ)) *
              S.place .BA'' (S.expPointEffectAtLineAnswer .bob .Z sample.2.2 z fZ)))) : ℂ) := by
  classical
  have hreal : ∀ lineX lineZ z fX fZ,
      inner ℂ S.psiHat (applyOperatorToState
        (S.place .AA' ((T lineX lineZ).effect (fX, fZ)) *
          S.place .BA'' (S.expPointEffectAtLineAnswer .bob .Z lineZ z fZ)) S.psiHat) =
      (stateQForm S.psiHat (S.place .AA' ((T lineX lineZ).effect (fX, fZ)) *
        S.place .BA'' (S.expPointEffectAtLineAnswer .bob .Z lineZ z fZ)) : ℂ) := by
    intro lineX lineZ z fX fZ
    apply placed_positive_overlap_eq_real S _ _ ((T lineX lineZ).pos (fX, fZ))
    rw [← S.pointMeasExpOption_effect_evalOpt]
    exact (S.pointMeasExpOption .bob .Z z).pos _
  simp only [hreal, avgOver, uniformDistribution, Distribution.uniformOnFinset_support,
    Distribution.uniformOnFinset_weight, Finset.mem_univ, if_true, Finset.card_univ, one_div]
  push_cast
  simp only [Finset.mul_sum, mul_assoc]

end

end MIPStarRE.QPBT
