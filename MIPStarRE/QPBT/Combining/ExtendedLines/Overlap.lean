import MIPStarRE.QPBT.Combining.ExtendedLines.Measurement
import MIPStarRE.QPBT.Combining.SubLineXDeficit

/-!
# Consistency of the extended-line measurements

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

/-- The completed point-pair effect is bounded by the effect of its linear
combination at the actual combined evaluation. Undefined source evaluations
contribute zero on the point side. The statement holds for either player's
measurement without any symmetry assumption on the strategy or local spaces. -/
theorem SubLineWitness.completedPoint_effect_le {params : AdmissibleParams}
    {Carrier : Type*} [Fintype Carrier] [DecidableEq Carrier]
    (sublines : SubLineWitness params) (sample : SubLineTriple params)
    (hsample : sample ∈ sublines.D.support)
    (polynomials : DegPoly params.toLdParams (params.m * params.d) ×
      DegPoly params.toLdParams (params.m * params.d))
    (point : Fin params.extendedDirectLd.m → DirectScalarQ params.extendedDirectLd)
    (hpoint : point ∈ sample.1.pointSet)
    (measurement : Quantum.Measurement (PauliScalar params × PauliScalar params) Carrier) :
    (measurement.postprocess (fun pair => (some pair.1, some pair.2))).effect
      (evalOpt sample.2.1 (projX (directPointToPauli params point)) polynomials.1,
        evalOpt sample.2.2 (projZ (directPointToPauli params point)) polynomials.2) ≤
      (measurement.postprocess (fun pair => some
        ((directPointToPauli params point) (alphaVar params.m) * pair.1 +
          (directPointToPauli params point) (betaVar params.m) * pair.2))).effect
        ((directEvalOpt sample.1 point
          (sublines.combinedPolynomial sample hsample polynomials)).map
            (extendedDirectScalarEquiv params)) := by
  classical
  have hnoneX (value : Option (PauliScalar params)) :
      (measurement.postprocess (fun pair => (some pair.1, some pair.2))).effect (none, value) =
        0 := by
    rw [Quantum.Measurement.postprocess_effect]
    apply Finset.sum_eq_zero
    intro pair hpair
    have himpossible := congrArg Prod.fst (Finset.mem_filter.mp hpair).2
    simp at himpossible
  have hnoneZ (value : Option (PauliScalar params)) :
      (measurement.postprocess (fun pair => (some pair.1, some pair.2))).effect (value, none) =
        0 := by
    rw [Quantum.Measurement.postprocess_effect]
    apply Finset.sum_eq_zero
    intro pair hpair
    have himpossible := congrArg Prod.snd (Finset.mem_filter.mp hpair).2
    simp at himpossible
  cases hevalX : evalOpt sample.2.1 (projX (directPointToPauli params point)) polynomials.1 with
  | none =>
    erw [hnoneX]
    exact Quantum.Submeasurement.pos _ _
  | some valueX =>
    cases hevalZ : evalOpt sample.2.2 (projZ (directPointToPauli params point)) polynomials.2 with
    | none =>
      erw [hnoneZ]
      exact Quantum.Submeasurement.pos _ _
    | some valueZ =>
      rw [sublines.combinedPolynomial_evalOpt sample hsample polynomials point hpoint
        valueX valueZ hevalX hevalZ]
      have hinjective : Function.Injective
          (fun pair : PauliScalar params × PauliScalar params => (some pair.1, some pair.2)) := by
        intro left right hequal
        exact Prod.ext (Option.some.inj (congrArg Prod.fst hequal))
          (Option.some.inj (congrArg Prod.snd hequal))
      erw [SandwichProduct.postprocess_effect_of_injective measurement _ hinjective
        (valueX, valueZ)]
      rw [Quantum.Measurement.postprocess_effect]
      exact Finset.single_le_sum (fun pair _ => measurement.pos pair)
        (Finset.mem_filter.mpr ⟨Finset.mem_univ _, rfl⟩)

/-- Uniform parameter resampling preserves the full direct line-point law,
including its canonical line, rather than merely its point marginal. -/
theorem avgOver_directLinePointDist_resample_parameter (params : DirectLdParams)
    (quantity : DirectLineDesc params × (Fin params.m → DirectScalarQ params) → ℝ) :
    avgOver (directLinePointDist params) quantity =
      avgOver ((directLinePointDist params).map Prod.fst) (fun line =>
        avgOver (uniformDistribution (DirectScalarQ params)) (fun parameter =>
          quantity (line, line.base + parameter • line.direction))) := by
  classical
  rw [Distribution.avgOver_map, directLinePointDist, avgOver_mix, avgOver_mix]
  congr 1
  · congr 1
    unfold directALinePointDist
    simp only [Distribution.avgOver_map]
    rw [← uniformDistribution_map_equiv (directLdSpaceIndexEquiv params).symm]
    simp only [Distribution.avgOver_map, uniformDistribution_prod, avgOver_prod]
    apply avgOver_congr
    intro index
    conv_lhs => rw [avgOver_comm]
    conv_rhs => rw [avgOver_comm]
    apply avgOver_congr
    intro direction
    simpa only [directLdSpaceIndexEquiv, Equiv.coe_fn_symm_mk, directALineDescOf,
      DirectLineDesc.base, DirectLineDesc.direction, lineRepMap_apply_self] using
      avgOver_lineRepMap_resample_parameter (coordinateDirection index)
        (fun base point => quantity
          (.axis (lineRepMap (coordinateDirection index) base) index
            (lineRepMap_apply_self _ _), point))
  · congr 1
    unfold directDLinePointDist
    simp only [Distribution.avgOver_map]
    rw [← uniformDistribution_map_equiv (directLdSpaceIndexEquiv params).symm]
    simp only [Distribution.avgOver_map, uniformDistribution_prod, avgOver_prod]
    apply avgOver_congr
    intro index
    conv_lhs => rw [avgOver_comm]
    conv_rhs => rw [avgOver_comm]
    apply avgOver_congr
    intro direction
    simpa only [directLdSpaceIndexEquiv, Equiv.coe_fn_symm_mk, directDLineDescOf,
      DirectLineDesc.base, DirectLineDesc.direction, lineRepMap_apply_self] using
      avgOver_lineRepMap_resample_parameter (directPrefixProjection index direction)
        (fun base point => quantity
          (.diagonal (lineRepMap (directPrefixProjection index direction) base) index
            (directPrefixProjection index direction) (lineRepMap_apply_self _ _)
            (by intro coordinate hbefore; simp [directPrefixProjection, hbefore]), point))

/-- Real scalar multiplication commutes with placement. -/
private theorem place_real_smul {params : AdmissibleParams} {error : ℝ}
    (setting : ProjectiveSetting params error) (placement : Placement) (scalar : ℝ)
    (operator : Op (setting.ExpandedLocalSpace placement.side)) :
    setting.place placement (scalar • operator) = scalar • setting.place placement operator := by
  ext row column
  cases placement <;> simp only [ProjectiveSetting.place, Matrix.smul_apply, Complex.real_smul] <;>
    ring

/-- A placed overlap is linear in an averaged left operator. -/
private theorem placed_overlap_average {params : AdmissibleParams} {error : ℝ}
    {Sample : Type*} (setting : ProjectiveSetting params error) (first second : Placement)
    (law : Distribution Sample) (family : Sample → Op (setting.ExpandedLocalSpace first.side))
    (right : Op (setting.ExpandedLocalSpace second.side)) :
    stateQForm setting.psiHat
      (setting.place first (averageOperatorOverDistribution law family) *
        setting.place second right) =
      avgOver law (fun sample => stateQForm setting.psiHat
        (setting.place first (family sample) * setting.place second right)) := by
  unfold averageOperatorOverDistribution avgOver
  rw [setting.place_finsetSum, Finset.sum_mul, stateQForm_finset_sum]
  apply Finset.sum_congr rfl
  intro sample _
  rw [place_real_smul, smul_mul_assoc]
  have hscalar (operator : Op (SixReg params setting.toStrategy.ιA setting.toStrategy.ιB)) :
      law.weight sample • operator = (law.weight sample : ℂ) • operator := by
    ext row column
    simp [Complex.real_smul]
  rw [hscalar]
  simp only [stateQForm, WinImplications.applyOperatorToState_smul_op, inner_smul_right,
    Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]

/-- Postprocessing the left measurement groups, but does not alter, its overlap
with a family indexed by the postprocessed answer. -/
private theorem placed_overlap_postprocess {params : AdmissibleParams} {error : ℝ}
    {Answer Output : Type*} [Fintype Answer] [DecidableEq Answer]
    [Fintype Output] [DecidableEq Output]
    (setting : ProjectiveSetting params error) (first second : Placement)
    (measurement : Quantum.Measurement Answer (setting.ExpandedLocalSpace first.side))
    (mapping : Answer → Output) (right : Output → Op (setting.ExpandedLocalSpace second.side)) :
    (∑ output, stateQForm setting.psiHat
      (setting.place first ((measurement.postprocess mapping).effect output) *
        setting.place second (right output))) =
      ∑ answer, stateQForm setting.psiHat
        (setting.place first (measurement.effect answer) *
          setting.place second (right (mapping answer))) := by
  classical
  simp only [Quantum.Measurement.postprocess_effect, setting.place_finsetSum,
    Finset.sum_mul, stateQForm_finset_sum]
  calc
    (∑ output, ∑ answer ∈ Finset.univ.filter (fun answer => mapping answer = output),
        stateQForm setting.psiHat (setting.place first (measurement.effect answer) *
          setting.place second (right output))) =
        ∑ output, ∑ answer ∈ Finset.univ.filter (fun answer => mapping answer = output),
          stateQForm setting.psiHat (setting.place first (measurement.effect answer) *
            setting.place second (right (mapping answer))) := by
      apply Finset.sum_congr rfl
      intro output _
      apply Finset.sum_congr rfl
      intro answer hanswer
      rw [(Finset.mem_filter.mp hanswer).2]
    _ = _ := Finset.sum_fiberwise _ _ _

/-- On opposite registers a positive left effect preserves order in the right
effect. This applies to both directed player placements without exchanging spaces. -/
private theorem placed_overlap_mono {params : AdmissibleParams} {error : ℝ}
    (setting : ProjectiveSetting params error) (first second : Placement)
    (hopposite : first.IsOpposite second)
    (left : Op (setting.ExpandedLocalSpace first.side))
    (lower upper : Op (setting.ExpandedLocalSpace second.side))
    (hleft : 0 ≤ left) (hright : lower ≤ upper) :
    stateQForm setting.psiHat (setting.place first left * setting.place second lower) ≤
      stateQForm setting.psiHat (setting.place first left * setting.place second upper) := by
  have hpositive := setting.place_mul_place_nonneg first second hopposite hleft
    (sub_nonneg.mpr hright)
  rw [setting.place_sub, mul_sub] at hpositive
  exact quadratic_form_mono (sub_nonneg.mp hpositive) setting.psiHat

/-- Expand the actual conditional extended-line POVM in a placed overlap.
This is exactly the averaging step at paper lines 1118--1134. -/
theorem SubLineWitness.extendedMeasurement_overlap {params : AdmissibleParams}
    {error pointError lineError : ℝ} {setting : ProjectiveSetting params error}
    {points : CombinedPointsWitness setting pointError}
    (sublines : SubLineWitness params) (lines : CombinedLinesWitness setting points lineError)
    (first second : Placement) (line : DirectLineDesc params.extendedDirectLd)
    (point : Fin params.extendedDirectLd.m → DirectScalarQ params.extendedDirectLd)
    (right : Option (PauliScalar params) → Op (setting.ExpandedLocalSpace second.side)) :
    (∑ answer, stateQForm setting.psiHat
      (setting.place first (((sublines.extendedMeasurement lines first.side line).postprocess
        (fun polynomial => (directEvalOpt line point polynomial).map
          (extendedDirectScalarEquiv params))).effect answer) *
            setting.place second (right answer))) =
      avgOver (sublines.conditionalLaw line) (fun sample =>
        ∑ pair, stateQForm setting.psiHat
          (setting.place first ((lines.T first.side sample.val.2.1 sample.val.2.2).effect pair) *
            setting.place second (right ((directEvalOpt line point
              (sublines.combinedPolynomial sample.val
                (Finset.mem_filter.mp sample.property).1 pair)).map
                  (extendedDirectScalarEquiv params))))) := by
  rw [placed_overlap_postprocess]
  change (∑ polynomial, stateQForm setting.psiHat
    (setting.place first (averageOperatorOverDistribution (sublines.conditionalLaw line)
      (fun sample => ((lines.T first.side sample.val.2.1 sample.val.2.2).postprocess
        (sublines.combinedPolynomial sample.val
          (Finset.mem_filter.mp sample.property).1)).effect polynomial)) *
      setting.place second (right ((directEvalOpt line point polynomial).map
        (extendedDirectScalarEquiv params))))) = _
  simp_rw [placed_overlap_average]
  rw [← avgOver_sum]
  apply avgOver_congr
  intro sample
  exact placed_overlap_postprocess setting first second _ _ _

/-- The actual paired-line versus point-pair overlap on one subline triple,
with its uniform affine parameter. This is the integrand of the first route. -/
def pairedSublineOverlap {params : AdmissibleParams} {error pointError lineError : ℝ}
    (setting : ProjectiveSetting params error) (points : CombinedPointsWitness setting pointError)
    (lines : CombinedLinesWitness setting points lineError) (first second : Placement)
    (sample : SubLineTriple params) : ℝ :=
  avgOver (uniformDistribution (DirectScalarQ params.extendedDirectLd)) (fun parameter =>
    let point := directPointToPauli params (sample.1.base + parameter • sample.1.direction)
    ∑ pair, stateQForm setting.psiHat
      (setting.place first ((lines.T first.side sample.2.1 sample.2.2).effect pair) *
        setting.place second (((points.Q second.side (projX point) (projZ point)).postprocess
          (fun values => (some values.1, some values.2))).effect
            (evalOpt sample.2.1 (projX point) pair.1,
              evalOpt sample.2.2 (projZ point) pair.2))))

/-- The actual extended-line versus extended-point overlap. Both families use
the supplied witnesses and the source polynomial combination. -/
def extendedPointOverlap {params : AdmissibleParams} {error pointError lineError : ℝ}
    (setting : ProjectiveSetting params error) (points : CombinedPointsWitness setting pointError)
    (lines : CombinedLinesWitness setting points lineError) (sublines : SubLineWitness params)
    (first second : Placement)
    (sample : DirectLineDesc params.extendedDirectLd ×
      (Fin params.extendedDirectLd.m → DirectScalarQ params.extendedDirectLd)) : ℝ :=
  ∑ answer, stateQForm setting.psiHat
    (setting.place first (((sublines.extendedMeasurement lines first.side sample.1).postprocess
      (fun polynomial => (directEvalOpt sample.1 sample.2 polynomial).map
        (extendedDirectScalarEquiv params))).effect answer) *
      setting.place second (((points.Q second.side
        (projX (directPointToPauli params sample.2))
        (projZ (directPointToPauli params sample.2))).postprocess (fun values => some
          ((directPointToPauli params sample.2) (alphaVar params.m) * values.1 +
            (directPointToPauli params sample.2) (betaVar params.m) * values.2))).effect answer))

/-- The completed point-effect comparison survives conditional averaging and
placement on either directed opposite register pair. -/
theorem SubLineWitness.extendedPointOverlap_ge {params : AdmissibleParams}
    {error pointError lineError : ℝ} {setting : ProjectiveSetting params error}
    {points : CombinedPointsWitness setting pointError}
    (sublines : SubLineWitness params) (lines : CombinedLinesWitness setting points lineError)
    (first second : Placement) (hopposite : first.IsOpposite second)
    (line : DirectLineDesc params.extendedDirectLd)
    (point : Fin params.extendedDirectLd.m → DirectScalarQ params.extendedDirectLd)
    (hpoint : point ∈ line.pointSet) :
    avgOver (sublines.conditionalLaw line) (fun sample =>
      ∑ pair, stateQForm setting.psiHat
        (setting.place first ((lines.T first.side sample.val.2.1 sample.val.2.2).effect pair) *
          setting.place second (((points.Q second.side
            (projX (directPointToPauli params point))
            (projZ (directPointToPauli params point))).postprocess
              (fun values => (some values.1, some values.2))).effect
                (evalOpt sample.val.2.1 (projX (directPointToPauli params point)) pair.1,
                  evalOpt sample.val.2.2 (projZ (directPointToPauli params point)) pair.2)))) ≤
      extendedPointOverlap setting points lines sublines first second (line, point) := by
  rw [extendedPointOverlap, sublines.extendedMeasurement_overlap]
  apply avgOver_mono
  intro sample
  apply Finset.sum_le_sum
  intro pair _
  apply placed_overlap_mono setting first second hopposite _ _ _
    ((lines.T first.side sample.val.2.1 sample.val.2.2).pos pair)
  have hline := (Finset.mem_filter.mp sample.property).2
  have hsample := (Finset.mem_filter.mp sample.property).1
  have hpointSample : point ∈ sample.val.1.pointSet := by rw [hline]; exact hpoint
  have hcomparison := sublines.completedPoint_effect_le sample.val hsample pair point hpointSample
    (points.Q second.side (projX (directPointToPauli params point))
      (projZ (directPointToPauli params point)))
  rw [hline] at hcomparison
  exact hcomparison

/-- The actual extended-line average dominates the first-route paired overlap.
This integrates the source conditional POVM without assuming any joint product
law for projected points. It holds for all directed opposite placements. -/
theorem SubLineWitness.avgOver_extendedPointOverlap_ge {params : AdmissibleParams}
    {error pointError lineError : ℝ} {setting : ProjectiveSetting params error}
    {points : CombinedPointsWitness setting pointError}
    (sublines : SubLineWitness params) (lines : CombinedLinesWitness setting points lineError)
    (first second : Placement) (hopposite : first.IsOpposite second) :
    avgOver sublines.D (pairedSublineOverlap setting points lines first second) ≤
      avgOver (directLinePointDist params.extendedDirectLd)
        (extendedPointOverlap setting points lines sublines first second) := by
  rw [avgOver_directLinePointDist_resample_parameter, ← sublines.extended_marginal,
    ← sublines.avgOver_conditionalLaw]
  apply avgOver_mono
  intro line
  unfold pairedSublineOverlap
  rw [avgOver_comm]
  apply avgOver_mono
  intro parameter
  have hpoint : line.base + parameter • line.direction ∈ line.pointSet := ⟨parameter, rfl⟩
  refine le_trans ?_ (sublines.extendedPointOverlap_ge lines first second hopposite line _ hpoint)
  apply le_of_eq
  apply avgOver_congr
  intro sample
  rw [(Finset.mem_filter.mp sample.property).2]

/-- The completed consistency defect of the actual extended-line POVM is
bounded by the first-route deficit, for both player placements. -/
theorem SubLineWitness.extended_consistencyDefect_le {params : AdmissibleParams}
    {error pointError lineError : ℝ} {setting : ProjectiveSetting params error}
    {points : CombinedPointsWitness setting pointError}
    (sublines : SubLineWitness params) (lines : CombinedLinesWitness setting points lineError)
    (first second : Placement) (hopposite : first.IsOpposite second) :
    consistencyDefect (directLinePointDist params.extendedDirectLd)
      (fun sample answer => setting.place first
        (((sublines.extendedMeasurement lines first.side sample.1).postprocess
          (fun polynomial => (directEvalOpt sample.1 sample.2 polynomial).map
            (extendedDirectScalarEquiv params))).effect answer))
      (fun sample answer => setting.place second
        (((points.Q second.side (projX (directPointToPauli params sample.2))
          (projZ (directPointToPauli params sample.2))).postprocess (fun values => some
            ((directPointToPauli params sample.2) (alphaVar params.m) * values.1 +
              (directPointToPauli params sample.2) (betaVar params.m) * values.2))).effect answer))
      setting.psiHat ≤ 1 - avgOver sublines.D
        (pairedSublineOverlap setting points lines first second) := by
  erw [consistencyDefect_eq_one_sub_overlap (directLinePointDist params.extendedDirectLd)
    (fun sample => setting.placedMeasurement first
      ((sublines.extendedMeasurement lines first.side sample.1).postprocess
        (fun polynomial => (directEvalOpt sample.1 sample.2 polynomial).map
          (extendedDirectScalarEquiv params))))
    (fun sample => setting.placedMeasurement second
      ((points.Q second.side (projX (directPointToPauli params sample.2))
        (projZ (directPointToPauli params sample.2))).postprocess (fun values => some
          ((directPointToPauli params sample.2) (alphaVar params.m) * values.1 +
            (directPointToPauli params sample.2) (betaVar params.m) * values.2))))
    setting.psiHat (directLinePointDist_isProbability _) setting.psiHat_norm]
  exact sub_le_sub_left (sublines.avgOver_extendedPointOverlap_ge lines first second hopposite) 1

/-- The ordered Z-then-X point overlap on the actual subline law. -/
def orderedSublineOverlap {params : AdmissibleParams} {error pointError lineError : ℝ}
    (setting : ProjectiveSetting params error) (points : CombinedPointsWitness setting pointError)
    (lines : CombinedLinesWitness setting points lineError) (first second : Placement)
    (sample : SubLineTriple params) : ℝ :=
  avgOver (uniformDistribution (DirectScalarQ params.extendedDirectLd)) (fun parameter =>
    let point := directPointToPauli params (sample.1.base + parameter • sample.1.direction)
    ∑ pair, stateQForm setting.psiHat
      (setting.place first ((lines.T first.side sample.2.1 sample.2.2).effect pair) *
        setting.place second
          ((setting.pointMeasExpOption second.side .Z (projZ point)).effect
              (evalOpt sample.2.2 (projZ point) pair.2) *
            (setting.pointMeasExpOption second.side .X (projX point)).effect
              (evalOpt sample.2.1 (projX point) pair.1))))

/-- The first-route replacement by the ordered point product holds for any
placement, in particular for the missing second-player orientation. Its only
distributional input is the uniform joint point marginal, not a product law
conditional on the projected lines. -/
theorem SubLineWitness.paired_ordered_overlap_gap_le {params : AdmissibleParams}
    {error pointError lineError : ℝ} {setting : ProjectiveSetting params error}
    {points : CombinedPointsWitness setting pointError}
    (sublines : SubLineWitness params) (lines : CombinedLinesWitness setting points lineError)
    (first second : Placement) :
    |avgOver sublines.D (pairedSublineOverlap setting points lines first second) -
      avgOver sublines.D (orderedSublineOverlap setting points lines first second)| ≤
        Real.sqrt (4 * pointError) := by
  let law := Distribution.prod sublines.D
    (uniformDistribution (DirectScalarQ params.extendedDirectLd))
  let point (sample : SubLineTriple params × DirectScalarQ params.extendedDirectLd) :=
    directPointToPauli params (sample.1.1.base + sample.2 • sample.1.1.direction)
  let lineMeasurement (sample : SubLineTriple params × DirectScalarQ params.extendedDirectLd) :=
    setting.placedMeasurement first
      ((lines.T first.side sample.1.2.1 sample.1.2.2).postprocess (fun pair =>
        (evalOpt sample.1.2.1 (projX (point sample)) pair.1,
          evalOpt sample.1.2.2 (projZ (point sample)) pair.2)))
  let joint (sample : SubLineTriple params × DirectScalarQ params.extendedDirectLd)
      (answer : Option (PauliScalar params) × Option (PauliScalar params)) :=
    setting.place second (((points.Q second.side (projX (point sample))
      (projZ (point sample))).postprocess (fun values => (some values.1, some values.2))).effect
        answer)
  let ordered (sample : SubLineTriple params × DirectScalarQ params.extendedDirectLd)
      (answer : Option (PauliScalar params) × Option (PauliScalar params)) :=
    setting.place second
      ((setting.pointMeasExpOption second.side .Z (projZ (point sample))).effect answer.2 *
        (setting.pointMeasExpOption second.side .X (projX (point sample))).effect answer.1)
  have hprob : law.IsProbability := Distribution.prod_isProbability _ _ sublines.isProbability
    (uniformDistribution_isProbability _)
  have hdist : opFamilyDistSq law joint ordered setting.psiHat ≤ 4 * pointError := by
    unfold opFamilyDistSq
    change avgOver law (fun sample => ∑ answer,
      ‖applyOperatorToState (joint sample answer - ordered sample answer) setting.psiHat‖ ^ 2) ≤ _
    have hcompleted := avgOver_congr law _ _ (fun sample =>
      setting.completedPair_norm_sq_sum_ZX points second
        (projX (point sample)) (projZ (point sample)))
    dsimp only [joint, ordered] at *
    rw [hcompleted]
    change avgOver law (fun sample => ∑ answer : PauliScalar params × PauliScalar params,
      ‖applyOperatorToState
        (setting.place second ((points.Q second.side (projX (point sample))
          (projZ (point sample))).effect answer) -
          setting.place second
            ((setting.pointMeasExp second.side .Z (projZ (point sample))).effect answer.2 *
              (setting.pointMeasExp second.side .X (projX (point sample))).effect answer.1))
        setting.psiHat‖ ^ 2) ≤ _
    rw [show law = Distribution.prod sublines.D
      (uniformDistribution (DirectScalarQ params.extendedDirectLd)) from rfl, avgOver_prod]
    dsimp only [point]
    rw [SubLineWitness.avgOver_projX_projZ params sublines
      (fun coordinates => ∑ answer : PauliScalar params × PauliScalar params,
        ‖applyOperatorToState
          (setting.place second ((points.Q second.side coordinates.1 coordinates.2).effect answer) -
            setting.place second
              ((setting.pointMeasExp second.side .Z coordinates.2).effect answer.2 *
                (setting.pointMeasExp second.side .X coordinates.1).effect answer.1))
          setting.psiHat‖ ^ 2)]
    exact points.orderedZX_dist_le second
  have hgap := abs_overlap_gap_le_sqrt_of_opFamilyDistSq law lineMeasurement joint ordered
    setting.psiHat hprob setting.psiHat_norm (4 * pointError) hdist
  have hregroup (right : (SubLineTriple params × DirectScalarQ params.extendedDirectLd) →
      Option (PauliScalar params) × Option (PauliScalar params) →
        Op (setting.ExpandedLocalSpace second.side)) :
      avgOver law (fun sample => ∑ answer, stateQForm setting.psiHat
        ((lineMeasurement sample).effect answer * setting.place second (right sample answer))) =
      avgOver sublines.D (fun sample =>
        avgOver (uniformDistribution (DirectScalarQ params.extendedDirectLd)) (fun parameter =>
          ∑ pair, stateQForm setting.psiHat
            (setting.place first ((lines.T first.side sample.2.1 sample.2.2).effect pair) *
              setting.place second (right (sample, parameter)
                (evalOpt sample.2.1 (projX (point (sample, parameter))) pair.1,
                  evalOpt sample.2.2 (projZ (point (sample, parameter))) pair.2))))) := by
    change avgOver (Distribution.prod sublines.D
      (uniformDistribution (DirectScalarQ params.extendedDirectLd))) _ = _
    rw [avgOver_prod]
    apply avgOver_congr
    intro sample
    apply avgOver_congr
    intro parameter
    exact placed_overlap_postprocess setting first second _ _ _
  dsimp only [joint, ordered] at hgap
  rw [hregroup, hregroup] at hgap
  exact hgap


end

end MIPStarRE.QPBT
