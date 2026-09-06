import MIPStarRE.QPBT.Combining.Points
import MIPStarRE.QPBT.Games.Sandwich.Support

/-!
# A direct-game strategy from supplied extended-line measurements

The input is an existing `ExtendedLinesWitness`, not an existence assertion
for that witness. Axis answers are restricted using its degree-support field;
diagonal answers are extended by zero coefficients. Point answers are the
scalar coarse-grainings of the supplied joint point measurements.

These are construction lemmas for the first paragraph of the proof of
`lem:qld-4-7`, not a proof of that lemma or of the existence of its input.
The remaining game-value estimates and the dependency on issue #119 are
recorded in `audits/2026-09-06_extended-line-game-244.md`.

## References

- `references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1020-1034`
- `references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1267-1402`
- Blueprint `lem:qld-4-7` and `rem:qld-4-7-divisibility`.
- `docs/paper-gaps/qpbt_ld-dimension-divisibility.tex`
-/

open scoped BigOperators

namespace MIPStarRE.QPBT

open MIPStarRE.LDT hiding Measurement
open MIPStarRE.Quantum

noncomputable section

namespace ExtendedLineGame

/-- Successful completed evaluation means evaluation at every parameter
presenting the point, including when the line direction is zero. -/
theorem directEvalOpt_eq_some_iff {params : DirectLdParams} {degree : ℕ}
    (line : DirectLineDesc params) (point : Fin params.m → DirectScalarQ params)
    (coeffs : DirectDegPoly params degree) (answer : DirectScalarQ params) :
    directEvalOpt line point coeffs = some answer ↔
      DirectEvaluatesTo line coeffs point answer := by
  classical
  unfold directEvalOpt
  split_ifs with hexists
  · simp only [Option.some.injEq]
    constructor
    · intro heq
      simpa [heq] using Classical.choose_spec hexists
    · intro heval
      obtain ⟨parameter, hparameter⟩ := heval.1
      exact ((Classical.choose_spec hexists).2 parameter hparameter).symm.trans
        (heval.2 parameter hparameter)
  · simp only [false_iff]
    exact fun heval => hexists ⟨answer, heval⟩

/-- The axis answer length fits inside the extended-line coefficient list. -/
theorem axis_degree_le (params : AdmissibleParams) :
    params.d + 1 ≤ params.m * params.d + 2 := by
  have hmul := Nat.mul_le_mul_right params.d params.one_le_m
  omega

/-- Restrict an extended-line answer to the axis degree bound. -/
def axisRead (params : AdmissibleParams)
    (coeffs : DirectDegPoly params.extendedDirectLd (params.m * params.d + 1)) :
    DirectDegPoly params.extendedDirectLd params.d :=
  fun index => coeffs (Fin.castLE (axis_degree_le params) index)

/-- Restriction preserves evaluation when the discarded coefficients vanish. -/
theorem axisRead_eval (params : AdmissibleParams)
    (coeffs : DirectDegPoly params.extendedDirectLd (params.m * params.d + 1))
    (hsupport : ∀ index, params.d < index.val → coeffs index = 0)
    (parameter : DirectScalarQ params.extendedDirectLd) :
      evalCoefficient (axisRead params coeffs) parameter = evalCoefficient coeffs parameter := by
  unfold evalCoefficient axisRead
  refine Fintype.sum_of_injective (Fin.castLE (axis_degree_le params))
    (Fin.castLE_injective _) _ (fun index => coeffs index * parameter ^ index.val)
    ?_ (fun _ => rfl)
  intro index hindex
  have hlarge : params.d < index.val := by
    by_contra hlarge
    exact hindex ⟨⟨index.val, by omega⟩, Fin.ext rfl⟩
  simp [hsupport index hlarge]

/-- The extended-line degree fits the direct game's diagonal answer bound. -/
theorem diagonal_degree_le (params : AdmissibleParams) :
    params.m * params.d + 2 ≤
      params.extendedDirectLd.m * params.extendedDirectLd.d + 1 := by
  change params.m * params.d + 2 ≤ (2 * params.m + 2) * params.d + 1
  have hdegree := params.hd
  nlinarith

/-- Extend a diagonal-line coefficient list by zeros, without changing its polynomial. -/
def diagonalRead (params : AdmissibleParams)
    (coeffs : DirectDegPoly params.extendedDirectLd (params.m * params.d + 1)) :
    DirectDegPoly params.extendedDirectLd
      (params.extendedDirectLd.m * params.extendedDirectLd.d) :=
  fun index => if bound : index.val < params.m * params.d + 2
    then coeffs ⟨index.val, bound⟩ else 0

/-- Extending a diagonal answer by zeros preserves evaluation at every parameter. -/
theorem diagonalRead_eval (params : AdmissibleParams)
    (coeffs : DirectDegPoly params.extendedDirectLd (params.m * params.d + 1))
    (parameter : DirectScalarQ params.extendedDirectLd) :
    evalCoefficient (diagonalRead params coeffs) parameter =
      evalCoefficient coeffs parameter := by
  symm
  apply Fintype.sum_of_injective (Fin.castLE (diagonal_degree_le params))
    (Fin.castLE_injective _) _ _ ?_ ?_
  · intro index hindex
    have hlarge : ¬index.val < params.m * params.d + 2 := by
      intro hsmall
      exact hindex ⟨⟨index.val, hsmall⟩, Fin.ext rfl⟩
    simp [diagonalRead, hlarge]
  · intro index
    simp [diagonalRead, index.isLt]

/-- A scalar answer, transported to the direct field and made a singleton tuple. -/
def pointAnswer (params : AdmissibleParams) (answer : PauliScalar params) :
    DirectLdAnswer params.extendedDirectLd :=
  .pointVals (fun _ => (extendedDirectScalarEquiv params).symm answer)

/-- A singleton axis answer with the game's required degree. -/
def axisAnswer (params : AdmissibleParams)
    (coeffs : DirectDegPoly params.extendedDirectLd (params.m * params.d + 1)) :
    DirectLdAnswer params.extendedDirectLd :=
  .alinePolys (fun _ => axisRead params coeffs)

/-- A singleton diagonal answer with the game's required coefficient length. -/
def diagonalAnswer (params : AdmissibleParams)
    (coeffs : DirectDegPoly params.extendedDirectLd (params.m * params.d + 1)) :
    DirectLdAnswer params.extendedDirectLd :=
  .dlinePolys (fun _ => diagonalRead params coeffs)

/-- Re-reading a canonical axis question preserves its line description. -/
theorem axis_description_canonical (params : DirectLdParams) (sample : DirectLdSpace params) :
    directALineDescOf params (directLdMap params .aline sample) =
      directALineDescOf params sample := by
  simp [directALineDescOf, directLdMap, lineRepMap_apply_self]

/-- Re-reading a canonical diagonal question preserves its line description,
also for zero directions. -/
theorem diagonal_description_canonical (params : DirectLdParams)
    (sample : DirectLdSpace params) :
    directDLineDescOf params (directLdMap params .dline sample) =
      directDLineDescOf params sample := by
  have hprefix : directPrefixProjection sample.index
      (directPrefixProjection sample.index sample.direction) =
        directPrefixProjection sample.index sample.direction := by
    funext index
    by_cases hindex : index.val < sample.index.val <;> simp [directPrefixProjection, hindex]
  simp [directDLineDescOf, directLdMap, hprefix, lineRepMap_apply_self]

/-- On degree-supported outcomes, the axis verifier checks precisely successful
completed evaluation, after the canonical field transport. -/
theorem axisAnswer_win_iff (params : AdmissibleParams)
    (sample : DirectLdSpace params.extendedDirectLd)
    (coeffs : DirectDegPoly params.extendedDirectLd (params.m * params.d + 1))
    (hsupport : ∀ index, params.d < index.val → coeffs index = 0)
    (answer : DirectScalarQ params.extendedDirectLd) :
    directLdWinPredicate params.extendedDirectLd
      (.aline, directLdMap params.extendedDirectLd .aline sample)
      (.point, directLdMap params.extendedDirectLd .point sample)
      (axisAnswer params coeffs) (pointAnswer params ((extendedDirectScalarEquiv params) answer)) =
        true ↔ directEvalOpt (directALineDescOf params.extendedDirectLd sample)
          sample.point coeffs = some answer := by
  rw [directEvalOpt_eq_some_iff]
  simp only [directLdWinPredicate, axisAnswer, pointAnswer, validDirectLdAnswer,
    Bool.and_self, ↓reduceIte, decide_eq_true_eq,
    RingEquiv.symm_apply_apply, directAlinePointCondition]
  change (∀ parameter, sample.point = _ + parameter • _ →
    ∀ _ : Fin 1, evalCoefficient (axisRead params coeffs) parameter = answer) ↔
    (∃ parameter, sample.point = _ + parameter • _) ∧
      ∀ parameter, sample.point = _ + parameter • _ → evalCoefficient coeffs parameter = answer
  simp only [axisRead_eval params coeffs hsupport, forall_const]
  exact (and_iff_right (mem_linePoints_lineRepMap
    (coordinateDirection sample.index) sample.point)).symm

/-- The diagonal verifier checks precisely successful completed evaluation.
No nonzero-direction hypothesis is needed, and `none` is not replaced by zero. -/
theorem diagonalAnswer_win_iff (params : AdmissibleParams)
    (sample : DirectLdSpace params.extendedDirectLd)
    (coeffs : DirectDegPoly params.extendedDirectLd (params.m * params.d + 1))
    (answer : DirectScalarQ params.extendedDirectLd) :
    directLdWinPredicate params.extendedDirectLd
      (.dline, directLdMap params.extendedDirectLd .dline sample)
      (.point, directLdMap params.extendedDirectLd .point sample)
      (diagonalAnswer params coeffs)
      (pointAnswer params ((extendedDirectScalarEquiv params) answer)) = true ↔
        directEvalOpt (directDLineDescOf params.extendedDirectLd sample)
          sample.point coeffs = some answer := by
  rw [directEvalOpt_eq_some_iff]
  simp only [directLdWinPredicate, diagonalAnswer, pointAnswer, validDirectLdAnswer,
    Bool.and_self, ↓reduceIte, decide_eq_true_eq,
    RingEquiv.symm_apply_apply, directDlinePointCondition]
  change (∀ parameter, sample.point = _ + parameter • _ →
    ∀ _ : Fin 1, evalCoefficient (diagonalRead params coeffs) parameter = answer) ↔
    (∃ parameter, sample.point = _ + parameter • _) ∧
      ∀ parameter, sample.point = _ + parameter • _ → evalCoefficient coeffs parameter = answer
  simp only [diagonalRead_eval, forall_const]
  exact (and_iff_right (mem_linePoints_lineRepMap
    (directPrefixProjection sample.index sample.direction) sample.point)).symm

variable {params : AdmissibleParams} {epsilon deltaQ deltaL : ℝ}
variable {setting : ProjectiveSetting params epsilon}
variable {points : CombinedPointsWitness setting deltaQ}

/-- The actual answer measurement at each direct-game question. No strategy
passing premise or producer of the supplied line witness is used. -/
def answerMeasurement (lines : ExtendedLinesWitness setting points deltaL)
    (side : PlayerSide) (question : DirectLdQuestion params.extendedDirectLd) :
    Measurement (DirectLdAnswer params.extendedDirectLd) (setting.ExpandedLocalSpace side) :=
  match question.1 with
  | .point =>
    let point := directPointToPauli params question.2.point
    (points.extendedQ side (projX point) (projZ point)
      (point (alphaVar params.m)) (point (betaVar params.m))).postprocess (pointAnswer params)
  | .aline =>
    (lines.Qline side (directALineDescOf params.extendedDirectLd question.2)).postprocess
      (axisAnswer params)
  | .dline =>
    (lines.Qline side (directDLineDescOf params.extendedDirectLd question.2)).postprocess
      (diagonalAnswer params)

/-- All wrong-tag effects vanish: the measurement construction never uses the
game's wrong-format fallback answers. -/
theorem answerMeasurement_effect_eq_zero
    (lines : ExtendedLinesWitness setting points deltaL) (side : PlayerSide)
    (question : DirectLdQuestion params.extendedDirectLd)
    (answer : DirectLdAnswer params.extendedDirectLd)
    (hanswer : validDirectLdAnswer question.1 answer = false) :
    (answerMeasurement lines side question).effect answer = 0 := by
  classical
  rcases question with ⟨kind, question⟩
  cases kind <;> cases answer <;>
    simp_all [validDirectLdAnswer, answerMeasurement,
      MIPStarRE.Quantum.Measurement.postprocess, MIPStarRE.Quantum.Submeasurement.postprocess,
      pointAnswer, axisAnswer, diagonalAnswer]

/-- The point measurements are projective by coarse-graining the supplied joint
projective measurements. This does not invoke the unfinished `extendedQ_spec`. -/
theorem point_answerMeasurement_isProjective
    (lines : ExtendedLinesWitness setting points deltaL) (side : PlayerSide)
    (question : DirectLdSpace params.extendedDirectLd) :
    MIPStarRE.QPBT.Measurement.IsProjective (answerMeasurement lines side (.point, question)) := by
  apply SandwichProduct.postprocess_isProjective
  apply SandwichProduct.postprocess_isProjective
  exact points.projective _ _ _

/-- Axis truncation preserves evaluation on every nonzero effect, directly by
the degree-support field of the supplied extended-line witness. -/
theorem axisRead_eval_of_effect_ne_zero
    (lines : ExtendedLinesWitness setting points deltaL) (side : PlayerSide)
    (line : DirectLineDesc params.extendedDirectLd) (hline : line.kind = .axis)
    (coeffs : DirectDegPoly params.extendedDirectLd (params.m * params.d + 1))
    (heffect : (lines.Qline side line).effect coeffs ≠ 0)
    (parameter : DirectScalarQ params.extendedDirectLd) :
    evalCoefficient (axisRead params coeffs) parameter = evalCoefficient coeffs parameter := by
  apply axisRead_eval
  by_contra hsupport
  exact heffect (lines.axis_degree side line coeffs hline hsupport)

/-- On a nonzero outcome of the supplied axis measurement, the axis verifier
is exactly the completed-evaluation check. The degree premise of
`axisAnswer_win_iff` is discharged by the witness, not assumed by the caller. -/
theorem axisAnswer_win_iff_of_effect_ne_zero
    (lines : ExtendedLinesWitness setting points deltaL) (side : PlayerSide)
    (sample : DirectLdSpace params.extendedDirectLd)
    (coeffs : DirectDegPoly params.extendedDirectLd (params.m * params.d + 1))
    (heffect : (lines.Qline side
      (directALineDescOf params.extendedDirectLd sample)).effect coeffs ≠ 0)
    (answer : DirectScalarQ params.extendedDirectLd) :
    directLdWinPredicate params.extendedDirectLd
      (.aline, directLdMap params.extendedDirectLd .aline sample)
      (.point, directLdMap params.extendedDirectLd .point sample)
      (axisAnswer params coeffs) (pointAnswer params ((extendedDirectScalarEquiv params) answer)) =
        true ↔ directEvalOpt (directALineDescOf params.extendedDirectLd sample)
          sample.point coeffs = some answer := by
  apply axisAnswer_win_iff
  by_contra hsupport
  exact heffect (lines.axis_degree side _ coeffs rfl hsupport)

/-- The supplied completed line-point defect, with the two register placements
explicit. This still uses the six-register state, not the constructed game's state. -/
def completedLinePointDefect (lines : ExtendedLinesWitness setting points deltaL)
    (linePlacement pointPlacement : Placement)
    (law : Distribution (DirectLineDesc params.extendedDirectLd ×
      (Fin params.extendedDirectLd.m → DirectScalarQ params.extendedDirectLd))) : ℝ :=
  consistencyDefect law
    (fun sample answer => setting.place linePlacement
      (((lines.Qline linePlacement.side sample.1).postprocess
        (fun coeffs => (directEvalOpt sample.1 sample.2 coeffs).map
          (extendedDirectScalarEquiv params))).effect answer))
    (fun sample answer => setting.place pointPlacement
      (((points.Q pointPlacement.side
        (projX (directPointToPauli params sample.2))
        (projZ (directPointToPauli params sample.2))).postprocess fun values =>
          some (directPointToPauli params sample.2 (alphaVar params.m) * values.1 +
            directPointToPauli params sample.2 (betaVar params.m) * values.2)).effect answer))
    setting.psiHat

/-- Exact separation of the witness's equal axis/diagonal mixture. -/
theorem completedLinePointDefect_eq_half_sum
    (lines : ExtendedLinesWitness setting points deltaL)
    (linePlacement pointPlacement : Placement) :
    completedLinePointDefect lines linePlacement pointPlacement
        (directLinePointDist params.extendedDirectLd) =
      (completedLinePointDefect lines linePlacement pointPlacement
          (directALinePointDist params.extendedDirectLd) +
        completedLinePointDefect lines linePlacement pointPlacement
          (directDLinePointDist params.extendedDirectLd)) / 2 := by
  unfold completedLinePointDefect consistencyDefect
  rw [directLinePointDist, WinImplications.avgOver_mix]
  ring

/-- Both oriented sums of axis and diagonal completed defects are bounded by
`2 * deltaL`, using exactly the two consistency fields supplied by `lines`.
Identifying these quantities with game rejection requires the separate
register-correlation transport recorded in the packet audit. -/
theorem completedLinePointDefect_sums_le
    (lines : ExtendedLinesWitness setting points deltaL) :
    (completedLinePointDefect lines .AA' .BA''
        (directALinePointDist params.extendedDirectLd) +
      completedLinePointDefect lines .AA' .BA''
        (directDLinePointDist params.extendedDirectLd) ≤ 2 * deltaL) ∧
    (completedLinePointDefect lines .BB' .AB''
        (directALinePointDist params.extendedDirectLd) +
      completedLinePointDefect lines .BB' .AB''
        (directDLinePointDist params.extendedDirectLd) ≤ 2 * deltaL) := by
  constructor
  · have hbound : completedLinePointDefect lines .AA' .BA''
        (directLinePointDist params.extendedDirectLd) ≤ deltaL := lines.consistent_alice
    rw [completedLinePointDefect_eq_half_sum] at hbound
    linarith
  · have hbound : completedLinePointDefect lines .BB' .AB''
        (directLinePointDist params.extendedDirectLd) ≤ deltaL := lines.consistent_bob
    rw [completedLinePointDefect_eq_half_sum] at hbound
    linarith

/-- The bipartite state on the two expanded local spaces, with one shared EPR
pair. It is not the six-register vector `psiHat` on a smaller index type. -/
def pairState (setting : ProjectiveSetting params epsilon) :
    EuclideanSpace ℂ (setting.ExpandedLocalSpace .alice × setting.ExpandedLocalSpace .bob) :=
  reindexState prodShuffle (vecTensor setting.toStrategy.ψ (eprState (PauliRegister params)))

/-- The two-player state used by the constructed game is normalized. -/
theorem pairState_norm (setting : ProjectiveSetting params epsilon) :
    ‖pairState setting‖ = 1 := by
  change ‖reindexState prodShuffle
    (vecTensor setting.toStrategy.ψ (eprState (PauliRegister params)))‖ = 1
  rw [reindexState_norm_eq, vecTensor_norm_eq, setting.toStrategy.ψ_norm,
    eprState_norm, mul_one]

/-- The concrete direct-game strategy determined by the supplied measurements. -/
def strategy (lines : ExtendedLinesWitness setting points deltaL) :
    Strategy (directLdGame params.extendedDirectLd) where
  ιA := setting.ExpandedLocalSpace .alice
  ιB := setting.ExpandedLocalSpace .bob
  ψ := pairState setting
  ψ_norm := pairState_norm setting
  A := answerMeasurement lines .alice
  B := answerMeasurement lines .bob

/-- A wrong-format answer pair has zero Born weight in the constructed strategy. -/
theorem outcomeWeight_eq_zero_of_invalid
    (lines : ExtendedLinesWitness setting points deltaL)
    (questionA questionB : DirectLdQuestion params.extendedDirectLd)
    (answerA answerB : DirectLdAnswer params.extendedDirectLd)
    (hinvalid : validDirectLdAnswer questionA.1 answerA = false ∨
      validDirectLdAnswer questionB.1 answerB = false) :
    outcomeWeight (strategy lines) questionA questionB answerA answerB = 0 := by
  rcases hinvalid with hinvalid | hinvalid
  · have hzero := answerMeasurement_effect_eq_zero lines .alice questionA answerA hinvalid
    change (inner ℂ (pairState setting) (applyOperatorToState
      (heteroKron ((answerMeasurement lines .alice questionA).effect answerA)
        ((answerMeasurement lines .bob questionB).effect answerB)) (pairState setting))).re = 0
    rw [hzero]
    simp [heteroKron, applyOperatorToState]
  · have hzero := answerMeasurement_effect_eq_zero lines .bob questionB answerB hinvalid
    change (inner ℂ (pairState setting) (applyOperatorToState
      (heteroKron ((answerMeasurement lines .alice questionA).effect answerA)
        ((answerMeasurement lines .bob questionB).effect answerB)) (pairState setting))).re = 0
    rw [hzero]
    simp [heteroKron, applyOperatorToState]

/-- The two mixed line-type branches accept with probability one. Their only
possible rejections are wrong-format answers, which have zero effect. -/
theorem mixed_branch_rejection_eq_zero
    (lines : ExtendedLinesWitness setting points deltaL) (types : LdType × LdType)
    (htypes : types = (.aline, .dline) ∨ types = (.dline, .aline)) :
    directLdBranchRejectionProbability params.extendedDirectLd (strategy lines) types = 0 := by
  unfold directLdBranchRejectionProbability
  conv_rhs => rw [← avgOver_zero (uniformDistribution (DirectLdSpace params.extendedDirectLd))]
  apply avgOver_congr
  intro sample
  apply Finset.sum_eq_zero
  intro answerA _
  apply Finset.sum_eq_zero
  intro answerB _
  by_cases hvalidA : validDirectLdAnswer types.1 answerA = false
  · rw [outcomeWeight_eq_zero_of_invalid lines _ _ _ _ (Or.inl hvalidA)]
    simp
  by_cases hvalidB : validDirectLdAnswer types.2 answerB = false
  · rw [outcomeWeight_eq_zero_of_invalid lines _ _ _ _ (Or.inr hvalidB)]
    simp
  rcases htypes with rfl | rfl <;> cases answerA <;> cases answerB <;>
    simp_all [validDirectLdAnswer, directLdWinPredicate]

/-- Exact accounting of the seven potentially rejecting branches of the
constructed strategy. Same-type line branches are retained: their coefficient
equality checks do not follow merely from the answer tags. -/
theorem strategy_value_eq (lines : ExtendedLinesWitness setting points deltaL) :
    (strategy lines).value = 1 -
      (directLdBranchRejectionProbability params.extendedDirectLd (strategy lines)
          (.point, .point) +
        directLdBranchRejectionProbability params.extendedDirectLd (strategy lines)
          (.point, .aline) +
        directLdBranchRejectionProbability params.extendedDirectLd (strategy lines)
          (.point, .dline) +
        directLdBranchRejectionProbability params.extendedDirectLd (strategy lines)
          (.aline, .point) +
        directLdBranchRejectionProbability params.extendedDirectLd (strategy lines)
          (.aline, .aline) +
        directLdBranchRejectionProbability params.extendedDirectLd (strategy lines)
          (.dline, .point) +
        directLdBranchRejectionProbability params.extendedDirectLd (strategy lines)
          (.dline, .dline)) / 9 := by
  have hvalue := directLdRejectionProbability_eq_one_sub_value
    params.extendedDirectLd (strategy lines)
  rw [directLdRejectionProbability, avgOver_ldType_pair,
    mixed_branch_rejection_eq_zero lines _ (Or.inl rfl),
    mixed_branch_rejection_eq_zero lines _ (Or.inr rfl)] at hvalue
  linarith

/-- Naimark dilation of the constructed strategy with a question-independent
ancilla. It does not assert a game-value lower bound. -/
def projectiveStrategy (lines : ExtendedLinesWitness setting points deltaL) :
    Strategy (directLdGame params.extendedDirectLd) :=
  paddedStrategy (strategy lines) (none : Option (DirectLdAnswer params.extendedDirectLd))
    (none : Option (DirectLdAnswer params.extendedDirectLd))
    (fun question => dilatedMeasurement (default : DirectLdAnswer params.extendedDirectLd)
      ((strategy lines).A question))
    (fun question => dilatedMeasurement (default : DirectLdAnswer params.extendedDirectLd)
      ((strategy lines).B question))

/-- Both measurement families of the constructed Naimark strategy are projective. -/
theorem projectiveStrategy_isProjective
    (lines : ExtendedLinesWitness setting points deltaL) :
    (projectiveStrategy lines).IsProjective :=
  paddedStrategy_isProjective (strategy lines) none none _ _
    (fun question => dilatedMeasurement_isProjective
      (default : DirectLdAnswer params.extendedDirectLd) ((strategy lines).A question))
    (fun question => dilatedMeasurement_isProjective
      (default : DirectLdAnswer params.extendedDirectLd) ((strategy lines).B question))

/-- Exact game-value transport through the explicit Naimark construction. -/
theorem projectiveStrategy_value (lines : ExtendedLinesWitness setting points deltaL) :
    (projectiveStrategy lines).value = (strategy lines).value :=
  paddedStrategy_value (strategy lines) none none _ _
    (fun question answer =>
      dilatedMeasurement_compression (default : DirectLdAnswer params.extendedDirectLd)
        answer ((strategy lines).A question))
    (fun question answer =>
      dilatedMeasurement_compression (default : DirectLdAnswer params.extendedDirectLd)
        answer ((strategy lines).B question))

end ExtendedLineGame

end

end MIPStarRE.QPBT
