import MIPStarRE.QPBT.Combining.Lines.Conditioning
import MIPStarRE.QPBT.Combining.ErrorBounds

/-!
# Construction of consistent combined lines

The heterogeneous pasting theorem bounds the actual X-Z-X measurement.
Polynomial absorption produces a line error for each polynomial point family.

## References

Paper `references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:882-963`,
blueprint `lem:qld-xz-lines`. The construction is recovered from commit
`6e8d67ef8ba22de69a0c166adcdf23ba6e7a33aa` for issue #512; the
source and completed-answer distinctions remain as documented in
`docs/paper-gaps/qpbt_combined-lines-error-term.tex`.
-/

namespace MIPStarRE.QPBT

open MIPStarRE.LDT hiding Measurement
open MIPStarRE.Quantum MIPStarRE.QPBT.DistanceCalculus
open scoped BigOperators Matrix MatrixOrder ComplexOrder

noncomputable section

/-- The fourth directed bipartition, with `BB'` first, `AB''` second, and
the unused `A'A''` pair retained on the second side. This is a coordinate
equivalence, not an identification of the two strategy-player spaces. -/
def bbAbBipartition (params : AdmissibleParams) (left right : Type*) :
    SixReg params left right ≃
      (right × PauliRegister params) ×
        ((left × PauliRegister params) × (PauliRegister params × PauliRegister params)) where
  toFun indices := ((indices.2.1, indices.2.2.1),
    ((indices.1.1, indices.2.2.2), (indices.1.2.1, indices.1.2.2)))
  invFun indices := ((indices.2.1.1, (indices.2.2.1, indices.2.2.2)),
    (indices.1.1, (indices.1.2, indices.2.1.2)))
  left_inv indices := by cases indices; rfl
  right_inv indices := by cases indices; rfl

/-- Coordinates of the `BB' | AB''(A'A'')` bipartition. -/
@[simp] theorem bbAbBipartition_apply (params : AdmissibleParams) (left right : Type*)
    (indices : SixReg params left right) :
    bbAbBipartition params left right indices =
      ((indices.2.1, indices.2.2.1),
        ((indices.1.1, indices.2.2.2), (indices.1.2.1, indices.1.2.2))) := rfl

set_option synthInstance.maxSize 400 in
/-- Every directed opposite placement has an actual heterogeneous
bipartition. The unused EPR pair is included on the right. This discharges the
register identities needed for the application of pasting in all symmetric
equivalents of `lem:qld-xz-lines`, paper
`14_analysis_of_the_pauli_basis_test.tex:959-963`. -/
theorem ProjectiveSetting.exists_opposite_bipartition {params : AdmissibleParams}
    {error : ℝ} (setting : ProjectiveSetting params error)
    (first second : Placement) (hopposite : first.IsOpposite second) :
    ∃ equivalence : SixReg params setting.toStrategy.ιA setting.toStrategy.ιB ≃
        setting.ExpandedLocalSpace first.side ×
          (setting.ExpandedLocalSpace second.side ×
            (PauliRegister params × PauliRegister params)),
      (∀ operator : Op (setting.ExpandedLocalSpace first.side),
        reindexOp equivalence (heteroKron operator 1) = setting.place first operator) ∧
      (∀ operator : Op (setting.ExpandedLocalSpace second.side),
        reindexOp equivalence (heteroKron 1 (heteroKron operator
          (1 : Op (PauliRegister params × PauliRegister params)))) =
          setting.place second operator) := by
  classical
  cases first <;> cases second <;> try exact False.elim hopposite
  · exact ⟨aaBaBipartition params _ _, setting.reindexOp_aaBaBipartition_left,
      setting.reindexOp_aaBaBipartition_right⟩
  · exact ⟨baAaBipartition params _ _, setting.reindexOp_baAaBipartition_left,
      setting.reindexOp_baAaBipartition_right⟩
  · refine ⟨bbAbBipartition params _ _, ?_, ?_⟩
    · intro operator
      ext row column
      change operator (row.2.1, row.2.2.1) (column.2.1, column.2.2.1) *
        (1 : Op ((setting.toStrategy.ιA × PauliRegister params) ×
          (PauliRegister params × PauliRegister params)))
          ((row.1.1, row.2.2.2), row.1.2) ((column.1.1, column.2.2.2), column.1.2) = _
      simp only [ProjectiveSetting.place, Matrix.one_apply, Prod.ext_iff]
      split_ifs <;> simp_all
    · intro operator
      ext row column
      change (1 : Op (setting.toStrategy.ιB × PauliRegister params))
        (row.2.1, row.2.2.1) (column.2.1, column.2.2.1) *
          (operator (row.1.1, row.2.2.2) (column.1.1, column.2.2.2) *
            (1 : Op (PauliRegister params × PauliRegister params)) row.1.2 column.1.2) = _
      simp only [ProjectiveSetting.place, Matrix.one_apply, Prod.ext_iff]
      split_ifs <;> simp_all
  · exact ⟨abBbBipartition params _ _, setting.reindexOp_abBbBipartition_left,
      setting.reindexOp_abBbBipartition_right⟩

set_option synthInstance.maxSize 400 in
open DistanceCalculus in
/-- Coordinate transport of arbitrary placed operator families through a
specified opposite bipartition. The two identities are representation data,
constructed for every opposite pair by `exists_opposite_bipartition`; no
mathematical approximation or extra assumption on the strategy is introduced. -/
theorem ProjectiveSetting.consistencyDefect_bipartition {params : AdmissibleParams}
    {error : ℝ} (setting : ProjectiveSetting params error) (first second : Placement)
    (equivalence : SixReg params setting.toStrategy.ιA setting.toStrategy.ιB ≃
      setting.ExpandedLocalSpace first.side ×
        (setting.ExpandedLocalSpace second.side × (PauliRegister params × PauliRegister params)))
    (hfirst : ∀ operator : Op (setting.ExpandedLocalSpace first.side),
      reindexOp equivalence (heteroKron operator 1) = setting.place first operator)
    (hsecond : ∀ operator : Op (setting.ExpandedLocalSpace second.side),
      reindexOp equivalence (heteroKron 1 (heteroKron operator
        (1 : Op (PauliRegister params × PauliRegister params)))) =
        setting.place second operator)
    {question answer : Type*} [Fintype question] [DecidableEq question]
    [Fintype answer] [DecidableEq answer] (law : Distribution question)
    (firstFamily : question → answer → Op (setting.ExpandedLocalSpace first.side))
    (secondFamily : question → answer → Op (setting.ExpandedLocalSpace second.side)) :
    consistencyDefect law (fun query output => heteroKron (firstFamily query output) 1)
      (fun query output => heteroKron 1 (heteroKron (secondFamily query output)
        (1 : Op (PauliRegister params × PauliRegister params))))
      (reindexState equivalence setting.psiHat) =
    consistencyDefect law (fun query output => setting.place first (firstFamily query output))
      (fun query output => setting.place second (secondFamily query output)) setting.psiHat := by
  unfold consistencyDefect
  congr 1
  funext query
  apply Finset.sum_congr rfl
  intro output _
  apply Finset.sum_congr rfl
  intro other _
  split_ifs
  · rfl
  · rw [consistency_term_eq_stateQForm, consistency_term_eq_stateQForm,
      WinImplications.stateQForm_reindexState, WinImplications.reindexOp_mul,
      hfirst, hsecond]

/-- An unused tensor factor commutes with both the ordered sandwich and its
evaluation. This identity keeps the unused EPR pair when applying the
heterogeneous pasting theorem to the expanded state. -/
theorem evaluated_pastedMeasurement_heteroKron_one
    {firstAnswer secondAnswer result carrier unused : Type*}
    [Fintype firstAnswer] [Fintype secondAnswer] [DecidableEq result]
    [Fintype carrier] [DecidableEq carrier] [Fintype unused] [DecidableEq unused]
    (first : firstAnswer → Op carrier) (second : secondAnswer → Op carrier)
    (evaluate : firstAnswer → secondAnswer → result) (output : result) :
    (∑ firstAnswer, ∑ secondAnswer, if evaluate firstAnswer secondAnswer = output then
      pastedMeasurement (fun answer => heteroKron (first answer) (1 : Op unused))
        (fun answer => heteroKron (second answer) (1 : Op unused)) firstAnswer secondAnswer
      else 0) =
    heteroKron (∑ firstAnswer, ∑ secondAnswer,
      if evaluate firstAnswer secondAnswer = output then
        pastedMeasurement first second firstAnswer secondAnswer else 0) (1 : Op unused) := by
  simp only [pastedMeasurement, heteroKron_mul, mul_one]
  ext row column
  simp [heteroKron, Matrix.kronecker, Matrix.sum_apply, Matrix.ite_apply,
    Finset.sum_mul, ite_mul]

/-- Reversing a paired postprocessing reverses the effect's answer index.
This formalization identity is valid without an injectivity assumption on the
evaluation functions, including completed evaluation at a degenerate line. -/
theorem postprocess_pair_swap_effect {answer first second carrier : Type*}
    [Fintype answer] [DecidableEq answer] [Fintype first] [DecidableEq first]
    [Fintype second] [DecidableEq second] [Fintype carrier] [DecidableEq carrier]
    (measurement : Quantum.Measurement answer carrier) (evaluate : answer → first × second)
    (output : second × first) :
    (measurement.postprocess (fun answer => (evaluate answer).swap)).effect output =
      (measurement.postprocess evaluate).effect output.swap := by
  simp only [Quantum.Measurement.postprocess_effect]
  congr 1
  ext answer
  simp [Prod.ext_iff, and_comm]

/-- Evaluating the actual X-outer paired-line POVM in Z-then-X answer order
gives precisely the evaluated sandwich in the one-sided pasting conclusion.
This is an identity for all descriptors and points, not only on the support
of the conditioned law. Source: `eq:qld-4-13-1`, paper
`14_analysis_of_the_pauli_basis_test.tex:950-963`. -/
theorem ProjectiveSetting.combinedLineMeasurement_evaluated_eq_pasted
    {params : AdmissibleParams} {error : ℝ} (setting : ProjectiveSetting params error)
    (side : PlayerSide) (lineX lineZ : LineDesc params.toLdParams)
    (pointX pointZ : Fin params.m → PauliScalar params)
    (output : Option (PauliScalar params) × Option (PauliScalar params)) :
    ((setting.combinedLineMeasurement side lineX lineZ).postprocess
      (fun polys => (evalOpt lineZ pointZ polys.2, evalOpt lineX pointX polys.1))).effect output =
    ∑ polyZ, ∑ polyX,
      if (evalOpt lineZ pointZ polyZ, evalOpt lineX pointX polyX) = output then
        pastedMeasurement (setting.lineMeasExp side .Z lineZ).effect
          (setting.lineMeasExp side .X lineX).effect polyZ polyX else 0 := by
  classical
  rw [Quantum.Measurement.postprocess_effect, Finset.sum_filter, Fintype.sum_prod_type]
  simp_rw [setting.combinedLineMeasurement_effect_eq_pastedMeasurement]
  exact Finset.sum_comm

set_option synthInstance.maxSize 400 in
set_option maxHeartbeats 800000 in
/-- Applying heterogeneous one-sided pasting to the actual completed point
and line families bounds their conditional defect. Both supplied point
families and both marginal errors are retained. Answers are ordered Z then X,
as required by the X-outer sandwich. Source: `eq:qld-4-13-1`, paper
`14_analysis_of_the_pauli_basis_test.tex:950-963`; the proof-only conditioning
and point-error dependence are explained in
`docs/paper-gaps/qpbt_combined-lines-error-term.tex`. -/
theorem exists_combinedLine_conditioned_defect_le :
    ∃ constant : ℝ, 1 ≤ constant ∧
      ∃ pastingError : ℝ → ℝ → ℝ, IsPolyErr₂ pastingError ∧
        ∀ (params : AdmissibleParams) (error pointError : ℝ)
          (setting : ProjectiveSetting params error)
          (points : CombinedPointsWitness setting pointError)
          (first second : Placement), first.IsOpposite second →
          consistencyDefect (nondegenerateLinePastingDist params.toLdParams)
            (fun query output => setting.place first
              (((points.Q first.side query.2.2 query.1.2.2).postprocess
                (fun pair => (some pair.2, some pair.1))).effect output))
            (fun query output => setting.place second
              (((setting.combinedLineMeasurement second.side query.1.1.1 query.1.1.2).postprocess
                (fun polys => (evalOpt query.1.1.2 query.1.2.2 polys.2,
                  evalOpt query.1.1.1 query.2.2 polys.1))).effect output)) setting.psiHat ≤
            pastingError ((params.m * params.d : ℕ) /
              (Fintype.card (ScalarQ params.toLdParams) : ℝ))
              ((8 * pointError + constant * (error + deltaLine error)) /
                nondegenerateLinePastingMass params.toLdParams) := by
  classical
  obtain ⟨constant, hconstant, hmarginals⟩ :=
    exists_combinedPoints_conditioned_line_marginal_defect_le
  obtain ⟨pastingError, hpoly, hpasting⟩ := exists_pasting_error_heterogeneous
  refine ⟨constant, hconstant, pastingError, hpoly, ?_⟩
  intro params error pointError setting points first second hopposite
  obtain ⟨equivalence, hfirst, hsecond⟩ :=
    setting.exists_opposite_bipartition first second hopposite
  have hpoint : 0 ≤ pointError :=
    (DistanceCalculus.opFamilyDistSq_nonneg _ _ _ _).trans
      (points.self_consistent first second hopposite)
  have hmass := (prod_linePointDist_nondegenerate_mass_pos params.toLdParams).le
  have hextra : 0 ≤ constant * (error + deltaLine error) :=
    mul_nonneg (by linarith) (add_nonneg setting.eps_nonneg (Real.sqrt_nonneg _))
  have herror : 0 ≤ (8 * pointError + constant * (error + deltaLine error)) /
      nondegenerateLinePastingMass params.toLdParams :=
    div_nonneg (by linarith) hmass
  have hbound := hpasting (nondegenerateLinePastingDist params.toLdParams)
    (fun (poly : DegPoly params.toLdParams (params.m * params.d)) sample =>
      evalOpt sample.1 sample.2 poly)
    (fun (poly : DegPoly params.toLdParams (params.m * params.d)) sample =>
      evalOpt sample.1 sample.2 poly)
    (fun pair => DistanceCalculus.leftPlacedMeasurement
      (ιB := PauliRegister params × PauliRegister params)
      (setting.lineMeasExp second.side .Z pair.2))
    (fun pair => DistanceCalculus.leftPlacedMeasurement
      (ιB := PauliRegister params × PauliRegister params)
      (setting.lineMeasExp second.side .X pair.1))
    (fun query => (points.Q first.side query.2.2 query.1.2.2).postprocess
      (fun pair => (some pair.2, some pair.1)))
    (reindexState equivalence setting.psiHat)
    ((params.m * params.d : ℕ) / (Fintype.card (ScalarQ params.toLdParams) : ℝ))
    ((8 * pointError + constant * (error + deltaLine error)) /
      nondegenerateLinePastingMass params.toLdParams)
    (nondegenerateLinePastingDist_isProbability params.toLdParams)
    (by rw [reindexState_norm_eq, setting.psiHat_norm]) (by positivity) herror
    (fun pair => MIPStarRE.QPBT.Measurement.isProjective_leftPlacement _
      (setting.lineMeasExp_isProjective second.side .X pair.1))
    (fun query => SandwichProduct.postprocess_isProjective _ (points.projective _ _ _) _)
    (nondegenerateLinePastingDist_collision_bound params (params.m * params.d))
  simp_rw [leftPlacedMeasurement_postprocess_effect] at hbound
  simp only [DistanceCalculus.leftPlacedMeasurement, Quantum.Measurement.ofSumEqOne] at hbound
  simp_rw [evaluated_pastedMeasurement_heteroKron_one,
    setting.consistencyDefect_bipartition first second equivalence hfirst hsecond] at hbound
  have hmarginal := hmarginals params error pointError setting points first second hopposite
  unfold consistencyDefect nondegenerateLinePastingDist at hbound hmarginal ⊢
  simp only [Distribution.avgOver_map, ProjectiveSetting.lineEvalMeasExp]
    at hbound hmarginal ⊢
  have hresult := hbound hmarginal.1 hmarginal.2
  simp_rw [setting.combinedLineMeasurement_evaluated_eq_pasted]
  convert hresult using 1
  clear hpasting hmarginals hbound hmarginal hresult
  apply avgOver_congr
  intro sample
  apply Finset.sum_congr rfl
  intro output _
  apply Finset.sum_congr rfl
  intro other _
  by_cases hsame : output = other
  · subst other
    simp
  · have hsame' : ¬ @Eq
        (Option (ScalarQ params.toLdParams) × Option (ScalarQ params.toLdParams))
        output other := hsame
    simp only [if_neg hsame, if_neg hsame']
    congr 1

set_option synthInstance.maxSize 400 in
set_option maxHeartbeats 800000 in
/-- The actual X-outer line POVM and the supplied points satisfy the restored
source-law bound. Only zero X directions are discarded during the proof;
their contribution is restored as `1/(2q)`, and the retained mass multiplies
the pasting error. Source: `lem:qld-xz-lines`, paper
`14_analysis_of_the_pauli_basis_test.tex:950-963`; see
`docs/paper-gaps/qpbt_combined-lines-error-term.tex`. -/
theorem exists_combinedLine_restored_defect_le :
    ∃ constant : ℝ, 1 ≤ constant ∧
      ∃ pastingError : ℝ → ℝ → ℝ, IsPolyErr₂ pastingError ∧
        ∀ (params : AdmissibleParams) (error pointError : ℝ)
          (setting : ProjectiveSetting params error)
          (points : CombinedPointsWitness setting pointError)
          (first second : Placement), first.IsOpposite second →
          consistencyDefect (Distribution.prod (linePointDist params.toLdParams)
            (linePointDist params.toLdParams))
            (fun sample output => setting.place first
              (((points.Q first.side sample.1.2 sample.2.2).postprocess
                (fun pair => (some pair.1, some pair.2))).effect output))
            (fun sample output => setting.place second
              (((setting.combinedLineMeasurement second.side sample.1.1 sample.2.1).postprocess
                (fun polys => (evalOpt sample.1.1 sample.1.2 polys.1,
                  evalOpt sample.2.1 sample.2.2 polys.2))).effect output)) setting.psiHat ≤
            nondegenerateLinePastingMass params.toLdParams *
              pastingError ((params.m * params.d : ℕ) /
                (Fintype.card (ScalarQ params.toLdParams) : ℝ))
                ((8 * pointError + constant * (error + deltaLine error)) /
                  nondegenerateLinePastingMass params.toLdParams) +
              1 / (2 * Fintype.card (ScalarQ params.toLdParams)) := by
  classical
  obtain ⟨constant, hconstant, pastingError, hpoly, hconditional⟩ :=
    exists_combinedLine_conditioned_defect_le
  refine ⟨constant, hconstant, pastingError, hpoly, ?_⟩
  intro params error pointError setting points first second hopposite
  have hbound := hconditional params error pointError setting points first second hopposite
  have hswapPoints (side : PlayerSide) (pointX pointZ : Fin params.m → PauliScalar params)
      (output : Option (PauliScalar params) × Option (PauliScalar params)) :
      ((points.Q side pointX pointZ).postprocess
        (fun pair => (some pair.2, some pair.1))).effect output =
      ((points.Q side pointX pointZ).postprocess
        (fun pair => (some pair.1, some pair.2))).effect output.swap :=
    postprocess_pair_swap_effect (points.Q side pointX pointZ)
      (fun pair : PauliScalar params × PauliScalar params => (some pair.1, some pair.2)) output
  have hswapLines (side : PlayerSide) (lineX lineZ : LineDesc params.toLdParams)
      (pointX pointZ : Fin params.m → PauliScalar params)
      (output : Option (PauliScalar params) × Option (PauliScalar params)) :
      ((setting.combinedLineMeasurement side lineX lineZ).postprocess
        (fun polys => (evalOpt lineZ pointZ polys.2, evalOpt lineX pointX polys.1))).effect
          output =
      ((setting.combinedLineMeasurement side lineX lineZ).postprocess
        (fun polys => (evalOpt lineX pointX polys.1, evalOpt lineZ pointZ polys.2))).effect
          output.swap :=
    postprocess_pair_swap_effect (setting.combinedLineMeasurement side lineX lineZ)
      (fun polys => (evalOpt lineX pointX polys.1, evalOpt lineZ pointZ polys.2)) output
  simp_rw [hswapPoints, hswapLines] at hbound
  have hswap := consistencyDefect_outcome_equiv
    (nondegenerateLinePastingDist params.toLdParams)
    (Equiv.prodComm (Option (PauliScalar params)) (Option (PauliScalar params)))
    (fun query output => setting.place first
      (((points.Q first.side query.2.2 query.1.2.2).postprocess
        (fun pair => (some pair.1, some pair.2))).effect output))
    (fun query output => setting.place second
      (((setting.combinedLineMeasurement second.side query.1.1.1 query.1.1.2).postprocess
        (fun polys => (evalOpt query.1.1.1 query.2.2 polys.1,
          evalOpt query.1.1.2 query.1.2.2 polys.2))).effect output)) setting.psiHat
  have hnatural := hswap.symm.trans_le hbound
  refine (setting.combinedLineMeasurement_consistency_le_conditioned
    points first second hopposite).trans ?_
  unfold consistencyDefect nondegenerateLinePastingDist at hnatural ⊢
  simp only [Distribution.avgOver_map] at hnatural ⊢
  have hmass : 0 ≤ nondegenerateLinePastingMass params.toLdParams :=
    (prod_linePointDist_nondegenerate_mass_pos params.toLdParams).le
  exact add_le_add (mul_le_mul_of_nonneg_left hnatural hmass) le_rfl

/-- The retained product-law mass lies between one half and one. The sharper
single-line lower bound is three quarters. This proof-only estimate is used in
the quantitative specialization of `lem:qld-xz-lines`, paper lines 950--963. -/
theorem nondegenerateLinePastingMass_bounds (params : LdParams) :
    1 / 2 ≤ nondegenerateLinePastingMass params ∧
      nondegenerateLinePastingMass params ≤ 1 := by
  classical
  have hmass : nondegenerateLinePastingMass params =
      ∑ sample ∈ (linePointDist params).support.filter
        (fun sample => sample.1.direction ≠ 0), (linePointDist params).weight sample := by
    unfold nondegenerateLinePastingMass
    rw [Distribution.sum_filter_weight_eq_avgOver, avgOver_prod]
    change avgOver (linePointDist params) (fun sample => avgOver (linePointDist params)
      (fun _ => if sample.1.direction ≠ 0 then 1 else 0)) = _
    simp_rw [avgOver_const_of_isProbability _ (linePointDist_isProbability params)]
    rw [Distribution.sum_filter_weight_eq_avgOver]
  rw [hmass]
  refine ⟨(by norm_num : (1 / 2 : ℝ) ≤ 3 / 4).trans
    (linePointDist_nondegenerate_mass_ge params), ?_⟩
  rw [Distribution.sum_filter_weight_eq_avgOver]
  calc
    _ ≤ avgOver (linePointDist params) (fun _ => 1) :=
      avgOver_mono _ _ _ fun _ => by split_ifs <;> norm_num
    _ = 1 := avgOver_const_of_isProbability _ (linePointDist_isProbability params) 1

/-- Consistency is symmetric for measurements on opposite registers. The
operator commutation, rather than symmetry of the state or equality of local
dimensions, justifies exchanging the placements in `lem:qld-xz-lines`. -/
theorem consistencyDefect_opposite_symm {params : AdmissibleParams} {error : ℝ}
    {Question Outcome : Type*} [Fintype Question] [DecidableEq Question]
    [Fintype Outcome] [DecidableEq Outcome]
    (setting : ProjectiveSetting params error) (first second : Placement)
    (hopposite : first.IsOpposite second) (distribution : Distribution Question)
    (left : Question → Quantum.Measurement Outcome (setting.ExpandedLocalSpace first.side))
    (right : Question → Quantum.Measurement Outcome (setting.ExpandedLocalSpace second.side)) :
    consistencyDefect distribution
      (fun question answer => setting.place first ((left question).effect answer))
      (fun question answer => setting.place second ((right question).effect answer))
      setting.psiHat =
    consistencyDefect distribution
      (fun question answer => setting.place second ((right question).effect answer))
      (fun question answer => setting.place first ((left question).effect answer))
      setting.psiHat := by
  unfold consistencyDefect
  congr 1
  funext question
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro answer _
  apply Finset.sum_congr rfl
  intro other _
  rw [setting.place_comm first second hopposite]
  simp only [eq_comm]

/-- Lean-only consistency theorem for the particular X-Z-X measurement
constructed in the proof of `lem:qld-xz-lines`, paper
`14_analysis_of_the_pauli_basis_test.tex:942-961`.

The point family is supplied with its polynomial error bound. The line error
may depend on this function, as in `exists_combinedLinesWitness_ofPointsWitness`.
The conclusion concerns `combinedLineMeasurement` itself, so subsequent uses of
Claim 17-2 retain the source construction.

The point-to-line comparisons and pasting argument at paper lines 900--961
prove this estimate. Conditioning excludes only zero X directions; their
probability is bounded and restored in the original law. This construction
was recovered for issue #512 from the saved proof of issue #118. See
`docs/paper-gaps/qpbt_subline-claims-line-marginal.tex`; no equality or marginal
assumption is added to a paper-facing theorem. -/
theorem combined_line_measurement_consistency (deltaQ : ℝ → ℝ)
    (hdeltaQ : IsPolyErr deltaQ) :
    ∃ deltaP : ℝ → ℝ → ℝ, IsPolyErr₂ deltaP ∧
      ∀ (P : AdmissibleParams) (ε : ℝ) (S : ProjectiveSetting P ε)
        (points : CombinedPointsWitness S (deltaQ ε))
        (p1 p2 : Placement), p1.IsOpposite p2 →
        consistencyDefect
          (Distribution.prod (linePointDist P.toLdParams)
            (linePointDist P.toLdParams))
          (fun sample answer => S.place p1
            (((S.combinedLineMeasurement p1.side sample.1.1 sample.2.1).postprocess
              fun fs => (evalOpt sample.1.1 sample.1.2 fs.1,
                evalOpt sample.2.1 sample.2.2 fs.2)).effect answer))
          (fun sample answer => S.place p2
            (((points.Q p2.side sample.1.2 sample.2.2).postprocess fun ab =>
              (some ab.1, some ab.2)).effect answer))
          S.psiHat ≤ deltaP ε (((P.m * P.d : ℕ) : ℝ) / (P.q : ℝ)) := by
  classical
  obtain ⟨constant, hconstant, pastingError, hpasting, hrestored⟩ :=
    exists_combinedLine_restored_defect_le
  obtain ⟨lineError, hlineError, hscalar⟩ :=
    exists_conditioned_polynomial_bound deltaQ hdeltaQ constant hconstant pastingError hpasting
  refine ⟨lineError, hlineError, ?_⟩
  intro params error setting points first second hopposite
  have hreverse : second.IsOpposite first := by
    cases first <;> cases second <;> trivial
  rw [consistencyDefect_opposite_symm setting first second hopposite]
  have hbound := hrestored params error (deltaQ error) setting points second first hreverse
  have hcard : Fintype.card (ScalarQ params.toLdParams) = params.q :=
    @FieldModel.card params.q params.model.toFieldModel
  rw [hcard] at hbound
  have hq : (0 : ℝ) < params.q := by
    rw [← hcard]
    exact_mod_cast Fintype.card_pos (α := ScalarQ params.toLdParams)
  have hmd : (1 : ℝ) ≤ (params.m * params.d : ℕ) := by
    exact_mod_cast (show 1 ≤ params.m * params.d by
      simpa using Nat.mul_le_mul params.one_le_m params.hd)
  have hdiscard : 1 / (2 * (params.q : ℝ)) ≤
      (params.m * params.d : ℕ) / (params.q : ℝ) := by
    calc
      _ ≤ 1 / (params.q : ℝ) := one_div_le_one_div_of_le hq (by linarith)
      _ ≤ _ := div_le_div_of_nonneg_right hmd hq.le
  have hunit : consistencyDefect
      (Distribution.prod (linePointDist params.toLdParams) (linePointDist params.toLdParams))
      (fun sample answer => setting.place second
        (((points.Q second.side sample.1.2 sample.2.2).postprocess
          (fun pair => (some pair.1, some pair.2))).effect answer))
      (fun sample answer => setting.place first
        (((setting.combinedLineMeasurement first.side sample.1.1 sample.2.1).postprocess
          (fun polys => (evalOpt sample.1.1 sample.1.2 polys.1,
            evalOpt sample.2.1 sample.2.2 polys.2))).effect answer)) setting.psiHat ≤ 1 := by
    unfold consistencyDefect
    calc
      _ ≤ avgOver (Distribution.prod (linePointDist params.toLdParams)
          (linePointDist params.toLdParams)) (fun _ => 1) :=
        avgOver_mono _ _ _ fun sample =>
          consistencyDefect_integrand_le_one setting second first hreverse _ _
      _ = 1 := avgOver_const_of_isProbability _
        (Distribution.prod_isProbability _ _ (linePointDist_isProbability params.toLdParams)
          (linePointDist_isProbability params.toLdParams)) 1
  exact (le_min hunit (hbound.trans (add_le_add le_rfl hdiscard))).trans
    (hscalar error _ _ setting.eps_nonneg (by positivity)
      (nondegenerateLinePastingMass_bounds params.toLdParams).1
      (nondegenerateLinePastingMass_bounds params.toLdParams).2)


end

end MIPStarRE.QPBT
