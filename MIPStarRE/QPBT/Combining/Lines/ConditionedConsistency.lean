import MIPStarRE.QPBT.Combining.Lines.CombinedMeasurement
import MIPStarRE.QPBT.Combining.Lines.ConditionedPointLineMarginalDefect
import MIPStarRE.QPBT.Combining.Lines.ConditionalCollision
import MIPStarRE.QPBT.Combining.Lines.PastingPlacement

/-!
# Consistency of the conditioned combined line measurement

Apply heterogeneous pasting to the two point-to-line marginal comparisons.
The answer order is Z then X so that the pasted measurement is the X-Z-X
sandwich. No conditioning changes the measurement itself.

## References

The pasting step is `eq:qld-4-13-1`,
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:950-963`.
The proof from commit `f6a340c8` uses the current two-marginal pasting API.
-/

namespace MIPStarRE.QPBT

open MIPStarRE.LDT MIPStarRE.Quantum
open scoped Matrix MatrixOrder

noncomputable section

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
-- Reindexing the pasted families elaborates several nested finite sums.
/-- Applying heterogeneous one-sided pasting to the actual completed point
and line families bounds their conditional defect. The supplied point
family and both marginal errors are retained. Answers are ordered Z then X,
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

end

end MIPStarRE.QPBT
