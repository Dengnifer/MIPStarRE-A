import MIPStarRE.QPBT.Combining.Lines.ConditionedConsistency
import MIPStarRE.QPBT.Combining.Lines.MixedZeroDirectionMass
import MIPStarRE.QPBT.Combining.Lines.PastingRestoration
import MIPStarRE.QPBT.Combining.ErrorBounds

/-!
# Restoring combined line consistency

The bound for the nondegenerate conditional law transfers to the original
product line-point law. The retained mass multiplies the conditional error;
the discarded zero-direction contribution is at most `1/(2q)`.

## References

This completes the distributional step in `eq:qld-4-13-1`,
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:950-963`.
The measurement and answer-permutation arguments are recovered from
commit `f6a340c8`.
-/

namespace MIPStarRE.QPBT

open MIPStarRE.LDT MIPStarRE.Quantum
open scoped Matrix MatrixOrder

noncomputable section

/-- Restore the unconditioned consistency defect with its retained-mass factor
and additive cost at most `1/(2q)`. This holds for the supplied measurement
families on every directed opposite placement, without a defect hypothesis.
Proof-only support for `lem:qld-xz-lines`, paper lines 950--963. -/
theorem consistencyDefect_le_nondegenerateLinePastingDist_add_mass
    {P : AdmissibleParams} {ε : ℝ}
    {Outcome : Type*} [Fintype Outcome] [DecidableEq Outcome]
    (S : ProjectiveSetting P ε) (p1 p2 : Placement) (hopp : p1.IsOpposite p2)
    (first : ((LineDesc P.toLdParams × (Fin P.m → PauliScalar P)) ×
      (LineDesc P.toLdParams × (Fin P.m → PauliScalar P))) →
      MIPStarRE.Quantum.Measurement Outcome (S.ExpandedLocalSpace p1.side))
    (second : ((LineDesc P.toLdParams × (Fin P.m → PauliScalar P)) ×
      (LineDesc P.toLdParams × (Fin P.m → PauliScalar P))) →
      MIPStarRE.Quantum.Measurement Outcome (S.ExpandedLocalSpace p2.side)) :
    consistencyDefect (Distribution.prod (linePointDist P.toLdParams)
      (linePointDist P.toLdParams))
      (fun sample answer => S.place p1 ((first sample).effect answer))
      (fun sample answer => S.place p2 ((second sample).effect answer)) S.psiHat ≤
    nondegenerateLinePastingMass P.toLdParams *
      consistencyDefect (nondegenerateLinePastingDist P.toLdParams)
        (fun question answer => S.place p1 ((first (question.2, question.1.2)).effect answer))
        (fun question answer => S.place p2 ((second (question.2, question.1.2)).effect answer))
        S.psiHat + 1 / (2 * Fintype.card (ScalarQ P.toLdParams)) := by
  classical
  refine (consistencyDefect_le_nondegenerateLinePastingDist_add_discarded_mass
    S p1 p2 hopp first second).trans (add_le_add le_rfl ?_)
  rw [Distribution.sum_filter_weight_eq_avgOver, avgOver_prod]
  change avgOver (linePointDist P.toLdParams) (fun sample =>
    avgOver (linePointDist P.toLdParams)
      (fun _ => if sample.1.direction = 0 then (1 : ℝ) else 0)) ≤ _
  simp_rw [avgOver_const_of_isProbability _ (linePointDist_isProbability P.toLdParams)]
  exact linePointDist_zero_direction_mass_le P.toLdParams

/-- The actual X-outer line sandwich and the supplied completed points satisfy
the mass-restoration inequality on every directed opposite placement. This is
not the final consistency estimate: its right side still contains the
conditioned defect to be bounded by one-sided pasting. Source:
`lem:qld-xz-lines`, paper `14_analysis_of_the_pauli_basis_test.tex:942-963`;
the conditioning is explained in `docs/paper-gaps/qpbt_combined-lines-error-term.tex`. -/
theorem ProjectiveSetting.combinedLineMeasurement_consistency_le_conditioned
    {P : AdmissibleParams} {ε δQ : ℝ} (S : ProjectiveSetting P ε)
    (points : CombinedPointsWitness S δQ)
    (p1 p2 : Placement) (hopp : p1.IsOpposite p2) :
    consistencyDefect (Distribution.prod (linePointDist P.toLdParams)
      (linePointDist P.toLdParams))
      (fun sample answer => S.place p1
        (((points.Q p1.side sample.1.2 sample.2.2).postprocess
          (fun pair => (some pair.1, some pair.2))).effect answer))
      (fun sample answer => S.place p2
        (((S.combinedLineMeasurement p2.side sample.1.1 sample.2.1).postprocess
          (fun polys => (evalOpt sample.1.1 sample.1.2 polys.1,
            evalOpt sample.2.1 sample.2.2 polys.2))).effect answer)) S.psiHat ≤
    nondegenerateLinePastingMass P.toLdParams *
      consistencyDefect (nondegenerateLinePastingDist P.toLdParams)
        (fun question answer => S.place p1
          (((points.Q p1.side question.2.2 question.1.2.2).postprocess
            (fun pair => (some pair.1, some pair.2))).effect answer))
        (fun question answer => S.place p2
          (((S.combinedLineMeasurement p2.side question.2.1 question.1.2.1).postprocess
            (fun polys => (evalOpt question.2.1 question.2.2 polys.1,
              evalOpt question.1.2.1 question.1.2.2 polys.2))).effect answer)) S.psiHat +
      1 / (2 * Fintype.card (ScalarQ P.toLdParams)) := by
  exact consistencyDefect_le_nondegenerateLinePastingDist_add_mass S p1 p2 hopp
    (fun sample => (points.Q p1.side sample.1.2 sample.2.2).postprocess
      (fun pair => (some pair.1, some pair.2)))
    (fun sample => (S.combinedLineMeasurement p2.side sample.1.1 sample.2.1).postprocess
      (fun polys => (evalOpt sample.1.1 sample.1.2 polys.1,
        evalOpt sample.2.1 sample.2.2 polys.2)))

set_option synthInstance.maxSize 400 in
set_option maxHeartbeats 800000 in
-- Rewriting both answer permutations traverses the nested consistency sums.
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

end

end MIPStarRE.QPBT
