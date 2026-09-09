import MIPStarRE.QPBT.Combining.ExtendedLineGame

/-!
# Parameter evaluation versus completed line evaluation

Completed evaluation of a coefficient vector may return `none`, notably on a
zero-direction line when the represented polynomial is not constant.  A
successful completed readout at the point represented by a parameter agrees
with ordinary coefficient evaluation at that parameter.  Consequently,
parameter-value disagreement is contained in the union of completed-readout
disagreement and the two failure events.

The final theorem lifts this inclusion to the Born weights of two arbitrary
strategy POVMs.  It uses neither projectivity nor a collision estimate.

## References

- `references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:230-390`
- `references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1267-1402`
-/

namespace MIPStarRE.QPBT

open MIPStarRE.LDT

noncomputable section

namespace ExtendedLineGame

/-- A successful completed readout at the point represented by `parameter`
equals coefficient evaluation at `parameter`.  This includes zero directions. -/
theorem evalCoefficient_eq_of_directEvalOpt_affine_eq_some
    {params : DirectLdParams} {degree : ℕ}
    (line : DirectLineDesc params) (coeffs : DirectDegPoly params degree)
    (parameter answer : DirectScalarQ params)
    (hread : directEvalOpt line (line.base + parameter • line.direction) coeffs =
      some answer) :
    evalCoefficient coeffs parameter = answer := by
  have heval := (directEvalOpt_eq_some_iff line
    (line.base + parameter • line.direction) coeffs answer).mp hread
  exact heval.2 parameter rfl

/-- If two coefficient vectors disagree at a parameter, then their completed
readouts at the represented point disagree, or at least one readout is `none`. -/
theorem evalCoefficient_ne_imp_directEvalOpt_ne_or_eq_none
    {params : DirectLdParams} {degree : ℕ}
    (line : DirectLineDesc params) (coeffsA coeffsB : DirectDegPoly params degree)
    (parameter : DirectScalarQ params)
    (hne : evalCoefficient coeffsA parameter ≠ evalCoefficient coeffsB parameter) :
    directEvalOpt line (line.base + parameter • line.direction) coeffsA ≠
        directEvalOpt line (line.base + parameter • line.direction) coeffsB ∨
      directEvalOpt line (line.base + parameter • line.direction) coeffsA = none ∨
      directEvalOpt line (line.base + parameter • line.direction) coeffsB = none := by
  generalize hreadA : directEvalOpt line
    (line.base + parameter • line.direction) coeffsA = readA
  generalize hreadB : directEvalOpt line
    (line.base + parameter • line.direction) coeffsB = readB
  cases readA with
  | none => exact Or.inr (Or.inl rfl)
  | some answerA =>
      cases readB with
      | none => exact Or.inr (Or.inr rfl)
      | some answerB =>
          apply Or.inl
          intro hread
          have hab : answerA = answerB := Option.some.inj hread
          apply hne
          calc
            evalCoefficient coeffsA parameter = answerA :=
              evalCoefficient_eq_of_directEvalOpt_affine_eq_some
                line coeffsA parameter answerA hreadA
            _ = answerB := hab
            _ = evalCoefficient coeffsB parameter :=
              (evalCoefficient_eq_of_directEvalOpt_affine_eq_some
                line coeffsB parameter answerB hreadB).symm

/-- Born mass of disagreement between the two parameter evaluations. -/
def parameterEvalDefect {G : Game} {params : DirectLdParams} {degree : ℕ}
    (S : Strategy G) (questionA : G.QuestionA) (questionB : G.QuestionB)
    (readA : G.AnswerA → DirectDegPoly params degree)
    (readB : G.AnswerB → DirectDegPoly params degree)
    (parameter : DirectScalarQ params) : ℝ :=
  outcomeEventWeight S questionA questionB fun answerA answerB =>
    evalCoefficient (readA answerA) parameter ≠
      evalCoefficient (readB answerB) parameter

/-- Born mass of disagreement between the two completed evaluation readouts. -/
def completedEvalDefect {G : Game} {params : DirectLdParams} {degree : ℕ}
    (S : Strategy G) (questionA : G.QuestionA) (questionB : G.QuestionB)
    (readA : G.AnswerA → DirectDegPoly params degree)
    (readB : G.AnswerB → DirectDegPoly params degree)
    (line : DirectLineDesc params) (parameter : DirectScalarQ params) : ℝ :=
  outcomeEventWeight S questionA questionB fun answerA answerB =>
    directEvalOpt line (line.base + parameter • line.direction) (readA answerA) ≠
      directEvalOpt line (line.base + parameter • line.direction) (readB answerB)

/-- Alice's marginal Born mass of a failed completed evaluation. -/
def completedEvalNoneMassA {G : Game} {params : DirectLdParams} {degree : ℕ}
    (S : Strategy G) (questionA : G.QuestionA)
    (readA : G.AnswerA → DirectDegPoly params degree)
    (line : DirectLineDesc params) (parameter : DirectScalarQ params) : ℝ :=
  aliceEventWeight S questionA fun answerA =>
    directEvalOpt line (line.base + parameter • line.direction) (readA answerA) = none

/-- Bob's marginal Born mass of a failed completed evaluation. -/
def completedEvalNoneMassB {G : Game} {params : DirectLdParams} {degree : ℕ}
    (S : Strategy G) (questionB : G.QuestionB)
    (readB : G.AnswerB → DirectDegPoly params degree)
    (line : DirectLineDesc params) (parameter : DirectScalarQ params) : ℝ :=
  bobEventWeight S questionB fun answerB =>
    directEvalOpt line (line.base + parameter • line.direction) (readB answerB) = none

set_option maxHeartbeats 600000 in
-- Expanding three nested outcome events requires repeated finite-sum normalization.
/-- Parameter-evaluation disagreement is bounded by completed-evaluation
disagreement plus the two failed-completion marginals.  The result applies to
arbitrary strategy POVMs and needs no projectivity assumption. -/
theorem parameterEvalDefect_le_completed_add_none
    {G : Game} {params : DirectLdParams} {degree : ℕ}
    (S : Strategy G) (questionA : G.QuestionA) (questionB : G.QuestionB)
    (readA : G.AnswerA → DirectDegPoly params degree)
    (readB : G.AnswerB → DirectDegPoly params degree)
    (line : DirectLineDesc params) (parameter : DirectScalarQ params) :
    parameterEvalDefect S questionA questionB readA readB parameter ≤
      completedEvalDefect S questionA questionB readA readB line parameter +
        completedEvalNoneMassA S questionA readA line parameter +
        completedEvalNoneMassB S questionB readB line parameter := by
  classical
  unfold completedEvalNoneMassA completedEvalNoneMassB
  rw [← outcome_event_weight_left_eq S questionA questionB,
    ← outcome_event_weight_right_eq S questionA questionB]
  unfold parameterEvalDefect completedEvalDefect outcomeEventWeight
  calc
    (∑ answerA : G.AnswerA, ∑ answerB : G.AnswerB,
        if evalCoefficient (readA answerA) parameter ≠
            evalCoefficient (readB answerB) parameter then
          outcomeWeight S questionA questionB answerA answerB else 0) ≤
      ∑ answerA : G.AnswerA, ∑ answerB : G.AnswerB,
        ((if directEvalOpt line (line.base + parameter • line.direction)
              (readA answerA) ≠
            directEvalOpt line (line.base + parameter • line.direction)
              (readB answerB) then
            outcomeWeight S questionA questionB answerA answerB else 0) +
          (if directEvalOpt line (line.base + parameter • line.direction)
              (readA answerA) = none then
            outcomeWeight S questionA questionB answerA answerB else 0) +
          if directEvalOpt line (line.base + parameter • line.direction)
              (readB answerB) = none then
            outcomeWeight S questionA questionB answerA answerB else 0) := by
      apply Finset.sum_le_sum
      intro answerA _
      apply Finset.sum_le_sum
      intro answerB _
      have hweight := outcomeWeight_nonneg S questionA questionB answerA answerB
      by_cases hparameter : evalCoefficient (readA answerA) parameter ≠
          evalCoefficient (readB answerB) parameter
      · rcases evalCoefficient_ne_imp_directEvalOpt_ne_or_eq_none
          line (readA answerA) (readB answerB) parameter hparameter with
          hcompleted | hnoneA | hnoneB
        · simp [hparameter, hcompleted]
          split_ifs <;> linarith
        · simp [hparameter, hnoneA]
          split_ifs <;> linarith
        · simp [hparameter, hnoneB]
          split_ifs <;> linarith
      · simp [hparameter]
        split_ifs <;> linarith
    _ =
        (∑ answerA : G.AnswerA, ∑ answerB : G.AnswerB,
          if directEvalOpt line (line.base + parameter • line.direction)
                (readA answerA) ≠
              directEvalOpt line (line.base + parameter • line.direction)
                (readB answerB) then
            outcomeWeight S questionA questionB answerA answerB else 0) +
        (∑ answerA : G.AnswerA, ∑ answerB : G.AnswerB,
          if directEvalOpt line (line.base + parameter • line.direction)
              (readA answerA) = none then
            outcomeWeight S questionA questionB answerA answerB else 0) +
        ∑ answerA : G.AnswerA, ∑ answerB : G.AnswerB,
          if directEvalOpt line (line.base + parameter • line.direction)
              (readB answerB) = none then
            outcomeWeight S questionA questionB answerA answerB else 0 := by
      simp_rw [Finset.sum_add_distrib]

end ExtendedLineGame

end

end MIPStarRE.QPBT
