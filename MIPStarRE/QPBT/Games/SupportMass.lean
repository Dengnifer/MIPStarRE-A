import MIPStarRE.QPBT.Games.Sandwich.Support

/-! # Marginal mass outside the support of a reference measurement

A complete reference measurement supported on an allowed outcome set bounds
the other measurement's mass outside that set by their bipartite consistency
defect. The measurements act on separate tensor factors of the same state.
Neither projectivity nor state normalization is needed; for a unit vector the
quadratic forms are the corresponding Born probabilities.

These are formalization-only auxiliary estimates for the non-encoding mass
calculation in blueprint `eq:qld-nonencoding-mass`. They can be composed with
`SandwichProduct.point_codeword_defect_le_avg_evaluated_add` after constructing
an encoding-supported reference measurement on the opposite tensor factor.
They do not construct that reference or establish its evaluated consistency,
and do not prove `nonencodingMarginalMass_le` or global-pair witness existence.

## References

- Blueprint `eq:qld-nonencoding-mass` and `lem:qld-nonencoding-mass-bound`.
- `references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1483-1498`,
  the consistency calculation in `lem:qld-construct-the-paulis` that the
  blueprint's non-encoding mass estimate supports.
- `references/qpbt-paper/06_nonlocal_games_and_mipstar.tex:232-248`,
  the bipartite consistency defect.
-/

open scoped BigOperators MatrixOrder

namespace MIPStarRE.QPBT

open MIPStarRE.LDT hiding Measurement
open MIPStarRE.Quantum DistanceCalculus

/-- The mass of a measurement outside the support of a complete reference
measurement is at most their off-diagonal tensor overlap. Completeness of the
reference expands each marginal mass into a row of joint probabilities;
support makes the diagonal term zero, and positivity bounds the restricted
sum by the full defect. This is a formalization-only auxiliary for blueprint
`eq:qld-nonencoding-mass`, valid for arbitrary state vectors. -/
theorem mass_outside_support_le_point_defect
    {Outcome Left Right : Type*}
    [Fintype Outcome] [DecidableEq Outcome]
    [Fintype Left] [DecidableEq Left] [Fintype Right] [DecidableEq Right]
    (meas : Measurement Outcome Left) (reference : Measurement Outcome Right)
    (psi : EuclideanSpace ℂ (Left × Right)) (allowed : Finset Outcome)
    (hsupport : ∀ outcome, outcome ∉ allowed → reference.effect outcome = 0) :
    (∑ outcome ∈ Finset.univ.filter (fun outcome => outcome ∉ allowed),
      stateQForm psi (heteroKron (meas.effect outcome) 1)) ≤
      ∑ outcome : Outcome, ∑ other : Outcome, if outcome = other then 0 else
        stateQForm psi (heteroKron (meas.effect outcome) (reference.effect other)) := by
  have hnonneg (outcome other : Outcome) :
      0 ≤ stateQForm psi (heteroKron (meas.effect outcome) (reference.effect other)) :=
    stateQForm_nonneg psi (kronecker_nonneg (meas.pos outcome) (reference.pos other))
  calc
    (∑ outcome ∈ Finset.univ.filter (fun outcome => outcome ∉ allowed),
        stateQForm psi (heteroKron (meas.effect outcome) 1)) =
        ∑ outcome ∈ Finset.univ.filter (fun outcome => outcome ∉ allowed),
          ∑ other : Outcome, if outcome = other then 0 else
            stateQForm psi
              (heteroKron (meas.effect outcome) (reference.effect other)) := by
      apply Finset.sum_congr rfl
      intro outcome houtcome
      have hzero := hsupport outcome (Finset.mem_filter.mp houtcome).2
      rw [← reference.sum_eq_one, heteroKron_finset_sum_right, stateQForm_finset_sum]
      apply Finset.sum_congr rfl
      intro other _
      by_cases heq : outcome = other
      · subst other
        simp [hzero, heteroKron, stateQForm, applyOperatorToState]
      · rw [if_neg heq]
    _ ≤ _ := by
      apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      intro outcome _ _
      apply Finset.sum_nonneg
      intro other _
      split_ifs
      · exact le_rfl
      · exact hnonneg outcome other

/-- Averaging the supported-reference mass bound gives the same inequality
for `consistencyDefect` with the existing left and right tensor placements.
This formalization-only auxiliary for blueprint `eq:qld-nonencoding-mass`
requires neither a probability distribution nor a normalized state, so it
applies in particular to the normalized state used in that calculation. -/
theorem avg_mass_outside_support_le_consistency_defect
    {Question Outcome Left Right : Type*}
    [Fintype Question] [DecidableEq Question] [Fintype Outcome] [DecidableEq Outcome]
    [Fintype Left] [DecidableEq Left] [Fintype Right] [DecidableEq Right]
    (mu : Distribution Question) (meas : Question → Measurement Outcome Left)
    (reference : Question → Measurement Outcome Right)
    (psi : EuclideanSpace ℂ (Left × Right)) (allowed : Finset Outcome)
    (hsupport : ∀ question outcome,
      outcome ∉ allowed → (reference question).effect outcome = 0) :
    avgOver mu (fun question =>
      ∑ outcome ∈ Finset.univ.filter (fun outcome => outcome ∉ allowed),
        stateQForm psi (heteroKron ((meas question).effect outcome) 1)) ≤
      consistencyDefect mu
        (fun question outcome => heteroKron ((meas question).effect outcome) 1)
        (fun question outcome => heteroKron 1 ((reference question).effect outcome)) psi := by
  rw [SandwichProduct.consistencyDefect_placed_eq_avg_point]
  apply avgOver_mono
  intro question
  exact mass_outside_support_le_point_defect
    (meas question) (reference question) psi allowed (hsupport question)

end MIPStarRE.QPBT
