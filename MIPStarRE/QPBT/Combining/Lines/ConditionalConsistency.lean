import MIPStarRE.QPBT.Combining.Lines.ConsistencyPositivity
import MIPStarRE.QPBT.Games.RestrictedAverage

/-!
# Consistency defects under finite conditioning

This module bounds the consistency defect of two complete measurements after
the question distribution is conditioned on a positive-mass event.  For
measurements placed on opposite expanded registers, the pointwise defect is
nonnegative, so conditioning inflates the average by at most the inverse
retained mass.

## References

This is a formalization-only finite-conditioning estimate supporting the line
comparisons at
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:936-963`.
-/

open scoped BigOperators

namespace MIPStarRE.QPBT

open MIPStarRE.LDT MIPStarRE.Quantum

noncomputable section

/-- Conditioning the question distribution of two complete measurements on a
positive-mass event inflates their consistency defect by at most the inverse
retained mass.  This is a formalization-only auxiliary for the conditioned
line comparisons in paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:936-963`.

Pointwise nonnegativity is derived from positivity of POVM effects placed on
opposite expanded registers; it is not an additional hypothesis. -/
theorem consistencyDefect_restrict_le_div_mass
    {P : AdmissibleParams} {ε : ℝ} {Question Outcome : Type*}
    [Fintype Question] [DecidableEq Question]
    [Fintype Outcome] [DecidableEq Outcome]
    (S : ProjectiveSetting P ε) (p₁ p₂ : Placement)
    (hopp : p₁.IsOpposite p₂) (dist : Distribution Question)
    (good : Question → Prop) [DecidablePred good]
    (hpos : 0 < ∑ question ∈ dist.support.filter good, dist.weight question)
    (first : Question →
      MIPStarRE.Quantum.Measurement Outcome (S.ExpandedLocalSpace p₁.side))
    (second : Question →
      MIPStarRE.Quantum.Measurement Outcome (S.ExpandedLocalSpace p₂.side)) :
    consistencyDefect (Distribution.restrict dist good hpos)
        (fun question answer => S.place p₁ ((first question).effect answer))
        (fun question answer => S.place p₂ ((second question).effect answer))
        S.psiHat ≤
      consistencyDefect dist
          (fun question answer => S.place p₁ ((first question).effect answer))
          (fun question answer => S.place p₂ ((second question).effect answer))
          S.psiHat /
        (∑ question ∈ dist.support.filter good, dist.weight question) := by
  unfold consistencyDefect
  let value : Question → ℝ := fun question =>
    ∑ a : Outcome, ∑ b : Outcome,
      if a = b then 0
      else (inner ℂ S.psiHat
        ((EuclideanSpace.equiv (SixReg P S.toStrategy.ιA S.toStrategy.ιB)
            ℂ).symm
          ((S.place p₁ ((first question).effect a) *
            S.place p₂ ((second question).effect b)).mulVec S.psiHat))).re
  exact avgOver_restrict_le_div_mass dist good hpos value fun question =>
    consistencyDefect_integrand_nonneg S p₁ p₂ hopp (first question) (second question)

end

end MIPStarRE.QPBT
