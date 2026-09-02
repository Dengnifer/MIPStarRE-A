import MIPStarRE.QPBT.Test.PauliBasisTest

/-!
# Commuting and anticommuting Pauli tuples

This module defines the tuple phase used in the Pauli basis test and the
conditional uniform distributions used by its observable analysis.

## References

The definitions and probability bounds formalize `def:anticommuting-tuple`
and `fact:omega-anticomm-prob` in
`blueprint/src/chapter/ch14_qpbt_observables.tex:128-267`, with paper origin
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:64-95`.
-/

namespace MIPStarRE.QPBT

open MIPStarRE.LDT

noncomputable section

/-- A tuple `(u_X,u_Z,r_X,r_Z)` over the fixed field model of an admissible
Pauli-test parameter tuple. This is the tuple space of
`def:anticommuting-tuple`, blueprint `ch14_qpbt_observables.tex:128-148`, paper
`14_analysis_of_the_pauli_basis_test.tex:64-68`. -/
abbrev PauliTuple (P : AdmissibleParams) :=
  (Fin P.m → PauliScalar P) ×
    (Fin P.m → PauliScalar P) × PauliScalar P × PauliScalar P

/-- A Pauli tuple is anticommuting when its phase bit is nonzero. This is
`def:anticommuting-tuple`, blueprint `ch14_qpbt_observables.tex:128-148`, paper
`14_analysis_of_the_pauli_basis_test.tex:64-68`. -/
def IsAnticommuting {P : AdmissibleParams} (ω : PauliTuple P) : Prop :=
  gammaValue P ω.1 ω.2.1 ω.2.2.1 ω.2.2.2 ≠ 0

/-- A Pauli tuple is commuting when its phase bit vanishes. This is the
complementary case in `def:anticommuting-tuple`, blueprint
`ch14_qpbt_observables.tex:128-148`, paper
`14_analysis_of_the_pauli_basis_test.tex:64-68`. -/
def IsCommuting {P : AdmissibleParams} (ω : PauliTuple P) : Prop :=
  gammaValue P ω.1 ω.2.1 ω.2.2.1 ω.2.2.2 = 0

noncomputable instance (P : AdmissibleParams) :
    DecidablePred (@IsAnticommuting P) := Classical.decPred _

noncomputable instance (P : AdmissibleParams) :
    DecidablePred (@IsCommuting P) := Classical.decPred _

/-- The uniform probability of the anticommuting event. This is the first
quantity in `fact:omega-anticomm-prob`, blueprint
`ch14_qpbt_observables.tex:151-178`, paper
`14_analysis_of_the_pauli_basis_test.tex:70-77`. -/
noncomputable def anticommProb (P : AdmissibleParams) : ℝ :=
  ((Finset.univ.filter (@IsAnticommuting P)).card : ℝ) /
    Fintype.card (PauliTuple P)

/-- The complementary uniform probability of the commuting event in
`fact:omega-anticomm-prob`, blueprint `ch14_qpbt_observables.tex:151-178`,
paper `14_analysis_of_the_pauli_basis_test.tex:70-77`. -/
noncomputable def commProb (P : AdmissibleParams) : ℝ :=
  ((Finset.univ.filter (@IsCommuting P)).card : ℝ) /
    Fintype.card (PauliTuple P)

/-- Exact anticommuting probability from `fact:omega-anticomm-prob`, blueprint
`ch14_qpbt_observables.tex:151-178`; its derivation replaces the erroneous
Schwartz--Zippel argument at paper
`14_analysis_of_the_pauli_basis_test.tex:79-93`. -/
theorem anticommProb_eq (P : AdmissibleParams) :
    anticommProb P = (1 - (P.q : ℝ)⁻¹) ^ (P.m + 1) / 2 := by
  sorry

/-- The commuting event has probability at least one half. This is the
complementary bound in `fact:omega-anticomm-prob`, blueprint
`ch14_qpbt_observables.tex:151-178`, paper
`14_analysis_of_the_pauli_basis_test.tex:70-77`. -/
theorem commProb_ge_half (P : AdmissibleParams) : 1 / 2 ≤ commProb P := by
  sorry

/-- When `m ≤ q`, the anticommuting event has the uniform constant lower
bound added in `fact:omega-anticomm-prob`, blueprint
`ch14_qpbt_observables.tex:151-178`. -/
theorem anticommProb_ge_of_m_le_q (P : AdmissibleParams) (hmq : P.m ≤ P.q) :
    (2 : ℝ) ^ (-4 : ℤ) ≤ anticommProb P := by
  sorry

/-- **Local fix:** For the positive parameters in `AdmissibleParams`, the
source lower bounds hold with the missing hypotheses restored. This is the
final display of `fact:omega-anticomm-prob`, blueprint
`ch14_qpbt_observables.tex:151-178`, correcting paper
`14_analysis_of_the_pauli_basis_test.tex:70-77`; see
`rem:omega-anticomm-prob-correction`. -/
theorem anticommProb_ge_of_one_le_md (P : AdmissibleParams) :
    (1 - (P.q : ℝ)⁻¹ ^ P.m) * (1 - (P.q : ℝ)⁻¹) *
        (1 - ((P.m * P.d : ℕ) : ℝ) / P.q) / 2 ≤ anticommProb P ∧
      (1 - 3 * ((P.m * P.d : ℕ) : ℝ) / P.q) / 2 ≤ anticommProb P ∧
      (1 - 3 * ((P.m * P.d : ℕ) : ℝ) / P.q) / 2 ≤ commProb P := by
  sorry

/-- The conditional uniform distribution on anticommuting tuples. This is the
sampling convention for the anticommuting cases of
`lem:qld-win-implications`, blueprint `ch14_qpbt_observables.tex:505-660`,
paper `14_analysis_of_the_pauli_basis_test.tex:210-287`. -/
noncomputable def anticommTupleDist (P : AdmissibleParams) :
    Distribution (PauliTuple P) :=
  Distribution.uniformOnFinset (Finset.univ.filter (@IsAnticommuting P))

/-- The conditional uniform distribution on commuting tuples. This is the
sampling convention for the commuting cases of `lem:qld-win-implications`,
blueprint `ch14_qpbt_observables.tex:505-660`, paper
`14_analysis_of_the_pauli_basis_test.tex:210-287`. -/
noncomputable def commTupleDist (P : AdmissibleParams) :
    Distribution (PauliTuple P) :=
  Distribution.uniformOnFinset (Finset.univ.filter (@IsCommuting P))

/-- The anticommuting conditional distribution is probabilistic. This is the
well-formedness companion to the conditional sampling in
`lem:qld-win-implications`, blueprint `ch14_qpbt_observables.tex:505-660`. -/
theorem anticommTupleDist_isProbability (P : AdmissibleParams) :
    (anticommTupleDist P).IsProbability := by
  sorry

/-- The commuting conditional distribution is probabilistic. This is the
well-formedness companion to the conditional sampling in
`lem:qld-win-implications`, blueprint `ch14_qpbt_observables.tex:505-660`. -/
theorem commTupleDist_isProbability (P : AdmissibleParams) :
    (commTupleDist P).IsProbability := by
  sorry

end

end MIPStarRE.QPBT
