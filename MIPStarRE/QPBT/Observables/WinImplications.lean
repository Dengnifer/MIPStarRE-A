import MIPStarRE.QPBT.Observables.WinImplications.Consistency

/-!
# Winning implications for strategy observables

This module states the seven consequences of success in the Pauli basis test
and their operator-distance companions. It also constructs the actual Magic
Square strategy associated with a Pauli tuple and records the two observable
consequences used by the expanded-state argument.

## References

The declarations formalize `lem:qld-win-implications` and
`lem:qld-win-implications-obs` in
`blueprint/src/chapter/ch14_qpbt_observables.tex:505-733`. Their paper source
is `references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:192-354`.
-/

open scoped BigOperators Matrix ComplexOrder

namespace MIPStarRE.QPBT

open MIPStarRE.LDT hiding Measurement
open MIPStarRE.Quantum

noncomputable section

/-- The consistency subtest bounds the off-diagonal defect of the two strategy
measurement families. This is item 1 of `lem:qld-win-implications`, paper
`14_analysis_of_the_pauli_basis_test.tex:197-199`, blueprint
`ch14_qpbt_observables.tex:515-522`. -/
theorem win_cons :
    ∃ C : ℝ, 1 ≤ C ∧
      ∀ (P : AdmissibleParams) (ε : ℝ) (S : ProjectiveSetting P ε),
      0 ≤ ε →
      consistencyDefect (pauliQuestionMarginal P)
        (fun question a => heteroKron
          ((S.strategyMeasurement .alice question).effect a) 1)
        (fun question a => heteroKron 1
          ((S.strategyMeasurement .bob question).effect a))
        S.toStrategy.ψ ≤ C * ε := WinImplications.win_cons_proof

/-- The low-degree subtest bounds completed line-evaluation classes against
completed point measurements. This is item 2 of
`lem:qld-win-implications`, paper
`14_analysis_of_the_pauli_basis_test.tex:200-204`, blueprint
`ch14_qpbt_observables.tex:523-548`. -/
theorem win_low_degree :
    ∃ C : ℝ, 1 ≤ C ∧
      ∀ (P : AdmissibleParams) (ε : ℝ) (S : ProjectiveSetting P ε),
      0 ≤ ε → ∀ W : PauliKind,
      consistencyDefect (linePointDist P.toLdParams)
        (fun sample a => heteroKron
          ((S.lineEvalMeas .alice W sample.1 sample.2).effect a) 1)
        (fun sample a => heteroKron 1
          ((S.pointMeasOption .bob W sample.2).effect a))
        S.toStrategy.ψ ≤ C * ε := WinImplications.win_low_degree_proof

/-- The Pauli-basis consistency subtest compares point values with evaluated
low-degree encodings of Pauli answers. This is item 3 of
`lem:qld-win-implications`, paper
`14_analysis_of_the_pauli_basis_test.tex:205-209`, blueprint
`ch14_qpbt_observables.tex:549-566`. -/
theorem win_pauli_basis_cons :
    ∃ C : ℝ, 1 ≤ C ∧
      ∀ (P : AdmissibleParams) (ε : ℝ) (S : ProjectiveSetting P ε),
      0 ≤ ε → ∀ W : PauliKind,
      consistencyDefect (uniformDistribution (Fin P.m → PauliScalar P))
        (fun u a => heteroKron ((S.pointMeas .alice W u).effect a) 1)
        (fun u a => heteroKron 1 ((S.pauliEvalMeas .bob W u).effect a))
        S.toStrategy.ψ ≤ C * ε := WinImplications.win_pauli_basis_cons_proof

/-- On commuting tuples, Pair/W answers agree with the corresponding
component of Pair answers. This is item 4 of `lem:qld-win-implications`, paper
`14_analysis_of_the_pauli_basis_test.tex:210-231`, blueprint
`ch14_qpbt_observables.tex:567-582`. -/
theorem win_comm :
    ∃ C : ℝ, 1 ≤ C ∧
      ∀ (P : AdmissibleParams) (ε : ℝ) (S : ProjectiveSetting P ε),
      0 ≤ ε → ∀ W : PauliKind,
      consistencyDefect (commTupleDist P)
        (fun ω a => heteroKron
          ((S.pairWMeas .alice W ω.1 ω.2.1 ω.2.2.1 ω.2.2.2).effect a) 1)
        (fun ω a => heteroKron 1 ((S.pairComponentMeas .bob W ω).effect a))
        S.toStrategy.ψ ≤ C * ε := WinImplications.win_comm_proof

/-- On commuting tuples, trace-coarse-grained point answers agree with Pair/W
answers. This is item 5 of `lem:qld-win-implications`, paper
`14_analysis_of_the_pauli_basis_test.tex:232-239`, blueprint
`ch14_qpbt_observables.tex:583-598`. -/
theorem win_comm_cons :
    ∃ C : ℝ, 1 ≤ C ∧
      ∀ (P : AdmissibleParams) (ε : ℝ) (S : ProjectiveSetting P ε),
      0 ≤ ε → ∀ W : PauliKind,
      consistencyDefect (commTupleDist P)
        (fun ω a => heteroKron
          ((S.pointTraceMeas .alice W
            (match W with | .X => ω.1 | .Z => ω.2.1)
            (match W with | .X => ω.2.2.1 | .Z => ω.2.2.2)).effect a) 1)
        (fun ω a => heteroKron 1
          ((S.pairWMeas .bob W ω.1 ω.2.1 ω.2.2.1 ω.2.2.2).effect a))
        S.toStrategy.ψ ≤ C * ε := WinImplications.win_comm_cons_proof

/-- The average value of the actual induced Magic Square strategies is close
to one on anticommuting tuples. This is item 6 of
`lem:qld-win-implications`, paper
`14_analysis_of_the_pauli_basis_test.tex:240-249`, blueprint
`ch14_qpbt_observables.tex:599-625`. -/
theorem win_magic_square :
    ∃ C : ℝ, 1 ≤ C ∧
      ∀ (P : AdmissibleParams) (ε : ℝ) (S : ProjectiveSetting P ε),
      0 ≤ ε →
      |1 - avgOver (anticommTupleDist P) S.msValueAt| ≤ C * ε :=
  WinImplications.win_magic_square_proof

/-- On anticommuting tuples, the X and Z point traces agree respectively with
Magic Square variables 1 and 5. This is item 7 of
`lem:qld-win-implications`, paper
`14_analysis_of_the_pauli_basis_test.tex:250-263`, blueprint
`ch14_qpbt_observables.tex:626-660`. -/
theorem win_ms_cons :
    ∃ C : ℝ, 1 ≤ C ∧
      ∀ (P : AdmissibleParams) (ε : ℝ) (S : ProjectiveSetting P ε),
      0 ≤ ε → ∀ W : PauliKind,
      consistencyDefect (anticommTupleDist P)
        (fun ω a => heteroKron
          ((S.pointTraceMeas .alice W
            (match W with | .X => ω.1 | .Z => ω.2.1)
            (match W with | .X => ω.2.2.1 | .Z => ω.2.2.2)).effect a) 1)
        (fun ω a => heteroKron 1
          ((S.msVarBitMeas .bob (match W with | .X => 0 | .Z => 4) ω).effect a))
        S.toStrategy.ψ ≤ C * ε := WinImplications.win_ms_cons_proof

/-- Operator-distance and factor-interchanged companions to the consistency
item of `lem:qld-win-implications`. This is the trailing clause at paper
`14_analysis_of_the_pauli_basis_test.tex:264-266`, blueprint
`ch14_qpbt_observables.tex:651-660`. -/
theorem win_cons_approx :
    ∃ C : ℝ, 1 ≤ C ∧
      ∀ (P : AdmissibleParams) (ε : ℝ) (S : ProjectiveSetting P ε),
      0 ≤ ε →
      opFamilyDistSq (pauliQuestionMarginal P)
        (fun question a => heteroKron
          ((S.strategyMeasurement .alice question).effect a) 1)
        (fun question a => heteroKron 1
          ((S.strategyMeasurement .bob question).effect a))
        S.toStrategy.ψ ≤ C * ε ∧
      opFamilyDistSq (pauliQuestionMarginal P)
        (fun question a => heteroKron
          ((S.strategyMeasurement .bob question).effect a) 1)
        (fun question a => heteroKron 1
          ((S.strategyMeasurement .alice question).effect a))
        S.swappedState ≤ C * ε := by
  sorry

/-- Operator-distance and factor-interchanged companions to the low-degree
item of `lem:qld-win-implications`. This is the trailing clause at paper
`14_analysis_of_the_pauli_basis_test.tex:264-266`, blueprint
`ch14_qpbt_observables.tex:651-660`. -/
theorem win_low_degree_approx :
    ∃ C : ℝ, 1 ≤ C ∧
      ∀ (P : AdmissibleParams) (ε : ℝ) (S : ProjectiveSetting P ε),
      0 ≤ ε → ∀ W : PauliKind,
      opFamilyDistSq (linePointDist P.toLdParams)
        (fun sample a => heteroKron
          ((S.lineEvalMeas .alice W sample.1 sample.2).effect a) 1)
        (fun sample a => heteroKron 1
          ((S.pointMeasOption .bob W sample.2).effect a))
        S.toStrategy.ψ ≤ C * ε ∧
      opFamilyDistSq (linePointDist P.toLdParams)
        (fun sample a => heteroKron
          ((S.lineEvalMeas .bob W sample.1 sample.2).effect a) 1)
        (fun sample a => heteroKron 1
          ((S.pointMeasOption .alice W sample.2).effect a))
        S.swappedState ≤ C * ε := by
  sorry

/-- Operator-distance and factor-interchanged companions to Pauli-basis
consistency. This is the trailing clause of `lem:qld-win-implications`, paper
`14_analysis_of_the_pauli_basis_test.tex:264-266`, blueprint
`ch14_qpbt_observables.tex:651-660`. -/
theorem win_pauli_basis_cons_approx :
    ∃ C : ℝ, 1 ≤ C ∧
      ∀ (P : AdmissibleParams) (ε : ℝ) (S : ProjectiveSetting P ε),
      0 ≤ ε → ∀ W : PauliKind,
      opFamilyDistSq (uniformDistribution (Fin P.m → PauliScalar P))
        (fun u a => heteroKron ((S.pointMeas .alice W u).effect a) 1)
        (fun u a => heteroKron 1 ((S.pauliEvalMeas .bob W u).effect a))
        S.toStrategy.ψ ≤ C * ε ∧
      opFamilyDistSq (uniformDistribution (Fin P.m → PauliScalar P))
        (fun u a => heteroKron ((S.pointMeas .bob W u).effect a) 1)
        (fun u a => heteroKron 1 ((S.pauliEvalMeas .alice W u).effect a))
        S.swappedState ≤ C * ε := by
  sorry

/-- Operator-distance and factor-interchanged companions to the commuting
Pair check. This is the trailing clause of `lem:qld-win-implications`, paper
`14_analysis_of_the_pauli_basis_test.tex:264-266`, blueprint
`ch14_qpbt_observables.tex:651-660`. -/
theorem win_comm_approx :
    ∃ C : ℝ, 1 ≤ C ∧
      ∀ (P : AdmissibleParams) (ε : ℝ) (S : ProjectiveSetting P ε),
      0 ≤ ε → ∀ W : PauliKind,
      opFamilyDistSq (commTupleDist P)
        (fun ω a => heteroKron
          ((S.pairWMeas .alice W ω.1 ω.2.1 ω.2.2.1 ω.2.2.2).effect a) 1)
        (fun ω a => heteroKron 1 ((S.pairComponentMeas .bob W ω).effect a))
        S.toStrategy.ψ ≤ C * ε ∧
      opFamilyDistSq (commTupleDist P)
        (fun ω a => heteroKron
          ((S.pairWMeas .bob W ω.1 ω.2.1 ω.2.2.1 ω.2.2.2).effect a) 1)
        (fun ω a => heteroKron 1 ((S.pairComponentMeas .alice W ω).effect a))
        S.swappedState ≤ C * ε := by
  sorry

/-- Operator-distance and factor-interchanged companions to commuting point
consistency. This is the trailing clause of `lem:qld-win-implications`, paper
`14_analysis_of_the_pauli_basis_test.tex:264-266`, blueprint
`ch14_qpbt_observables.tex:651-660`. -/
theorem win_comm_cons_approx :
    ∃ C : ℝ, 1 ≤ C ∧
      ∀ (P : AdmissibleParams) (ε : ℝ) (S : ProjectiveSetting P ε),
      0 ≤ ε → ∀ W : PauliKind,
      opFamilyDistSq (commTupleDist P)
        (fun ω a => heteroKron
          ((S.pointTraceMeas .alice W
            (match W with | .X => ω.1 | .Z => ω.2.1)
            (match W with | .X => ω.2.2.1 | .Z => ω.2.2.2)).effect a) 1)
        (fun ω a => heteroKron 1
          ((S.pairWMeas .bob W ω.1 ω.2.1 ω.2.2.1 ω.2.2.2).effect a))
        S.toStrategy.ψ ≤ C * ε ∧
      opFamilyDistSq (commTupleDist P)
        (fun ω a => heteroKron
          ((S.pointTraceMeas .bob W
            (match W with | .X => ω.1 | .Z => ω.2.1)
            (match W with | .X => ω.2.2.1 | .Z => ω.2.2.2)).effect a) 1)
        (fun ω a => heteroKron 1
          ((S.pairWMeas .alice W ω.1 ω.2.1 ω.2.2.1 ω.2.2.2).effect a))
        S.swappedState ≤ C * ε := by
  sorry

/-- Operator-distance and factor-interchanged companions to Magic Square
variable consistency. This is the trailing clause of
`lem:qld-win-implications`, paper
`14_analysis_of_the_pauli_basis_test.tex:264-266`, blueprint
`ch14_qpbt_observables.tex:651-660`. -/
theorem win_ms_cons_approx :
    ∃ C : ℝ, 1 ≤ C ∧
      ∀ (P : AdmissibleParams) (ε : ℝ) (S : ProjectiveSetting P ε),
      0 ≤ ε → ∀ W : PauliKind,
      opFamilyDistSq (anticommTupleDist P)
        (fun ω a => heteroKron
          ((S.pointTraceMeas .alice W
            (match W with | .X => ω.1 | .Z => ω.2.1)
            (match W with | .X => ω.2.2.1 | .Z => ω.2.2.2)).effect a) 1)
        (fun ω a => heteroKron 1
          ((S.msVarBitMeas .bob (match W with | .X => 0 | .Z => 4) ω).effect a))
        S.toStrategy.ψ ≤ C * ε ∧
      opFamilyDistSq (anticommTupleDist P)
        (fun ω a => heteroKron
          ((S.pointTraceMeas .bob W
            (match W with | .X => ω.1 | .Z => ω.2.1)
            (match W with | .X => ω.2.2.1 | .Z => ω.2.2.2)).effect a) 1)
        (fun ω a => heteroKron 1
          ((S.msVarBitMeas .alice (match W with | .X => 0 | .Z => 4) ω).effect a))
        S.swappedState ≤ C * ε := by
  sorry

/-- Observable self-consistency on both tensor-factor orientations. This is
Equation `eq:pts-obs-consistency` in `lem:qld-win-implications-obs`, paper
`14_analysis_of_the_pauli_basis_test.tex:294-308`, blueprint
`ch14_qpbt_observables.tex:663-682`. -/
theorem pointObs_self_consistent :
    ∃ C : ℝ, 1 ≤ C ∧
      ∀ (P : AdmissibleParams) (ε : ℝ) (S : ProjectiveSetting P ε),
      0 ≤ ε → ∀ (W : PauliKind) (r : PauliScalar P),
      opDistSq (uniformDistribution (Fin P.m → PauliScalar P))
        (fun u => heteroKron (S.pointObs .alice W r u) 1)
        (fun u => heteroKron 1 (S.pointObs .bob W r u))
        S.toStrategy.ψ ≤ C * ε ∧
      opDistSq (uniformDistribution (Fin P.m → PauliScalar P))
        (fun u => heteroKron 1 (S.pointObs .bob W r u))
        (fun u => heteroKron (S.pointObs .alice W r u) 1)
        S.toStrategy.ψ ≤ C * ε := by
  sorry

/-- The strategy observables satisfy the phase-signed commutation relation on
Alice's factor. This is Equation `eq:pts-obs-commutation`, paper
`14_analysis_of_the_pauli_basis_test.tex:309-354`, blueprint
`ch14_qpbt_observables.tex:683-733`. -/
theorem pointObs_twisted_commutation :
    ∃ C : ℝ, 1 ≤ C ∧
      ∀ (P : AdmissibleParams) (ε : ℝ) (S : ProjectiveSetting P ε),
      0 ≤ ε →
      opDistSq (uniformDistribution (PauliTuple P))
        (fun ω => heteroKron
          (S.pointObs .alice .X ω.2.2.1 ω.1 *
            S.pointObs .alice .Z ω.2.2.2 ω.2.1) 1)
        (fun ω => phaseSign (gammaValue P ω.1 ω.2.1 ω.2.2.1 ω.2.2.2) •
          heteroKron
            (S.pointObs .alice .Z ω.2.2.2 ω.2.1 *
              S.pointObs .alice .X ω.2.2.1 ω.1) 1)
        S.toStrategy.ψ ≤ C * Real.sqrt ε := by
  sorry

/-- The factor-interchanged phase-signed commutation relation on Bob's factor.
This is the trailing clause of `lem:qld-win-implications-obs`, paper
`14_analysis_of_the_pauli_basis_test.tex:309-354`, blueprint
`ch14_qpbt_observables.tex:683-733`. -/
theorem pointObs_twisted_commutation_interchanged :
    ∃ C : ℝ, 1 ≤ C ∧
      ∀ (P : AdmissibleParams) (ε : ℝ) (S : ProjectiveSetting P ε),
      0 ≤ ε →
      opDistSq (uniformDistribution (PauliTuple P))
        (fun ω => heteroKron 1
          (S.pointObs .bob .X ω.2.2.1 ω.1 *
            S.pointObs .bob .Z ω.2.2.2 ω.2.1))
        (fun ω => phaseSign (gammaValue P ω.1 ω.2.1 ω.2.2.1 ω.2.2.2) •
          heteroKron 1
            (S.pointObs .bob .Z ω.2.2.2 ω.2.1 *
              S.pointObs .bob .X ω.2.2.1 ω.1))
        S.toStrategy.ψ ≤ C * Real.sqrt ε := by
  sorry

end


end MIPStarRE.QPBT
