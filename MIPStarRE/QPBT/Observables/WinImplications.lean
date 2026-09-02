import MIPStarRE.QPBT.Games.DistanceTheorems
import MIPStarRE.QPBT.Observables.Anticommuting
import MIPStarRE.QPBT.Observables.Defs

/-!
# Winning implications for strategy observables

This module packages the seven consequences of success in the Pauli basis test
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

open MIPStarRE.LDT MIPStarRE.Quantum

noncomputable section

/-- Finite-carrier support for applying the chapter-12 defect functional to
the Pauli question-pair distribution. The question space is finite by the
fixed finite field model; paper `14_analysis_of_the_pauli_basis_test.tex:197-199`,
blueprint `ch14_qpbt_observables.tex:515-522`. -/
noncomputable instance pauliQuestionPairFintype (P : AdmissibleParams) :
    Fintype (PauliQuestion P × PauliQuestion P) :=
  Fintype.ofFinite _

/-- Classical equality for the finite Pauli question-pair carrier. This is
Lean-only support for `consistencyDefect` in item 1 of
`lem:qld-win-implications`, blueprint `ch14_qpbt_observables.tex:515-522`. -/
noncomputable instance pauliQuestionPairDecidableEq (P : AdmissibleParams) :
    DecidableEq (PauliQuestion P × PauliQuestion P) :=
  Classical.decEq _

private abbrev LineDescCode (P : AdmissibleParams) :=
  ((Fin P.m → PauliScalar P) × PauliScalar P) ⊕
    ((Fin P.m → PauliScalar P) × PauliScalar P ×
      (Fin P.m → PauliScalar P))

private def lineDescCode (P : AdmissibleParams) :
    LineDesc P.toLdParams → LineDescCode P
  | .axis base seed _ => .inl (base, seed)
  | .diagonal base seed direction _ _ => .inr (base, seed, direction)

private theorem lineDescCode_injective (P : AdmissibleParams) :
    Function.Injective (lineDescCode P) := by
  intro x y h
  cases x with
  | axis base seed baseFixed =>
      cases y with
      | axis base' seed' baseFixed' =>
          simp only [lineDescCode, Sum.inl.injEq, Prod.mk.injEq] at h
          rcases h with ⟨rfl, rfl⟩
          rfl
      | diagonal => simp [lineDescCode] at h
  | diagonal base seed direction baseFixed prefixZero =>
      cases y with
      | axis => simp [lineDescCode] at h
      | diagonal base' seed' direction' baseFixed' prefixZero' =>
          simp only [lineDescCode, Sum.inr.injEq, Prod.mk.injEq] at h
          rcases h with ⟨rfl, rfl, rfl⟩
          rfl

/-- Finite enumeration of the proof-bearing canonical line descriptions,
obtained by an injective code that forgets only proposition-valued invariants.
This is Lean-only support for the line-point average in item 2 of
`lem:qld-win-implications`, blueprint `ch14_qpbt_observables.tex:523-548`. -/
noncomputable instance lineDescFintype (P : AdmissibleParams) :
    Fintype (LineDesc P.toLdParams) :=
  Fintype.ofInjective (lineDescCode P) (lineDescCode_injective P)

/-- Finite-carrier support for the canonical line-point distribution in the
low-degree winning implication. Paper
`14_analysis_of_the_pauli_basis_test.tex:200-204`, blueprint
`ch14_qpbt_observables.tex:523-548`. -/
noncomputable instance linePointFintype (P : AdmissibleParams) :
    Fintype (LineDesc P.toLdParams × (Fin P.m → PauliScalar P)) :=
  Fintype.ofFinite _

namespace ProjectiveSetting

variable {P : AdmissibleParams} {ε : ℝ}

/-- Complete a point measurement with a zero `none` outcome. This is the
right-hand family in the corrected low-degree item of
`lem:qld-win-implications`, blueprint
`ch14_qpbt_observables.tex:523-548`, paper
`14_analysis_of_the_pauli_basis_test.tex:197-204`. -/
noncomputable def pointMeasOption (S : ProjectiveSetting P ε)
    (side : PlayerSide) (W : PauliKind) (u : Fin P.m → PauliScalar P) :
    Measurement (Option (PauliScalar P)) (S.LocalSpace side) :=
  (S.pointMeas side W u).postprocess some

/-- Trace-coarse-graining of a strategy point measurement. This is the family
`M^((Point,W),u)_[tr(·r)=a]` in items 5 and 7 of
`lem:qld-win-implications`, paper
`14_analysis_of_the_pauli_basis_test.tex:232-263`, blueprint
`ch14_qpbt_observables.tex:583-660`. -/
noncomputable def pointTraceMeas (S : ProjectiveSetting P ε)
    (side : PlayerSide) (W : PauliKind) (u : Fin P.m → PauliScalar P)
    (r : PauliScalar P) : Measurement (ZMod 2) (S.LocalSpace side) :=
  (S.pointMeas side W u).postprocess fun a => fixedBinTrace P.model (a * r)

/-- Evaluate a Pauli-register answer through its low-degree encoding at `u`.
This is `M^(Pauli,W)_[g_h(u)=a]` in item 3 of
`lem:qld-win-implications`, paper
`14_analysis_of_the_pauli_basis_test.tex:205-209`, blueprint
`ch14_qpbt_observables.tex:549-566`. -/
noncomputable def pauliEvalMeas (S : ProjectiveSetting P ε)
    (side : PlayerSide) (W : PauliKind) (u : Fin P.m → PauliScalar P) :
    Measurement (PauliScalar P) (S.LocalSpace side) :=
  (S.pauliMeas side W).postprocess fun h => lowDegreeEnc h u

/-- Select the `W` bit of a Pair answer. This is the bracketed Pair family in
item 4 of `lem:qld-win-implications`, paper
`14_analysis_of_the_pauli_basis_test.tex:210-231`, blueprint
`ch14_qpbt_observables.tex:567-582`. -/
noncomputable def pairComponentMeas (S : ProjectiveSetting P ε)
    (side : PlayerSide) (W : PauliKind) (ω : PauliTuple P) :
    Measurement (ZMod 2) (S.LocalSpace side) :=
  (S.pairMeas side ω.1 ω.2.1 ω.2.2.1 ω.2.2.2).postprocess fun bits =>
    match W with
    | .X => bits.1
    | .Z => bits.2

/-- Extract a bit from a typed Magic Square answer, folding the impossible
triple constructor to zero. This Lean-only postprocessing is used only for
variable questions in item 7 of `lem:qld-win-implications`, blueprint
`ch14_qpbt_observables.tex:626-660`. -/
def msBitOrZero : MsAnswer → ZMod 2
  | .bit b => b
  | .triple _ => 0

/-- The bit measurement for a Magic Square variable question. This is
`M^(Variable_j,omega)_a` in item 7 of `lem:qld-win-implications`, paper
`14_analysis_of_the_pauli_basis_test.tex:250-263`, blueprint
`ch14_qpbt_observables.tex:626-660`. -/
noncomputable def msVarBitMeas (S : ProjectiveSetting P ε)
    (side : PlayerSide) (j : Fin 9) (ω : PauliTuple P) :
    Measurement (ZMod 2) (S.LocalSpace side) :=
  (S.msMeas side (.var j) ω.1 ω.2.1 ω.2.2.1 ω.2.2.2).postprocess msBitOrZero

/-- The Magic Square strategy induced by the test measurements at a fixed
Pauli tuple. It retains the original heterogeneous local spaces and state, as
required by item 6 of `lem:qld-win-implications`, paper
`14_analysis_of_the_pauli_basis_test.tex:240-249`, blueprint
`ch14_qpbt_observables.tex:599-625`. -/
noncomputable def msStrategyAt (S : ProjectiveSetting P ε)
    (ω : PauliTuple P) : Strategy msGame where
  ιA := S.toStrategy.ιA
  ιB := S.toStrategy.ιB
  ψ := S.toStrategy.ψ
  ψ_norm := S.toStrategy.ψ_norm
  A t := S.msMeas .alice t ω.1 ω.2.1 ω.2.2.1 ω.2.2.2
  B t := S.msMeas .bob t ω.1 ω.2.1 ω.2.2.1 ω.2.2.2

/-- The Magic Square value `Lambda_omega` is the ordinary tensor-product game
value of `msStrategyAt`. This is item 6 of `lem:qld-win-implications`, paper
`14_analysis_of_the_pauli_basis_test.tex:240-249`, blueprint
`ch14_qpbt_observables.tex:599-625`. -/
noncomputable def msValueAt (S : ProjectiveSetting P ε) (ω : PauliTuple P) : ℝ :=
  (S.msStrategyAt ω).value

end ProjectiveSetting

/-- The consistency subtest bounds the off-diagonal defect of the two raw
strategy families. This is item 1 of `lem:qld-win-implications`, paper
`14_analysis_of_the_pauli_basis_test.tex:197-199`, blueprint
`ch14_qpbt_observables.tex:515-522`. -/
theorem win_cons :
    ∃ C : ℝ, 1 ≤ C ∧
      ∀ (P : AdmissibleParams) (ε : ℝ) (S : ProjectiveSetting P ε),
      0 ≤ ε →
      consistencyDefect (pauliQuestionDistribution P)
        (fun questions a => heteroKron
          ((S.rawMeasurement .alice questions.1).effect a) 1)
        (fun questions a => heteroKron 1
          ((S.rawMeasurement .bob questions.2).effect a))
        S.toStrategy.ψ ≤ C * ε := by
  sorry

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
        S.toStrategy.ψ ≤ C * ε := by
  sorry

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
        S.toStrategy.ψ ≤ C * ε := by
  sorry

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
        S.toStrategy.ψ ≤ C * ε := by
  sorry

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
        S.toStrategy.ψ ≤ C * ε := by
  sorry

/-- The average value of the actual induced Magic Square strategies is close
to one on anticommuting tuples. This is item 6 of
`lem:qld-win-implications`, paper
`14_analysis_of_the_pauli_basis_test.tex:240-249`, blueprint
`ch14_qpbt_observables.tex:599-625`. -/
theorem win_magic_square :
    ∃ C : ℝ, 1 ≤ C ∧
      ∀ (P : AdmissibleParams) (ε : ℝ) (S : ProjectiveSetting P ε),
      0 ≤ ε →
      |1 - avgOver (anticommTupleDist P) S.msValueAt| ≤ C * ε := by
  sorry

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
        S.toStrategy.ψ ≤ C * ε := by
  sorry

/-- Operator-distance and factor-interchanged companions to the consistency
item of `lem:qld-win-implications`. This is the trailing clause at paper
`14_analysis_of_the_pauli_basis_test.tex:264-266`, blueprint
`ch14_qpbt_observables.tex:651-660`. -/
theorem win_cons_approx :
    ∃ C : ℝ, 1 ≤ C ∧
      ∀ (P : AdmissibleParams) (ε : ℝ) (S : ProjectiveSetting P ε),
      0 ≤ ε →
      opFamilyDistSq (pauliQuestionDistribution P)
        (fun questions a => heteroKron
          ((S.rawMeasurement .alice questions.1).effect a) 1)
        (fun questions a => heteroKron 1
          ((S.rawMeasurement .bob questions.2).effect a))
        S.toStrategy.ψ ≤ C * ε ∧
      opFamilyDistSq (pauliQuestionDistribution P)
        (fun questions a => heteroKron 1
          ((S.rawMeasurement .bob questions.2).effect a))
        (fun questions a => heteroKron
          ((S.rawMeasurement .alice questions.1).effect a) 1)
        S.toStrategy.ψ ≤ C * ε := by
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
        (fun sample a => heteroKron 1
          ((S.pointMeasOption .bob W sample.2).effect a))
        (fun sample a => heteroKron
          ((S.lineEvalMeas .alice W sample.1 sample.2).effect a) 1)
        S.toStrategy.ψ ≤ C * ε := by
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
        (fun u a => heteroKron 1 ((S.pauliEvalMeas .bob W u).effect a))
        (fun u a => heteroKron ((S.pointMeas .alice W u).effect a) 1)
        S.toStrategy.ψ ≤ C * ε := by
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
        (fun ω a => heteroKron 1 ((S.pairComponentMeas .bob W ω).effect a))
        (fun ω a => heteroKron
          ((S.pairWMeas .alice W ω.1 ω.2.1 ω.2.2.1 ω.2.2.2).effect a) 1)
        S.toStrategy.ψ ≤ C * ε := by
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
        (fun ω a => heteroKron 1
          ((S.pairWMeas .bob W ω.1 ω.2.1 ω.2.2.1 ω.2.2.2).effect a))
        (fun ω a => heteroKron
          ((S.pointTraceMeas .alice W
            (match W with | .X => ω.1 | .Z => ω.2.1)
            (match W with | .X => ω.2.2.1 | .Z => ω.2.2.2)).effect a) 1)
        S.toStrategy.ψ ≤ C * ε := by
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
        (fun ω a => heteroKron 1
          ((S.msVarBitMeas .bob (match W with | .X => 0 | .Z => 4) ω).effect a))
        (fun ω a => heteroKron
          ((S.pointTraceMeas .alice W
            (match W with | .X => ω.1 | .Z => ω.2.1)
            (match W with | .X => ω.2.2.1 | .Z => ω.2.2.2)).effect a) 1)
        S.toStrategy.ψ ≤ C * ε := by
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
