import MIPStarRE.QPBT.Games.DistanceTheorems
import MIPStarRE.QPBT.Observables.Anticommuting
import MIPStarRE.QPBT.Observables.Defs

/-!
# Definitions for winning implications

This module defines the measurements, marginals, and induced Magic Square
strategy used by the exact and approximate winning implications.

## References

The definitions support `lem:qld-win-implications` and
`lem:qld-win-implications-obs` in
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:192-354` and
`blueprint/src/chapter/ch14_qpbt_observables.tex:505-733`.
-/

open scoped BigOperators Matrix ComplexOrder

namespace MIPStarRE.QPBT

open MIPStarRE.LDT hiding Measurement
open MIPStarRE.Quantum

noncomputable section

/-- The single-question marginal used by the consistency check. Both players
receive this same question; paper
`14_analysis_of_the_pauli_basis_test.tex:197-202`, blueprint
`ch14_qpbt_observables.tex:555-559`. -/
noncomputable def pauliQuestionMarginal (P : AdmissibleParams) :
    Distribution (PauliQuestion P) :=
  (pauliQuestionDistribution P).map Prod.fst

/-- Reindex a heterogeneous strategy state after interchanging its two tensor
factors. This is the state used by the factor-interchanged conclusions at
paper `14_analysis_of_the_pauli_basis_test.tex:227-228`. -/
noncomputable def ProjectiveSetting.swappedState
    {P : AdmissibleParams} {ε : ℝ} (S : ProjectiveSetting P ε) :
    EuclideanSpace ℂ (S.toStrategy.ιB × S.toStrategy.ιA) :=
  reindexState (Equiv.prodComm S.toStrategy.ιA S.toStrategy.ιB)
    S.toStrategy.ψ

/-- The space of Pauli question pairs is finite because the underlying field
model is finite. Paper `14_analysis_of_the_pauli_basis_test.tex:197-199`;
blueprint `ch14_qpbt_observables.tex:515-522`. -/
noncomputable instance pauliQuestionPairFintype (P : AdmissibleParams) :
    Fintype (PauliQuestion P × PauliQuestion P) :=
  Fintype.ofFinite _

/-- Equality of Pauli question pairs is decidable. This is used in the
consistency defect from item 1 of `lem:qld-win-implications`; blueprint
`ch14_qpbt_observables.tex:515-522`. -/
noncomputable instance pauliQuestionPairDecidableEq (P : AdmissibleParams) :
    DecidableEq (PauliQuestion P × PauliQuestion P) :=
  Classical.decEq _

/-- The coordinate space records the base and seed of an axis line, or the
base, seed, and direction of a diagonal line. It is finite and indexes the
line-point average in `lem:qld-win-implications`; blueprint
`ch14_qpbt_observables.tex:523-548`. -/
private abbrev LineDescCode (P : AdmissibleParams) :=
  ((Fin P.m → PauliScalar P) × PauliScalar P) ⊕
    ((Fin P.m → PauliScalar P) × PauliScalar P ×
      (Fin P.m → PauliScalar P))

/-- Map a canonical line to its kind and coordinate data: base and seed for an
axis line, and base, seed, and direction for a diagonal line. Blueprint
`ch14_qpbt_observables.tex:523-548`. -/
private def lineDescCode (P : AdmissibleParams) :
    LineDesc P.toLdParams → LineDescCode P
  | .axis base seed _ => .inl (base, seed)
  | .diagonal base seed direction _ _ => .inr (base, seed, direction)

/-- The coordinate-data map on canonical lines is injective: lines of the same
kind with equal base, seed, and direction data are equal. This supports the
line-point average in `lem:qld-win-implications`; blueprint
`ch14_qpbt_observables.tex:523-548`. -/
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

/-- The set of canonical axis and diagonal lines is finite. This finiteness is
used in the line-point average from item 2 of `lem:qld-win-implications`;
blueprint `ch14_qpbt_observables.tex:523-548`. -/
noncomputable instance lineDescFintype (P : AdmissibleParams) :
    Fintype (LineDesc P.toLdParams) :=
  Fintype.ofInjective (lineDescCode P) (lineDescCode_injective P)

/-- The set of pairs consisting of a canonical line and a point is finite.
These pairs index the line-point distribution in the low-degree winning
implication. Paper
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

end

end MIPStarRE.QPBT
