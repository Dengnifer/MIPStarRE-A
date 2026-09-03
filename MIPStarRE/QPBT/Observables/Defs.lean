import MIPStarRE.QPBT.Games.StrategyClasses
import MIPStarRE.QPBT.Observables.LineDefs
import MIPStarRE.QPBT.Test.PauliBasisTest

/-!
# Typed strategy measurements and point observables

This file fixes a projective, possibly heterogeneous strategy for the Pauli
basis test and extracts the typed measurement families used in the analysis.
Malformed answers are folded into a fixed valid answer, so the extracted
families remain complete measurements. The winning hypothesis bounds their
original wrong-form mass by the rejection probability. `Option` is used only
for the completed line-evaluation classes.

## References

The ambient strategy convention and the observable `W^r(u)` are in
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:160-190`,
corresponding to `def:strategy-observables` in
`blueprint/src/chapter/ch14_qpbt_observables.tex:480-503`. The typed question
and answer forms come from `def:pauli-question-distribution` and
`def:pauli-win-predicate`, paper
`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:964-1225`
and blueprint `blueprint/src/chapter/ch13_qpbt_test.tex:310-392`.
-/

open scoped BigOperators Matrix ComplexOrder

namespace MIPStarRE.QPBT

open MIPStarRE.LDT MIPStarRE.Quantum

noncomputable section

/-- The two local registers of a heterogeneous bipartite strategy. This is
formalization-only indexing for the player-dependent notation at paper
`14_analysis_of_the_pauli_basis_test.tex:160-190`. -/
inductive PlayerSide where
  | alice
  | bob
  deriving DecidableEq, Repr, Inhabited, Fintype

/-- A projective strategy satisfying the winning premise used throughout
Section `sec:commutation`. The structure retains the distinct player spaces and
measurement families of `Strategy`. Paper
`14_analysis_of_the_pauli_basis_test.tex:160-172`; blueprint
`ch14_qpbt_observables.tex:385-475`. -/
structure ProjectiveSetting (P : AdmissibleParams) (ε : ℝ) where
  toStrategy : Strategy (pauliBasisTest P)
  isProjective : toStrategy.IsProjective
  win : 1 - ε ≤ toStrategy.value

namespace ProjectiveSetting

variable {P : AdmissibleParams} {ε : ℝ}

/-- The local Hilbert-space index type on a specified player side. It indexes
the side-qualified operators at paper
`14_analysis_of_the_pauli_basis_test.tex:174-190`. -/
def LocalSpace (S : ProjectiveSetting P ε) : PlayerSide → Type
  | .alice => S.toStrategy.ιA
  | .bob => S.toStrategy.ιB

instance localSpaceFintype (S : ProjectiveSetting P ε) (side : PlayerSide) :
    Fintype (S.LocalSpace side) := by
  cases side <;> simp only [LocalSpace] <;> infer_instance

instance localSpaceDecidableEq (S : ProjectiveSetting P ε) (side : PlayerSide) :
    DecidableEq (S.LocalSpace side) := by
  cases side <;> simp only [LocalSpace] <;> infer_instance

/-- Select the strategy measurement before outcome postprocessing on one
player side. This is the heterogeneous interpretation of the shared symbol `M` at
paper `14_analysis_of_the_pauli_basis_test.tex:160-184`. -/
def strategyMeasurement (S : ProjectiveSetting P ε) (side : PlayerSide)
    (question : PauliQuestion P) :
    Measurement (PauliAnswer P) (S.LocalSpace side) := by
  cases side with
  | alice => exact S.toStrategy.A question
  | bob => exact S.toStrategy.B question

/-- Embed a point into the full Pauli question space in basis `W`. This is the
point-question content from `def:pauli-question-distribution`, paper
`08_classical_and_quantum_low_degree_tests.tex:997-1008`, blueprint
`ch13_qpbt_test.tex:310-354`. -/
def contentOfPoint (P : AdmissibleParams) (W : PauliKind)
    (u : Fin P.m → PauliScalar P) : PauliSpace P :=
  embedLd P W fun i =>
    match i with
    | .inl (.inl j) => u j
    | .inl (.inr _) => 0
    | .inr _ => 0

/-- Embed a canonical line description into the full Pauli question space.
Axis lines clear the direction block, whereas diagonal lines retain their
canonical projected direction. Paper
`08_classical_and_quantum_low_degree_tests.tex:997-1008`; blueprint
`ch13_qpbt_test.tex:310-354` and `rem:deg-line-representatives`. -/
def contentOfLine (P : AdmissibleParams) (W : PauliKind)
    (line : LineDesc P.toLdParams) : PauliSpace P :=
  embedLd P W fun i =>
    match i with
    | .inl (.inl j) => line.base j
    | .inl (.inr _) => line.seed
    | .inr j =>
        match line with
        | .axis _ _ _ => 0
        | .diagonal _ _ direction _ _ => direction j

/-- Fill the point, scalar, and phase blocks shared by Pair, Pair/W, and Magic
Square questions. This is the type-4 content of
`def:pauli-question-distribution`, paper
`08_classical_and_quantum_low_degree_tests.tex:1030-1120`, blueprint
`ch13_qpbt_test.tex:310-354`. -/
def contentOfTuple (P : AdmissibleParams)
    (uX uZ : Fin P.m → PauliScalar P) (rX rZ : PauliScalar P) : PauliSpace P :=
  fun i =>
    match i with
    | .inl (.inl (.inl (.inl (.inl j)))) => uX j
    | .inl (.inl (.inl (.inl (.inr j)))) => uZ j
    | .inl (.inl (.inl (.inr _))) => 0
    | .inl (.inl (.inr _)) => 0
    | .inl (.inr _) => rX
    | .inr _ => rZ

/-- The typed point question in basis `W`, from the strategy notation at paper
`14_analysis_of_the_pauli_basis_test.tex:174-190` and
`def:pauli-question-distribution`, blueprint `ch13_qpbt_test.tex:310-354`. -/
def pointQuestion (P : AdmissibleParams) (W : PauliKind)
    (u : Fin P.m → PauliScalar P) : PauliQuestion P :=
  (.point W, contentOfPoint P W u)

/-- The typed axis or diagonal line question represented by a canonical
`LineDesc`. Paper `14_analysis_of_the_pauli_basis_test.tex:174-184`; blueprint
`def:strategy-observables` and `rem:deg-line-representatives`. -/
def lineQuestion (P : AdmissibleParams) (W : PauliKind)
    (line : LineDesc P.toLdParams) : PauliQuestion P :=
  match line.kind with
  | .axis => (.aline W, contentOfLine P W line)
  | .diagonal => (.dline W, contentOfLine P W line)

/-- The typed Pair question for a tuple `(u_X,u_Z,r_X,r_Z)`. Paper
`14_analysis_of_the_pauli_basis_test.tex:210-249`; blueprint
`lem:qld-win-implications`. -/
def pairQuestion (P : AdmissibleParams)
    (uX uZ : Fin P.m → PauliScalar P) (rX rZ : PauliScalar P) : PauliQuestion P :=
  (.pair, contentOfTuple P uX uZ rX rZ)

/-- The typed Pair/W question for a tuple `(u_X,u_Z,r_X,r_Z)`. Paper
`14_analysis_of_the_pauli_basis_test.tex:210-249`; blueprint
`lem:qld-win-implications`. -/
def pairWQuestion (P : AdmissibleParams) (W : PauliKind)
    (uX uZ : Fin P.m → PauliScalar P) (rX rZ : PauliScalar P) : PauliQuestion P :=
  (.pairW W, contentOfTuple P uX uZ rX rZ)

/-- The typed Magic Square question for a tuple `(u_X,u_Z,r_X,r_Z)`. Paper
`14_analysis_of_the_pauli_basis_test.tex:213-258`; blueprint
`lem:qld-win-implications`. -/
def msQuestion (P : AdmissibleParams) (t : MsType)
    (uX uZ : Fin P.m → PauliScalar P) (rX rZ : PauliScalar P) : PauliQuestion P :=
  (.ms t, contentOfTuple P uX uZ rX rZ)

/-- A typed question occurs in the Pauli-test distribution when it is the first
or second component of a question pair in the support. This is the support
condition satisfied by the typed question embeddings; blueprint
`def:pauli-question-distribution`, `ch13_qpbt_test.tex:310-354`, paper
`08_classical_and_quantum_low_degree_tests.tex:964-1120`. -/
def QuestionAppearsInSupport (P : AdmissibleParams) (question : PauliQuestion P) : Prop :=
  ∃ other : PauliQuestion P,
    (question, other) ∈ (pauliQuestionDistribution P).support ∨
      (other, question) ∈ (pauliQuestionDistribution P).support

/-- Point embeddings occur in the typed Pauli question support. This is the
support well-formedness companion to `def:pauli-question-distribution`,
blueprint `ch13_qpbt_test.tex:310-354`, paper
`08_classical_and_quantum_low_degree_tests.tex:997-1008`. -/
theorem pointQuestion_appears_in_support (P : AdmissibleParams) (W : PauliKind)
    (u : Fin P.m → PauliScalar P) :
    QuestionAppearsInSupport P (pointQuestion P W u) := by
  sorry

/-- Canonical axis and diagonal line embeddings occur in the typed Pauli
question support. This is the line companion to
`def:pauli-question-distribution`, blueprint `ch13_qpbt_test.tex:310-354`,
paper `08_classical_and_quantum_low_degree_tests.tex:997-1008`. -/
theorem lineQuestion_appears_in_support (P : AdmissibleParams) (W : PauliKind)
    (line : LineDesc P.toLdParams) :
    QuestionAppearsInSupport P (lineQuestion P W line) := by
  sorry

/-- Pair embeddings occur in the typed Pauli question support. This is the
Pair companion to `def:pauli-question-distribution`, blueprint
`ch13_qpbt_test.tex:310-354`, paper
`08_classical_and_quantum_low_degree_tests.tex:1030-1057`. -/
theorem pairQuestion_appears_in_support (P : AdmissibleParams)
    (uX uZ : Fin P.m → PauliScalar P) (rX rZ : PauliScalar P) :
    QuestionAppearsInSupport P (pairQuestion P uX uZ rX rZ) := by
  sorry

/-- Pair/W embeddings occur in the typed Pauli question support. This is the
Pair/W companion to `def:pauli-question-distribution`, blueprint
`ch13_qpbt_test.tex:310-354`, paper
`08_classical_and_quantum_low_degree_tests.tex:1030-1057`. -/
theorem pairWQuestion_appears_in_support (P : AdmissibleParams) (W : PauliKind)
    (uX uZ : Fin P.m → PauliScalar P) (rX rZ : PauliScalar P) :
    QuestionAppearsInSupport P (pairWQuestion P W uX uZ rX rZ) := by
  sorry

/-- Magic Square embeddings occur in the typed Pauli question support. This is
the Magic Square companion to `def:pauli-question-distribution`, blueprint
`ch13_qpbt_test.tex:310-354`, paper
`08_classical_and_quantum_low_degree_tests.tex:1059-1120`. -/
theorem msQuestion_appears_in_support (P : AdmissibleParams) (t : MsType)
    (uX uZ : Fin P.m → PauliScalar P) (rX rZ : PauliScalar P) :
    QuestionAppearsInSupport P (msQuestion P t uX uZ rX rZ) := by
  sorry

/-- Pauli/W embeddings occur in the typed Pauli question support. This is the
zero-content companion to `def:pauli-question-distribution`, blueprint
`ch13_qpbt_test.tex:310-354`, paper
`08_classical_and_quantum_low_degree_tests.tex:1006-1008`. -/
theorem pauliQuestion_appears_in_support (P : AdmissibleParams) (W : PauliKind) :
    QuestionAppearsInSupport P (MIPStarRE.QPBT.pauliQuestion P W) := by
  sorry

/-- Fold every non-point answer into the fixed point answer `0`. This realizes
the typed point family without adding a bottom outcome; wrong-form mass remains
visible through `wrongFormEffect`. Paper
`14_analysis_of_the_pauli_basis_test.tex:174-190`; blueprint
`def:strategy-observables`. -/
def pointAnswerOrZero {P : AdmissibleParams} : PauliAnswer P → PauliScalar P
  | .value a => a
  | _ => 0

/-- Fold every answer not prescribed for `line` into the zero coefficient
list. Axis answers are padded from degree `d` to degree `m*d`. This realizes
the coefficient convention of `def:ideg-deg-polynomials`, paper
`14_analysis_of_the_pauli_basis_test.tex:51-62`, blueprint
`ch14_qpbt_observables.tex:51-118`. -/
def lineAnswerOrZero (P : AdmissibleParams) (line : LineDesc P.toLdParams) :
    PauliAnswer P → DegPoly P.toLdParams (P.m * P.d) :=
  match line with
  | .axis _ _ _ => fun answer =>
      match answer with
      | .alinePoly f =>
          DegPoly.padTo (Nat.le_mul_of_pos_left P.d (Nat.zero_lt_of_lt P.one_le_m)) f
      | _ => 0
  | .diagonal _ _ _ _ _ => fun answer =>
      match answer with
      | .dlinePoly f => f
      | _ => 0

/-- Fold every non-Pair answer into `(0,0)`. This is the complete typed Pair
family used in items 4 and 6 of `lem:qld-win-implications`, paper
`14_analysis_of_the_pauli_basis_test.tex:210-258`. -/
def pairAnswerOrZero {P : AdmissibleParams} : PauliAnswer P → ZMod 2 × ZMod 2
  | .pairBits bits => bits
  | _ => (0, 0)

/-- Fold every non-Pair/W answer into bit `0`. This is the complete typed
Pair/W family used in items 4 and 7 of `lem:qld-win-implications`, paper
`14_analysis_of_the_pauli_basis_test.tex:210-263`. -/
def pairWAnswerOrZero {P : AdmissibleParams} : PauliAnswer P → ZMod 2
  | .bit bit => bit
  | _ => 0

/-- Fold wrong-form Pauli-test answers into a fixed valid Magic Square answer
of the requested question type. This supplies the typed families needed for an
actual `Strategy msGame`; paper
`14_analysis_of_the_pauli_basis_test.tex:213-258`, blueprint
`lem:qld-win-implications`. -/
def msAnswerOrZero {P : AdmissibleParams} (t : MsType) : PauliAnswer P → MsAnswer :=
  match t with
  | .constraint _ => fun answer =>
      match answer with
      | .msTriple bits => .triple bits
      | _ => .triple 0
  | .var _ => fun answer =>
      match answer with
      | .bit bit => .bit bit
      | _ => .bit 0

/-- The complete typed point measurement on one player side. It is the
corresponding strategy measurement postprocessed by `pointAnswerOrZero`; paper
`14_analysis_of_the_pauli_basis_test.tex:174-190`, blueprint
`def:strategy-observables`. -/
noncomputable def pointMeas (S : ProjectiveSetting P ε) (side : PlayerSide)
    (W : PauliKind) (u : Fin P.m → PauliScalar P) :
    Measurement (PauliScalar P) (S.LocalSpace side) :=
  (S.strategyMeasurement side (pointQuestion P W u)).postprocess pointAnswerOrZero

/-- The complete typed line measurement on one player side, uniformly indexed
by degree-`m*d` coefficient lists. Paper
`14_analysis_of_the_pauli_basis_test.tex:174-184`; blueprint
`def:ideg-deg-polynomials` and `lem:qld-win-implications`. -/
noncomputable def lineMeas (S : ProjectiveSetting P ε) (side : PlayerSide)
    (W : PauliKind) (line : LineDesc P.toLdParams) :
    Measurement (DegPoly P.toLdParams (P.m * P.d)) (S.LocalSpace side) :=
  (S.strategyMeasurement side (lineQuestion P W line)).postprocess
    (lineAnswerOrZero P line)

/-- The completed evaluation classes of a typed line measurement. This is the
only strategy-side family whose outcome uses `Option`; `none` is precisely the
non-evaluating class of `def:ideg-deg-polynomials`, paper
`14_analysis_of_the_pauli_basis_test.tex:51-62`, blueprint
`ch14_qpbt_observables.tex:51-118`. -/
noncomputable def lineEvalMeas (S : ProjectiveSetting P ε) (side : PlayerSide)
    (W : PauliKind) (line : LineDesc P.toLdParams)
    (u : Fin P.m → PauliScalar P) :
    Measurement (Option (PauliScalar P)) (S.LocalSpace side) :=
  (S.lineMeas side W line).postprocess (evalOpt line u)

/-- The complete typed Pair measurement on one player side. Paper
`14_analysis_of_the_pauli_basis_test.tex:210-249`; blueprint
`lem:qld-win-implications`. -/
noncomputable def pairMeas (S : ProjectiveSetting P ε) (side : PlayerSide)
    (uX uZ : Fin P.m → PauliScalar P) (rX rZ : PauliScalar P) :
    Measurement (ZMod 2 × ZMod 2) (S.LocalSpace side) :=
  (S.strategyMeasurement side (pairQuestion P uX uZ rX rZ)).postprocess pairAnswerOrZero

/-- The complete typed Pair/W measurement on one player side. Paper
`14_analysis_of_the_pauli_basis_test.tex:210-263`; blueprint
`lem:qld-win-implications`. -/
noncomputable def pairWMeas (S : ProjectiveSetting P ε) (side : PlayerSide)
    (W : PauliKind) (uX uZ : Fin P.m → PauliScalar P)
    (rX rZ : PauliScalar P) : Measurement (ZMod 2) (S.LocalSpace side) :=
  (S.strategyMeasurement side (pairWQuestion P W uX uZ rX rZ)).postprocess
    pairWAnswerOrZero

/-- The complete typed Pauli/W measurement on one player side. Paper
`14_analysis_of_the_pauli_basis_test.tex:205-209`; blueprint
`lem:qld-win-implications`. -/
noncomputable def pauliMeas (S : ProjectiveSetting P ε) (side : PlayerSide)
    (W : PauliKind) : Measurement (PauliRegister P) (S.LocalSpace side) :=
  (S.strategyMeasurement side (pauliQuestion P W)).postprocess pauliAnswerOrZero

/-- The complete typed Magic Square measurement on one player side. Its answer
alphabet is exactly `MsAnswer`; these families therefore define a Magic Square
strategy. Paper `14_analysis_of_the_pauli_basis_test.tex:213-258`;
blueprint `lem:qld-win-implications`. -/
noncomputable def msMeas (S : ProjectiveSetting P ε) (side : PlayerSide)
    (t : MsType) (uX uZ : Fin P.m → PauliScalar P)
    (rX rZ : PauliScalar P) : Measurement MsAnswer (S.LocalSpace side) :=
  (S.strategyMeasurement side (msQuestion P t uX uZ rX rZ)).postprocess
    (msAnswerOrZero t)

/-- The sum of effects corresponding to answers that are invalid for a given
question type. This mass is kept separate from the fixed valid outcome into
which typed postprocessing folds it. Paper
`08_classical_and_quantum_low_degree_tests.tex:1126-1225`, blueprint
`def:pauli-win-predicate`. -/
noncomputable def wrongFormEffect {ι : Type*} [Fintype ι] [DecidableEq ι]
    (t : PauliType) (M : Measurement (PauliAnswer P) ι) : Op ι :=
  ∑ answer ∈ Finset.univ.filter (fun answer => validPauliAnswer t answer = false),
    M.effect answer

/-- The average state-dependent wrong-form answer mass for one player. Since
the Pauli-test predicate rejects every wrong-form answer, the winning premise
bounds this quantity. Paper
`08_classical_and_quantum_low_degree_tests.tex:1126-1225`, used at paper
`14_analysis_of_the_pauli_basis_test.tex:197-266`; blueprint
`lem:qld-win-implications`. -/
noncomputable def wrongFormMass (S : ProjectiveSetting P ε) (side : PlayerSide) : ℝ :=
  avgOver (pauliQuestionDistribution P) fun questions =>
    match side with
    | .alice =>
        (inner ℂ S.toStrategy.ψ
          (applyOperatorToState
            (heteroKron
              (wrongFormEffect questions.1.1 (S.toStrategy.A questions.1)) 1)
            S.toStrategy.ψ)).re
    | .bob =>
        (inner ℂ S.toStrategy.ψ
          (applyOperatorToState
            (heteroKron 1
              (wrongFormEffect questions.2.1 (S.toStrategy.B questions.2)))
            S.toStrategy.ψ)).re

/-- The Alice-side wrong-form mass is at most the strategy's rejection
probability. Paper `08_classical_and_quantum_low_degree_tests.tex:1126-1225`, used at
`14_analysis_of_the_pauli_basis_test.tex:197-266`. -/
theorem wrongFormMass_alice_le_error (S : ProjectiveSetting P ε) :
    S.wrongFormMass .alice ≤ ε := by
  sorry

/-- The Bob-side wrong-form mass is at most the strategy's rejection
probability. Paper `08_classical_and_quantum_low_degree_tests.tex:1126-1225`, used at
`14_analysis_of_the_pauli_basis_test.tex:197-266`. -/
theorem wrongFormMass_bob_le_error (S : ProjectiveSetting P ε) :
    S.wrongFormMass .bob ≤ ε := by
  sorry

/-- The side-indexed strategy observable
`W^r(u) = sum_a (-1)^(tr(ar)) M_a^((Point,W),u)`. It uses the canonical
character `phaseSign` and the fixed trace of `P.model`. This is
`def:strategy-observables`, paper
`14_analysis_of_the_pauli_basis_test.tex:174-190`, blueprint
`ch14_qpbt_observables.tex:480-503`. -/
noncomputable def pointObs (S : ProjectiveSetting P ε) (side : PlayerSide)
    (W : PauliKind) (r : PauliScalar P) (u : Fin P.m → PauliScalar P) :
    Op (S.LocalSpace side) :=
  ∑ a : PauliScalar P,
    phaseSign (fixedBinTrace P.model (a * r)) • (S.pointMeas side W u).effect a

/-- The point observable squares to the identity. This is the assertion that
the operator in `def:strategy-observables` has eigenvalues in `{+1,-1}`;
paper `14_analysis_of_the_pauli_basis_test.tex:174-190`, blueprint
`ch14_qpbt_observables.tex:480-503`. -/
theorem pointObs_sq_eq_one (S : ProjectiveSetting P ε) (side : PlayerSide)
    (W : PauliKind) (r : PauliScalar P) (u : Fin P.m → PauliScalar P) :
    S.pointObs side W r u * S.pointObs side W r u = 1 := by
  sorry

/-- The point observable is Hermitian. This is the self-adjoint part of the
observable assertion following `eq:qld-strat-obs`, paper
`14_analysis_of_the_pauli_basis_test.tex:174-190`, blueprint
`def:strategy-observables`. -/
theorem pointObs_isHermitian (S : ProjectiveSetting P ε) (side : PlayerSide)
    (W : PauliKind) (r : PauliScalar P) (u : Fin P.m → PauliScalar P) :
    (S.pointObs side W r u).IsHermitian := by
  sorry

end ProjectiveSetting

end

end MIPStarRE.QPBT
