import MIPStarRE.QPBT.Games.StrategyClasses
import MIPStarRE.QPBT.Games.DistanceTheorems.Support
import MIPStarRE.QPBT.Games.Sandwich.Support
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

open MIPStarRE.LDT hiding Measurement
open MIPStarRE.Quantum

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

/-- Reading a low-degree vector immediately after embedding it in either Pauli
basis recovers the original vector. -/
private theorem pauliToLd_embedLd (P : AdmissibleParams) (W : PauliKind)
    (z : LdSpace P.toLdParams) :
    pauliToLd P W (embedLd P W z) = z := by
  funext i
  rcases i with ((j | x) | j) <;> cases W <;> rfl

-- The support rewrites below elaborate the `Fintype` instance of
-- `PauliEdge × PauliSpace P`, whose nested sigma/sum instance chain exceeds the
-- default recursion depth.
set_option maxRecDepth 2000 in
/-- A fixed point of a conditioning map occurs in the Pauli sampler through
the corresponding self-loop. -/
private theorem questionAppearsInSupport_of_fixed (P : AdmissibleParams)
    (t : PauliType) (z : PauliSpace P) (hfixed : pauliCL P t z = z) :
    QuestionAppearsInSupport P (t, z) := by
  classical
  letI : Nonempty PauliEdge := pauliEdge_nonempty
  let edge : PauliEdge := ⟨(t, t), by simp [pauliEdges]⟩
  let sample : PauliEdge × PauliSpace P := (edge, z)
  refine ⟨(t, z), Or.inl ?_⟩
  rw [pauliQuestionDistribution, Distribution.map_support]
  have hsample : sample ∈ (uniformDistribution (PauliEdge × PauliSpace P)).support := by
    rw [uniformDistribution_support]
    exact Finset.mem_univ sample
  have himage := Finset.mem_image_of_mem
    (fun s : PauliEdge × PauliSpace P =>
      ((s.1.1.1, pauliCL P s.1.1.1 s.2),
        (s.1.1.2, pauliCL P s.1.1.2 s.2)))
    hsample
  simpa only [sample, edge, hfixed] using himage

/-- Point embeddings occur in the typed Pauli question support. This is the
support well-formedness companion to `def:pauli-question-distribution`,
blueprint `ch13_qpbt_test.tex:310-354`, paper
`08_classical_and_quantum_low_degree_tests.tex:997-1008`. -/
theorem pointQuestion_appears_in_support (P : AdmissibleParams) (W : PauliKind)
    (u : Fin P.m → PauliScalar P) :
    QuestionAppearsInSupport P (pointQuestion P W u) := by
  apply questionAppearsInSupport_of_fixed P (.point W) (contentOfPoint P W u)
  funext i
  rcases i with ((((j | j) | x) | j) | x) | x <;> cases W <;> rfl

/-- Canonical axis and diagonal line embeddings occur in the typed Pauli
question support. This is the line companion to
`def:pauli-question-distribution`, blueprint `ch13_qpbt_test.tex:310-354`,
paper `08_classical_and_quantum_low_degree_tests.tex:997-1008`. -/
theorem lineQuestion_appears_in_support (P : AdmissibleParams) (W : PauliKind)
    (line : LineDesc P.toLdParams) :
    QuestionAppearsInSupport P (lineQuestion P W line) := by
  cases line with
  | axis base seed baseFixed =>
      apply questionAppearsInSupport_of_fixed P (.aline W)
        (contentOfLine P W (.axis base seed baseFixed))
      let z : LdSpace P.toLdParams := fun i =>
        match i with
        | .inl (.inl j) => base j
        | .inl (.inr _) => seed
        | .inr _ => 0
      change pauliCL P (.aline W) (embedLd P W z) = embedLd P W z
      dsimp only [pauliCL]
      rw [pauliToLd_embedLd]
      apply congrArg (embedLd P W)
      funext i
      rcases i with ((j | x) | j)
      · exact congrFun baseFixed j
      · rfl
      · rfl
  | diagonal base seed direction baseFixed prefixZero =>
      apply questionAppearsInSupport_of_fixed P (.dline W)
        (contentOfLine P W (.diagonal base seed direction baseFixed prefixZero))
      let z : LdSpace P.toLdParams := fun i =>
        match i with
        | .inl (.inl j) => base j
        | .inl (.inr _) => seed
        | .inr j => direction j
      change pauliCL P (.dline W) (embedLd P W z) = embedLd P W z
      dsimp only [pauliCL]
      rw [pauliToLd_embedLd]
      have hprojection :
          prefixProjection (chiIndex P.toLdParams seed) direction = direction := by
        funext j
        by_cases hj : j.val < (chiIndex P.toLdParams seed).val
        · simp [prefixProjection, hj, prefixZero j hj]
        · simp [prefixProjection, hj]
      apply congrArg (embedLd P W)
      funext i
      rcases i with ((j | x) | j)
      · change (lineRepMap (prefixProjection (chiIndex P.toLdParams seed) direction)
            base) j = base j
        rw [hprojection]
        exact congrFun baseFixed j
      · rfl
      · exact congrFun hprojection j

/-- Pair embeddings occur in the typed Pauli question support. This is the
Pair companion to `def:pauli-question-distribution`, blueprint
`ch13_qpbt_test.tex:310-354`, paper
`08_classical_and_quantum_low_degree_tests.tex:1030-1057`. -/
theorem pairQuestion_appears_in_support (P : AdmissibleParams)
    (uX uZ : Fin P.m → PauliScalar P) (rX rZ : PauliScalar P) :
    QuestionAppearsInSupport P (pairQuestion P uX uZ rX rZ) := by
  apply questionAppearsInSupport_of_fixed P .pair (contentOfTuple P uX uZ rX rZ)
  funext i
  rcases i with ((((j | j) | x) | j) | x) | x <;> rfl

/-- Pair/W embeddings occur in the typed Pauli question support. This is the
Pair/W companion to `def:pauli-question-distribution`, blueprint
`ch13_qpbt_test.tex:310-354`, paper
`08_classical_and_quantum_low_degree_tests.tex:1030-1057`. -/
theorem pairWQuestion_appears_in_support (P : AdmissibleParams) (W : PauliKind)
    (uX uZ : Fin P.m → PauliScalar P) (rX rZ : PauliScalar P) :
    QuestionAppearsInSupport P (pairWQuestion P W uX uZ rX rZ) := by
  apply questionAppearsInSupport_of_fixed P (.pairW W) (contentOfTuple P uX uZ rX rZ)
  funext i
  rcases i with ((((j | j) | x) | j) | x) | x <;> rfl

/-- Magic Square embeddings occur in the typed Pauli question support. This is
the Magic Square companion to `def:pauli-question-distribution`, blueprint
`ch13_qpbt_test.tex:310-354`, paper
`08_classical_and_quantum_low_degree_tests.tex:1059-1120`. -/
theorem msQuestion_appears_in_support (P : AdmissibleParams) (t : MsType)
    (uX uZ : Fin P.m → PauliScalar P) (rX rZ : PauliScalar P) :
    QuestionAppearsInSupport P (msQuestion P t uX uZ rX rZ) := by
  apply questionAppearsInSupport_of_fixed P (.ms t) (contentOfTuple P uX uZ rX rZ)
  funext i
  rcases i with ((((j | j) | x) | j) | x) | x <;> rfl

/-- Pauli/W embeddings occur in the typed Pauli question support. This is the
zero-content companion to `def:pauli-question-distribution`, blueprint
`ch13_qpbt_test.tex:310-354`, paper
`08_classical_and_quantum_low_degree_tests.tex:1006-1008`. -/
theorem pauliQuestion_appears_in_support (P : AdmissibleParams) (W : PauliKind) :
    QuestionAppearsInSupport P (MIPStarRE.QPBT.pauliQuestion P W) := by
  apply questionAppearsInSupport_of_fixed P (.pauli W) 0
  rfl

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

/-- Expand the Alice wrong-form effect into its joint Born weights. -/
private theorem leftWrongFormEffectMass_eq {P : AdmissibleParams}
    (S : Strategy (pauliBasisTest P))
    (questions : (pauliBasisTest P).QuestionA × (pauliBasisTest P).QuestionB) :
    (inner ℂ S.ψ
      (applyOperatorToState
        (heteroKron (wrongFormEffect questions.1.1 (S.A questions.1)) 1)
        S.ψ)).re =
      ∑ a ∈ Finset.univ.filter
          (fun a => validPauliAnswer questions.1.1 a = false),
        ∑ b, outcomeWeight S questions.1 questions.2 a b := by
  classical
  exact leftEffectMass_eq S questions.1 questions.2
    (validPauliAnswer questions.1.1)

/-- Expand the Bob wrong-form effect into its joint Born weights. -/
private theorem rightWrongFormEffectMass_eq {P : AdmissibleParams}
    (S : Strategy (pauliBasisTest P))
    (questions : (pauliBasisTest P).QuestionA × (pauliBasisTest P).QuestionB) :
    (inner ℂ S.ψ
      (applyOperatorToState
        (heteroKron 1 (wrongFormEffect questions.2.1 (S.B questions.2)))
        S.ψ)).re =
      ∑ a, ∑ b ∈ Finset.univ.filter
          (fun b => validPauliAnswer questions.2.1 b = false),
        outcomeWeight S questions.1 questions.2 a b := by
  classical
  exact rightEffectMass_eq S questions.1 questions.2
    (validPauliAnswer questions.2.1)

/-- Alice's wrong-form mass at fixed questions is part of the rejection mass. -/
private theorem leftInvalidMass_le_rejection {P : AdmissibleParams}
    (S : Strategy (pauliBasisTest P))
    (questions : (pauliBasisTest P).QuestionA × (pauliBasisTest P).QuestionB) :
    (∑ a ∈ Finset.univ.filter
        (fun a => validPauliAnswer questions.1.1 a = false),
      ∑ b, outcomeWeight S questions.1 questions.2 a b) ≤
    ∑ a, ∑ b,
      if (pauliBasisTest P).decide questions.1 questions.2 a b then 0
      else outcomeWeight S questions.1 questions.2 a b := by
  classical
  rcases questions with ⟨⟨tA, xA⟩, ⟨tB, xB⟩⟩
  let invalid := Finset.univ.filter
    (fun a : (pauliBasisTest P).AnswerA => validPauliAnswer tA a = false)
  calc
    (∑ a ∈ invalid, ∑ b, outcomeWeight S (tA, xA) (tB, xB) a b) =
        ∑ a ∈ invalid, ∑ b,
          if (pauliBasisTest P).decide (tA, xA) (tB, xB) a b then 0
          else outcomeWeight S (tA, xA) (tB, xB) a b := by
      apply Finset.sum_congr rfl
      intro a ha
      apply Finset.sum_congr rfl
      intro b hb
      have hvalid := (Finset.mem_filter.mp ha).2
      have hdecide :
          (pauliBasisTest P).decide (tA, xA) (tB, xB) a b = false := by
        change pauliWinPredicate P (tA, xA) (tB, xB) a b = false
        simp [pauliWinPredicate, hvalid]
      simp [hdecide]
    _ ≤ ∑ a, ∑ b,
        if (pauliBasisTest P).decide (tA, xA) (tB, xB) a b then 0
        else outcomeWeight S (tA, xA) (tB, xB) a b := by
      apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      intro a ha haInvalid
      apply Finset.sum_nonneg
      intro b hb
      split <;> simp [outcomeWeight_nonneg]

/-- Bob's wrong-form mass at fixed questions is part of the rejection mass. -/
private theorem rightInvalidMass_le_rejection {P : AdmissibleParams}
    (S : Strategy (pauliBasisTest P))
    (questions : (pauliBasisTest P).QuestionA × (pauliBasisTest P).QuestionB) :
    (∑ a, ∑ b ∈ Finset.univ.filter
        (fun b => validPauliAnswer questions.2.1 b = false),
      outcomeWeight S questions.1 questions.2 a b) ≤
    ∑ a, ∑ b,
      if (pauliBasisTest P).decide questions.1 questions.2 a b then 0
      else outcomeWeight S questions.1 questions.2 a b := by
  classical
  rcases questions with ⟨⟨tA, xA⟩, ⟨tB, xB⟩⟩
  let invalid := Finset.univ.filter
    (fun b : (pauliBasisTest P).AnswerB => validPauliAnswer tB b = false)
  apply Finset.sum_le_sum
  intro a ha
  calc
    (∑ b ∈ invalid, outcomeWeight S (tA, xA) (tB, xB) a b) =
        ∑ b ∈ invalid,
          if (pauliBasisTest P).decide (tA, xA) (tB, xB) a b then 0
          else outcomeWeight S (tA, xA) (tB, xB) a b := by
      apply Finset.sum_congr rfl
      intro b hb
      have hvalid := (Finset.mem_filter.mp hb).2
      have hdecide :
          (pauliBasisTest P).decide (tA, xA) (tB, xB) a b = false := by
        change pauliWinPredicate P (tA, xA) (tB, xB) a b = false
        simp [pauliWinPredicate, hvalid]
      simp [hdecide]
    _ ≤ ∑ b,
        if (pauliBasisTest P).decide (tA, xA) (tB, xB) a b then 0
        else outcomeWeight S (tA, xA) (tB, xB) a b := by
      apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      intro b hb hbInvalid
      split <;> simp [outcomeWeight_nonneg]

/-- Wrong-form mass on either player side is bounded by the winning error. -/
private theorem wrongFormMass_le_error (S : ProjectiveSetting P ε)
    (side : PlayerSide) : S.wrongFormMass side ≤ ε := by
  classical
  have hmass : S.wrongFormMass side ≤ 1 - S.toStrategy.value := by
    calc
      S.wrongFormMass side ≤
          avgOver (pauliBasisTest P).μ (fun questions =>
            ∑ a, ∑ b,
              if (pauliBasisTest P).decide questions.1 questions.2 a b then 0
              else outcomeWeight S.toStrategy questions.1 questions.2 a b) := by
        apply avgOver_mono
        intro questions
        cases side with
        | alice =>
            simp only
            rw [leftWrongFormEffectMass_eq S.toStrategy questions]
            exact leftInvalidMass_le_rejection S.toStrategy questions
        | bob =>
            simp only
            rw [rightWrongFormEffectMass_eq S.toStrategy questions]
            exact rightInvalidMass_le_rejection S.toStrategy questions
      _ = 1 - S.toStrategy.value := rejectionMass_eq_one_sub_value S.toStrategy
  linarith [S.win]

/-- The Alice-side wrong-form mass is at most the strategy's rejection
probability. Paper `08_classical_and_quantum_low_degree_tests.tex:1126-1225`, used at
`14_analysis_of_the_pauli_basis_test.tex:197-266`. -/
theorem wrongFormMass_alice_le_error (S : ProjectiveSetting P ε) :
    S.wrongFormMass .alice ≤ ε := by
  exact wrongFormMass_le_error S .alice

/-- The Bob-side wrong-form mass is at most the strategy's rejection
probability. Paper `08_classical_and_quantum_low_degree_tests.tex:1126-1225`, used at
`14_analysis_of_the_pauli_basis_test.tex:197-266`. -/
theorem wrongFormMass_bob_le_error (S : ProjectiveSetting P ε) :
    S.wrongFormMass .bob ≤ ε := by
  exact wrongFormMass_le_error S .bob

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

/-- Select projectivity of the strategy POVM on either local space. -/
private theorem strategyMeasurement_isProjective
    (S : ProjectiveSetting P ε) (side : PlayerSide) (question : PauliQuestion P) :
    Measurement.IsProjective (S.strategyMeasurement side question) := by
  cases side with
  | alice => exact S.isProjective.1 question
  | bob => exact S.isProjective.2 question

/-- The typed point measurement remains projective after answer folding. -/
theorem pointMeas_isProjective (S : ProjectiveSetting P ε)
    (side : PlayerSide) (W : PauliKind) (u : Fin P.m → PauliScalar P) :
    Measurement.IsProjective (S.pointMeas side W u) := by
  apply SandwichProduct.postprocess_isProjective
  exact strategyMeasurement_isProjective S side _

/-- The point observables form an additive representation, as follows from
`eq:qld-strat-obs`, paper `14_analysis_of_the_pauli_basis_test.tex:174-190`.
This multiplication law is a formalization-only consequence of that definition. -/
theorem pointObs_mul (S : ProjectiveSetting P ε) (side : PlayerSide)
    (W : PauliKind) (r s : PauliScalar P)
    (u : Fin P.m → PauliScalar P) :
    S.pointObs side W r u * S.pointObs side W s u =
      S.pointObs side W (r + s) u := by
  classical
  let M := S.pointMeas side W u
  have hM : Measurement.IsProjective M := pointMeas_isProjective S side W u
  change (∑ a : PauliScalar P,
      phaseSign (fixedBinTrace P.model (a * r)) • M.effect a) *
      (∑ a : PauliScalar P,
        phaseSign (fixedBinTrace P.model (a * s)) • M.effect a) =
    ∑ a : PauliScalar P,
      phaseSign (fixedBinTrace P.model (a * (r + s))) • M.effect a
  calc
    _ = ∑ a : PauliScalar P, ∑ b : PauliScalar P,
        (phaseSign (fixedBinTrace P.model (a * r)) *
          phaseSign (fixedBinTrace P.model (b * s))) •
            (M.effect a * M.effect b) := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro a ha
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro b hb
      rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul]
    _ = ∑ a : PauliScalar P,
        phaseSign (fixedBinTrace P.model (a * (r + s))) • M.effect a := by
      apply Finset.sum_congr rfl
      intro a ha
      rw [Finset.sum_eq_single a]
      · rw [(hM a).isIdempotentElem.eq]
        congr 1
        rw [mul_add, fixedBinTrace, map_add, phaseSign_add]
      · intro b hb hba
        have hab : a ≠ b := fun h => hba h.symm
        rw [DistanceCalculus.projective_effect_mul_effect_eq_zero M hM hab]
        simp
      · intro ha'
        exact (ha' (Finset.mem_univ a)).elim

/-- The zero-label point observable is the identity by measurement completeness. -/
theorem pointObs_zero (S : ProjectiveSetting P ε) (side : PlayerSide)
    (W : PauliKind) (u : Fin P.m → PauliScalar P) :
    S.pointObs side W 0 u = 1 := by
  classical
  simpa [pointObs, fixedBinTrace, phaseSign] using (S.pointMeas side W u).sum_eq_one

/-- The point observable squares to the identity. This is the assertion that
the operator in `def:strategy-observables` has eigenvalues in `{+1,-1}`;
paper `14_analysis_of_the_pauli_basis_test.tex:174-190`, blueprint
`ch14_qpbt_observables.tex:480-503`. -/
theorem pointObs_sq_eq_one (S : ProjectiveSetting P ε) (side : PlayerSide)
    (W : PauliKind) (r : PauliScalar P) (u : Fin P.m → PauliScalar P) :
    S.pointObs side W r u * S.pointObs side W r u = 1 := by
  haveI : CharP (PauliScalar P) 2 :=
    (Algebra.charP_iff (ZMod 2) (PauliScalar P) 2).mp (ZMod.charP 2)
  rw [pointObs_mul, CharTwo.add_self_eq_zero, pointObs_zero]

/-- The point observable is Hermitian. This is the self-adjoint part of the
observable assertion following `eq:qld-strat-obs`, paper
`14_analysis_of_the_pauli_basis_test.tex:174-190`, blueprint
`def:strategy-observables`. -/
theorem pointObs_isHermitian (S : ProjectiveSetting P ε) (side : PlayerSide)
    (W : PauliKind) (r : PauliScalar P) (u : Fin P.m → PauliScalar P) :
    (S.pointObs side W r u).IsHermitian := by
  classical
  rw [pointObs, Matrix.IsHermitian]
  rw [Matrix.conjTranspose_sum]
  apply Finset.sum_congr rfl
  intro a ha
  rw [Matrix.conjTranspose_smul, star_phaseSign]
  rw [(Matrix.nonneg_iff_posSemidef.mp
    ((S.pointMeas side W u).pos a)).isHermitian.eq]

end ProjectiveSetting

end

end MIPStarRE.QPBT
