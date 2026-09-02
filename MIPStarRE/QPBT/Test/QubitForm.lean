import MIPStarRE.QPBT.Algebra.PauliTheorems
import MIPStarRE.QPBT.Test.Soundness

/-!
# Qubit form of Pauli basis test soundness

The fixed self-dual normal basis converts the qudit EPR register and generalized
Pauli projectors into qubit coordinates. The conversion uses only the basis
stored in the canonical `FixedFieldModel`.

## References

The conversion is `lem:pauli-binary` in
`blueprint/src/chapter/ch11_qpbt_algebra.tex:675-708`, from
`references/qpbt-paper/04_preliminaries.tex:1163-1208`. The resulting
`cor:pauli-binary` is in `blueprint/src/chapter/ch13_qpbt_test.tex:409-435`,
from `references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:1450-1501`.
-/

open scoped BigOperators Matrix

namespace MIPStarRE.QPBT

open MIPStarRE.LDT MIPStarRE.Quantum

noncomputable section

/-- The bit register obtained by expanding every Pauli-register field element
in the basis stored by `P.model`. -/
abbrev QubitRegister (P : AdmissibleParams) :=
  Cube P.m × Fin P.model.basisDim → ZMod 2

/-- The ideal auxiliary state tensored with the qubit EPR register, in the
local-player ordering used by `cor:pauli-binary`. -/
noncomputable def idealQubitState (P : AdmissibleParams)
    {ιA' ιB' : Type*} [Fintype ιA'] [DecidableEq ιA']
    [Fintype ιB'] [DecidableEq ιB']
    (aux : EuclideanSpace ℂ (ιA' × ιB')) :
    EuclideanSpace ℂ
      ((ιA' × QubitRegister P) × (ιB' × QubitRegister P)) :=
  (EuclideanSpace.equiv
      ((ιA' × QubitRegister P) × (ιB' × QubitRegister P)) ℂ).symm
    (fun p =>
      (EuclideanSpace.equiv (ιA' × ιB') ℂ aux (p.1.1, p.2.1)) *
        (EuclideanSpace.equiv (QubitRegister P × QubitRegister P) ℂ
          (eprState (QubitRegister P)) (p.1.2, p.2.2)))

/-- The local isometries, auxiliary spaces, and unit auxiliary state in
`cor:pauli-binary`; this structure introduces no hypothesis beyond the paper
theorem. -/
structure QubitSoundnessWitness (P : AdmissibleParams)
    (S : Strategy (pauliBasisTest P)) where
  ιA' : Type
  ιB' : Type
  [ιAFintype : Fintype ιA']
  [ιBFintype : Fintype ιB']
  [ιADecidableEq : DecidableEq ιA']
  [ιBDecidableEq : DecidableEq ιB']
  φA : EuclideanSpace ℂ S.ιA →ₗᵢ[ℂ]
    EuclideanSpace ℂ (ιA' × QubitRegister P)
  φB : EuclideanSpace ℂ S.ιB →ₗᵢ[ℂ]
    EuclideanSpace ℂ (ιB' × QubitRegister P)
  aux : EuclideanSpace ℂ (ιA' × ιB')
  aux_norm : ‖aux‖ = 1

attribute [instance] QubitSoundnessWitness.ιAFintype
  QubitSoundnessWitness.ιBFintype QubitSoundnessWitness.ιADecidableEq
  QubitSoundnessWitness.ιBDecidableEq

/-- Alice's ideal qubit projector placed on the joint target space. -/
noncomputable def qubitProjOnA'' (P : AdmissibleParams)
    {ιA' ιB' : Type*} [Fintype ιA'] [DecidableEq ιA']
    [Fintype ιB'] [DecidableEq ιB'] (W : PauliKind)
    (u : PauliRegister P) :
    Op ((ιA' × QubitRegister P) × (ιB' × QubitRegister P)) :=
  fun p q =>
    if p.1.1 = q.1.1 ∧ p.2 = q.2 then
      qubitPauliProj W (kappaVec P.model u) p.1.2 q.1.2
    else 0

/-- Bob's ideal qubit projector placed on the joint target space. -/
noncomputable def qubitProjOnB'' (P : AdmissibleParams)
    {ιA' ιB' : Type*} [Fintype ιA'] [DecidableEq ιA']
    [Fintype ιB'] [DecidableEq ιB'] (W : PauliKind)
    (u : PauliRegister P) :
    Op ((ιA' × QubitRegister P) × (ιB' × QubitRegister P)) :=
  fun p q =>
    if p.1 = q.1 ∧ p.2.1 = q.2.1 then
      qubitPauliProj W (kappaVec P.model u) p.2.2 q.2.2
    else 0

/-- Lift a conjugated Alice effect to the full qubit target space. -/
noncomputable def liftedQubitAEffect {P : AdmissibleParams} {G : Game}
    (S : Strategy G) {ιA' ιB' : Type*} [Fintype ιA'] [DecidableEq ιA']
    [Fintype ιB'] [DecidableEq ιB']
    (φA : EuclideanSpace ℂ S.ιA →ₗᵢ[ℂ]
      EuclideanSpace ℂ (ιA' × QubitRegister P))
    (M : Op S.ιA) :
    Op ((ιA' × QubitRegister P) × (ιB' × QubitRegister P)) :=
  heteroKron (conjIsometry φA M) 1

/-- Lift a conjugated Bob effect to the full qubit target space. -/
noncomputable def liftedQubitBEffect {P : AdmissibleParams} {G : Game}
    (S : Strategy G) {ιA' ιB' : Type*} [Fintype ιA'] [DecidableEq ιA']
    [Fintype ιB'] [DecidableEq ιB']
    (φB : EuclideanSpace ℂ S.ιB →ₗᵢ[ℂ]
      EuclideanSpace ℂ (ιB' × QubitRegister P))
    (M : Op S.ιB) :
    Op ((ιA' × QubitRegister P) × (ιB' × QubitRegister P)) :=
  heteroKron 1 (conjIsometry φB M)

/-- Alice's qubit-projector family distance in `cor:pauli-binary`. -/
noncomputable def qubitOperatorDistanceA
    (P : AdmissibleParams) (S : Strategy (pauliBasisTest P))
    (w : QubitSoundnessWitness P S) (W : PauliKind) : ℝ :=
  ∑ u : PauliRegister P,
    ‖applyOperatorToState
      (liftedQubitAEffect S w.φA
          ((S.A (pauliQuestion P W)).effect (.pauliOutcome u)) -
        qubitProjOnA'' P W u)
      (idealQubitState P w.aux)‖ ^ 2

/-- Bob's qubit-projector family distance in `cor:pauli-binary`. -/
noncomputable def qubitOperatorDistanceB
    (P : AdmissibleParams) (S : Strategy (pauliBasisTest P))
    (w : QubitSoundnessWitness P S) (W : PauliKind) : ℝ :=
  ∑ u : PauliRegister P,
    ‖applyOperatorToState
      (liftedQubitBEffect S w.φB
          ((S.B (pauliQuestion P W)).effect (.pauliOutcome u)) -
        qubitProjOnB'' P W u)
      (idealQubitState P w.aux)‖ ^ 2

/-- `cor:pauli-binary`: soundness of the Pauli basis test in qubit
coordinates. Blueprint `ch13_qpbt_test.tex:409-435`, paper
`08_classical_and_quantum_low_degree_tests.tex:1450-1501`.

The theorem retains the source-compatible nonnegative error boundary and uses
only `P.model` and its stored basis dimension. -/
theorem pauli_soundness_qubit :
    ∃ a b : ℝ, 1 ≤ a ∧ 0 < b ∧ b < 1 ∧
      ∀ (P : AdmissibleParams) (ε : ℝ), 0 ≤ ε →
        ∀ S : Strategy (pauliBasisTest P), 1 - ε ≤ S.value →
          ∃ w : QubitSoundnessWitness P S,
            ‖isometryTensor w.φA w.φB S.ψ - idealQubitState P w.aux‖ ≤
                deltaQld a b ε P.m P.d P.q ∧
            (∀ W : PauliKind,
              qubitOperatorDistanceA P S w W ≤
                deltaQld a b ε P.m P.d P.q) ∧
            ∀ W : PauliKind,
              qubitOperatorDistanceB P S w W ≤
                deltaQld a b ε P.m P.d P.q := by
  sorry

end

end MIPStarRE.QPBT
