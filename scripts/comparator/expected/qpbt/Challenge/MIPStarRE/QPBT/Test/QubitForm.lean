import Mathlib
import Challenge.MIPStarRE.QPBT.Algebra.PauliTheorems
import Challenge.MIPStarRE.QPBT.Observables.WinImplications.Setup
import Challenge.MIPStarRE.QPBT.Test.LowDegreeGameMeasurements
import Challenge.MIPStarRE.QPBT.Test.SoundnessDefs

/-! Challenge mirror of `MIPStarRE/QPBT/Test/QubitForm.lean`.

One challenge module per contributing library module, importing the
mirrors of the library modules this one imports.  The partition is
what makes Lean generate the same auxiliary declarations, under the
same names, as the library does. -/

open scoped BigOperators MatrixOrder Matrix ComplexOrder
namespace MIPStarRE.QPBT

-- elaboration context of MIPStarRE/QPBT/Test/QubitForm.lean:35-447
noncomputable section
open MIPStarRE.LDT MIPStarRE.Quantum

-- source: MIPStarRE/QPBT/Test/QubitForm.lean:37-40  (MIPStarRE.QPBT.QubitRegister)
/-- The bit register obtained by expanding every Pauli-register field element
in the basis stored by `P.model`. -/
abbrev QubitRegister (P : AdmissibleParams) :=
  Cube P.m × Fin P.model.basisDim → ZMod 2

-- source: MIPStarRE/QPBT/Test/QubitForm.lean:42-55  (MIPStarRE.QPBT.idealQubitState)
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

-- source: MIPStarRE/QPBT/Test/QubitForm.lean:57-73  (MIPStarRE.QPBT.QubitSoundnessWitness)
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

-- source: MIPStarRE/QPBT/Test/QubitForm.lean (attribute command)
attribute [instance] QubitSoundnessWitness.ιAFintype
  QubitSoundnessWitness.ιBFintype QubitSoundnessWitness.ιADecidableEq
  QubitSoundnessWitness.ιBDecidableEq

-- source: MIPStarRE/QPBT/Test/QubitForm.lean:79-88  (MIPStarRE.QPBT.qubitProjOnA'')
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

-- source: MIPStarRE/QPBT/Test/QubitForm.lean:90-99  (MIPStarRE.QPBT.qubitProjOnB'')
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

-- source: MIPStarRE/QPBT/Test/QubitForm.lean:101-109  (MIPStarRE.QPBT.liftedQubitAEffect)
/-- Lift a conjugated Alice effect to the full qubit target space. -/
noncomputable def liftedQubitAEffect {P : AdmissibleParams} {G : Game}
    (S : Strategy G) {ιA' ιB' : Type*} [Fintype ιA'] [DecidableEq ιA']
    [Fintype ιB'] [DecidableEq ιB']
    (φA : EuclideanSpace ℂ S.ιA →ₗᵢ[ℂ]
      EuclideanSpace ℂ (ιA' × QubitRegister P))
    (M : Op S.ιA) :
    Op ((ιA' × QubitRegister P) × (ιB' × QubitRegister P)) :=
  heteroKron (conjIsometry φA M) 1

-- source: MIPStarRE/QPBT/Test/QubitForm.lean:111-119  (MIPStarRE.QPBT.liftedQubitBEffect)
/-- Lift a conjugated Bob effect to the full qubit target space. -/
noncomputable def liftedQubitBEffect {P : AdmissibleParams} {G : Game}
    (S : Strategy G) {ιA' ιB' : Type*} [Fintype ιA'] [DecidableEq ιA']
    [Fintype ιB'] [DecidableEq ιB']
    (φB : EuclideanSpace ℂ S.ιB →ₗᵢ[ℂ]
      EuclideanSpace ℂ (ιB' × QubitRegister P))
    (M : Op S.ιB) :
    Op ((ιA' × QubitRegister P) × (ιB' × QubitRegister P)) :=
  heteroKron 1 (conjIsometry φB M)

-- source: MIPStarRE/QPBT/Test/QubitForm.lean:121-130  (MIPStarRE.QPBT.qubitOperatorDistanceA)
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

-- source: MIPStarRE/QPBT/Test/QubitForm.lean:132-141  (MIPStarRE.QPBT.qubitOperatorDistanceB)
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
end  -- module scope
end MIPStarRE.QPBT
