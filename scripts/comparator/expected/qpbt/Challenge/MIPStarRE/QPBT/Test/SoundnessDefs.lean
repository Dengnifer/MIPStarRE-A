import Mathlib
import Challenge.MIPStarRE.QPBT.State
import Challenge.MIPStarRE.QPBT.Test.PauliBasisTest

/-! Challenge mirror of `MIPStarRE/QPBT/Test/SoundnessDefs.lean`.

One challenge module per contributing library module, importing the
mirrors of the library modules this one imports.  The partition is
what makes Lean generate the same auxiliary declarations, under the
same names, as the library does. -/

open scoped BigOperators MatrixOrder Matrix ComplexOrder
namespace MIPStarRE.QPBT

-- elaboration context of MIPStarRE/QPBT/Test/SoundnessDefs.lean:28-229
noncomputable section
open MIPStarRE.LDT
open MIPStarRE.Quantum

-- source: MIPStarRE/QPBT/Test/SoundnessDefs.lean:30-38  (MIPStarRE.QPBT.deltaQld)
/-- The Pauli-test error scale.  The argument order is `(a, b, ε, m, d, q)`;
the powers are real `rpow`s and the asymptotic constants are absorbed into `a`,
as specified by blueprint `thm:pauli`,
paper `references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:1426-1447`).
-/
noncomputable def deltaQld (a b ε : ℝ) (m d q : ℕ) : ℝ :=
  a * Real.rpow ((m * d : ℕ) : ℝ) a *
    (Real.rpow ε b + Real.rpow (q : ℝ) (-b) +
      Real.rpow 2 (-(b * ((m * d : ℕ) : ℝ))))

-- source: MIPStarRE/QPBT/Test/SoundnessDefs.lean:80-95  (MIPStarRE.QPBT.idealState)
/-- The ideal auxiliary state `aux ⊗ EPR_q^{⊗M}` in the shuffled register
ordering.  The EPR factor is the concrete `eprState` from blueprint
`def:EPR`; paper
`references/qpbt-paper/04_preliminaries.tex:946-955`).
-/
noncomputable def idealState (P : AdmissibleParams)
    {ιA' ιB' : Type*} [Fintype ιA'] [DecidableEq ιA']
    [Fintype ιB'] [DecidableEq ιB']
    (aux : EuclideanSpace ℂ (ιA' × ιB')) :
    EuclideanSpace ℂ ((ιA' × PauliRegister P) × (ιB' × PauliRegister P)) :=
  (EuclideanSpace.equiv ((ιA' × PauliRegister P) ×
      (ιB' × PauliRegister P)) ℂ).symm
    (fun p =>
      ((EuclideanSpace.equiv (ιA' × ιB') ℂ) aux (p.1.1, p.2.1)) *
        ((EuclideanSpace.equiv (PauliRegister P × PauliRegister P) ℂ)
          (eprState (PauliRegister P)) (p.1.2, p.2.2)))

-- source: MIPStarRE/QPBT/Test/SoundnessDefs.lean:97-110  (MIPStarRE.QPBT.pauliProjOnA'')
/-- The A-side ideal Pauli projector, with identities on the auxiliary and
B-side registers.  This is a concrete matrix form of the operator comparison
in blueprint `thm:pauli`; paper
`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:1426-1447`).
-/
noncomputable def pauliProjOnA'' (P : AdmissibleParams)
    {ιA' ιB' : Type*} [Fintype ιA'] [DecidableEq ιA']
    [Fintype ιB'] [DecidableEq ιB'] (W : PauliKind)
    (u : PauliRegister P) :
    Op ((ιA' × PauliRegister P) × (ιB' × PauliRegister P)) :=
  fun p q =>
    if p.1.1 = q.1.1 ∧ p.2 = q.2 then
      pauliProj W u p.1.2 q.1.2
    else 0

-- source: MIPStarRE/QPBT/Test/SoundnessDefs.lean:112-124  (MIPStarRE.QPBT.pauliProjOnB'')
/-- The symmetric B-side ideal Pauli projector from blueprint
`thm:pauli`, paper origin
`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:1426-1447`.
-/
noncomputable def pauliProjOnB'' (P : AdmissibleParams)
    {ιA' ιB' : Type*} [Fintype ιA'] [DecidableEq ιA']
    [Fintype ιB'] [DecidableEq ιB'] (W : PauliKind)
    (u : PauliRegister P) :
    Op ((ιA' × PauliRegister P) × (ιB' × PauliRegister P)) :=
  fun p q =>
    if p.1 = q.1 ∧ p.2.1 = q.2.1 then
      pauliProj W u p.2.2 q.2.2
    else 0

-- source: MIPStarRE/QPBT/Test/SoundnessDefs.lean:126-140  (MIPStarRE.QPBT.liftedAEffect)
/-- Lift a conjugated A-side effect to the full ideal register in blueprint
`thm:pauli`, paper origin
`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:1426-1447`.
-/
noncomputable def liftedAEffect {P : AdmissibleParams} {G : Game}
    (S : Strategy G) {ιA' ιB' : Type*} [Fintype ιA'] [DecidableEq ιA']
    [Fintype ιB'] [DecidableEq ιB']
    (φA : EuclideanSpace ℂ S.ιA →ₗᵢ[ℂ]
      EuclideanSpace ℂ (ιA' × PauliRegister P))
    (M : Op S.ιA) :
    Op ((ιA' × PauliRegister P) × (ιB' × PauliRegister P)) :=
  fun p q =>
    if p.2 = q.2 then
      (conjIsometry φA M) p.1 q.1
    else 0

-- source: MIPStarRE/QPBT/Test/SoundnessDefs.lean:142-156  (MIPStarRE.QPBT.liftedBEffect)
/-- Lift a conjugated B-side effect to the full ideal register in blueprint
`thm:pauli`, paper origin
`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:1426-1447`.
-/
noncomputable def liftedBEffect {P : AdmissibleParams} {G : Game}
    (S : Strategy G) {ιA' ιB' : Type*} [Fintype ιA'] [DecidableEq ιA']
    [Fintype ιB'] [DecidableEq ιB']
    (φB : EuclideanSpace ℂ S.ιB →ₗᵢ[ℂ]
      EuclideanSpace ℂ (ιB' × PauliRegister P))
    (M : Op S.ιB) :
    Op ((ιA' × PauliRegister P) × (ιB' × PauliRegister P)) :=
  fun p q =>
    if p.1 = q.1 then
      (conjIsometry φB M) p.2 q.2
    else 0

-- source: MIPStarRE/QPBT/Test/SoundnessDefs.lean:158-177  (MIPStarRE.QPBT.PauliSoundnessWitness)
/-- A finite witness packaging the auxiliary dimensions, isometries, and state
from `thm:pauli`.  This structure is a Lean-only encoding of the existential
data in the paper theorem; it introduces no extra hypothesis.  Blueprint
`thm:pauli`, paper origin
`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:1426-1447`.
-/
structure PauliSoundnessWitness (P : AdmissibleParams)
    (S : Strategy (pauliBasisTest P)) where
  ιA' : Type
  ιB' : Type
  [ιAFintype : Fintype ιA']
  [ιBFintype : Fintype ιB']
  [ιADecidableEq : DecidableEq ιA']
  [ιBDecidableEq : DecidableEq ιB']
  φA : EuclideanSpace ℂ S.ιA →ₗᵢ[ℂ]
    EuclideanSpace ℂ (ιA' × PauliRegister P)
  φB : EuclideanSpace ℂ S.ιB →ₗᵢ[ℂ]
    EuclideanSpace ℂ (ιB' × PauliRegister P)
  aux : EuclideanSpace ℂ (ιA' × ιB')
  aux_norm : ‖aux‖ = 1

-- source: MIPStarRE/QPBT/Test/SoundnessDefs.lean (attribute command)
attribute [instance] PauliSoundnessWitness.ιAFintype PauliSoundnessWitness.ιBFintype
  PauliSoundnessWitness.ιADecidableEq PauliSoundnessWitness.ιBDecidableEq

-- source: MIPStarRE/QPBT/Test/SoundnessDefs.lean:205-216  (MIPStarRE.QPBT.rawPauliOperatorDistanceA)
/-- Alice's source-facing Pauli operator distance. The strategy effect is the
raw effect of the prescribed answer `.pauliOutcome u`, exactly as in
`thm:pauli`, paper
`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:1438-1443`.
The sum is the finite realization of blueprint `def:povm-distance`. -/
noncomputable def rawPauliOperatorDistanceA
    (P : AdmissibleParams) (S : Strategy (pauliBasisTest P))
    (w : PauliSoundnessWitness P S) (W : PauliKind) : ℝ :=
  ∑ u : PauliRegister P,
      ‖applyOperatorToState (liftedAEffect S w.φA
        ((S.A (pauliQuestion P W)).effect (.pauliOutcome u)) -
      pauliProjOnA'' P W u) (idealState P w.aux)‖ ^ 2

-- source: MIPStarRE/QPBT/Test/SoundnessDefs.lean:218-228  (MIPStarRE.QPBT.rawPauliOperatorDistanceB)
/-- Bob's source-facing Pauli operator distance, using the raw prescribed
answer effect from `thm:pauli`, paper
`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:1438-1443`.
-/
noncomputable def rawPauliOperatorDistanceB
    (P : AdmissibleParams) (S : Strategy (pauliBasisTest P))
    (w : PauliSoundnessWitness P S) (W : PauliKind) : ℝ :=
  ∑ u : PauliRegister P,
      ‖applyOperatorToState (liftedBEffect S w.φB
        ((S.B (pauliQuestion P W)).effect (.pauliOutcome u)) -
      pauliProjOnB'' P W u) (idealState P w.aux)‖ ^ 2
end  -- module scope
end MIPStarRE.QPBT
