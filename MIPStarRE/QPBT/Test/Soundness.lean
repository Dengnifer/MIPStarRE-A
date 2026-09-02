import MIPStarRE.QPBT.Test.PauliBasisTest

/-!
# Pauli basis test soundness

The quantitative error function and the source-shaped soundness statement live
here.  All analytic estimates are intentionally proof-level obligations in the
stage-4.1 skeleton; the carriers below are concrete finite-dimensional vectors
and matrices so that later proofs can use the existing Hilbert-space API.

## References

The main declaration is `thm:pauli` in
`blueprint/src/chapter/ch13_qpbt_test.tex:386-403`, with paper origin
`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:1426-1447`.
The distance functionals use `def:state-distance` and `def:povm-distance` from
`blueprint/src/chapter/ch12_qpbt_games.tex:171-220`.
-/

open scoped BigOperators Matrix ComplexOrder

namespace MIPStarRE.QPBT

open MIPStarRE.LDT
open MIPStarRE.Quantum

noncomputable section

/-- The Pauli-test error scale.  The argument order is `(a, b, ε, m, d, q)`;
the powers are real `rpow`s and the asymptotic constants are absorbed into `a`,
as specified by `thm:pauli` (`blueprint/src/chapter/ch13_qpbt_test.tex:386-403`,
paper `references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:1426-1447`).
-/
noncomputable def deltaQld (a b ε : ℝ) (m d q : ℕ) : ℝ :=
  a * Real.rpow ((m * d : ℕ) : ℝ) a *
    (Real.rpow ε b + Real.rpow (q : ℝ) (-b) +
      Real.rpow 2 (-(b * ((m * d : ℕ) : ℝ))))

/-- Matrix conjugation by a finite-dimensional linear isometry.  This is a
Lean-only helper for the operator conclusion of `thm:pauli`; it uses the
matrix representation of the isometry and its conjugate transpose.  Blueprint
`blueprint/src/chapter/ch13_qpbt_test.tex:386-403`, paper origin
`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:1426-1447`.
-/
noncomputable def conjIsometry {ι ι' : Type*}
    [Fintype ι] [DecidableEq ι] [Fintype ι'] [DecidableEq ι']
    (φ : EuclideanSpace ℂ ι →ₗᵢ[ℂ] EuclideanSpace ℂ ι')
    (M : Op ι) : Op ι' :=
  let U : Matrix ι' ι ℂ := Matrix.toEuclideanLin.symm φ.toLinearMap
  U * M * Uᴴ

/-- Reindex a finite Euclidean-space vector along an equivalence.  This is the
coordinate form of the tensor-register shuffle used in the paper's ideal
state (`def:EPR`, blueprint `blueprint/src/chapter/ch11_qpbt_algebra.tex:513-523`),
paper origin `references/qpbt-paper/04_preliminaries.tex:946-955`.
-/
noncomputable def reindexState {ι ι' : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype ι'] [DecidableEq ι'] (e : ι ≃ ι')
    (ψ : EuclideanSpace ℂ ι) : EuclideanSpace ℂ ι' :=
  (EuclideanSpace.equiv ι' ℂ).symm
    (fun j => (EuclideanSpace.equiv ι ℂ ψ) (e.symm j))

/-- Coordinate tensoring of two local maps on a bipartite state.  The formula
is a genuine finite sum over the input coordinates; preservation of the norm
is part of the later soundness proof for `thm:pauli`, blueprint
`blueprint/src/chapter/ch13_qpbt_test.tex:386-403`, paper origin
`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:1426-1447`.
-/
noncomputable def isometryTensor
    {ιA ιB ιA' ιB' R : Type*}
    [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB]
    [Fintype ιA'] [DecidableEq ιA'] [Fintype ιB'] [DecidableEq ιB']
    [Fintype R] [DecidableEq R]
    (φA : EuclideanSpace ℂ ιA →ₗᵢ[ℂ] EuclideanSpace ℂ (ιA' × R))
    (φB : EuclideanSpace ℂ ιB →ₗᵢ[ℂ] EuclideanSpace ℂ (ιB' × R))
    (ψ : EuclideanSpace ℂ (ιA × ιB)) :
    EuclideanSpace ℂ ((ιA' × R) × (ιB' × R)) :=
  (EuclideanSpace.equiv ((ιA' × R) × (ιB' × R)) ℂ).symm
    (fun p =>
      ∑ i : ιA, ∑ j : ιB,
        ((EuclideanSpace.equiv (ιA' × R) ℂ)
            (φA ((EuclideanSpace.equiv ιA ℂ).symm (Pi.single i 1))) p.1) *
          ((EuclideanSpace.equiv (ιB' × R) ℂ)
            (φB ((EuclideanSpace.equiv ιB ℂ).symm (Pi.single j 1))) p.2) *
          ((EuclideanSpace.equiv (ιA × ιB) ℂ) ψ (i, j)) )

/-- The ideal auxiliary state `aux ⊗ EPR_q^{⊗M}` in the shuffled register
ordering.  The EPR factor is the concrete `eprState` from
`def:EPR` (`blueprint/src/chapter/ch11_qpbt_algebra.tex:513-523`; paper
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

/-- The Pauli question carrying no additional coefficient data, as in
`def:pauli-win-predicate`, blueprint `ch13_qpbt_test.tex:331-367`, paper origin
`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:1006-1008`.
-/
def pauliQuestion (P : AdmissibleParams) (W : PauliKind) : PauliQuestion P :=
  (.pauli W, 0)

/-- The A-side ideal Pauli projector, with identities on the auxiliary and
B-side registers.  This is a concrete matrix form of the operator comparison
in `thm:pauli` (`blueprint/src/chapter/ch13_qpbt_test.tex:386-403`; paper
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

/-- The symmetric B-side ideal Pauli projector from `thm:pauli`, blueprint
`ch13_qpbt_test.tex:386-403`, paper origin
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

/-- Lift a conjugated A-side effect to the full ideal register in `thm:pauli`,
blueprint `ch13_qpbt_test.tex:386-403`, paper origin
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

/-- Lift a conjugated B-side effect to the full ideal register in `thm:pauli`,
blueprint `ch13_qpbt_test.tex:386-403`, paper origin
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

/-- A finite witness packaging the auxiliary dimensions, isometries, and state
from `thm:pauli`.  This structure is a Lean-only encoding of the existential
data in the paper theorem; it introduces no extra hypothesis.  Blueprint
`blueprint/src/chapter/ch13_qpbt_test.tex:386-403`, paper origin
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

attribute [instance] PauliSoundnessWitness.ιAFintype PauliSoundnessWitness.ιBFintype
  PauliSoundnessWitness.ιADecidableEq PauliSoundnessWitness.ιBDecidableEq

/-- The A-side operator-distance quantity appearing in the soundness
conclusion.  It is the finite-sum realization of `def:povm-distance` from
`blueprint/src/chapter/ch12_qpbt_games.tex:201-220`, paper origin
`references/qpbt-paper/06_nonlocal_games_and_mipstar.tex:258-271`.
-/
noncomputable def pauliOperatorDistanceA
    (P : AdmissibleParams) (S : Strategy (pauliBasisTest P))
    (w : PauliSoundnessWitness P S) (W : PauliKind) : ℝ :=
  ∑ u : PauliRegister P,
      ‖applyOperatorToState (liftedAEffect S w.φA
        ((S.A (pauliQuestion P W)).effect (.pauliOutcome u)) -
      pauliProjOnA'' P W u) (idealState P w.aux)‖ ^ 2

/-- The symmetric B-side operator-distance quantity from `def:povm-distance`,
blueprint `ch12_qpbt_games.tex:201-220`, paper origin
`references/qpbt-paper/06_nonlocal_games_and_mipstar.tex:258-271`.
-/
noncomputable def pauliOperatorDistanceB
    (P : AdmissibleParams) (S : Strategy (pauliBasisTest P))
    (w : PauliSoundnessWitness P S) (W : PauliKind) : ℝ :=
  ∑ u : PauliRegister P,
      ‖applyOperatorToState (liftedBEffect S w.φB
        ((S.B (pauliQuestion P W)).effect (.pauliOutcome u)) -
      pauliProjOnB'' P W u) (idealState P w.aux)‖ ^ 2

/-- `thm:pauli`: every sufficiently successful Pauli basis test strategy admits
local isometries and an auxiliary unit state for which the state and both
operator families are close at scale `deltaQld`.  The theorem uses the
once-and-for-all self-dual-normal field model selected by `fixedFieldModel` for
each admissible size, rather than a freshly quantified field identification.
Blueprint
`blueprint/src/chapter/ch13_qpbt_test.tex:386-403`; paper origin
`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:1426-1447`.

The paper's asymptotic constants are encoded by the explicit `deltaQld`
functional; the squared operator distances use the quantitative convention of
`def:povm-distance` (`blueprint/src/chapter/ch12_qpbt_games.tex:201-220`).
-/
theorem pauli_soundness :
    ∃ a b : ℝ, 1 ≤ a ∧ 0 < b ∧ b < 1 ∧
      ∀ (P : AdmissibleParams) (ε : ℝ), 0 ≤ ε →
        ∀ S : Strategy (pauliBasisTest P), 1 - ε ≤ S.value →
          ∃ w : PauliSoundnessWitness P S,
            ‖isometryTensor w.φA w.φB S.ψ - idealState P w.aux‖ ≤
                deltaQld a b ε P.m P.d P.q ∧
            (∀ W : PauliKind,
              pauliOperatorDistanceA P S w W ≤ deltaQld a b ε P.m P.d P.q) ∧
            (∀ W : PauliKind,
              pauliOperatorDistanceB P S w W ≤ deltaQld a b ε P.m P.d P.q) := by
  sorry

end

end MIPStarRE.QPBT
