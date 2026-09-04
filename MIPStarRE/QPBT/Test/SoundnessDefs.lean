import MIPStarRE.QPBT.Test.PauliBasisTest
import MIPStarRE.QPBT.State

/-!
# Pauli basis test soundness interface

This module contains the quantitative error function and the closed definitions
used to state Pauli basis test soundness.  The carriers are concrete
finite-dimensional vectors and matrices so that the soundness proof can use the
existing Hilbert-space API without introducing a dependency cycle.

## References

The interface supports `thm:pauli` in
`blueprint/src/chapter/ch13_qpbt_test.tex:407-424`, with paper origin
`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:1426-1447`.
The distance functionals use `def:state-distance` and `def:povm-distance` from
`blueprint/src/chapter/ch12_qpbt_games.tex:187-226`.
-/

open scoped BigOperators Matrix ComplexOrder

namespace MIPStarRE.QPBT

open MIPStarRE.LDT
open MIPStarRE.Quantum

noncomputable section

/-- The Pauli-test error scale.  The argument order is `(a, b, ε, m, d, q)`;
the powers are real `rpow`s and the asymptotic constants are absorbed into `a`,
as specified by `thm:pauli` (`blueprint/src/chapter/ch13_qpbt_test.tex:407-424`,
paper `references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:1426-1447`).
-/
noncomputable def deltaQld (a b ε : ℝ) (m d q : ℕ) : ℝ :=
  a * Real.rpow ((m * d : ℕ) : ℝ) a *
    (Real.rpow ε b + Real.rpow (q : ℝ) (-b) +
      Real.rpow 2 (-(b * ((m * d : ℕ) : ℝ))))

/-- Monotonicity obligation for adjusting the universal constants in
`deltaQld` on the source parameter domain. This Lean-only helper supports the
enlargement of `a` and shrinkage of `b` for `0 ≤ ε ≤ 1` described in the
Chapter 16 preamble (`blueprint/src/chapter/ch16_qpbt_extraction.tex:101-104`);
the source makes this constant adjustment at
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1402`. It is not
an additional hypothesis of `thm:pauli` or `lem:qld-4-7`. -/
theorem deltaQld_mono {P : AdmissibleParams} {a a' b b' ε : ℝ}
    (ha0 : 1 ≤ a) (ha : a ≤ a') (hb : b' ≤ b) (hb' : 0 < b')
    (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) :
    deltaQld a b ε P.m P.d P.q ≤ deltaQld a' b' ε P.m P.d P.q := by
  have hmd : (1 : ℝ) ≤ ((P.m * P.d : ℕ) : ℝ) :=
    Nat.one_le_cast.mpr (Nat.mul_pos P.one_le_m P.hd)
  have hmd0 : (0 : ℝ) ≤ ((P.m * P.d : ℕ) : ℝ) := by linarith
  have hq : (1 : ℝ) ≤ (P.q : ℝ) := by
    obtain ⟨k, -, hk⟩ := P.hq
    rw [hk]
    exact_mod_cast Nat.one_le_pow _ _ (by norm_num)
  unfold deltaQld
  simp only [Real.rpow_eq_pow]
  have h1 : ((P.m * P.d : ℕ) : ℝ) ^ a ≤ ((P.m * P.d : ℕ) : ℝ) ^ a' :=
    Real.rpow_le_rpow_of_exponent_le hmd ha
  have h2 : ε ^ b ≤ ε ^ b' := Real.rpow_le_rpow_of_exponent_ge' hε0 hε1 hb'.le hb
  have h3 : (P.q : ℝ) ^ (-b) ≤ (P.q : ℝ) ^ (-b') :=
    Real.rpow_le_rpow_of_exponent_le hq (neg_le_neg hb)
  have h4 : (2 : ℝ) ^ (-(b * ((P.m * P.d : ℕ) : ℝ))) ≤
      (2 : ℝ) ^ (-(b' * ((P.m * P.d : ℕ) : ℝ))) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num)
      (neg_le_neg (mul_le_mul_of_nonneg_right hb hmd0))
  have hsum : 0 ≤ ε ^ b + (P.q : ℝ) ^ (-b) +
      (2 : ℝ) ^ (-(b * ((P.m * P.d : ℕ) : ℝ))) := by
    have := Real.rpow_nonneg hε0 b
    have := Real.rpow_nonneg (Nat.cast_nonneg P.q) (-b)
    have := Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 2)
      (-(b * ((P.m * P.d : ℕ) : ℝ)))
    linarith
  exact mul_le_mul (mul_le_mul ha h1 (Real.rpow_nonneg hmd0 a) (by linarith))
    (add_le_add (add_le_add h2 h3) h4) hsum
    (mul_nonneg (by linarith) (Real.rpow_nonneg hmd0 a'))

/-- The ideal auxiliary state `aux ⊗ EPR_q^{⊗M}` in the shuffled register
ordering.  The EPR factor is the concrete `eprState` from
`def:EPR` (`blueprint/src/chapter/ch11_qpbt_algebra.tex:537-547`; paper
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

/-- The A-side ideal Pauli projector, with identities on the auxiliary and
B-side registers.  This is a concrete matrix form of the operator comparison
in `thm:pauli` (`blueprint/src/chapter/ch13_qpbt_test.tex:407-424`; paper
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
`ch13_qpbt_test.tex:407-424`, paper origin
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
blueprint `ch13_qpbt_test.tex:407-424`, paper origin
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
blueprint `ch13_qpbt_test.tex:407-424`, paper origin
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
`blueprint/src/chapter/ch13_qpbt_test.tex:407-424`, paper origin
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
`blueprint/src/chapter/ch12_qpbt_games.tex:219-226`, paper origin
`references/qpbt-paper/06_nonlocal_games_and_mipstar.tex:258-271`.
-/
noncomputable def pauliOperatorDistanceA
    (P : AdmissibleParams) (S : Strategy (pauliBasisTest P))
    (w : PauliSoundnessWitness P S) (W : PauliKind) : ℝ :=
  ∑ u : PauliRegister P,
      ‖applyOperatorToState (liftedAEffect S w.φA
        (((S.A (pauliQuestion P W)).postprocess pauliAnswerOrZero).effect u) -
      pauliProjOnA'' P W u) (idealState P w.aux)‖ ^ 2

/-- The symmetric B-side operator-distance quantity from `def:povm-distance`,
blueprint `ch12_qpbt_games.tex:219-226`, paper origin
`references/qpbt-paper/06_nonlocal_games_and_mipstar.tex:258-271`.
-/
noncomputable def pauliOperatorDistanceB
    (P : AdmissibleParams) (S : Strategy (pauliBasisTest P))
    (w : PauliSoundnessWitness P S) (W : PauliKind) : ℝ :=
  ∑ u : PauliRegister P,
      ‖applyOperatorToState (liftedBEffect S w.φB
        (((S.B (pauliQuestion P W)).postprocess pauliAnswerOrZero).effect u) -
      pauliProjOnB'' P W u) (idealState P w.aux)‖ ^ 2

end

end MIPStarRE.QPBT
