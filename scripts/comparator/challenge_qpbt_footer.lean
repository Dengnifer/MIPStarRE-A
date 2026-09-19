
namespace MIPStarRE.QPBT

open MIPStarRE.LDT MIPStarRE.Quantum

-- source: MIPStarRE/QPBT/Test/Soundness.lean:38-62  (MIPStarRE.QPBT.pauli_soundness)
/-- `thm:pauli`: every sufficiently successful Pauli basis test strategy admits
local isometries and an auxiliary unit state for which the state and both
operator families are close at scale `deltaQld`.  The theorem uses the
once-and-for-all self-dual-normal field model selected by `fixedFieldModel` for
each admissible size, rather than a freshly quantified field identification.
Blueprint
`thm:pauli`; paper origin
`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:1426-1447`.

The paper's asymptotic constants are encoded by the explicit `deltaQld`
functional; the squared operator distances use the quantitative convention of
blueprint `def:povm-distance`.
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

-- source: MIPStarRE/QPBT/Test/QubitForm.lean:411-436  (MIPStarRE.QPBT.pauli_soundness_qubit)
/-- `cor:pauli-binary`: soundness of the Pauli basis test in qubit
coordinates. Blueprint `cor:pauli-binary`, paper
`08_classical_and_quantum_low_degree_tests.tex:1450-1491`.

The theorem assumes a nonnegative error parameter, as in the source, and uses
only `P.model` and its stored basis dimension.

**Proof dependency:** The coordinate change and all three error identities are
proved, and the source theorem `pauli_soundness` is proved as well, so this
corollary is complete: its axiom closure is `propext`, `Classical.choice` and
`Quot.sound`. The composition that closed `pauli_soundness` is recorded in
issue #614, under the umbrella issue #529. -/
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

end MIPStarRE.QPBT
