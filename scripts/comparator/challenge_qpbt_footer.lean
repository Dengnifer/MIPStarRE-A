
namespace MIPStarRE.QPBT

open MIPStarRE.LDT MIPStarRE.Quantum
open MIPStarRE.LDT.Preliminaries

-- source: MIPStarRE/QPBT/Test/Completeness.lean:263-268
--   (MIPStarRE.QPBT.exists_spcc_value_one)
/-- `lem:pauli-completeness`: every admissible Pauli basis test has a
value-one SPCC strategy. Blueprint `lem:pauli-completeness`, paper
`08_classical_and_quantum_low_degree_tests.tex:1229-1421`. -/
theorem exists_spcc_value_one (P : AdmissibleParams) :
    ∃ S : SymmetricStrategy (pauliBasisTestSymm P),
      S.IsSPCC ∧ S.toStrategy.value = 1 := by
  sorry

-- source: MIPStarRE/QPBT/Test/LowDegreeGameTheorems.lean:82-108
--   (MIPStarRE.QPBT.exists_ld_soundness)
/-- Quantum soundness of the simultaneous classical low individual degree test.
Blueprint `lem:ld-soundness`, paper
`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:413-458`. -/
theorem exists_ld_soundness :
    ∃ a b : ℝ, 1 ≤ a ∧ 0 < b ∧ b ≤ 1 ∧
      ∀ (L : LdParams) (ε : ℝ), 0 < ε →
        ∀ S : Strategy (ldGame L), S.IsProjective → 1 - ε ≤ S.value →
          ∃ GA : PolyMeasTuple L S.ιA, ∃ GB : PolyMeasTuple L S.ιB,
            consistencyDefect (uniformDistribution (Fin L.m → ScalarQ L))
                (fun u outcome =>
                  heteroKron
                    (((S.A (ldPointQuestionOf L u)).postprocess
                      (ldPointValuesOrZero L)).effect outcome) 1)
                (fun u outcome =>
                  heteroKron 1
                    ((GB.postprocess (evalPolyTupleAt u)).effect outcome))
                S.ψ ≤ deltaLd a b ε L.q L.m L.d L.k ∧
            consistencyDefect (uniformDistribution (Fin L.m → ScalarQ L))
                (fun u outcome =>
                  heteroKron
                    ((GA.postprocess (evalPolyTupleAt u)).effect outcome) 1)
                (fun u outcome =>
                  heteroKron 1
                    (((S.B (ldPointQuestionOf L u)).postprocess
                      (ldPointValuesOrZero L)).effect outcome))
                S.ψ ≤ deltaLd a b ε L.q L.m L.d L.k ∧
            consistencyDefect (uniformDistribution Unit)
                (fun _ g => heteroKron (GA.effect g) 1)
                (fun _ g => heteroKron 1 (GB.effect g))
                S.ψ ≤ deltaLd a b ε L.q L.m L.d L.k := by
  sorry

-- source: MIPStarRE/QPBT/Test/Soundness.lean:40-65  (MIPStarRE.QPBT.pauli_soundness)
/-- `thm:pauli`: every sufficiently successful Pauli basis test strategy admits
local isometries and an auxiliary unit state for which the state and both
raw prescribed-answer operator families are close at scale `deltaQld`. The theorem uses the
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
              rawPauliOperatorDistanceA P S w W ≤ deltaQld a b ε P.m P.d P.q) ∧
            (∀ W : PauliKind,
              rawPauliOperatorDistanceB P S w W ≤ deltaQld a b ε P.m P.d P.q) := by
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
