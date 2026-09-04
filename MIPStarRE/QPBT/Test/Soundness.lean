import MIPStarRE.QPBT.Test.SoundnessDefs

/-!
# Pauli basis test soundness

This module states the source-shaped soundness theorem.  All analytic estimates
are intentionally proof-level obligations in the stage-4.1 skeleton.

## References

The main declaration is `thm:pauli` in
`blueprint/src/chapter/ch13_qpbt_test.tex:407-424`, with paper origin
`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:1426-1447`.
-/

open scoped BigOperators Matrix ComplexOrder

namespace MIPStarRE.QPBT

open MIPStarRE.LDT
open MIPStarRE.Quantum

noncomputable section

/-- `thm:pauli`: every sufficiently successful Pauli basis test strategy admits
local isometries and an auxiliary unit state for which the state and both
operator families are close at scale `deltaQld`.  The theorem uses the
once-and-for-all self-dual-normal field model selected by `fixedFieldModel` for
each admissible size, rather than a freshly quantified field identification.
Blueprint
`blueprint/src/chapter/ch13_qpbt_test.tex:407-424`; paper origin
`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:1426-1447`.

The paper's asymptotic constants are encoded by the explicit `deltaQld`
functional; the squared operator distances use the quantitative convention of
`def:povm-distance` (`blueprint/src/chapter/ch12_qpbt_games.tex:219-226`).
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
