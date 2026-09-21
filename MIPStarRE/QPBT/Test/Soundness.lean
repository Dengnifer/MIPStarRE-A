import MIPStarRE.QPBT.Test.SoundnessDefs
import MIPStarRE.QPBT.Test.Soundness.RangeProjection
import MIPStarRE.QPBT.Test.Soundness.Ancilla
import MIPStarRE.QPBT.Test.Soundness.OperatorTransfer
import MIPStarRE.QPBT.Test.Soundness.ProjectiveSetting
import MIPStarRE.QPBT.Test.Soundness.NaimarkReduction
import MIPStarRE.QPBT.Test.Soundness.NaimarkOperatorTransfer
import MIPStarRE.QPBT.Test.Soundness.NaimarkAssembly
import MIPStarRE.QPBT.Test.Soundness.EpsReduction
import MIPStarRE.QPBT.Test.Soundness.RawOperatorTransfer

/-!
# Pauli basis test soundness

This module states the source-shaped soundness theorem and provides auxiliary
range-projection estimates, ancilla isometries, and the transfer of supplied
extraction data to the three soundness estimates.
The scalar square-root error bound is in `MIPStarRE.QPBT.Combining.RootErrorBounds`.
The completed-family estimates are supplied by the Naimark reduction. The
final transfer bounds the rejected wrong-form mass and restores the raw Pauli
effects required by the paper before extending the result to the full error
domain.

## References

The main declaration is blueprint
`thm:pauli`, with paper origin
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
  exact exists_arbitrary_strategy_raw_isometry_bounds

end

end MIPStarRE.QPBT
