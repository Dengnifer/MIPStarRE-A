import MIPStarRE.QPBT.Extraction.Consistency
import MIPStarRE.QPBT.Test.SoundnessDefs

/-!
# Construction of consistent pulled-apart Pauli measurements

This module states the joint source-facing construction of the global
polynomial-pair measurements and their three extraction consistency estimates.
The supplied-witness estimates remain in `Extraction.Consistency`; their
unresolved construction and proof obligations are documented below.

## References

- Blueprint `lem:qld-construct-the-paulis`.
- `references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1267-1274,1463-1480`.
- `docs/paper-gaps/qpbt_decoding-identity.tex`, issue #519.
-/

namespace MIPStarRE.QPBT

open MIPStarRE.LDT hiding Measurement
open MIPStarRE.Quantum DistanceCalculus

noncomputable section

/-- Source-facing construction for `lem:qld-construct-the-paulis`, paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1463-1480`, using
the measurement constructed in `lem:qld-4-7` (lines 1267-1274). One pair of
global measurements satisfies both point-consistency conclusions and observable
self-consistency. The witness is an output, and all constants precede the
strategy quantifiers. Zero error is included, as in the source setting.

**Local fix:** The scale `deltaConstructPaulis` exposes the decoder correction
and error enlargement documented in `docs/paper-gaps/qpbt_decoding-identity.tex`
and blueprint `lem:qld-construct-the-paulis`.

**Proof obligation:** The `sorry` introduced in this paper realignment is tracked
by issue #519 and the cited gap note. Discharge `exists_pulled_apart_consistency`
by constructing the global measurements as in `exists_globalPairWitness`, including
the zero-error case missing from its current domain, and proving
`tildeM_consistent_pointMeas_ofGlobalPairWitness` and
`tildeObs_selfConsistent_ofGlobalPairWitness`. Apply the proved
`tildeM_consistent_pointMeas'_ofGlobalPairWitness` to the same constructed witness
and take a common maximum of the three constants. No witness is an input here. -/
theorem exists_pulled_apart_consistency :
    ∃ a b C : ℝ, 1 < a ∧ 0 < b ∧ b < 1 ∧ 1 ≤ C ∧
      ∀ (P : AdmissibleParams) (epsilon : ℝ),
        0 ≤ epsilon → epsilon ≤ 1 → ∀ S : ProjectiveSetting P epsilon,
          ∃ w : GlobalPairWitness S (deltaQld a b epsilon P.m P.d P.q),
            ∀ W : PauliKind,
              consistencyDefect (uniformDistribution (Fin P.m → PauliScalar P))
                  (fun u r => S.placePlayer .alice ((S.pointMeas .alice W u).effect r))
                  (fun u r => S.placeSide .bob (tildeM w .bob W (indicatorVec u) r))
                  S.psiHat ≤ deltaConstructPaulis C epsilon
                    (deltaQld a b epsilon P.m P.d P.q) P.m P.d P.q ∧
              consistencyDefect (uniformDistribution (Fin P.m → PauliScalar P))
                  (fun u r => S.placeSide .alice (tildeM w .alice W (indicatorVec u) r))
                  (fun u r => S.placePlayer .bob ((S.pointMeas .bob W u).effect r))
                  S.psiHat ≤ deltaConstructPaulis C epsilon
                    (deltaQld a b epsilon P.m P.d P.q) P.m P.d P.q ∧
              ∀ j : Fin P.model.basisDim,
                opDistSq (uniformDistribution (PauliRegister P))
                    (fun u => S.placeSide .alice (tildeObs w .alice W u j))
                    (fun u => S.placeSide .bob (tildeObs w .bob W u j))
                    S.psiHat ≤ deltaConstructPaulis C epsilon
                      (deltaQld a b epsilon P.m P.d P.q) P.m P.d P.q := by
  sorry

end

end MIPStarRE.QPBT
