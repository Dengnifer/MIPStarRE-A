import MIPStarRE.QPBT.Combining.Apply
import MIPStarRE.QPBT.Extraction.ObservableConsistency
import MIPStarRE.QPBT.Extraction.SuppliedPointConsistency

/-!
# Construction of consistent pulled-apart Pauli measurements

This module states the joint source-facing construction of the global
polynomial-pair measurements and their three extraction consistency estimates.
The corresponding estimates from a supplied global measurement are proved
separately and are composed here with the source construction.

## References

- Blueprint `lem:qld-construct-the-paulis`.
- `references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1267-1274,1463-1480`.
- `docs/paper-gaps/qpbt_decoding-identity.tex` for the decoder correction.
- `docs/paper-gaps/qpbt_extraction-transfer.tex`, issue #123, for the
  global-witness composition.
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

The theorem composes the full-domain construction `exists_globalPairWitness`
with the three supplied-witness estimates. All estimates use the same witness,
and taking the maximum of their constants gives the displayed common scale.
This discharges the pulled-apart consistency composition recorded under issue
#123 and `docs/paper-gaps/qpbt_extraction-transfer.tex`; no witness is an input
here. -/
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
  obtain ⟨a, b, ha, hb, hb_one, hglobal⟩ := exists_globalPairWitness
  obtain ⟨C_AB, hC_AB, hAB⟩ := tildeM_consistent_pointMeas_ofGlobalPairWitness
  obtain ⟨C_BA, _, hBA⟩ := tildeM_consistent_pointMeas'_ofGlobalPairWitness
  obtain ⟨C_obs, _, hobs⟩ := tildeObs_selfConsistent_ofGlobalPairWitness
  let C := max (max C_AB C_BA) C_obs
  have hAB_C : C_AB ≤ C := by
    exact (le_max_left C_AB C_BA).trans (le_max_left (max C_AB C_BA) C_obs)
  have hBA_C : C_BA ≤ C := by
    exact (le_max_right C_AB C_BA).trans (le_max_left (max C_AB C_BA) C_obs)
  have hobs_C : C_obs ≤ C := le_max_right (max C_AB C_BA) C_obs
  refine ⟨a, b, C, ha, hb, hb_one, hC_AB.trans hAB_C, ?_⟩
  intro P epsilon hepsilon hepsilon_one S
  obtain ⟨w⟩ := hglobal P epsilon S
  have ha_nonneg : 0 ≤ a := by linarith
  have hdelta : 0 ≤ deltaQld a b epsilon P.m P.d P.q := by
    simp only [deltaQld, Real.rpow_eq_pow]
    positivity
  have hscale : 0 ≤ deltaQld a b epsilon P.m P.d P.q + Real.sqrt epsilon +
      ((P.m * P.d : ℕ) : ℝ) / (P.q : ℝ) := by
    positivity
  have hmono (c : ℝ) (hc : c ≤ C) :
      deltaConstructPaulis c epsilon (deltaQld a b epsilon P.m P.d P.q)
          P.m P.d P.q ≤
        deltaConstructPaulis C epsilon (deltaQld a b epsilon P.m P.d P.q)
          P.m P.d P.q := by
    unfold deltaConstructPaulis
    exact mul_le_mul_of_nonneg_right hc hscale
  refine ⟨w, fun W => ⟨?_, ?_, fun j => ?_⟩⟩
  · exact (hAB P epsilon _ hepsilon hepsilon_one hdelta S w W).trans
      (hmono C_AB hAB_C)
  · exact (hBA P epsilon _ hepsilon hepsilon_one hdelta S w W).trans
      (hmono C_BA hBA_C)
  · exact (hobs P epsilon _ hepsilon hepsilon_one hdelta S w W j).trans
      (hmono C_obs hobs_C)

end

end MIPStarRE.QPBT
