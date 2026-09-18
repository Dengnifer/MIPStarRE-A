import MIPStarRE.QPBT.Combining.Apply
import MIPStarRE.QPBT.Extraction.Unitary

/-!
# Extraction from a projective Pauli-test strategy

The global polynomial-pair measurements are constructed from the strategy
before applying the extraction theorem for concrete swap unitaries.

## References

Blueprint `lem:qld-unitary`; paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1267-1274,1666-1860`.
The numerical corrections are documented in
`docs/paper-gaps/qpbt_extraction-transfer.tex`.
-/

namespace MIPStarRE.QPBT

noncomputable section

/-- **Source statement:** The projective strategy supplies the global
polynomial-pair measurements internally, and their concrete swap unitaries
extract a normalized auxiliary state and both Pauli measurement families at
the nested construction/extraction scale. No global measurement is assumed.

This is the existence claim of blueprint `lem:qld-unitary`, paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1666-1685`,
using the global construction at lines 1267-1274. The two-sided unitary
equations and both register placements are recorded in `ExtractionWitness`.
The separate isometry range-projection step of the subsequent soundness proof
at lines 1864-1875 is not asserted here; see
`docs/paper-gaps/qpbt_extraction-transfer.tex`, issue #123. -/
theorem exists_extractionWitness :
    ∃ a b C : ℝ, 1 < a ∧ 0 < b ∧ b < 1 ∧ 1 ≤ C ∧
      ∀ (P : AdmissibleParams) (epsilon : ℝ),
        0 ≤ epsilon → epsilon ≤ 1 → ∀ S : ProjectiveSetting P epsilon,
          ∃ w : GlobalPairWitness S (deltaQld a b epsilon P.m P.d P.q),
            Nonempty (ExtractionWitness S w
              (deltaExtract C
                (deltaConstructPaulis C epsilon
                  (deltaQld a b epsilon P.m P.d P.q) P.m P.d P.q)
                P.m P.d P.q)) := by
  obtain ⟨a, b, ha, hb, hb1, hglobal⟩ := exists_globalPairWitness
  obtain ⟨C, hC, hextract⟩ := exists_extractionWitness_ofGlobalPairWitness
  refine ⟨a, b, C, ha, hb, hb1, hC, ?_⟩
  intro P epsilon hepsilon0 hepsilon1 S
  obtain ⟨w⟩ := hglobal P epsilon S
  have hdeltaG : 0 ≤ deltaQld a b epsilon P.m P.d P.q := by
    simp only [deltaQld, Real.rpow_eq_pow]
    positivity
  exact ⟨w, hextract P epsilon _ hepsilon0 hepsilon1 hdeltaG S w⟩

end

end MIPStarRE.QPBT
