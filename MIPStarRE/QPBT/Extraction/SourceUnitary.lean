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

/-- Normalize the nested construction/extraction estimate to the fourth-root
error of blueprint `lem:qld-unitary`, paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1267-1274,1664-1685`.
The constants are chosen before the parameters and strategy. This is the
concrete swap-unitary conclusion; the isometry transfer is separate (issue
#123, `docs/paper-gaps/qpbt_extraction-transfer.tex`).

**Scope restriction:** The global constructor uses the directly indexed
low-degree carrier; the seed-indexed correspondence remains open in
`docs/paper-gaps/qpbt_ld-dimension-divisibility.tex`. -/
theorem exists_extractionWitness_fourth_root_rate :
    ∃ a b C : ℝ, 1 < a ∧ 0 < b ∧ b < 1 ∧ 1 ≤ C ∧
      ∀ (P : AdmissibleParams) (epsilon : ℝ),
        0 ≤ epsilon → epsilon ≤ 1 → ∀ S : ProjectiveSetting P epsilon,
          ∃ w : GlobalPairWitness S (deltaQld a b epsilon P.m P.d P.q),
            Nonempty (ExtractionWitness S w
              (deltaExtract C (deltaQld a b epsilon P.m P.d P.q)
                P.m P.d P.q)) := by
  obtain ⟨a₀, b₀, ha₀, hb₀, hb₀1, hglobal⟩ := exists_globalPairWitness
  obtain ⟨C₀, hC₀, hextract⟩ := exists_extractionWitness_ofGlobalPairWitness
  obtain ⟨a₁, b₁, ha₁, hb₁, hb₁1, hbound⟩ :=
    deltaExtract_le_deltaQld C₀ a₀ b₀ hC₀ ha₀ hb₀ hb₀1
  let a : ℝ := max (a₁ + 1) a₀
  let b : ℝ := min b₀ b₁
  let C : ℝ := max C₀ 4
  have ha : 1 < a := lt_of_lt_of_le ha₀ (le_max_right _ _)
  have hb : 0 < b := lt_min hb₀ hb₁
  have hb1 : b < 1 := (min_le_left _ _).trans_lt hb₀1
  have hb₀b : b ≤ b₀ := min_le_left _ _
  have hb₁b : b ≤ b₁ := min_le_right _ _
  have ha₁a : a₁ ≤ a := (le_add_of_nonneg_right (by norm_num)).trans (le_max_left _ _)
  have ha₀a : a₀ ≤ a := le_max_right _ _
  have hC : 1 ≤ C := hC₀.trans (le_max_left _ _)
  have hC4 : 4 ≤ C := le_max_right _ _
  refine ⟨a, b, C, ha, hb, hb1, hC, ?_⟩
  intro P epsilon hepsilon0 hepsilon1 S
  obtain ⟨w₀⟩ := hglobal P epsilon S
  have hsmall :
      deltaQld a₀ b₀ epsilon P.m P.d P.q ≤
        deltaQld a b epsilon P.m P.d P.q :=
    deltaQld_mono ha₀.le ha₀a hb₀b hb hepsilon0 hepsilon1
  let w : GlobalPairWitness S (deltaQld a b epsilon P.m P.d P.q) := {
    Smeas := w₀.Smeas
    projective := w₀.projective
    point_consistent_alice := fun W => (w₀.point_consistent_alice W).trans hsmall
    point_consistent_bob := fun W => (w₀.point_consistent_bob W).trans hsmall
  }
  refine ⟨w, ?_⟩
  have hdeltaG : 0 ≤ deltaQld a₀ b₀ epsilon P.m P.d P.q := by
    simp only [deltaQld, Real.rpow_eq_pow]
    positivity
  have hdelta : 0 ≤ deltaQld a b epsilon P.m P.d P.q := hdeltaG.trans hsmall
  have hratio : 0 ≤ ((P.m * P.d : ℕ) : ℝ) / (P.q : ℝ) := by positivity
  by_cases hunit : deltaQld a b epsilon P.m P.d P.q ≤ 1
  · obtain ⟨v⟩ := hextract P epsilon _ hepsilon0 hepsilon1 hdeltaG S w₀
    have herror :
        deltaExtract C₀
            (deltaConstructPaulis C₀ epsilon
              (deltaQld a₀ b₀ epsilon P.m P.d P.q) P.m P.d P.q)
            P.m P.d P.q ≤
          deltaExtract C (deltaQld a b epsilon P.m P.d P.q)
            P.m P.d P.q := by
      have hfirst := (hbound P epsilon hepsilon0 hepsilon1).trans
        (deltaQld_mono ha₁ ha₁a hb₁b hb hepsilon0 hepsilon1)
      have hroot := Real.self_le_rpow_of_le_one hdelta hunit
        (by norm_num : (1 / 4 : ℝ) ≤ 1)
      unfold deltaExtract
      exact hfirst.trans
        ((hroot.trans (le_add_of_nonneg_right hratio)).trans
          (le_mul_of_one_le_left (by positivity) hC))
    refine ⟨{
      swap_right_unitary := ?_
      swap_left_unitary := ?_
      aux := v.aux
      aux_norm := v.aux_norm
      state_close := ?_
      pauli_close := ?_
    }⟩
    · exact v.swap_right_unitary
    · exact v.swap_left_unitary
    · exact v.state_close.trans herror
    · intro side W
      exact (v.pauli_close side W).trans herror
  · apply exists_extractionWitness_ofGlobalPairWitness_of_four_le S w
    have hroot := Real.one_le_rpow (le_of_lt (lt_of_not_ge hunit))
      (by norm_num : (0 : ℝ) ≤ 1 / 4)
    unfold deltaExtract
    exact hC4.trans (le_mul_of_one_le_right (by linarith : (0 : ℝ) ≤ C)
      (hroot.trans (le_add_of_nonneg_right hratio)))

end MIPStarRE.QPBT
