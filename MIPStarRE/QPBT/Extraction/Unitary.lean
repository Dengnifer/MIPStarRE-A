import MIPStarRE.QPBT.Extraction.Consistency
import MIPStarRE.QPBT.Test.Soundness

/-!
# Extraction by the swap unitaries

The concrete swap operators below yield the Pauli extraction conclusion. The
local maps are constructed from the global polynomial
measurements, and all operators retain the heterogeneous Alice and Bob
placements. The generalized Pauli projectors use the field and basis fixed by
`P.model`.

## References

The extraction witness formalizes `lem:qld-unitary` in
`blueprint/src/chapter/ch16_qpbt_extraction.tex:248-270`, from
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1666-1860`.
The error-form comparison records `rem:pauli-robustness-form`, blueprint lines
330-334 and paper lines 1855-1858 and 1868-1876.
-/

open scoped BigOperators Matrix

namespace MIPStarRE.QPBT

open MIPStarRE.LDT MIPStarRE.Quantum

noncomputable section

/-- The concrete conclusion of `lem:qld-unitary`: the two swap maps extract an
EPR state and conjugate each player's total Pauli measurement to the canonical
Pauli projectors. The answer sum in `pauli_close` is over
`PauliRegister P`; the uniform distribution on `Unit` records that there is no
average over questions.

Blueprint `ch16_qpbt_extraction.tex:248-264`; paper
`14_analysis_of_the_pauli_basis_test.tex:1666-1685,1827-1859`. The swap maps
are `swapUnitary w .alice` and `swapUnitary w .bob`, defined from the
side-indexed global measurements, and use only the basis fixed by `P.model`.
-/
structure ExtractionWitness {P : AdmissibleParams} {epsilon deltaS : ℝ}
    (S : ProjectiveSetting P epsilon) (w : GlobalPairWitness S deltaS)
    (delta : ℝ) where
  /-- Each swap map is a right unitary. -/
  swap_right_unitary : ∀ side : PlayerSide,
    swapUnitary w side * (swapUnitary w side)ᴴ = 1
  /-- Each swap map is a left unitary. -/
  swap_left_unitary : ∀ side : PlayerSide,
    (swapUnitary w side)ᴴ * swapUnitary w side = 1
  /-- The auxiliary state on registers `AA'BB'`. -/
  aux : EuclideanSpace ℂ
    (ExtractionAuxRegisters P S.toStrategy.ιA S.toStrategy.ιB)
  /-- The auxiliary state is normalized. -/
  aux_norm : ‖aux‖ = 1
  /-- Applying both concrete swap maps to the expanded state extracts the ideal
  auxiliary-state/EPR tensor product. -/
  state_close :
    ‖S.applyBoth (swapUnitary w .alice) (swapUnitary w .bob) S.psiHat -
        S.idealExpState aux‖ ^ 2 ≤ delta
  /-- On the ideal extracted state, conjugated total-Pauli effects are close to
  the canonical projectors, for both players and both Pauli bases. -/
  pauli_close : ∀ (side : PlayerSide) (W : PauliKind),
    opFamilyDistSq (uniformDistribution Unit)
      (fun (_ : Unit) (h : PauliRegister P) =>
        conjBy (S.placeSide side (swapUnitary w side))
          (S.placePlayer side ((S.pauliMeas side W).effect h)))
      (fun (_ : Unit) (h : PauliRegister P) =>
        S.placeExtractedRegister side (pauliProj W h))
      (S.idealExpState aux) ≤ delta

/-- `lem:qld-unitary`: the concrete swap maps admit extraction data at the
explicit extraction scale applied to `deltaConstructPaulis`.

This is the source-facing existence statement from blueprint
`ch16_qpbt_extraction.tex:248-264` and paper
`14_analysis_of_the_pauli_basis_test.tex:1666-1860`. It introduces no transfer
premise or additional basis parameter.

**Local fix:** the positive-contraction estimate and normalization case split
repair the two numerical defects at paper lines 1743-1783 without changing the
conclusion; see `docs/paper-gaps/qpbt_extraction-transfer.tex`.

**Proof obligation:** issue #47 tracks the EPR projection argument and the
Schwartz-Zippel comparison at paper lines 1715-1858. Discharge: construct
`aux` from the EPR projection of the swapped state, use the corrected
small-error case split, and combine the point-measurement consistency with the
exact swap conjugation identities. -/
theorem exists_extractionWitness :
    ∃ C : ℝ, 1 ≤ C ∧
      ∀ (P : AdmissibleParams) (epsilon deltaG : ℝ),
        0 ≤ epsilon → epsilon ≤ 1 → 0 ≤ deltaG →
          ∀ (S : ProjectiveSetting P epsilon)
            (w : GlobalPairWitness S deltaG),
            Nonempty
              (ExtractionWitness S w
                (deltaExtract C
                  (deltaConstructPaulis C epsilon deltaG P.m P.d P.q)
                  P.m P.d P.q)) := by
  sorry

/-- The composed construction and extraction errors preserve the error family
of `thm:pauli`: when `deltaG` has the form
`deltaQld a b epsilon m d q`, the result is bounded by another member of that
family after decreasing the exponent and enlarging the universal constant.

This is the named quantitative obligation behind
`rem:pauli-robustness-form`, blueprint
`ch16_qpbt_extraction.tex:330-334`, and the concluding comparison at paper
`14_analysis_of_the_pauli_basis_test.tex:1855-1858,1868-1876`.

**Proof obligation:** issue #47 tracks this real-power estimate. Discharge:
take an exponent no larger than `b / 4` and `1 / 8`, bound the fourth root of
the terms in `deltaConstructPaulis`, absorb `md/q` using admissibility, and
enlarge the prefactor and polynomial exponent. -/
theorem deltaExtract_le_deltaQld (C a b : ℝ) (hC : 1 ≤ C) (ha : 1 < a)
    (hb : 0 < b) (hb1 : b < 1) :
    ∃ a' b' : ℝ, 1 ≤ a' ∧ 0 < b' ∧ b' < 1 ∧
      ∀ (P : AdmissibleParams) (epsilon : ℝ), 0 ≤ epsilon →
        epsilon ≤ 1 →
        deltaExtract C
            (deltaConstructPaulis C epsilon
              (deltaQld a b epsilon P.m P.d P.q) P.m P.d P.q)
            P.m P.d P.q ≤
          deltaQld a' b' epsilon P.m P.d P.q := by
  sorry

end

end MIPStarRE.QPBT
