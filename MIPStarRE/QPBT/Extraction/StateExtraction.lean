import MIPStarRE.QPBT.Extraction.ProjectionFromDistance

/-!
# Normalized state extraction from a supplied global witness

The Pauli disagreement estimate is transported to auxiliary/EPR coordinates.
Averaging and the EPR projection identity then select a normalized auxiliary
state, including the case where the unnormalized projection vanishes.

## References

Blueprint `lem:qld-unitary`, Item 1; paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1715-1783`;
`docs/paper-gaps/qpbt_extraction-transfer.tex`.
-/

open scoped BigOperators Matrix Classical

namespace MIPStarRE.QPBT

open MIPStarRE.Quantum MIPStarRE.LDT DistanceCalculus

noncomputable section

namespace ProjectiveSetting

variable {P : AdmissibleParams} {epsilon : ℝ} (S : ProjectiveSetting P epsilon)

private theorem reindex_extracted_left (T : Op (PauliRegister P)) :
    reindexOp (extractionIdealShuffle P S.toStrategy.ιA S.toStrategy.ιB).symm
      (heteroKron (1 : Op (ExtractionAuxRegisters P S.toStrategy.ιA S.toStrategy.ιB))
        (heteroKron T (1 : Op (PauliRegister P)))) =
      S.placeSide .alice (heteroKron (1 : Op (S.ExpandedLocalSpace .alice)) T) := by
  classical
  ext row col
  change (if ((row.1.1, row.1.2.1), (row.2.1, row.2.2.1)) =
      ((col.1.1, col.1.2.1), (col.2.1, col.2.2.1)) then (1 : ℂ) else 0) *
      (T row.1.2.2 col.1.2.2 * if row.2.2.2 = col.2.2.2 then 1 else 0) =
    ((if (row.1.1, row.1.2.1) = (col.1.1, col.1.2.1) then 1 else 0) *
      T row.1.2.2 col.1.2.2) *
      (if ((row.2.1, row.2.2.1), row.2.2.2) =
        ((col.2.1, col.2.2.1), col.2.2.2) then 1 else 0)
  simp only [Prod.mk.injEq, ite_and, ite_mul, mul_ite, one_mul, mul_one, zero_mul, mul_zero]
  split_ifs <;> rfl

private theorem reindex_extracted_right (T : Op (PauliRegister P)) :
    reindexOp (extractionIdealShuffle P S.toStrategy.ιA S.toStrategy.ιB).symm
      (heteroKron (1 : Op (ExtractionAuxRegisters P S.toStrategy.ιA S.toStrategy.ιB))
        (heteroKron (1 : Op (PauliRegister P)) T)) =
      S.placeSide .bob (heteroKron (1 : Op (S.ExpandedLocalSpace .bob)) T) := by
  classical
  ext row col
  change (if ((row.1.1, row.1.2.1), (row.2.1, row.2.2.1)) =
      ((col.1.1, col.1.2.1), (col.2.1, col.2.2.1)) then (1 : ℂ) else 0) *
      ((if row.1.2.2 = col.1.2.2 then 1 else 0) * T row.2.2.2 col.2.2.2) =
    (if ((row.1.1, row.1.2.1), row.1.2.2) =
      ((col.1.1, col.1.2.1), col.1.2.2) then 1 else 0) *
      ((if (row.2.1, row.2.2.1) = (col.2.1, col.2.2.1) then 1 else 0) *
        T row.2.2.2 col.2.2.2)
  simp only [Prod.mk.injEq, ite_and, ite_mul, mul_ite, one_mul, zero_mul, mul_zero]
  split_ifs <;> rfl

/-- Changing to auxiliary/EPR coordinates and multiplying all Pauli labels by
a nonzero basis element preserve the uniform disagreement distance. -/
theorem pauli_dist_reindex_extraction
    (theta : EuclideanSpace ℂ (SixReg P S.toStrategy.ιA S.toStrategy.ιB))
    (W : PauliKind) (j : Fin P.model.basisDim) :
    opDistSq (uniformDistribution (PauliRegister P))
      (fun u => heteroKron
        (1 : Op (ExtractionAuxRegisters P S.toStrategy.ιA S.toStrategy.ιB))
        (heteroKron (tauObservable W u) (1 : Op (PauliRegister P))))
      (fun u => heteroKron
        (1 : Op (ExtractionAuxRegisters P S.toStrategy.ιA S.toStrategy.ιB))
        (heteroKron (1 : Op (PauliRegister P)) (tauObservable W u)))
      (reindexState (extractionIdealShuffle P S.toStrategy.ιA S.toStrategy.ιB).symm theta) =
    opDistSq (uniformDistribution (PauliRegister P))
      (fun u => S.placeSide .alice (heteroKron (1 : Op (S.ExpandedLocalSpace .alice))
        (tauObservable W (P.model.basis j • u))))
      (fun u => S.placeSide .bob (heteroKron (1 : Op (S.ExpandedLocalSpace .bob))
        (tauObservable W (P.model.basis j • u)))) theta := by
  classical
  unfold opDistSq opFamilyDistSq
  simp only [Fintype.sum_unique]
  simp_rw [WinImplications.norm_applyOperatorToState_reindexState,
    WinImplications.reindexOp_sub, S.reindex_extracted_left, S.reindex_extracted_right]
  let e : PauliRegister P ≃ PauliRegister P := Equiv.piCongrRight
    (fun _ => Equiv.mulLeft₀ (P.model.basis j) (P.model.basis.ne_zero j))
  have he (u : PauliRegister P) : e u = P.model.basis j • u := rfl
  simpa only [Equiv.symm_symm, he] using avgOver_uniform_equiv e.symm
    (fun u => ‖applyOperatorToState
      (S.placeSide .alice (heteroKron (1 : Op (S.ExpandedLocalSpace .alice)) (tauObservable W u)) -
        S.placeSide .bob (heteroKron (1 : Op (S.ExpandedLocalSpace .bob)) (tauObservable W u)))
      theta‖ ^ 2)

end ProjectiveSetting

/-- A supplied global witness determines a normalized auxiliary state within
`16 * deltaConstructPaulis` squared distance of the concrete swapped state.
The universal constant is chosen before the parameters. This proves Item 1
of conditional extraction at the stronger linear construction-error scale.

**Unfaithful:** This uses `extracted_obs_selfConsistent_ofGlobalPairWitness`,
whose global measurement is supplied rather than constructed from
`lem:qld-4-7`. The planned composition with `exists_globalPairWitness` remains
open under issue #123 in `docs/paper-gaps/qpbt_extraction-transfer.tex`.

**Local fix:** The projection and normalization estimates replace the numerical
steps at paper lines 1743-1783 as documented in the same gap note. -/
theorem exists_extraction_aux_ofGlobalPairWitness :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (P : AdmissibleParams) (epsilon deltaG : ℝ),
      0 ≤ epsilon → epsilon ≤ 1 → 0 ≤ deltaG →
      ∀ (S : ProjectiveSetting P epsilon) (w : GlobalPairWitness S deltaG),
        ∃ aux : EuclideanSpace ℂ
            (ExtractionAuxRegisters P S.toStrategy.ιA S.toStrategy.ιB),
          ‖aux‖ = 1 ∧
            ‖S.applyBoth (swapUnitary w .alice) (swapUnitary w .bob) S.psiHat -
              S.idealExpState aux‖ ^ 2 ≤
                16 * deltaConstructPaulis C epsilon deltaG P.m P.d P.q := by
  obtain ⟨C, hC, hbound⟩ := extracted_obs_selfConsistent_ofGlobalPairWitness
  refine ⟨C, hC, ?_⟩
  intro P epsilon deltaG hepsilon hepsilon_one hdeltaG S w
  let theta := S.applyBoth (swapUnitary w .alice) (swapUnitary w .bob) S.psiHat
  let e := (extractionIdealShuffle P S.toStrategy.ιA S.toStrategy.ιB).symm
  let delta := deltaConstructPaulis C epsilon deltaG P.m P.d P.q
  have hdelta : 0 ≤ delta := by
    dsimp [delta, deltaConstructPaulis]
    positivity
  let j : Fin P.model.basisDim := ⟨0, P.model.basisDimOdd.pos⟩
  have hdist := Extraction.norm_sub_eprProjection_le_of_pauli_dist
    (reindexState e theta) delta hdelta (fun W => by
      exact (S.pauli_dist_reindex_extraction theta W j).trans_le
        (hbound P epsilon deltaG hepsilon hepsilon_one hdeltaG S w W j))
  have htransport :
      ‖reindexState e theta - applyOperatorToState
        (heteroKron (1 : Op (ExtractionAuxRegisters P S.toStrategy.ιA S.toStrategy.ιB))
          (Matrix.vecMulVec (fun x => eprState (PauliRegister P) x)
            (fun y => star (eprState (PauliRegister P) y)))) (reindexState e theta)‖ =
        ‖theta - applyOperatorToState S.extractionEprProjection theta‖ := by
    have h := WinImplications.norm_applyOperatorToState_reindexState e
      (1 - heteroKron (1 : Op (ExtractionAuxRegisters P S.toStrategy.ιA S.toStrategy.ιB))
        (Matrix.vecMulVec (fun x => eprState (PauliRegister P) x)
          (fun y => star (eprState (PauliRegister P) y)))) theta
    rw [WinImplications.reindexOp_sub] at h
    have hone : reindexOp e (1 : Op (ExtractionAuxRegisters P S.toStrategy.ιA
        S.toStrategy.ιB × (PauliRegister P × PauliRegister P))) = 1 := by
      ext x y
      simp [reindexOp, Matrix.one_apply]
    rw [hone] at h
    simpa only [MagicSquareRigidity.applyOperatorToState_sub_op,
      MagicSquareRigidity.applyOperatorToState_one,
      ProjectiveSetting.extractionEprProjection] using h
  have hprojection := htransport.symm.trans_le hdist
  obtain ⟨aux, haux, hclose⟩ := S.exists_unit_aux_near_eprProjection theta (S.applyBoth_swap_norm w)
  refine ⟨aux, haux, ?_⟩
  have hnorm := norm_nonneg (theta - S.idealExpState aux)
  have hsqrt := Real.sqrt_nonneg delta
  have hsquare := Real.sq_sqrt hdelta
  change ‖theta - S.idealExpState aux‖ ^ 2 ≤ 16 * delta
  nlinarith

end

end MIPStarRE.QPBT
