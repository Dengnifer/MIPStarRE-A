import MIPStarRE.QPBT.Extraction.Bounds
import MIPStarRE.QPBT.Extraction.ObservableConsistency

/-!
# Observable consistency after the concrete swaps

Unitary conjugation transports the supplied-witness observable estimate to
the canonical Pauli operators on the extracted registers. This is the input
to the EPR correlation argument, before projection and normalization.

## References

Blueprint `lem:qld-unitary`; paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1701-1724`.
-/

open scoped BigOperators Matrix

namespace MIPStarRE.QPBT

open MIPStarRE.Quantum MIPStarRE.LDT DistanceCalculus

noncomputable section

private theorem conjBy_reindexOp {I J : Type} [Fintype I] [Fintype J]
    (e : I ≃ J) (U A : Op J) :
    conjBy (reindexOp e U) (reindexOp e A) = reindexOp e (conjBy U A) := by
  rw [conjBy, ← ProjectiveSetting.reindexOp_conjTranspose,
    ← WinImplications.reindexOp_mul, ← WinImplications.reindexOp_mul, conjBy]

private theorem conjBy_heteroKron {I J : Type} [Fintype I] [Fintype J]
    (U A : Op I) (V B : Op J) :
    conjBy (heteroKron U V) (heteroKron A B) =
      heteroKron (conjBy U A) (conjBy V B) := by
  simp only [conjBy, MagicSquareRigidity.heteroKron_conjTranspose, heteroKron_mul]

/-- Simultaneous swaps conjugate each local operator by its own swap. This
retains the heterogeneous local spaces in the calculation at paper lines 1701-1713. -/
theorem ProjectiveSetting.conjBy_placeBoth_swap_placeSide
    {P : AdmissibleParams} {epsilon deltaG : ℝ} (S : ProjectiveSetting P epsilon)
    (w : GlobalPairWitness S deltaG) (side : PlayerSide)
    (A : Op (ExtractionBlock P (S.LocalSpace side))) :
    conjBy (S.placeBoth (swapUnitary w .alice) (swapUnitary w .bob)) (S.placeSide side A) =
      S.placeSide side (conjBy (swapUnitary w side) A) := by
  classical
  cases side <;> simp only [ProjectiveSetting.placeBoth, ProjectiveSetting.placeSide,
    conjBy_reindexOp, conjBy_heteroKron]
  · congr 2
    change swapUnitary w .bob * 1 * (swapUnitary w .bob)ᴴ = 1
    rw [Matrix.mul_one, swapUnitary_mul_conjTranspose]
  · congr 2
    change swapUnitary w .alice * 1 * (swapUnitary w .alice)ᴴ = 1
    rw [Matrix.mul_one, swapUnitary_mul_conjTranspose]

/-- Conjugating both operator families and the state by the same unitary
preserves their state-dependent distance. -/
theorem opDistSq_conjBy_apply_eq {X I : Type} [Fintype X] [DecidableEq X]
    [Fintype I] [DecidableEq I] (mu : Distribution X) (U : Op I)
    (hU : Uᴴ * U = 1) (A B : X → Op I) (psi : EuclideanSpace ℂ I) :
    opDistSq mu (fun x => conjBy U (A x)) (fun x => conjBy U (B x))
      (applyOperatorToState U psi) = opDistSq mu A B psi := by
  have hterm (M N : Op I) : (conjBy U M - conjBy U N) * U = U * (M - N) := by
    simp only [conjBy]
    calc
      _ = U * (M - N) * (Uᴴ * U) := by noncomm_ring
      _ = _ := by rw [hU, Matrix.mul_one]
  unfold opDistSq opFamilyDistSq
  simp only [Fintype.sum_unique]
  apply avgOver_congr
  intro x
  rw [← applyOperatorToState_mul, hterm,
    MagicSquareRigidity.norm_applyOperatorToState_isometry_mul hU]

/-- After the swaps, the pulled-apart distance is exactly the distance of the
canonical Pauli observables on the two extracted blocks. -/
theorem opDistSq_extracted_eq_tildeObs
    {P : AdmissibleParams} {epsilon deltaG : ℝ} (S : ProjectiveSetting P epsilon)
    (w : GlobalPairWitness S deltaG) (W : PauliKind) (j : Fin P.model.basisDim) :
    opDistSq (uniformDistribution (PauliRegister P))
      (fun u => S.placeSide .alice (heteroKron (1 : Op (S.ExpandedLocalSpace .alice))
        (tauObservable W (P.model.basis j • u))))
      (fun u => S.placeSide .bob (heteroKron (1 : Op (S.ExpandedLocalSpace .bob))
        (tauObservable W (P.model.basis j • u))))
      (S.applyBoth (swapUnitary w .alice) (swapUnitary w .bob) S.psiHat) =
    opDistSq (uniformDistribution (PauliRegister P))
      (fun u => S.placeSide .alice (tildeObs w .alice W u j))
      (fun u => S.placeSide .bob (tildeObs w .bob W u j)) S.psiHat := by
  have h := opDistSq_conjBy_apply_eq (uniformDistribution (PauliRegister P))
    _ (S.placeBoth_swap_left_unitary w)
    (fun u => S.placeSide .alice (tildeObs w .alice W u j))
    (fun u => S.placeSide .bob (tildeObs w .bob W u j)) S.psiHat
  simpa only [S.conjBy_placeBoth_swap_placeSide, swapUnitary_conj_tildeObs,
    ProjectiveSetting.applyBoth] using h

/-- The supplied global witness bounds the canonical Pauli disagreement on
the swapped state, with a universal constant independent of the parameters.
This is the distance form of paper `eq:qld-unitary-1`.

**Unfaithful:** This uses the supplied-witness theorem
`tildeObs_selfConsistent_ofGlobalPairWitness`, not the construction in
`lem:qld-4-7`. The missing source construction and its planned composition
with `exists_globalPairWitness` are recorded in
`docs/paper-gaps/qpbt_extraction-transfer.tex`, issue #123. -/
theorem extracted_obs_selfConsistent_ofGlobalPairWitness :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (P : AdmissibleParams) (epsilon deltaG : ℝ),
      0 ≤ epsilon → epsilon ≤ 1 → 0 ≤ deltaG →
      ∀ (S : ProjectiveSetting P epsilon) (w : GlobalPairWitness S deltaG)
        (W : PauliKind) (j : Fin P.model.basisDim),
        opDistSq (uniformDistribution (PauliRegister P))
          (fun u => S.placeSide .alice (heteroKron (1 : Op (S.ExpandedLocalSpace .alice))
            (tauObservable W (P.model.basis j • u))))
          (fun u => S.placeSide .bob (heteroKron (1 : Op (S.ExpandedLocalSpace .bob))
            (tauObservable W (P.model.basis j • u))))
          (S.applyBoth (swapUnitary w .alice) (swapUnitary w .bob) S.psiHat) ≤
            deltaConstructPaulis C epsilon deltaG P.m P.d P.q := by
  obtain ⟨C, hC, hbound⟩ := tildeObs_selfConsistent_ofGlobalPairWitness
  refine ⟨C, hC, ?_⟩
  intro P epsilon deltaG hepsilon hepsilon_one hdeltaG S w W j
  rw [opDistSq_extracted_eq_tildeObs]
  exact hbound P epsilon deltaG hepsilon hepsilon_one hdeltaG S w W j

end

end MIPStarRE.QPBT
