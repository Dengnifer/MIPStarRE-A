import MIPStarRE.QPBT.Extraction.Observables
import MIPStarRE.QPBT.Extraction.EPRState
import MIPStarRE.QPBT.Combining.Points.Closeness

/-!
# Uniform bounds for the extraction witness

The concrete swap preserves the norm of the expanded state. Completeness of
the two measurement families bounds their summed squared distance by four.
These bounds justify the large-error case of extraction.

## References

* Blueprint `lem:qld-unitary`, including its normalization case distinction.
* `references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1666-1860`.
* `docs/paper-gaps/qpbt_extraction-transfer.tex`.
-/

open scoped BigOperators Matrix MatrixOrder ComplexOrder

namespace MIPStarRE.QPBT

open MIPStarRE.Quantum DistanceCalculus

noncomputable section

namespace ProjectiveSetting

variable {P : AdmissibleParams} {epsilon deltaG : ℝ}
variable (S : ProjectiveSetting P epsilon)

/-- The simultaneous swap is an isometry on the six-register space. This is
the two-player consequence of the unitarity calculation at paper lines 1693-1700. -/
theorem placeBoth_swap_left_unitary (w : GlobalPairWitness S deltaG) :
    (S.placeBoth (swapUnitary w .alice) (swapUnitary w .bob))ᴴ *
      S.placeBoth (swapUnitary w .alice) (swapUnitary w .bob) = 1 := by
  classical
  rw [placeBoth, ← reindexOp_conjTranspose, ← WinImplications.reindexOp_mul,
    MagicSquareRigidity.heteroKron_conjTranspose, heteroKron_mul]
  erw [conjTranspose_mul_swapUnitary, conjTranspose_mul_swapUnitary]
  erw [heteroKron_one_one]
  ext x y
  simp [reindexOp, Matrix.one_apply]

/-- Applying the two concrete swap unitaries preserves normalization. -/
theorem applyBoth_swap_norm (w : GlobalPairWitness S deltaG) :
    ‖S.applyBoth (swapUnitary w .alice) (swapUnitary w .bob) S.psiHat‖ = 1 := by
  rw [applyBoth, MagicSquareRigidity.norm_applyOperatorToState_of_isometry
    (S.placeBoth_swap_left_unitary w), S.psiHat_norm]

/-- Each placed swap is an isometry on the six-register space. -/
theorem placeSide_swap_left_unitary (w : GlobalPairWitness S deltaG)
    (side : PlayerSide) :
    (S.placeSide side (swapUnitary w side))ᴴ *
      S.placeSide side (swapUnitary w side) = 1 := by
  classical
  cases side <;>
    simp only [placeSide, ← reindexOp_conjTranspose, ← WinImplications.reindexOp_mul,
      MagicSquareRigidity.heteroKron_conjTranspose, Matrix.conjTranspose_one,
      heteroKron_mul, Matrix.mul_one] <;>
    erw [conjTranspose_mul_swapUnitary] <;>
    erw [heteroKron_one_one] <;>
    ext x y <;> simp [reindexOp, Matrix.one_apply]

private theorem sum_place_sq_eq_one {α : Type*} [Fintype α]
    (p : Placement) (A : α → Op (S.ExpandedLocalSpace p.side))
    (hA : ∑ a, (A a)ᴴ * A a = 1) :
    ∑ a, (S.place p (A a))ᴴ * S.place p (A a) = 1 := by
  simp only [← S.place_conjTranspose, ← S.place_mul]
  rw [← S.place_finsetSum, hA, S.place_one]

/-- The original total-Pauli effects remain square-complete after placement.
This is the completeness used to expand the distance at paper lines 1827-1834. -/
theorem sum_placePlayer_pauli_sq (side : PlayerSide) (W : PauliKind) :
    ∑ h, (S.placePlayer side ((S.pauliMeas side W).effect h))ᴴ *
      S.placePlayer side ((S.pauliMeas side W).effect h) = 1 := by
  classical
  have hlocal : ∑ h, ((S.pauliMeas side W).effect h)ᴴ *
      (S.pauliMeas side W).effect h = 1 := by
    have hproj : Measurement.IsProjective (S.pauliMeas side W) := by
      apply SandwichProduct.postprocess_isProjective
      cases side with
      | alice => exact S.isProjective.1 _
      | bob => exact S.isProjective.2 _
    simp only [fun h => (hproj h).isSelfAdjoint.isHermitian.eq,
      fun h => (hproj h).isIdempotentElem.eq]
    exact (S.pauliMeas side W).sum_eq_one
  cases side <;> apply sum_place_sq_eq_one <;>
    simp only [MagicSquareRigidity.heteroKron_conjTranspose, Matrix.conjTranspose_one,
      heteroKron_mul, Matrix.one_mul, ← heteroKron_finset_sum_left] <;>
    erw [hlocal] <;> exact heteroKron_one_one

/-- The ideal total-Pauli effects are square-complete on either extracted register. -/
theorem sum_placeExtractedRegister_pauli_sq (side : PlayerSide) (W : PauliKind) :
    ∑ h : PauliRegister P, (S.placeExtractedRegister side (pauliProj W h))ᴴ *
      S.placeExtractedRegister side (pauliProj W h) = 1 := by
  classical
  have hlocal : ∑ h : PauliRegister P, (pauliProj W h)ᴴ * pauliProj W h = 1 := by
    simp only [fun h => (posSemidef_pauliProj W h).isHermitian.eq,
      pauliProj_mul_pauliProj, ite_true]
    exact sum_pauliProj_eq_one W
  have htensor {R : Type} [Fintype R] [DecidableEq R] :
      ∑ h : PauliRegister P, (heteroKron (1 : Op R) (pauliProj W h))ᴴ *
        heteroKron (1 : Op R) (pauliProj W h) = 1 := by
    simp only [MagicSquareRigidity.heteroKron_conjTranspose, Matrix.conjTranspose_one,
      heteroKron_mul, Matrix.one_mul, ← heteroKron_finset_sum_right, hlocal,
      heteroKron_one_one]
  cases side <;> apply sum_place_sq_eq_one <;> exact htensor

/-- The entire conjugated total-Pauli family is square-complete; conjugation
does not introduce a factor equal to the number of answers. -/
theorem sum_conj_pauli_sq (w : GlobalPairWitness S deltaG)
    (side : PlayerSide) (W : PauliKind) :
    ∑ h : PauliRegister P,
      (conjBy (S.placeSide side (swapUnitary w side))
        (S.placePlayer side ((S.pauliMeas side W).effect h)))ᴴ *
      conjBy (S.placeSide side (swapUnitary w side))
        (S.placePlayer side ((S.pauliMeas side W).effect h)) = 1 := by
  classical
  let U := S.placeSide side (swapUnitary w side)
  have hU : Uᴴ * U = 1 := S.placeSide_swap_left_unitary w side
  have hU' : U * Uᴴ = 1 := mul_eq_one_comm.mp hU
  have hterm (A : Op (SixReg P S.toStrategy.ιA S.toStrategy.ιB)) :
      (conjBy U A)ᴴ * conjBy U A = U * (Aᴴ * A) * Uᴴ := by
    simp only [conjBy, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
    calc
      _ = U * (Aᴴ * (Uᴴ * U) * A) * Uᴴ := by noncomm_ring
      _ = _ := by rw [hU, Matrix.mul_one]
  change (∑ h, (conjBy U _)ᴴ * conjBy U _) = 1
  simp_rw [hterm]
  rw [← Finset.sum_mul, ← Matrix.mul_sum, S.sum_placePlayer_pauli_sq,
    Matrix.mul_one, hU']

/-- On any normalized ideal state the extraction measurement error is at
most four, uniformly in the local dimensions and number of answers. -/
theorem extraction_pauli_dist_le_four (w : GlobalPairWitness S deltaG)
    (aux : EuclideanSpace ℂ (ExtractionAuxRegisters P S.toStrategy.ιA S.toStrategy.ιB))
    (haux : ‖aux‖ = 1) (side : PlayerSide) (W : PauliKind) :
    opFamilyDistSq (MIPStarRE.LDT.uniformDistribution Unit)
      (fun (_ : Unit) (h : PauliRegister P) =>
        conjBy (S.placeSide side (swapUnitary w side))
          (S.placePlayer side ((S.pauliMeas side W).effect h)))
      (fun (_ : Unit) (h : PauliRegister P) =>
        S.placeExtractedRegister side (pauliProj W h)) (S.idealExpState aux) ≤ 4 := by
  apply opFamilyDistSq_uniform_le_four
  · rw [S.idealExpState_norm, haux]
  · intro _
    exact (S.sum_conj_pauli_sq w side W).le
  · intro _
    exact (S.sum_placeExtractedRegister_pauli_sq side W).le

end ProjectiveSetting

end

end MIPStarRE.QPBT
