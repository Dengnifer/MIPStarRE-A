import MIPStarRE.QPBT.Extraction.SwappedConsistency

/-!
# EPR projection from Pauli disagreement

Averaging the paired Pauli operators contracts the disagreement norm. The X
and Z averages multiply to the EPR projection, giving the corrected projection
estimate directly in the squared-distance formulation.

## References

Blueprint `lem:qld-unitary`; paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1715-1783`;
`docs/paper-gaps/qpbt_extraction-transfer.tex`.
-/

open scoped BigOperators Matrix

namespace MIPStarRE.QPBT.Extraction

open MIPStarRE.Quantum MIPStarRE.LDT DistanceCalculus

noncomputable section

variable {K I R : Type} [Field K] [Fintype K] [DecidableEq K]
  [Algebra (ZMod 2) K] [Fintype I] [DecidableEq I] [Fintype R] [DecidableEq R]

/-- The averaged paired Pauli operator has squared displacement at most the
mean squared disagreement between the two players. This is Jensen's inequality
in the projection argument at paper lines 1715-1750. -/
theorem norm_sub_pauliCorrelation_sq_le
    (W : PauliKind) (psi : EuclideanSpace ℂ (R × ((I → K) × (I → K)))) :
    ‖psi - applyOperatorToState (heteroKron (1 : Op R) (pauliCorrelation W)) psi‖ ^ 2 ≤
      opDistSq (uniformDistribution (I → K))
        (fun u => heteroKron (1 : Op R) (heteroKron (tauObservable W u) 1))
        (fun u => heteroKron (1 : Op R) (heteroKron 1 (tauObservable W u))) psi := by
  classical
  let L (u : I → K) :=
    heteroKron (1 : Op R) (heteroKron (tauObservable W u) (1 : Op (I → K)))
  let B (u : I → K) :=
    heteroKron (1 : Op R) (heteroKron (1 : Op (I → K)) (tauObservable W u))
  let C (u : I → K) :=
    heteroKron (1 : Op R) (heteroKron (tauObservable W u) (tauObservable W u))
  have hL (u : I → K) : (L u)ᴴ * L u = 1 := by
    simp only [L, MagicSquareRigidity.heteroKron_conjTranspose, Matrix.conjTranspose_one,
      heteroKron_mul, Matrix.one_mul, tauObservable_conjTranspose_mul_self,
      heteroKron_one_one]
  have halg (u : I → K) : L u * (L u - B u) = 1 - C u := by
    simp only [L, B, C, Matrix.mul_sub, heteroKron_mul, Matrix.one_mul,
      Matrix.mul_one, tauObservable_sq, heteroKron_one_one]
  have hdist : opDistSq (uniformDistribution (I → K)) (fun _ => 1) C psi =
      opDistSq (uniformDistribution (I → K)) L B psi := by
    unfold opDistSq opFamilyDistSq
    simp only [Fintype.sum_unique]
    apply avgOver_congr
    intro u
    rw [← halg, MagicSquareRigidity.norm_applyOperatorToState_isometry_mul (hL u)]
  have havg : averageOperatorOverDistribution (uniformDistribution (I → K))
      (fun u => (1 : ℂ) • ((1 : Op (R × ((I → K) × (I → K)))) - C u)) =
      1 - heteroKron (1 : Op R) (pauliCorrelation W) := by
    simp only [one_smul]
    have hsub : averageOperatorOverDistribution (uniformDistribution (I → K))
        (fun u => (1 : Op (R × ((I → K) × (I → K)))) - C u) =
        averageOperatorOverDistribution (uniformDistribution (I → K)) (fun _ => 1) -
          averageOperatorOverDistribution (uniformDistribution (I → K)) C := by
      simp [averageOperatorOverDistribution, smul_sub, Finset.sum_sub_distrib]
    rw [hsub, averageOperatorOverDistribution_const_of_isProbability _
      (uniformDistribution_isProbability _)]
    congr 1
    rw [averageOperatorOverDistribution_uniform_eq_inv_card_smul_sum]
    change _ = (Matrix.kroneckerBilinear (R := ℂ) (α := ℂ) (1 : Op R)) _
    simp only [pauliCorrelation, map_smul, map_sum, C]
    rfl
  have h := avg_closeness (uniformDistribution (I → K))
    (uniformDistribution_isProbability _) (fun _ => 1) C (fun _ => 1)
    (fun _ => by simp) psi
  rw [havg, hdist] at h
  simpa only [MagicSquareRigidity.applyOperatorToState_sub_op,
    MagicSquareRigidity.applyOperatorToState_one] using h

/-- Bounds on both Pauli disagreements imply proximity to the EPR subspace.
The auxiliary register is arbitrary, and the estimate requires no division
by a projection norm or restriction to nonzero projection. -/
theorem norm_sub_eprProjection_le_of_pauli_dist
    (psi : EuclideanSpace ℂ (R × ((I → K) × (I → K))))
    (delta : ℝ) (hdelta : 0 ≤ delta)
    (hdist : ∀ W : PauliKind,
      opDistSq (uniformDistribution (I → K))
        (fun u => heteroKron (1 : Op R) (heteroKron (tauObservable W u) 1))
        (fun u => heteroKron (1 : Op R) (heteroKron 1 (tauObservable W u))) psi ≤ delta) :
    ‖psi - applyOperatorToState (heteroKron (1 : Op R)
      (Matrix.vecMulVec (fun x => eprState (I → K) x)
        (fun y => star (eprState (I → K) y)))) psi‖ ≤ 2 * Real.sqrt delta := by
  let H (W : PauliKind) := heteroKron (1 : Op R) (pauliCorrelation (K := K) (ι := I) W)
  have hstep (W : PauliKind) : ‖psi - applyOperatorToState (H W) psi‖ ≤ Real.sqrt delta := by
    have h := (norm_sub_pauliCorrelation_sq_le W psi).trans (hdist W)
    exact (Real.le_sqrt (norm_nonneg _) hdelta).mpr h
  have hprod : H .X * H .Z = heteroKron (1 : Op R)
      (Matrix.vecMulVec (fun x => eprState (I → K) x)
        (fun y => star (eprState (I → K) y))) := by
    dsimp only [H]
    rw [heteroKron_mul, Matrix.one_mul, pauliCorrelation_mul_eq_epr]
  rw [← hprod, applyOperatorToState_mul]
  calc
    _ ≤ ‖psi - applyOperatorToState (H .X) psi‖ +
        ‖applyOperatorToState (H .X) psi -
          applyOperatorToState (H .X) (applyOperatorToState (H .Z) psi)‖ :=
      norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ ≤ Real.sqrt delta + Real.sqrt delta := add_le_add (hstep .X) (by
      rw [← MagicSquareRigidity.applyOperatorToState_sub]
      exact (norm_heteroKron_pauliCorrelation_apply_le .X _).trans (hstep .Z))
    _ = 2 * Real.sqrt delta := by ring

end

end MIPStarRE.QPBT.Extraction
