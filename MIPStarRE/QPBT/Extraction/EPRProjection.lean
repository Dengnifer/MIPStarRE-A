import MIPStarRE.QPBT.Extraction.Defs
import MIPStarRE.QPBT.Observables.ExpandedCommutation

/-!
# The EPR projection in Pauli extraction

The product of the averaged, paired X and Z observables is the rank-one
projection onto the EPR vector. This is an algebraic prerequisite for constructing
the auxiliary state in `exists_extractionWitness_ofGlobalPairWitness`.

## References

Blueprint `lem:qld-unitary`; paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1725-1742`.
-/

open scoped BigOperators Matrix

namespace MIPStarRE.QPBT.Extraction

open MIPStarRE.Quantum MIPStarRE.LDT.Preliminaries

noncomputable section

variable {K ι : Type*} [Field K] [Fintype K] [DecidableEq K]
  [Algebra (ZMod 2) K] [Fintype ι] [DecidableEq ι]

/-- The operator `H_W` of the EPR projection argument, averaged over all
generalized Pauli labels. Paper lines 1725-1733 define this average after
reindexing by a nonzero element of the binary basis. -/
def pauliCorrelation (W : PauliKind) : Op ((ι → K) × (ι → K)) :=
  (Fintype.card (ι → K) : ℂ)⁻¹ •
    ∑ u : ι → K, heteroKron (tauObservable W u) (tauObservable W u)

private theorem avg_phaseSign_dotProduct (v : ι → K) :
    (Fintype.card (ι → K) : ℂ)⁻¹ *
        ∑ u : ι → K, phaseSign (binTrace K (dotProduct u v)) =
      if v = 0 then 1 else 0 := by
  have h := congrArg (fun A : Op (ι → K) => A v v)
    (pauliProj_eq_avg_tauObservable .Z (0 : ι → K))
  have hv : pauliProj .Z (0 : ι → K) v v = if v = 0 then 1 else 0 := by
    change (∏ i, if v i = 0 then (1 : ℂ) else 0) *
      star (∏ i, if v i = 0 then (1 : ℂ) else 0) = _
    simp only [Fintype.prod_boole, ← funext_iff]
    change (if v = 0 then (1 : ℂ) else 0) * star (if v = 0 then 1 else 0) = _
    split <;> simp
  simp only [dotProduct_zero, map_zero, phaseSign, ite_true, one_smul] at h
  rw [hv] at h
  simpa only [Matrix.smul_apply, Matrix.sum_apply, smul_eq_mul,
    tauObservable_Z_apply, ite_true, one_mul] using h.symm

/-- The Z correlation projects onto equal computational-basis labels.
This is the Fourier cancellation in paper lines 1736-1740. -/
theorem pauliCorrelation_Z_apply (x y : (ι → K) × (ι → K)) :
    pauliCorrelation .Z x y = if x = y ∧ y.1 = y.2 then 1 else 0 := by
  simp only [pauliCorrelation, Matrix.smul_apply, Matrix.sum_apply, smul_eq_mul,
    heteroKron, Matrix.kronecker, Matrix.kroneckerMap_apply]
  simp_rw [tauObservable_Z_apply]
  by_cases hxy : x = y
  · subst x
    simp only [ite_true, true_and]
    have hphase (u : ι → K) :
        phaseSign (binTrace K (dotProduct u y.1)) *
            phaseSign (binTrace K (dotProduct u y.2)) =
          phaseSign (binTrace K (dotProduct u (y.1 + y.2))) := by
      rw [← phaseSign_add, dotProduct_add, map_add]
    simp_rw [hphase]
    rw [avg_phaseSign_dotProduct]
    letI : CharP K 2 := (Algebra.charP_iff (ZMod 2) K 2).mp (ZMod.charP 2)
    simp only [funext_iff, Pi.add_apply, Pi.zero_apply, CharTwo.add_eq_zero]
  · have h : x.1 ≠ y.1 ∨ x.2 ≠ y.2 := by
      by_contra h
      push Not at h
      exact hxy (Prod.ext h.1 h.2)
    rcases h with h | h <;> simp [h, hxy]

/-- On a diagonal input, the X correlation is uniform over diagonal outputs.
This is the shift average in paper lines 1739-1742. -/
theorem pauliCorrelation_X_apply_diagonal (x : (ι → K) × (ι → K)) (a : ι → K) :
    pauliCorrelation .X x (a, a) =
      if x.1 = x.2 then (Fintype.card (ι → K) : ℂ)⁻¹ else 0 := by
  simp only [pauliCorrelation, Matrix.smul_apply, Matrix.sum_apply, smul_eq_mul,
    heteroKron, Matrix.kronecker, Matrix.kroneckerMap_apply]
  simp_rw [tauObservable_X_apply]
  rw [Finset.sum_eq_single (x.1 - a)]
  · simp [add_sub_cancel, eq_comm]
  · intro u _ hu
    have h : x.1 ≠ a + u := by
      intro h
      apply hu
      rw [h, add_sub_cancel_left]
    simp [h]
  · simp

/-- The product `H_X H_Z` is the ordinary rank-one EPR projection, with no
normalized-trace factor. This is the identity at paper lines 1735-1742 used
to construct the auxiliary state in blueprint `lem:qld-unitary`. -/
theorem pauliCorrelation_mul_eq_epr :
    pauliCorrelation (K := K) (ι := ι) .X * pauliCorrelation .Z =
      Matrix.vecMulVec (fun x => eprState (ι → K) x)
        (fun y => star (eprState (ι → K) y)) := by
  ext x y
  rw [Matrix.mul_apply]
  simp_rw [pauliCorrelation_Z_apply]
  rw [Finset.sum_eq_single y]
  · by_cases hy : y.1 = y.2
    · rcases y with ⟨a, b⟩
      dsimp only at hy
      subst b
      rw [if_pos ⟨rfl, rfl⟩, mul_one, pauliCorrelation_X_apply_diagonal]
      change (if x.1 = x.2 then (Fintype.card (ι → K) : ℂ)⁻¹ else 0) =
        (if x.1 = x.2 then (Real.sqrt (Fintype.card (ι → K) : ℝ) : ℂ)⁻¹ else 0) *
          star (if a = a then (Real.sqrt (Fintype.card (ι → K) : ℝ) : ℂ)⁻¹ else 0)
      by_cases hx : x.1 = x.2
      · rw [if_pos hx, if_pos hx, if_pos rfl]
        exact (inv_sqrt_natCast_mul_conj (Fintype.card (ι → K))).symm
      · simp [hx]
    · simp [hy, Matrix.vecMulVec_apply, eprState]
  · intro z _ hz
    simp [hz]
  · simp

/-- Each Pauli correlation average, with an arbitrary auxiliary register,
is a contraction. The triangle inequality
and the unitarity of its summands justify the norm estimate used in paper
lines 1743-1750, independently of any strategy-consistency hypothesis. -/
theorem norm_heteroKron_pauliCorrelation_apply_le {R : Type*}
    [Fintype R] [DecidableEq R] (W : PauliKind)
    (ψ : EuclideanSpace ℂ (R × ((ι → K) × (ι → K)))) :
    ‖applyOperatorToState (heteroKron (1 : Op R) (pauliCorrelation W)) ψ‖ ≤ ‖ψ‖ := by
  let U (u : ι → K) :=
    heteroKron (1 : Op R) (heteroKron (tauObservable W u) (tauObservable W u))
  have hnorm (u : ι → K) :
      ‖applyOperatorToState (U u) ψ‖ = ‖ψ‖ := by
    apply MagicSquareRigidity.norm_toEuclideanLin_of_conjTranspose_mul_eq_one
    simp only [U, heteroKron, Matrix.kronecker, Matrix.conjTranspose_kronecker,
      Matrix.conjTranspose_one]
    change heteroKron 1 (heteroKron (tauObservable W u)ᴴ (tauObservable W u)ᴴ) *
      heteroKron 1 (heteroKron (tauObservable W u) (tauObservable W u)) = 1
    rw [heteroKron_mul, heteroKron_mul, tauObservable_conjTranspose_mul_self,
      heteroKron_one_one, Matrix.one_mul, heteroKron_one_one]
  have haction : applyOperatorToState (heteroKron (1 : Op R) (pauliCorrelation W)) ψ =
      (Fintype.card (ι → K) : ℂ)⁻¹ • ∑ u : ι → K,
        applyOperatorToState (U u) ψ := by
    change applyOperatorToState
      ((Matrix.kroneckerBilinear (R := ℂ) (α := ℂ) (1 : Op R))
        ((Fintype.card (ι → K) : ℂ)⁻¹ •
          ∑ u : ι → K, heteroKron (tauObservable W u) (tauObservable W u))) ψ = _
    simp only [map_smul, map_sum, applyOperatorToState, LinearMap.sum_apply,
      LinearMap.smul_apply]
    rfl
  rw [haction, norm_smul]
  calc
    _ ≤ ‖(Fintype.card (ι → K) : ℂ)⁻¹‖ * ∑ u : ι → K,
        ‖applyOperatorToState (U u) ψ‖ :=
      mul_le_mul_of_nonneg_left (norm_sum_le _ _) (norm_nonneg _)
    _ = ‖ψ‖ := by
      simp only [hnorm, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      rw [norm_inv, Complex.norm_natCast, ← mul_assoc, inv_mul_cancel₀, one_mul]
      positivity

/-- Near-perfect X and Z correlations force proximity to the EPR subspace.
This is the corrected projection estimate for paper lines 1743-1767, with
arbitrary auxiliary registers. It uses the product identity and contraction
bounds, and avoids the invalid squared-triangle estimate in the source. -/
theorem norm_sub_eprProjection_le {R : Type*} [Fintype R] [DecidableEq R]
    (ψ : EuclideanSpace ℂ (R × ((ι → K) × (ι → K)))) (hψ : ‖ψ‖ = 1)
    (δ : ℝ) (hδ : 0 ≤ δ)
    (hcorr : ∀ W : PauliKind,
      1 - δ / 2 ≤ (inner ℂ ψ
        (applyOperatorToState (heteroKron (1 : Op R) (pauliCorrelation W)) ψ)).re) :
    ‖ψ - applyOperatorToState
      (heteroKron (1 : Op R) (Matrix.vecMulVec (fun x => eprState (ι → K) x)
        (fun y => star (eprState (ι → K) y)))) ψ‖ ≤ 2 * Real.sqrt δ := by
  let H (W : PauliKind) := heteroKron (1 : Op R) (pauliCorrelation (K := K) (ι := ι) W)
  have hdist (W : PauliKind) : ‖ψ - applyOperatorToState (H W) ψ‖ ≤ Real.sqrt δ := by
    have hn := norm_heteroKron_pauliCorrelation_apply_le W ψ
    rw [hψ] at hn
    have hs : ‖applyOperatorToState (H W) ψ‖ ^ 2 ≤ 1 := by
      dsimp only [H]
      nlinarith [norm_nonneg (applyOperatorToState (H W) ψ)]
    have he := norm_sub_sq (𝕜 := ℂ) ψ (applyOperatorToState (H W) ψ)
    rw [hψ] at he
    change ‖ψ - applyOperatorToState (H W) ψ‖ ^ 2 =
      1 ^ 2 - 2 * (inner ℂ ψ (applyOperatorToState (H W) ψ)).re +
        ‖applyOperatorToState (H W) ψ‖ ^ 2 at he
    have hc := hcorr W
    change 1 - δ / 2 ≤ (inner ℂ ψ (applyOperatorToState (H W) ψ)).re at hc
    nlinarith [Real.sq_sqrt hδ, Real.sqrt_nonneg δ,
      norm_nonneg (ψ - applyOperatorToState (H W) ψ)]
  have hprod : H .X * H .Z =
      heteroKron (1 : Op R) (Matrix.vecMulVec (fun x => eprState (ι → K) x)
        (fun y => star (eprState (ι → K) y))) := by
    dsimp only [H]
    rw [heteroKron_mul, Matrix.one_mul, pauliCorrelation_mul_eq_epr]
  rw [← hprod, DistanceCalculus.applyOperatorToState_mul]
  calc
    _ ≤ ‖ψ - applyOperatorToState (H .X) ψ‖ +
        ‖applyOperatorToState (H .X) ψ -
          applyOperatorToState (H .X) (applyOperatorToState (H .Z) ψ)‖ :=
      norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ ≤ Real.sqrt δ + Real.sqrt δ := add_le_add (hdist .X) (by
      rw [← MagicSquareRigidity.applyOperatorToState_sub]
      exact (norm_heteroKron_pauliCorrelation_apply_le .X _).trans (hdist .Z))
    _ = 2 * Real.sqrt δ := by ring

end

end MIPStarRE.QPBT.Extraction
