import MIPStarRE.QPBT.Combining.Linearity.Reservation

/-!
# Comparing the Option and Boolean projective strategies

The active-space inclusion intertwines the actual measurements of the two
initial dilations and maps their states exactly. In particular, the existing
arbitrary-strategy consumer `pauliNaimarkSetting` is retained.

## References

Initial projective padding is chosen at paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:160-172`.
This is construction support for blueprint `rem:linearity-import`, with the
remaining source absorption tracked in
`docs/paper-gaps/qpbt_linearity-theorem-quotation.tex`, issue #697.
-/

namespace MIPStarRE.QPBT

open MIPStarRE.Quantum MagicSquareRigidity
open scoped BigOperators Matrix

private theorem activeIsometry_ground (P : AdmissibleParams) (ι : Type)
    [Fintype ι] [DecidableEq ι] :
    (linearityActiveIsometry P ι).comp (naimarkEmbedding ι (PauliAnswer P)) =
      padWithZeros (Equiv.refl (ι ×
        (Fin (Fintype.card (PauliAnswer P) + 1) → Bool))) := by
  apply LinearIsometry.toLinearMap_injective
  apply Matrix.toEuclideanLin.symm.injective
  change isometryMatrix ((linearityActiveIsometry P ι).comp _) =
    isometryMatrix (padWithZeros _)
  rw [isometryMatrix_comp]
  ext j i
  simp only [Matrix.mul_apply, linearityActiveIsometry,
    isometryMatrix_indexEmbeddingIsometry]
  rw [Fintype.sum_prod_type]
  simp [isometryMatrix_apply, padWithZeros, optionBoolEmbedding_none,
    Function.Embedding.prodMap, Prod.map]
  by_cases hi : j.1 = i <;> by_cases hb : j.2 = 0 <;> simp [Prod.ext_iff, hi, hb]

private theorem paddedMeasurement_intertwines (P : AdmissibleParams) (ι : Type)
    [Fintype ι] [DecidableEq ι]
    (a0 a : PauliAnswer P) (M : MIPStarRE.Quantum.Measurement (PauliAnswer P) ι) :
    (paddedMeasurement a0 M).effect a * isometryMatrix (linearityActiveIsometry P ι) =
      isometryMatrix (linearityActiveIsometry P ι) * (dilatedMeasurement a0 M).effect a := by
  classical
  let e := paddedLocalEquiv ι (PauliAnswer P)
  ext j i
  obtain ⟨j, rfl⟩ := e.surjective j
  simp only [Matrix.mul_apply, linearityActiveIsometry,
    isometryMatrix_indexEmbeddingIsometry]
  have he (k : ι × Option (PauliAnswer P)) :
      ((Function.Embedding.refl ι).prodMap (optionBoolEmbedding (PauliAnswer P))) k =
        e (Sum.inl k) := (paddedLocalEquiv_inl _ _ k).symm
  simp_rw [he]
  simp only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  cases j with
  | inl j =>
      simp only [Equiv.apply_eq_iff_eq, Sum.inl.injEq, ite_mul, one_mul, zero_mul,
        Finset.sum_ite_eq, Finset.mem_univ, if_true]
      simp [paddedMeasurement, reindexMeasurement, reindexOp, e, blockMeasurement,
        MIPStarRE.LDT.ProjStrat.localDirectSumBlock, MIPStarRE.Quantum.Measurement.ofSumEqOne]
  | inr j =>
      simp [paddedMeasurement, reindexMeasurement, reindexOp, e, blockMeasurement,
        MIPStarRE.LDT.ProjStrat.localDirectSumBlock, MIPStarRE.Quantum.Measurement.ofSumEqOne]

/-- The Option-indexed strategy used by the arbitrary-strategy soundness
consumer embeds into the actual Boolean-padded setup. Its state and both full
question-indexed measurement families intertwine exactly, not merely after
compression. No strategy, answer postprocessing, or winning error is changed.
This is a formalization-only comparison of the constructions implementing
paper `14_analysis_of_the_pauli_basis_test.tex:160-172`. -/
theorem linearity_padding_naimark_comparison (P : AdmissibleParams)
    (S : Strategy (pauliBasisTest P)) :
    isometryTensor (linearityActiveIsometry P S.ιA)
        (linearityActiveIsometry P S.ιB) (pauliNaimarkStrategy P S).ψ =
      (paddedProjectiveStrategy S (default : PauliAnswer P) (default : PauliAnswer P)).ψ ∧
      (∀ (x : PauliQuestion P) (a : PauliAnswer P),
        (paddedMeasurement (default : PauliAnswer P)
          (show MIPStarRE.Quantum.Measurement (PauliAnswer P) S.ιA from S.A x)).effect a *
            isometryMatrix (linearityActiveIsometry P S.ιA) =
          isometryMatrix (linearityActiveIsometry P S.ιA) *
            (dilatedMeasurement (default : PauliAnswer P)
              (show MIPStarRE.Quantum.Measurement (PauliAnswer P) S.ιA from S.A x)).effect a) ∧
      (∀ (y : PauliQuestion P) (a : PauliAnswer P),
        (paddedMeasurement (default : PauliAnswer P)
          (show MIPStarRE.Quantum.Measurement (PauliAnswer P) S.ιB from S.B y)).effect a *
            isometryMatrix (linearityActiveIsometry P S.ιB) =
          isometryMatrix (linearityActiveIsometry P S.ιB) *
            (dilatedMeasurement (default : PauliAnswer P)
              (show MIPStarRE.Quantum.Measurement (PauliAnswer P) S.ιB from S.B y)).effect a) := by
  refine ⟨?_, fun x a => paddedMeasurement_intertwines P S.ιA _ a (S.A x),
    fun y a => paddedMeasurement_intertwines P S.ιB _ a (S.B y)⟩
  rw [pauliNaimarkStrategy_state]
  change isometryTensor (linearityActiveIsometry P S.ιA)
    (linearityActiveIsometry P S.ιB)
    (isometryTensor (naimarkEmbedding S.ιA (PauliAnswer P))
      (naimarkEmbedding S.ιB (PauliAnswer P)) S.ψ) = _
  rw [← isometryTensor_comp, activeIsometry_ground, activeIsometry_ground,
    isometryTensor_padWithZeros_refl]
  rfl

end MIPStarRE.QPBT
