import MIPStarRE.QPBT.Extraction.PointConsistency

/-!
# Point consistency with Alice's pulled-apart measurement

This module proves the register-interchanged overlap calculation for Item 1 of
blueprint `lem:qld-construct-the-paulis`. Polynomial evaluation is replaced by
decoded evaluation only on encoding outcomes; the remaining loss is bounded
by the mass of the non-encoding outcomes.

## References

* `references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1463-1492`.
* `docs/paper-gaps/qpbt_decoding-identity.tex` records the necessary restriction
  on the decoder identity.
-/

open scoped BigOperators Matrix MatrixOrder ComplexOrder

namespace MIPStarRE.QPBT

open MIPStarRE.LDT hiding Measurement
open MIPStarRE.Quantum DistanceCalculus

noncomputable section

namespace ProjectiveSetting

variable {P : AdmissibleParams} {epsilon : ℝ}

/-- Placing a tensor with an identity on Alice's last register recovers `AA'`. -/
theorem placeSide_alice_tensor_one (S : ProjectiveSetting P epsilon)
    (B : Op (S.ExpandedLocalSpace .alice)) :
    S.placeSide .alice (heteroKron B (1 : Op (PauliRegister P))) = S.place .AA' B := by
  ext row col
  simp [placeSide, sixRegExtractionEquiv, reindexOp, heteroKron, Matrix.kronecker,
    place, Matrix.one_apply, Prod.ext_iff, ite_and, mul_ite]
  split_ifs <;> rfl

/-- The factors on `AA'A''` and `B` can be regrouped on `AA'` and `BA''`
without exchanging registers or assuming symmetry of the strategy. -/
theorem placeSide_alice_tensor_mul_placePlayer_bob (S : ProjectiveSetting P epsilon)
    (B : Op (S.ExpandedLocalSpace .alice)) (T : Op (PauliRegister P))
    (A : Op S.toStrategy.ιB) :
    S.placeSide .alice (heteroKron B T) * S.placePlayer .bob A =
      S.place .AA' B * S.place .BA'' (heteroKron A T) := by
  classical
  ext row col
  simp [placePlayer, placeSide, sixRegExtractionEquiv, reindexOp, heteroKron,
    Matrix.kronecker, place, Matrix.mul_apply, Fintype.sum_prod_type,
    Matrix.one_apply, Prod.ext_iff, ite_and, mul_ite, ite_mul]
  split_ifs <;> ac_rfl

/-- Alice's extraction-block placement preserves finite sums. -/
theorem placeSide_alice_finset_sum (S : ProjectiveSetting P epsilon)
    {I : Type*} (s : Finset I) (B : I → Op (ExtractionBlock P S.toStrategy.ιA)) :
    S.placeSide .alice (∑ i ∈ s, B i) = ∑ i ∈ s, S.placeSide .alice (B i) := by
  classical
  change reindexOp (sixRegExtractionEquiv P S.toStrategy.ιA S.toStrategy.ιB)
    (heteroKron (∑ i ∈ s, B i) (1 : Op (ExtractionBlock P S.toStrategy.ιB))) = _
  rw [heteroKron_finset_sum_left]
  ext row col
  simp only [placeSide, reindexOp, Matrix.reindex_apply, Matrix.submatrix_apply,
    Matrix.sum_apply]

end ProjectiveSetting


end

end MIPStarRE.QPBT
