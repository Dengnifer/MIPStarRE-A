import MIPStarRE.QPBT.Extraction.Observables
import MIPStarRE.QPBT.Combining.Points.PlacementSupport
import MIPStarRE.QPBT.Combining.Lines.ConsistencyPositivity

/-!
# Point consistency after decoding polynomial outcomes

This module expands the overlap of an original point measurement with a
pulled-apart measurement. The decoded polynomial is kept explicit, so the
calculation does not use the decoder identity outside the encoding image.

## References

These are auxiliary identities for blueprint `lem:qld-construct-the-paulis`,
paper `references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1483-1492`.
The restriction on the decoder identity is recorded in
`docs/paper-gaps/qpbt_decoding-identity.tex`.
-/

open scoped BigOperators Matrix MatrixOrder ComplexOrder

namespace MIPStarRE.QPBT

open MIPStarRE.LDT hiding Measurement
open MIPStarRE.Quantum DistanceCalculus

noncomputable section

namespace ProjectiveSetting

variable {P : AdmissibleParams} {epsilon : ℝ}

/-- Placing a tensor with an identity on Bob's last register recovers `BB'`. -/
theorem placeSide_bob_tensor_one (S : ProjectiveSetting P epsilon)
    (B : Op (S.ExpandedLocalSpace .bob)) :
    S.placeSide .bob (heteroKron B (1 : Op (PauliRegister P))) = S.place .BB' B := by
  ext row col
  simp [placeSide, sixRegExtractionEquiv, reindexOp, heteroKron, Matrix.kronecker,
    place, Matrix.one_apply, Prod.ext_iff, ite_and, mul_ite, ite_mul]
  split_ifs <;> rfl

/-- The point factor on `A` and the factors on `BB'B''` can be regrouped as
the factors on `BB'` and `AB''`, without moving any register. -/
theorem placePlayer_alice_mul_placeSide_bob_tensor (S : ProjectiveSetting P epsilon)
    (A : Op S.toStrategy.ιA) (B : Op (S.ExpandedLocalSpace .bob))
    (T : Op (PauliRegister P)) :
    S.placePlayer .alice A * S.placeSide .bob (heteroKron B T) =
      S.place .BB' B * S.place .AB'' (heteroKron A T) := by
  classical
  ext row col
  simp [placePlayer, placeSide, sixRegExtractionEquiv, reindexOp, heteroKron,
    Matrix.kronecker, place, Matrix.mul_apply, Fintype.sum_prod_type,
    Matrix.one_apply, Prod.ext_iff, ite_and, mul_ite, ite_mul]
  split_ifs <;> ac_rfl

/-- Bob's extraction-block placement preserves finite sums. -/
theorem placeSide_bob_finset_sum (S : ProjectiveSetting P epsilon)
    {I : Type*} (s : Finset I) (B : I → Op (ExtractionBlock P S.toStrategy.ιB)) :
    S.placeSide .bob (∑ i ∈ s, B i) = ∑ i ∈ s, S.placeSide .bob (B i) := by
  classical
  change reindexOp (sixRegExtractionEquiv P S.toStrategy.ιA S.toStrategy.ιB)
    (heteroKron (1 : Op (ExtractionBlock P S.toStrategy.ιA)) (∑ i ∈ s, B i)) = _
  rw [heteroKron_finset_sum_right]
  ext row col
  simp only [placeSide, reindexOp, Matrix.reindex_apply, Matrix.submatrix_apply,
    Matrix.sum_apply]

/-- The convolution formula with its second outcome solved for. This is the
third line of the overlap calculation in paper lines 1483--1492. -/
theorem pointMeasExp_effect_eq_sum_sub (S : ProjectiveSetting P epsilon)
    (side : PlayerSide) (W : PauliKind) (u : Fin P.m → PauliScalar P)
    (a : PauliScalar P) :
    (S.pointMeasExp side W u).effect a =
      ∑ b : PauliScalar P, heteroKron ((S.pointMeas side W u).effect b)
        (tauDotProj W (indicatorVec u) (a - b)) := by
  classical
  change S.expPointOp side W u a = _
  rw [S.expPointOp_eq_convolution]
  simp only [Finset.sum_filter, Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro b _
  have h (c : PauliScalar P) : b + c = a ↔ c = a - b := by
    rw [eq_sub_iff_add_eq, add_comm]
  simp only [h, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  rfl

end ProjectiveSetting


end

end MIPStarRE.QPBT
