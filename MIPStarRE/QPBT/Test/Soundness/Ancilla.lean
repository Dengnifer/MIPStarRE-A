import MIPStarRE.QPBT.Test.Soundness.RangeProjection

/-!
# Ancilla isometries for Pauli soundness

Adjoining a unit vector and applying a unitary gives the local isometry in the
final soundness argument. The exact intertwining identity below supplies the
algebraic hypothesis of the range-projection estimates. These results are
recorded in blueprint `thm:pauli-ancilla-intertwining-support`.

## References

Formalization support for blueprint `thm:pauli`, specifically the isometry at
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1864-1875`.
The registers are ordered as `AA'A''`, with the first two factors grouped.
These constructions do not assume or construct a global polynomial measurement.
-/

open scoped BigOperators Matrix MatrixOrder ComplexOrder

namespace MIPStarRE.QPBT

open MIPStarRE.Quantum MagicSquareRigidity

noncomputable section

variable {ι κ ν : Type} [Fintype ι] [DecidableEq ι]
  [Fintype κ] [DecidableEq κ] [Fintype ν] [DecidableEq ν]

/-- Adjoin a unit ancilla on the last two registers, in the extraction order
`(AA')A''`. The norm condition is precisely the normalization of that ancilla. -/
def ancillaBlockIsometry (eta : EuclideanSpace ℂ (κ × ν)) (heta : ‖eta‖ = 1) :
    EuclideanSpace ℂ ι →ₗᵢ[ℂ] EuclideanSpace ℂ ((ι × κ) × ν) where
  toFun psi := reindexState (Equiv.prodAssoc ι κ ν).symm (vecTensor psi eta)
  map_add' psi chi := by
    ext p
    simp [reindexState, vecTensor, add_mul]
  map_smul' c psi := by
    ext p
    simp [reindexState, vecTensor, mul_assoc]
  norm_map' psi := by
    change ‖reindexState (Equiv.prodAssoc ι κ ν).symm (vecTensor psi eta)‖ = ‖psi‖
    rw [reindexState_norm_eq, vecTensor_norm_eq, heta, mul_one]

/-- The columns of the ancilla isometry are the original basis vectors
tensored with the fixed ancilla. -/
theorem ancillaBlockIsometry_matrix_apply
    (eta : EuclideanSpace ℂ (κ × ν)) (heta : ‖eta‖ = 1)
    (p : (ι × κ) × ν) (i : ι) :
    isometryMatrix (ancillaBlockIsometry (ι := ι) eta heta) p i =
      if p.1.1 = i then eta (p.1.2, p.2) else 0 := by
  rw [isometryMatrix_apply]
  simp [ancillaBlockIsometry, reindexState, vecTensor, eq_comm]

/-- Extending an operator by identities commutes with adjoining a fixed ancilla.
This exact identity is independent of any success or consistency estimate. -/
theorem ancillaBlockIsometry_intertwines
    (eta : EuclideanSpace ℂ (κ × ν)) (heta : ‖eta‖ = 1) (M : Op ι) :
    heteroKron (heteroKron M (1 : Op κ)) (1 : Op ν) *
        isometryMatrix (ancillaBlockIsometry (ι := ι) eta heta) =
      isometryMatrix (ancillaBlockIsometry (ι := ι) eta heta) * M := by
  ext p i
  simp [Matrix.mul_apply, ancillaBlockIsometry_matrix_apply, heteroKron,
    Matrix.kronecker, Matrix.one_apply, Fintype.sum_prod_type, mul_comm]

/-- Apply a matrix isometry after adjoining the unit ancilla. In the source
proof the matrix is the swap unitary and the ancilla is the local EPR state. -/
def unitaryAncillaIsometry (eta : EuclideanSpace ℂ (κ × ν)) (heta : ‖eta‖ = 1)
    (U : Op ((ι × κ) × ν)) (hU : Uᴴ * U = 1) :
    EuclideanSpace ℂ ι →ₗᵢ[ℂ] EuclideanSpace ℂ ((ι × κ) × ν) where
  toLinearMap := (Matrix.toEuclideanLin U).comp
    (ancillaBlockIsometry eta heta).toLinearMap
  norm_map' psi := by
    change ‖Matrix.toEuclideanLin U (ancillaBlockIsometry eta heta psi)‖ = ‖psi‖
    rw [norm_toEuclideanLin_of_conjTranspose_mul_eq_one hU, LinearIsometry.norm_map]

/-- The matrix of the extraction isometry is the unitary times the ancilla
embedding, with no range projection omitted. -/
theorem unitaryAncillaIsometry_matrix
    (eta : EuclideanSpace ℂ (κ × ν)) (heta : ‖eta‖ = 1)
    (U : Op ((ι × κ) × ν)) (hU : Uᴴ * U = 1) :
    isometryMatrix (unitaryAncillaIsometry eta heta U hU) =
      U * isometryMatrix (ancillaBlockIsometry (ι := ι) eta heta) := by
  apply Matrix.toEuclideanLin.injective
  apply LinearMap.ext
  intro psi
  rw [toEuclideanLin_mul_apply]
  simp only [isometryMatrix, Matrix.toEuclideanLin.apply_symm_apply]
  rfl

/-- The unitary conjugate of an extended operator intertwines with the
extraction isometry. This proves the exact hypothesis needed by
`sum_norm_leftTensor_conjIsometry_sub_sq_le` and its Bob-side counterpart
for the local isometries used in the final proof of `thm:pauli`. -/
theorem unitaryAncillaIsometry_intertwines
    (eta : EuclideanSpace ℂ (κ × ν)) (heta : ‖eta‖ = 1)
    (U : Op ((ι × κ) × ν)) (hU : Uᴴ * U = 1) (M : Op ι) :
    (U * heteroKron (heteroKron M (1 : Op κ)) (1 : Op ν) * Uᴴ) *
        isometryMatrix (unitaryAncillaIsometry eta heta U hU) =
      isometryMatrix (unitaryAncillaIsometry eta heta U hU) * M := by
  rw [unitaryAncillaIsometry_matrix]
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc Uᴴ U, hU, Matrix.one_mul,
    ancillaBlockIsometry_intertwines]

end

end MIPStarRE.QPBT
