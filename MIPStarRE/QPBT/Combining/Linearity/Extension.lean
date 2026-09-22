import MIPStarRE.QPBT.Combining.Linearity.Reservation
import MIPStarRE.QPBT.Combining.Linearity
import MIPStarRE.QPBT.Test.MagicSquareTheorems.Rigidity.GroundSlice

/-!
# Extensions across the reserved linearity subspace

An exact observable acts as the identity on the complementary subspace. A
projective measurement assigns that subspace to its distinguished outcome.
These constructions retain the action on the embedded state exactly.

## References

This is formalization-only support for the padding used at
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:825-832`,
blueprint `rem:linearity-import`, and issue #697. The source construction is
tracked in `docs/paper-gaps/qpbt_linearity-theorem-quotation.tex`.
-/

namespace MIPStarRE.QPBT

open MIPStarRE.Quantum MagicSquareRigidity
open scoped BigOperators Matrix MatrixOrder ComplexOrder

namespace LinearityPadding

variable {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
variable (J : EuclideanSpace ℂ ι →ₗᵢ[ℂ] EuclideanSpace ℂ κ)

private theorem conj_isProj {A : Op ι} (hA : IsProj A) : IsProj (conjIsometry J A) := by
  constructor
  · change conjIsometry J A * conjIsometry J A = conjIsometry J A
    rw [conjIsometry_mul, hA.isIdempotentElem.eq]
  · change (conjIsometry J A)ᴴ = conjIsometry J A
    simp [conjIsometry_eq, Matrix.conjTranspose_mul, hA.isSelfAdjoint.isHermitian.eq,
      Matrix.mul_assoc]

private theorem conj_mul_embedding (A : Op ι) :
    conjIsometry J A * isometryMatrix J = isometryMatrix J * A := by
  simp [conjIsometry_eq, Matrix.mul_assoc, isometryMatrix_conjTranspose_mul]

/-- Extend an operator by the identity on the orthogonal complement of `J`.
For exactly linear observables this is the trivial representation there. -/
noncomputable def extendObservable (A : Op ι) : Op κ :=
  conjIsometry J A + (1 - conjIsometry J 1)

/-- Extension by the identity preserves multiplication. -/
theorem extendObservable_mul (A B : Op ι) :
    extendObservable J A * extendObservable J B = extendObservable J (A * B) := by
  simp only [extendObservable, add_mul, mul_add, sub_mul, mul_sub, one_mul, mul_one,
    conjIsometry_mul]
  abel

/-- The extended identity is the identity on the whole target space. -/
@[simp] theorem extendObservable_one : extendObservable J 1 = 1 := by
  simp [extendObservable]

/-- A binary observable remains a binary observable under this extension. -/
theorem extendObservable_binary {A : Op ι} (hA : IsBinaryObservable A) :
    IsBinaryObservable (extendObservable J A) := by
  constructor
  · change (extendObservable J A)ᴴ = extendObservable J A
    simp [extendObservable, conjIsometry_eq, Matrix.conjTranspose_mul,
      hA.conjTranspose_eq, Matrix.mul_assoc]
  · rw [extendObservable_mul, hA.mul_self_eq_one, extendObservable_one]

/-- The extended observable intertwines with the original one on the range. -/
theorem extendObservable_intertwines (A : Op ι) :
    extendObservable J A * isometryMatrix J = isometryMatrix J * A := by
  simp [extendObservable, Matrix.add_mul, Matrix.sub_mul, conj_mul_embedding]

private theorem measurement_effect_isProj {α : Type} [DecidableEq α]
    (a0 a : α) {A : Op ι} (hA : IsProj A) :
    IsProj (conjIsometry J A + if a = a0 then 1 - conjIsometry J 1 else 0) := by
  by_cases ha : a = a0
  · simp only [ha, if_true]
    apply (conj_isProj J hA).add ((conj_isProj J (IsStarProjection.one _)).one_sub)
    simp [mul_sub, conjIsometry_mul]
  · simpa [ha] using conj_isProj J hA

/-- Extend a projective measurement, assigning the complementary projection
to `a0`. The linearity application uses `a0 = 0`. -/
noncomputable def extendMeasurement {α : Type} [Fintype α] [DecidableEq α]
    (M : MIPStarRE.Quantum.Measurement α ι) (hM : Measurement.IsProjective M)
    (a0 : α) : MIPStarRE.Quantum.Measurement α κ :=
  MIPStarRE.Quantum.Measurement.ofSumEqOne
    (fun a => conjIsometry J (M.effect a) + if a = a0 then 1 - conjIsometry J 1 else 0)
    (fun a => (measurement_effect_isProj J a0 a (hM a)).nonneg)
    (by
      rw [Finset.sum_add_distrib]
      have hsum : ∑ a, conjIsometry J (M.effect a) = conjIsometry J 1 := by
        simp only [conjIsometry_eq, ← Matrix.sum_mul, ← Matrix.mul_sum, M.sum_eq_one]
      rw [hsum]
      simp)

end LinearityPadding

/-- Projective measurements extend across any constructed isometry by adding
the complementary projection to the distinguished outcome. Their effects
intertwine on the entire source space. Taking `J` to be the reservation above
and the outcome to be zero gives the required measurement-extension step.
This auxiliary constructs transport; it is not an assumed transport package
or the complete source absorption at paper
`14_analysis_of_the_pauli_basis_test.tex:825-832`. -/
theorem linearity_padding_measurement_transport {ι κ α : Type}
    [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    [Fintype α] [DecidableEq α]
    (J : EuclideanSpace ℂ ι →ₗᵢ[ℂ] EuclideanSpace ℂ κ)
    (M : MIPStarRE.Quantum.Measurement α ι) (hM : Measurement.IsProjective M) (a0 : α) :
    Measurement.IsProjective (LinearityPadding.extendMeasurement J M hM a0) ∧
      ∀ a, (LinearityPadding.extendMeasurement J M hM a0).effect a * isometryMatrix J =
        isometryMatrix J * M.effect a := by
  constructor
  · intro a
    exact LinearityPadding.measurement_effect_isProj J a0 a (hM a)
  · intro a
    change (conjIsometry J (M.effect a) +
      if a = a0 then 1 - conjIsometry J 1 else 0) * isometryMatrix J = _
    by_cases ha : a = a0 <;>
      simp [ha, Matrix.add_mul, Matrix.sub_mul, LinearityPadding.conj_mul_embedding]

end MIPStarRE.QPBT
