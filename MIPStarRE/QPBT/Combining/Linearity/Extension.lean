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

/-- The action of the extension on an embedded vector is exactly transported. -/
theorem extendObservable_apply (A : Op ι) (ψ : EuclideanSpace ℂ ι) :
    applyOperatorToState (extendObservable J A) (J ψ) =
      J (applyOperatorToState A ψ) := by
  have h := congrArg (fun V => Matrix.toEuclideanLin V ψ)
    (extendObservable_intertwines J A)
  simpa only [applyOperatorToState, toEuclideanLin_mul_apply, isometryMatrix,
    Matrix.toEuclideanLin.apply_symm_apply, LinearIsometry.coe_toLinearMap] using h

private theorem extendObservable_sub (A B : Op ι) :
    extendObservable J A - extendObservable J B = conjIsometry J (A - B) := by
  rw [conjIsometry_sub]
  unfold extendObservable
  abel

private theorem trace_conj (A : Op ι) : (conjIsometry J A).trace = A.trace := by
  rw [conjIsometry_eq, Matrix.trace_mul_cycle, isometryMatrix_conjTranspose_mul,
    Matrix.one_mul]

/-- Isometric extension preserves each density-weighted squared error. No
positivity or normalization is needed for this algebraic identity. -/
theorem extendObservable_stateDepDistSq (A B ρ : Op ι) :
    stateDepDistSq (extendObservable J A) (extendObservable J B) (conjIsometry J ρ) =
      stateDepDistSq A B ρ := by
  have hstar (C : Op ι) : (conjIsometry J C)ᴴ = conjIsometry J Cᴴ := by
    simp [conjIsometry_eq, Matrix.conjTranspose_mul, Matrix.mul_assoc]
  simp only [stateDepDistSq, extendObservable_sub, hstar, conjIsometry_mul, trace_conj]

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

/-- Each squared vector error is unchanged by extension across the reserved
subspace. This pointwise identity precedes, and justifies, all finite averages.
It applies in particular to the parameter-only reservation constructed above;
six-register placement and the source's earlier binary-rounding choices are
separate construction steps under issue #697. -/
theorem linearity_padding_error_transport {ι κ : Type}
    [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (J : EuclideanSpace ℂ ι →ₗᵢ[ℂ] EuclideanSpace ℂ κ)
    (A B : Op ι) (ψ : EuclideanSpace ℂ ι) :
    ‖applyOperatorToState
      (LinearityPadding.extendObservable J A - LinearityPadding.extendObservable J B)
      (J ψ)‖ ^ 2 = ‖applyOperatorToState (A - B) ψ‖ ^ 2 := by
  have hact (C D : Op κ) : applyOperatorToState (C - D) (J ψ) =
      applyOperatorToState C (J ψ) - applyOperatorToState D (J ψ) := by
    simp [applyOperatorToState]
  rw [hact, LinearityPadding.extendObservable_apply, LinearityPadding.extendObservable_apply,
    ← map_sub, J.norm_map]
  congr 2
  simp [applyOperatorToState]

/-- Compare a rounded operator on an extension with an original operator on
its ground slice. Both operators are extended by the identity on their
respective complementary subspaces. The equality retains the actual action
of the original operator, rather than replacing it by a compression of the
rounded measurement. In the reservation construction `E` is the canonical
ground embedding and `J` is the already constructed reservation. -/
theorem linearity_padding_ground_error_transport {ι κ ν : Type}
    [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    [Fintype ν] [DecidableEq ν]
    (J : EuclideanSpace ℂ κ →ₗᵢ[ℂ] EuclideanSpace ℂ ν)
    (E : EuclideanSpace ℂ ι →ₗᵢ[ℂ] EuclideanSpace ℂ κ)
    (L : Op κ) (O : Op ι) (ψ : EuclideanSpace ℂ ι) :
    ‖applyOperatorToState
      (LinearityPadding.extendObservable J L -
        LinearityPadding.extendObservable (J.comp E) O) ((J.comp E) ψ)‖ ^ 2 =
      ‖applyOperatorToState L (E ψ) - E (applyOperatorToState O ψ)‖ ^ 2 := by
  have hsub (A B : Op ν) (v : EuclideanSpace ℂ ν) :
      applyOperatorToState (A - B) v =
        applyOperatorToState A v - applyOperatorToState B v := by
    simp [applyOperatorToState]
  rw [hsub, LinearityPadding.extendObservable_apply]
  change ‖applyOperatorToState (LinearityPadding.extendObservable J L) (J (E ψ)) -
    J (E (applyOperatorToState O ψ))‖ ^ 2 = _
  rw [LinearityPadding.extendObservable_apply, ← map_sub, J.norm_map]

/-- Both finite averages preserve the same exact squared-error identity. The
embedding is quantified before the indices and all the operator families. -/
theorem linearity_padding_average_error_transport {ι κ : Type}
    [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (J : EuclideanSpace ℂ ι →ₗᵢ[ℂ] EuclideanSpace ℂ κ)
    {X U : Type} (μ : MIPStarRE.LDT.Distribution X) (ν : MIPStarRE.LDT.Distribution U)
    (A B : X → U → Op ι) (ψ : EuclideanSpace ℂ ι) :
    MIPStarRE.LDT.avgOver μ (fun x => MIPStarRE.LDT.avgOver ν (fun u =>
      ‖applyOperatorToState
        (LinearityPadding.extendObservable J (A x u) -
          LinearityPadding.extendObservable J (B x u)) (J ψ)‖ ^ 2)) =
      MIPStarRE.LDT.avgOver μ (fun x => MIPStarRE.LDT.avgOver ν (fun u =>
        ‖applyOperatorToState (A x u - B x u) ψ‖ ^ 2)) := by
  simp_rw [linearity_padding_error_transport]

end MIPStarRE.QPBT
