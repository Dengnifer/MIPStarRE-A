import MIPStarRE.QPBT.Games.DistanceTheorems.Support

/-!
# Finite controlled unitaries

A complete projective measurement controls a family of operators on a second
finite-dimensional space. Orthogonality of the measurement effects makes
multiplication of the resulting operator sums componentwise. In particular,
unitary components give a unitary controlled operator.

These are formalization-only algebraic lemmas, not the extraction theorem:
they do not construct the global measurement or establish the Pauli relations.

## References

- `references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1687-1700`,
  the unitarity calculation in the proof of `lem:qld-unitary`.
- Blueprint `def:v-swap-unitary` and `lem:v-swap-conjugation`.
-/

open scoped BigOperators Matrix

namespace MIPStarRE.Quantum

open MIPStarRE.QPBT

variable {Outcome Control Target : Type*}
variable [Fintype Outcome] [Fintype Control] [DecidableEq Control]
variable [Fintype Target]

/-- Multiplication of operator sums controlled by the same projective measurement
is componentwise. This isolates the orthogonality calculation in the proof of
`lem:qld-unitary`, before any unitarity of the controlled components is used. -/
theorem sum_heteroKron_mul_sum_heteroKron
    (measurement : Measurement Outcome Control)
    (hprojective : MIPStarRE.QPBT.Measurement.IsProjective measurement)
    (leftOperators rightOperators : Outcome → Op Target) :
    (∑ outcome, heteroKron (measurement.effect outcome) (leftOperators outcome)) *
        (∑ outcome, heteroKron (measurement.effect outcome) (rightOperators outcome)) =
      ∑ outcome, heteroKron (measurement.effect outcome)
        (leftOperators outcome * rightOperators outcome) := by
  classical
  rw [Finset.sum_mul]
  simp_rw [Finset.mul_sum, heteroKron_mul]
  apply Finset.sum_congr rfl
  intro outcome _
  rw [Finset.sum_eq_single outcome]
  · rw [(hprojective outcome).isIdempotentElem.eq]
  · intro other _ hother
    rw [DistanceCalculus.projective_effect_mul_effect_eq_zero
      measurement hprojective hother.symm]
    exact Matrix.zero_kronecker _
  · simp

variable [DecidableEq Target]

/-- A controlled operator times its adjoint is the identity when each component
times its adjoint is the identity. This is the finite controlled-unitary
calculation at paper `14_analysis_of_the_pauli_basis_test.tex:1687-1700`,
with arbitrary unitary components in place of the products of Pauli observables. -/
theorem sum_heteroKron_mul_conjTranspose
    (measurement : Measurement Outcome Control)
    (hprojective : MIPStarRE.QPBT.Measurement.IsProjective measurement)
    (operators : Outcome → Op Target)
    (hunitary : ∀ outcome, operators outcome * (operators outcome)ᴴ = 1) :
    (∑ outcome, heteroKron (measurement.effect outcome) (operators outcome)) *
        (∑ outcome, heteroKron (measurement.effect outcome) (operators outcome))ᴴ = 1 := by
  have hself (outcome : Outcome) :
      (measurement.effect outcome)ᴴ = measurement.effect outcome :=
    (hprojective outcome).isSelfAdjoint.star_eq
  calc
    _ = (∑ outcome, heteroKron (measurement.effect outcome) (operators outcome)) *
        (∑ outcome, heteroKron (measurement.effect outcome) ((operators outcome)ᴴ)) := by
      simp only [Matrix.conjTranspose_sum, heteroKron, Matrix.kronecker,
        Matrix.conjTranspose_kronecker, hself]
    _ = ∑ outcome, heteroKron (measurement.effect outcome)
        (operators outcome * (operators outcome)ᴴ) :=
      sum_heteroKron_mul_sum_heteroKron measurement hprojective _ _
    _ = ∑ outcome, heteroKron (measurement.effect outcome) (1 : Op Target) := by
      simp_rw [hunitary]
    _ = 1 := by
      rw [← DistanceCalculus.heteroKron_finset_sum_left, measurement.sum_eq_one,
        heteroKron_one_one]

/-- The reverse adjoint product of a controlled operator is also the identity.
For finite square matrices, Mathlib's `mul_eq_one_comm` converts either inverse
identity to the other, both for the components and for the controlled operator.
This supplies the reverse identity implicit in the same source calculation. -/
theorem conjTranspose_mul_sum_heteroKron
    (measurement : Measurement Outcome Control)
    (hprojective : MIPStarRE.QPBT.Measurement.IsProjective measurement)
    (operators : Outcome → Op Target)
    (hunitary : ∀ outcome, (operators outcome)ᴴ * operators outcome = 1) :
    (∑ outcome, heteroKron (measurement.effect outcome) (operators outcome))ᴴ *
        (∑ outcome, heteroKron (measurement.effect outcome) (operators outcome)) = 1 := by
  apply mul_eq_one_comm.mp
  apply sum_heteroKron_mul_conjTranspose measurement hprojective operators
  intro outcome
  exact mul_eq_one_comm.mp (hunitary outcome)

/-- A finite sum of unitary operators controlled by a complete projective
measurement is unitary. The hypotheses concern the actual component operators;
no unitarity or extraction conclusion is assumed for their controlled sum. -/
theorem sum_heteroKron_mem_unitary
    (measurement : Measurement Outcome Control)
    (hprojective : MIPStarRE.QPBT.Measurement.IsProjective measurement)
    (operators : Outcome → Op Target)
    (hunitary : ∀ outcome, operators outcome ∈ unitary (Op Target)) :
    (∑ outcome, heteroKron (measurement.effect outcome) (operators outcome)) ∈
      unitary (Op (Control × Target)) := by
  exact ⟨conjTranspose_mul_sum_heteroKron measurement hprojective operators
      (fun outcome => (hunitary outcome).1),
    sum_heteroKron_mul_conjTranspose measurement hprojective operators
      (fun outcome => (hunitary outcome).2)⟩

end MIPStarRE.Quantum
