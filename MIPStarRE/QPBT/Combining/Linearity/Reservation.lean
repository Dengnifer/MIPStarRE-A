import MIPStarRE.QPBT.Observables.Setup
import MIPStarRE.QPBT.Test.PauliBasisTest
import MIPStarRE.QPBT.Test.Soundness.NaimarkReduction
import Mathlib.Logic.Equiv.Fintype

/-!
# Reserving the common linearity ancilla in Boolean padding

The active Naimark summand and the common linearity ancilla fit in the Boolean
cube already allocated by the initial projective strategy construction. The
reservation is chosen from the parameter tuple, before any observable family.

## References

The initial padding and its later use occur in
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:160-172,825-832`.
These are construction lemmas for blueprint `rem:linearity-import`, tracked in
`docs/paper-gaps/qpbt_linearity-theorem-quotation.tex` and issue #697.
-/

namespace MIPStarRE.QPBT

open MIPStarRE.LDT
open MagicSquareRigidity
open scoped BigOperators

/-- The existing Boolean allocation contains the active Naimark summand times
the common ancilla for the group of field pairs. The estimate follows from the
actual Pauli-answer alphabet and admissibility, without a capacity hypothesis.
This is a formalization-only construction lemma for the padding at paper
`14_analysis_of_the_pauli_basis_test.tex:160-172,825-832`. -/
theorem linearity_padding_capacity (P : AdmissibleParams) :
    Fintype.card (Option (PauliAnswer P) ×
      Option (Fin (2 * P.model.basisDim) → ZMod 2)) ≤
      Fintype.card (Fin (Fintype.card (PauliAnswer P) + 1) → Bool) := by
  have hfield : Fintype.card (PauliScalar P) = P.q :=
    @FieldModel.card P.q P.model.toFieldModel
  have hregister : P.q ^ (2 ^ P.m) ≤ Fintype.card (PauliAnswer P) := by
    have h := Fintype.card_le_of_injective
      (PauliAnswer.pauliOutcome (P := P)) (fun _ _ h => PauliAnswer.pauliOutcome.inj h)
    simpa [PauliRegister, Cube, Fintype.card_fun, hfield] using h
  have hm : 2 ≤ 2 ^ P.m := by
    simpa using Nat.pow_le_pow_right (by decide : 0 < 2) P.one_le_m
  have hqpos : 0 < P.q := lt_of_lt_of_le (by decide) P.hq.two_le
  have hq : P.q ^ 2 ≤ Fintype.card (PauliAnswer P) :=
    (Nat.pow_le_pow_right hqpos hm).trans hregister
  have hN : 4 ≤ Fintype.card (PauliAnswer P) := by
    have := P.hq.two_le
    nlinarith
  have hsquare : ∀ n : ℕ, 5 ≤ n → n ^ 2 ≤ 2 ^ n := by
    intro n hn
    induction n, hn using Nat.le_induction with
    | base => norm_num
    | succ n hn ih =>
        calc
          (n + 1) ^ 2 ≤ 2 * n ^ 2 := by nlinarith
          _ ≤ 2 * 2 ^ n := by omega
          _ = 2 ^ (n + 1) := by rw [pow_succ]; omega
  have hanc : 2 ^ (2 * P.model.basisDim) = P.q ^ 2 := by
    rw [Nat.mul_comm 2, pow_mul]
    exact congrArg (fun n : ℕ => n ^ 2) P.model.basisCard.symm
  simp only [Fintype.card_prod, Fintype.card_option, Fintype.card_fun,
    Fintype.card_fin, ZMod.card, Fintype.card_bool, hanc]
  calc
    (Fintype.card (PauliAnswer P) + 1) * (P.q ^ 2 + 1) ≤
        (Fintype.card (PauliAnswer P) + 1) ^ 2 := by nlinarith
    _ ≤ _ := hsquare _ (by omega)

/-- Choose the common ancillary index inside the existing Boolean cube, fixing
the complete active Naimark summand on the `none` slice. The choice depends only
on `P`, and therefore serves both players and every point pair simultaneously.
This constructs the index reservation required at paper
`14_analysis_of_the_pauli_basis_test.tex:825-832`; operator and state transport
are separate assertions. -/
theorem linearity_padding_ground_embedding (P : AdmissibleParams) :
    ∃ e : (Option (PauliAnswer P) ×
        Option (Fin (2 * P.model.basisDim) → ZMod 2)) ↪
        (Fin (Fintype.card (PauliAnswer P) + 1) → Bool),
      ∀ a : Option (PauliAnswer P),
        e (a, none) = optionBoolEmbedding (PauliAnswer P) a := by
  classical
  obtain ⟨f⟩ := Function.Embedding.nonempty_of_card_le (linearity_padding_capacity P)
  obtain ⟨σ, hσ⟩ := Equiv.Perm.exists_extending_pair
    (fun a : Option (PauliAnswer P) => f (a, none))
    (optionBoolEmbedding (PauliAnswer P))
    (fun _ _ h => congrArg Prod.fst (f.injective h))
    (optionBoolEmbedding (PauliAnswer P)).injective
  exact ⟨f.trans σ.toEmbedding, hσ⟩

/-- The common ancillary index, chosen independently of the strategy and all
families, inside the original Boolean allocation. -/
noncomputable def linearityPaddingEmbedding (P : AdmissibleParams) :
    (Option (PauliAnswer P) × Option (Fin (2 * P.model.basisDim) → ZMod 2)) ↪
      (Fin (Fintype.card (PauliAnswer P) + 1) → Bool) :=
  Classical.choose (linearity_padding_ground_embedding P)

/-- The chosen reservation restricts to the existing Naimark encoding. -/
@[simp] theorem linearityPaddingEmbedding_none (P : AdmissibleParams)
    (a : Option (PauliAnswer P)) :
    linearityPaddingEmbedding P (a, none) = optionBoolEmbedding (PauliAnswer P) a :=
  Classical.choose_spec (linearity_padding_ground_embedding P) a

/-- The Euclidean isometry induced by an injection of computational bases.
Mathlib's orthonormal-basis construction supplies the norm preservation. -/
noncomputable def indexEmbeddingIsometry {ι κ : Type}
    [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (e : ι ↪ κ) : EuclideanSpace ℂ ι →ₗᵢ[ℂ] EuclideanSpace ℂ κ := by
  let b : OrthonormalBasis ι ℂ (EuclideanSpace ℂ ι) := EuclideanSpace.basisFun ι ℂ
  let L : EuclideanSpace ℂ ι →ₗ[ℂ] EuclideanSpace ℂ κ :=
    b.toBasis.constr ℂ (fun i => EuclideanSpace.single (e i) (1 : ℂ))
  refine L.isometryOfOrthonormal (v := b.toBasis) b.orthonormal ?_
  simpa [L, Function.comp_def] using
    (EuclideanSpace.orthonormal_single (𝕜 := ℂ) (ι := κ)).comp e e.injective

/-- The matrix of an index embedding has the corresponding coordinate columns. -/
@[simp] theorem isometryMatrix_indexEmbeddingIsometry {ι κ : Type}
    [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (e : ι ↪ κ) (j : κ) (i : ι) :
    isometryMatrix (indexEmbeddingIsometry e) j i = if j = e i then 1 else 0 := by
  rw [isometryMatrix_apply]
  change (indexEmbeddingIsometry e (EuclideanSpace.single i 1)) j = _
  rw [← EuclideanSpace.basisFun_apply]
  simp [indexEmbeddingIsometry]

/-- The active Naimark coordinates in the initial padded local space. -/
noncomputable def linearityActiveIsometry (P : AdmissibleParams) (ι : Type)
    [Fintype ι] [DecidableEq ι] :
    EuclideanSpace ℂ (ι × Option (PauliAnswer P)) →ₗᵢ[ℂ]
      EuclideanSpace ℂ (ι × (Fin (Fintype.card (PauliAnswer P) + 1) → Bool)) :=
  indexEmbeddingIsometry
    ((Function.Embedding.refl ι).prodMap (optionBoolEmbedding (PauliAnswer P)))

/-- The common reservation on a player's original space; no Pauli register is
enlarged. Tensoring this isometry with its identity leaves `M = 2 ^ m` fixed. -/
noncomputable def linearityReservationIsometry (P : AdmissibleParams) (ι : Type)
    [Fintype ι] [DecidableEq ι] :
    EuclideanSpace ℂ ((ι × Option (PauliAnswer P)) ×
      Option (Fin (2 * P.model.basisDim) → ZMod 2)) →ₗᵢ[ℂ]
      EuclideanSpace ℂ (ι × (Fin (Fintype.card (PauliAnswer P) + 1) → Bool)) :=
  indexEmbeddingIsometry
    ((Equiv.prodAssoc ι _ _).toEmbedding.trans
      ((Function.Embedding.refl ι).prodMap (linearityPaddingEmbedding P)))

private theorem linearityReservationIsometry_ground (P : AdmissibleParams) (ι : Type)
    [Fintype ι] [DecidableEq ι] :
    (linearityReservationIsometry P ι).comp
        (naimarkEmbedding (ι × Option (PauliAnswer P))
          (Fin (2 * P.model.basisDim) → ZMod 2)) =
      linearityActiveIsometry P ι := by
  apply LinearIsometry.toLinearMap_injective
  apply Matrix.toEuclideanLin.symm.injective
  change isometryMatrix ((linearityReservationIsometry P ι).comp _) = _
  rw [isometryMatrix_comp]
  change isometryMatrix (linearityReservationIsometry P ι) *
    isometryMatrix (naimarkEmbedding _ _) = isometryMatrix (linearityActiveIsometry P ι)
  ext j i
  simp only [Matrix.mul_apply, linearityReservationIsometry, linearityActiveIsometry,
    isometryMatrix_indexEmbeddingIsometry]
  rw [Fintype.sum_prod_type]
  simp [isometryMatrix_apply, naimarkEmbedding_apply]
  rfl

/-- Appending the common pure ancilla to the active bipartite state and then
applying the reservation gives exactly its original Boolean embedding. This
identity is valid for every active state, so in particular for the actual
Option-indexed `pauliNaimarkStrategy`. It is the bipartite state-transport step
of the construction in paper `14_analysis_of_the_pauli_basis_test.tex:825-832`.
The six-register placements are separate transport assertions. -/
theorem linearity_padding_state_transport (P : AdmissibleParams) (ιA ιB : Type)
    [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB]
    (ψ : EuclideanSpace ℂ
      ((ιA × Option (PauliAnswer P)) × (ιB × Option (PauliAnswer P)))) :
    isometryTensor (linearityReservationIsometry P ιA)
        (linearityReservationIsometry P ιB)
        (naimarkDilatedState (Fin (2 * P.model.basisDim) → ZMod 2) ψ) =
      isometryTensor (linearityActiveIsometry P ιA) (linearityActiveIsometry P ιB) ψ := by
  rw [naimarkDilatedState, ← isometryTensor_comp,
    linearityReservationIsometry_ground, linearityReservationIsometry_ground]

end MIPStarRE.QPBT
