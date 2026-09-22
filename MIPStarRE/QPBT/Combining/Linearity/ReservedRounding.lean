import MIPStarRE.QPBT.Combining.Linearity.Extension

/-!
# Fourier--Naimark rounding in the allocated Boolean space

The reservation acts on the initial padding and leaves the Pauli register
unchanged. Every family of binary observables on the active expanded subspace
can use the same reservation, with the original averaged error constant.

## References

Paper `references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:825-832`
and blueprint `rem:linearity-import`. This auxiliary transports the proved
rounding theorem; constructing the source's earlier binary families and their
six-register comparisons remains part of issue #697 and
`docs/paper-gaps/qpbt_linearity-theorem-quotation.tex`.
-/

namespace MIPStarRE.QPBT

open MIPStarRE.Quantum MIPStarRE.LDT
open scoped BigOperators Matrix ComplexOrder

/-- The same reservation with the prescribed Pauli register left unchanged.
The ancillary coordinate is moved next to the active Naimark coordinate. -/
noncomputable def linearityExpandedReservationEmbedding (P : AdmissibleParams) (ι : Type) :
    (((ι × Option (PauliAnswer P)) × PauliRegister P) ×
      Option (Fin (2 * P.model.basisDim) → ZMod 2)) ↪
      ((ι × (Fin (Fintype.card (PauliAnswer P) + 1) → Bool)) × PauliRegister P) where
  toFun p := ((p.1.1.1, linearityPaddingEmbedding P (p.1.1.2, p.2)), p.1.2)
  inj' := by
    rintro ⟨⟨⟨i, a⟩, r⟩, k⟩ ⟨⟨⟨j, b⟩, s⟩, l⟩ h
    have hi := congrArg (fun p => p.1.1) h
    have hanc := (linearityPaddingEmbedding P).injective (congrArg (fun p => p.1.2) h)
    have hr := congrArg Prod.snd h
    simp only [Prod.mk.injEq] at hanc
    rcases hanc with ⟨ha, hk⟩
    cases hi
    cases ha
    cases hr
    cases hk
    rfl

/-- The ground slice keeps both the existing one-hot encoding and every Pauli
coordinate. In particular, its definition does not change `M = 2 ^ m`. -/
@[simp] theorem linearityExpandedReservationEmbedding_ground (P : AdmissibleParams)
    (ι : Type) (i : ι) (a : Option (PauliAnswer P)) (r : PauliRegister P) :
    linearityExpandedReservationEmbedding P ι (((i, a), r), none) =
      ((i, optionBoolEmbedding (PauliAnswer P) a), r) := by
  simp [linearityExpandedReservationEmbedding]

/-- The expanded reservation as a Euclidean isometry. It depends on `P` and
the original local index only, before any density or observable family. -/
noncomputable def linearityExpandedReservationIsometry (P : AdmissibleParams) (ι : Type)
    [Fintype ι] [DecidableEq ι] :
    EuclideanSpace ℂ (((ι × Option (PauliAnswer P)) × PauliRegister P) ×
      Option (Fin (2 * P.model.basisDim) → ZMod 2)) →ₗᵢ[ℂ]
      EuclideanSpace ℂ
        ((ι × (Fin (Fintype.card (PauliAnswer P) + 1) → Bool)) × PauliRegister P) :=
  indexEmbeddingIsometry (linearityExpandedReservationEmbedding P ι)

/-- Transport every fiber of the concrete Fourier--Naimark rounding into the
already allocated expanded player space. Exact linearity and the corrected
`2 * delta` bound are preserved, for one reservation chosen before all fibers.
The comparator and density below are the explicitly transported extension.
This is an auxiliary rounding theorem, not the full source absorption: their
identification with the earlier binary families on all four placements is
still required by `rem:linearity-import` and issue #697. -/
theorem linearity_padding_rounding_transport (P : AdmissibleParams) (ι : Type)
    [Fintype ι] [DecidableEq ι] {X : Type} (μ : Distribution X)
    (δ : X → ℝ)
    (ρ : Op ((ι × Option (PauliAnswer P)) × PauliRegister P))
    (hρ : ρ.PosSemidef) (htrace : ρ.trace = 1)
    (O : X → (Fin (2 * P.model.basisDim) → ZMod 2) →
      Op ((ι × Option (PauliAnswer P)) × PauliRegister P))
    (hO : ∀ x u, IsBinaryObservable (O x u))
    (hcorrelation : ∀ x, 1 - δ x ≤ avgOver
      (uniformDistribution ((Fin (2 * P.model.basisDim) → ZMod 2) ×
        (Fin (2 * P.model.basisDim) → ZMod 2)))
      (fun uv => (Matrix.trace (O x uv.1 * O x uv.2 * O x (uv.1 + uv.2) * ρ)).re)) :
    ∃ L : X → (Fin (2 * P.model.basisDim) → ZMod 2) →
        Op ((ι × (Fin (Fintype.card (PauliAnswer P) + 1) → Bool)) × PauliRegister P),
      (∀ x u, IsBinaryObservable (L x u)) ∧
      (∀ x u v, L x u * L x v = L x (u + v)) ∧
      (∀ x, L x 0 = 1) ∧
      avgOver μ (fun x => avgOver
        (uniformDistribution (Fin (2 * P.model.basisDim) → ZMod 2))
        (fun u => stateDepDistSq (L x u)
          (LinearityPadding.extendObservable (linearityExpandedReservationIsometry P ι)
            (heteroKron (O x u) 1))
          (conjIsometry (linearityExpandedReservationIsometry P ι)
            (heteroKron ρ (ancProj (naimarkAncilla (2 * P.model.basisDim))))))) ≤
        2 * avgOver μ δ := by
  let J := linearityExpandedReservationIsometry P ι
  refine ⟨fun x u => LinearityPadding.extendObservable J (roundedObservable (O x) (hO x) u),
    fun x u => LinearityPadding.extendObservable_binary J
      (roundedObservable_isBinaryObservable (O x) (hO x) u), ?_, ?_, ?_⟩
  · intro x u v
    rw [LinearityPadding.extendObservable_mul, roundedObservable_mul]
  · intro x
    dsimp only
    rw [roundedObservable_zero, LinearityPadding.extendObservable_one]
  · dsimp only [J]
    simp_rw [LinearityPadding.extendObservable_stateDepDistSq]
    calc
      _ ≤ avgOver μ (fun x => 2 * δ x) := by
        apply avgOver_mono
        intro x
        rw [avg_stateDepDistSq_roundedObservable_eq_avg_multiplicativeDefect
          (O x) (hO x) ρ hρ htrace]
        exact avg_multiplicativeDefect_le_two_mul_error
          (O x) (hO x) ρ hρ htrace (δ x) (hcorrelation x)
      _ = _ := avgOver_const_mul μ 2 δ

end MIPStarRE.QPBT
