import MIPStarRE.QPBT.Test.MagicSquareTheorems.Rigidity.Swap

/-!
# The two-qubit controlled-swap isometry

The conclusion of `thm:ms-rigidity` places each player's extracted register on
two qubits, indexed by `Fin 2 → ZMod 2`: the first carries the logical pair at
the cells `0` and `4`, the second the logical pair at the cells `1` and `3`.
`Rigidity/Swap.lean` builds the controlled-swap embedding attached to a single
anticommuting pair.  This file composes two of them.

For two pairs of binary observables `(X₁, Z₁)` and `(X₂, Z₂)` on one local
space, the map defined here sends a vector `ψ` to the family

    (e, i) ↦ (X₂^{e(1)} P^{Z₂}_{e(1)} X₁^{e(0)} P^{Z₁}_{e(0)} ψ) (i),

where `P^{Z}_b` is the spectral effect `reflectionEffect Z b`.  It is the
composition of the controlled swap of the first pair with the controlled swap
of the second pair applied to the residual copy of the local space, so it is an
*exact* isometry with no commutation assumption on the two pairs; approximate
commutation of the two pairs enters only when the second pair's observables are
transported through the first swap, which is not part of this file.

The first pair is applied innermost and is indexed by the register coordinate
`0`, matching `idealMagicBitProj`, whose marginal is taken over the coordinate
`0` of the label.

## References

`thm:ms-rigidity`, blueprint `blueprint/src/chapter/ch13_qpbt_test.tex:224-253`,
paper `references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:612-652`;
the cited robust self-test is Coladangelo--Stark, arXiv:1709.09267v2,
Theorem 6.9, `references/cs-paper/self-testing.tex:660-730`.  The one-qubit
construction is `binarySwapIsometry` in `Rigidity/Swap.lean`.
-/

open scoped BigOperators Matrix MatrixOrder ComplexOrder

namespace MIPStarRE.QPBT.MagicSquareRigidity

open MIPStarRE.LDT MIPStarRE.Quantum

noncomputable section

/-! ## Sums over a two-qubit label -/

/-- Formalization-only: a sum over two-qubit labels is a double sum over the two
coordinates. -/
theorem sum_pi_fin_two {M : Type*} [AddCommMonoid M] (f : ZMod 2 → ZMod 2 → M) :
    (∑ e : Fin 2 → ZMod 2, f (e 0) (e 1)) = ∑ b : ZMod 2, ∑ c : ZMod 2, f b c :=
  calc (∑ e : Fin 2 → ZMod 2, f (e 0) (e 1))
      = ∑ p : ZMod 2 × ZMod 2, f p.1 p.2 :=
        Fintype.sum_equiv (piFinTwoEquiv fun _ => ZMod 2) _ _ fun _ => rfl
    _ = ∑ b : ZMod 2, ∑ c : ZMod 2, f b c := Fintype.sum_prod_type _

/-- Formalization-only: the squared norm of the one-qubit controlled-swap image
is the sum of the squared norms of its two residual components. -/
theorem sum_norm_sq_binarySwapComponent {ι : Type} [Fintype ι] [DecidableEq ι]
    (X Z : Op ι) (v : EuclideanSpace ℂ ι) :
    (∑ b : ZMod 2,
        ‖applyOperatorToState (X ^ b.val * reflectionEffect Z b) v‖ ^ 2) =
      ‖binarySwapMap X Z v‖ ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq, Fintype.sum_prod_type]
  exact Finset.sum_congr rfl fun b _ => EuclideanSpace.norm_sq_eq _

/-- The two residual components of a controlled swap carry the whole squared
norm of the input.  This is `binarySwapMap_norm` in the form in which the
two-qubit construction iterates it. -/
theorem sum_norm_sq_binarySwapComponent_eq {ι : Type} [Fintype ι] [DecidableEq ι]
    (X Z : Op ι) (hX : IsBinaryObservable X) (hZ : IsBinaryObservable Z)
    (v : EuclideanSpace ℂ ι) :
    (∑ b : ZMod 2,
        ‖applyOperatorToState (X ^ b.val * reflectionEffect Z b) v‖ ^ 2) = ‖v‖ ^ 2 := by
  rw [sum_norm_sq_binarySwapComponent, binarySwapMap_norm X Z hX hZ]

/-! ## The two-qubit controlled-swap map -/

/-- Formalization-only linear controlled-swap map on a two-qubit register
supporting `thm:ms-rigidity`.  The component at the label `e` is obtained by
applying the residual component of the first pair at `e 0` and then that of the
second pair at `e 1`. -/
def twoBinarySwapMap {ι : Type} [Fintype ι] [DecidableEq ι]
    (X₁ Z₁ X₂ Z₂ : Op ι) :
    EuclideanSpace ℂ ι →ₗ[ℂ] EuclideanSpace ℂ ((Fin 2 → ZMod 2) × ι) where
  toFun ψ := (EuclideanSpace.equiv ((Fin 2 → ZMod 2) × ι) ℂ).symm
    (fun p => applyOperatorToState
      (X₂ ^ (p.1 1).val * reflectionEffect Z₂ (p.1 1) *
        (X₁ ^ (p.1 0).val * reflectionEffect Z₁ (p.1 0))) ψ p.2)
  map_add' ψ ξ := by
    apply (EuclideanSpace.equiv ((Fin 2 → ZMod 2) × ι) ℂ).injective
    funext p
    simp only [ContinuousLinearEquiv.apply_symm_apply]
    unfold applyOperatorToState
    rw [map_add]
    rfl
  map_smul' c ψ := by
    apply (EuclideanSpace.equiv ((Fin 2 → ZMod 2) × ι) ℂ).injective
    funext p
    simp only [ContinuousLinearEquiv.apply_symm_apply, RingHom.id_apply]
    unfold applyOperatorToState
    rw [map_smul]
    rfl

/-- Formalization-only coordinate formula for the two-qubit controlled-swap
map. -/
@[simp]
theorem twoBinarySwapMap_apply {ι : Type} [Fintype ι] [DecidableEq ι]
    (X₁ Z₁ X₂ Z₂ : Op ι) (ψ : EuclideanSpace ℂ ι) (e : Fin 2 → ZMod 2) (i : ι) :
    twoBinarySwapMap X₁ Z₁ X₂ Z₂ ψ (e, i) =
      applyOperatorToState
        (X₂ ^ (e 1).val * reflectionEffect Z₂ (e 1) *
          (X₁ ^ (e 0).val * reflectionEffect Z₁ (e 0))) ψ i := rfl

/-- The two-qubit controlled-swap map preserves norms whenever the four
controlling operators are binary observables.  No commutation assumption between
the two pairs is needed: the map is the composition of the controlled swap of
the first pair with the controlled swap of the second pair applied to the
residual space. -/
theorem twoBinarySwapMap_norm {ι : Type} [Fintype ι] [DecidableEq ι]
    (X₁ Z₁ X₂ Z₂ : Op ι)
    (hX₁ : IsBinaryObservable X₁) (hZ₁ : IsBinaryObservable Z₁)
    (hX₂ : IsBinaryObservable X₂) (hZ₂ : IsBinaryObservable Z₂)
    (ψ : EuclideanSpace ℂ ι) :
    ‖twoBinarySwapMap X₁ Z₁ X₂ Z₂ ψ‖ = ‖ψ‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [EuclideanSpace.norm_sq_eq, Fintype.sum_prod_type]
  have hcomp : ∀ (e : Fin 2 → ZMod 2),
      (∑ i : ι, ‖twoBinarySwapMap X₁ Z₁ X₂ Z₂ ψ (e, i)‖ ^ 2) =
        ‖applyOperatorToState (X₂ ^ (e 1).val * reflectionEffect Z₂ (e 1))
          (applyOperatorToState
            (X₁ ^ (e 0).val * reflectionEffect Z₁ (e 0)) ψ)‖ ^ 2 := by
    intro e
    rw [← MIPStarRE.QPBT.DistanceCalculus.applyOperatorToState_mul]
    exact (EuclideanSpace.norm_sq_eq (applyOperatorToState
      (X₂ ^ (e 1).val * reflectionEffect Z₂ (e 1) *
        (X₁ ^ (e 0).val * reflectionEffect Z₁ (e 0))) ψ)).symm
  rw [Finset.sum_congr rfl
    fun e (_ : e ∈ (Finset.univ : Finset (Fin 2 → ZMod 2))) => hcomp e]
  rw [sum_pi_fin_two (fun b c =>
    ‖applyOperatorToState (X₂ ^ c.val * reflectionEffect Z₂ c)
      (applyOperatorToState (X₁ ^ b.val * reflectionEffect Z₁ b) ψ)‖ ^ 2)]
  have hinner : ∀ b : ZMod 2,
      (∑ c : ZMod 2, ‖applyOperatorToState (X₂ ^ c.val * reflectionEffect Z₂ c)
          (applyOperatorToState (X₁ ^ b.val * reflectionEffect Z₁ b) ψ)‖ ^ 2) =
        ‖applyOperatorToState (X₁ ^ b.val * reflectionEffect Z₁ b) ψ‖ ^ 2 :=
    fun b => sum_norm_sq_binarySwapComponent_eq X₂ Z₂ hX₂ hZ₂ _
  rw [Finset.sum_congr rfl
    fun b (_ : b ∈ (Finset.univ : Finset (ZMod 2))) => hinner b]
  exact sum_norm_sq_binarySwapComponent_eq X₁ Z₁ hX₁ hZ₁ ψ

/-- Formalization-only local two-qubit controlled-swap embedding for
`thm:ms-rigidity`, bundled as a linear isometric embedding.  Its codomain is the
two-qubit register of the conclusion, `(Fin 2 → ZMod 2) × ι`. -/
noncomputable def twoBinarySwapIsometry {ι : Type} [Fintype ι] [DecidableEq ι]
    (X₁ Z₁ X₂ Z₂ : Op ι)
    (hX₁ : IsBinaryObservable X₁) (hZ₁ : IsBinaryObservable Z₁)
    (hX₂ : IsBinaryObservable X₂) (hZ₂ : IsBinaryObservable Z₂) :
    EuclideanSpace ℂ ι →ₗᵢ[ℂ] EuclideanSpace ℂ ((Fin 2 → ZMod 2) × ι) where
  toLinearMap := twoBinarySwapMap X₁ Z₁ X₂ Z₂
  norm_map' := twoBinarySwapMap_norm X₁ Z₁ X₂ Z₂ hX₁ hZ₁ hX₂ hZ₂

/-- Formalization-only coordinate formula for the two-qubit controlled-swap
isometry. -/
@[simp]
theorem twoBinarySwapIsometry_apply {ι : Type} [Fintype ι] [DecidableEq ι]
    (X₁ Z₁ X₂ Z₂ : Op ι)
    (hX₁ : IsBinaryObservable X₁) (hZ₁ : IsBinaryObservable Z₁)
    (hX₂ : IsBinaryObservable X₂) (hZ₂ : IsBinaryObservable Z₂)
    (ψ : EuclideanSpace ℂ ι) (e : Fin 2 → ZMod 2) (i : ι) :
    twoBinarySwapIsometry X₁ Z₁ X₂ Z₂ hX₁ hZ₁ hX₂ hZ₂ ψ (e, i) =
      applyOperatorToState
        (X₂ ^ (e 1).val * reflectionEffect Z₂ (e 1) *
          (X₁ ^ (e 0).val * reflectionEffect Z₁ (e 0))) ψ i := rfl

/-! ## Magic Square specialization -/

/-- Alice's local reflection at one position of a constraint question of the
projectively dilated strategy, before tensor placement.  It is the local factor
of `msCellObsA`, and the second logical pair of `Rigidity/SecondPair.lean` is
carried by these operators at the cells `1` and `3`. -/
noncomputable def msLocalCellObsA (S : Strategy msGame) (i : Fin 6) (k : Fin 3) :
    Op (msDilatedStrategy S).ιA :=
  signObs ((msDilatedStrategy S).A (MsType.constraint i)) (constraintBitOrZero k)

/-- Alice's dilated local constraint reflection is binary. -/
theorem isBinaryObservable_msLocalCellObsA (S : Strategy msGame) (i : Fin 6)
    (k : Fin 3) : IsBinaryObservable (msLocalCellObsA S i k) :=
  isBinaryObservable_signObs _ (msDilatedStrategy_isProjective_A S _) _

/-- The placed form of Alice's local constraint reflection. -/
theorem msCellObsA_eq_heteroKron (S : Strategy msGame) (i : Fin 6) (k : Fin 3) :
    msCellObsA S i k = heteroKron (msLocalCellObsA S i k) 1 := rfl

/-- The placed form of Alice's local variable reflection. -/
theorem msVarObsA_eq_heteroKron (S : Strategy msGame) (j : Fin 9) :
    msVarObsA S j = heteroKron (msLocalVarObsA S j) 1 := rfl

/-- The placed form of Bob's local variable reflection. -/
theorem msVarObsB_eq_heteroKron (S : Strategy msGame) (j : Fin 9) :
    msVarObsB S j = heteroKron 1 (msLocalVarObsB S j) := rfl

/-- Alice's two-qubit controlled-swap embedding for `thm:ms-rigidity`: the first
qubit is extracted from the logical pair at the cells `0` and `4`, read from her
variable questions, and the second from the logical pair at the cells `1` and
`3`, read from her constraint questions as in `Rigidity/SecondPair.lean`. -/
noncomputable def msAliceTwoQubitSwapIsometry (S : Strategy msGame) :
    EuclideanSpace ℂ (msDilatedStrategy S).ιA →ₗᵢ[ℂ]
      EuclideanSpace ℂ ((Fin 2 → ZMod 2) × (msDilatedStrategy S).ιA) :=
  twoBinarySwapIsometry (msLocalVarObsA S 0) (msLocalVarObsA S 4)
    (msLocalCellObsA S 0 1) (msLocalCellObsA S 1 0)
    (isBinaryObservable_msLocalVarObsA S 0) (isBinaryObservable_msLocalVarObsA S 4)
    (isBinaryObservable_msLocalCellObsA S 0 1) (isBinaryObservable_msLocalCellObsA S 1 0)

/-- Bob's two-qubit controlled-swap embedding for `thm:ms-rigidity`: both
logical pairs are read from his variable questions, at the cells `0` and `4` and
at the cells `1` and `3`. -/
noncomputable def msBobTwoQubitSwapIsometry (S : Strategy msGame) :
    EuclideanSpace ℂ (msDilatedStrategy S).ιB →ₗᵢ[ℂ]
      EuclideanSpace ℂ ((Fin 2 → ZMod 2) × (msDilatedStrategy S).ιB) :=
  twoBinarySwapIsometry (msLocalVarObsB S 0) (msLocalVarObsB S 4)
    (msLocalVarObsB S 1) (msLocalVarObsB S 3)
    (isBinaryObservable_msLocalVarObsB S 0) (isBinaryObservable_msLocalVarObsB S 4)
    (isBinaryObservable_msLocalVarObsB S 1) (isBinaryObservable_msLocalVarObsB S 3)

end

end MIPStarRE.QPBT.MagicSquareRigidity
