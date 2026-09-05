import MIPStarRE.QPBT.Test.MagicSquareTheorems.Rigidity.Transfer
import MIPStarRE.QPBT.Test.MagicSquareTheorems.Rigidity.IdealTarget

/-!
# Coarse estimates and the large-error regime of Magic Square rigidity

The rigidity theorem `thm:ms-rigidity` asserts a bound at the scale
`C * (sqrt ε + sqrt δ)` with a universal constant `C`.  Once `sqrt ε + sqrt δ`
exceeds one, that scale exceeds `C`, and the assertion is carried by the trivial
estimates available for *any* witness: two unit vectors are at distance at most
two, the state-dependent distance between two contractions on a unit vector is
at most two, and a two-outcome family therefore has squared distance at most
eight.

This file collects those estimates together with the elementary isometry used to
build a witness for an arbitrary strategy: the embedding of a local space as the
fiber of the extracted register over one fixed basis vector.  The estimates are
stated for the one-point distribution and the binary alphabet in which the
rigidity conclusions are phrased.

## References

blueprint `thm:ms-rigidity`,
paper `references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:612-652`.
The distance conventions are blueprint
`def:povm-distance`, paper `06_nonlocal_games_and_mipstar.tex:258-285`.
-/

open scoped BigOperators Matrix MatrixOrder ComplexOrder

namespace MIPStarRE.QPBT.MagicSquareRigidity

open MIPStarRE.LDT MIPStarRE.Quantum

noncomputable section

/-! ## The fiber embedding of a local space in an extracted register -/

/-- Formalization-only linear embedding of a local space as the fiber of a
register over one fixed basis vector.  It is the coarse counterpart of the
swap isometries of `Rigidity/Swap.lean`, used to exhibit a witness of
`thm:ms-rigidity` for an arbitrary strategy in the regime where the asserted
bound is vacuous. -/
def registerFiberEmbeddingMap (κ ι : Type) [Fintype κ] [DecidableEq κ]
    [Fintype ι] [DecidableEq ι] (k : κ) :
    EuclideanSpace ℂ ι →ₗ[ℂ] EuclideanSpace ℂ (κ × ι) where
  toFun x := (EuclideanSpace.equiv (κ × ι) ℂ).symm
    (fun p => if p.1 = k then x p.2 else 0)
  map_add' x y := by
    ext p
    by_cases h : p.1 = k <;> simp [h]
  map_smul' c x := by
    ext p
    by_cases h : p.1 = k <;> simp [h]

/-- Formalization-only isometric embedding of a local space as the fiber of a
register over one fixed basis vector. -/
noncomputable def registerFiberEmbedding (κ ι : Type) [Fintype κ] [DecidableEq κ]
    [Fintype ι] [DecidableEq ι] (k : κ) :
    EuclideanSpace ℂ ι →ₗᵢ[ℂ] EuclideanSpace ℂ (κ × ι) :=
  LinearMap.isometryOfInner (registerFiberEmbeddingMap κ ι k) <| by
    intro x y
    simp [PiLp.inner_apply, Fintype.sum_prod_type, registerFiberEmbeddingMap]

/-- The coordinates of the fiber embedding. -/
@[simp]
theorem registerFiberEmbedding_apply {κ ι : Type} [Fintype κ] [DecidableEq κ]
    [Fintype ι] [DecidableEq ι] (k : κ) (x : EuclideanSpace ℂ ι) (p : κ × ι) :
    registerFiberEmbedding κ ι k x p = if p.1 = k then x p.2 else 0 := rfl

/-! ## Coarse contraction estimates -/

/-- The negation of a contraction is a contraction. -/
theorem conjTranspose_mul_le_one_neg {ι : Type*} [Fintype ι] [DecidableEq ι]
    {M : Op ι} (h : Mᴴ * M ≤ 1) : (-M)ᴴ * (-M) ≤ 1 := by
  rwa [Matrix.conjTranspose_neg, neg_mul, mul_neg, neg_neg]

/-- Two contractions are at squared state-dependent distance at most four on a
unit vector, so a binary family of contractions is at distance at most eight in
the convention of `def:povm-distance`. -/
theorem opFamilyDistSq_uniform_unit_binary_le {ι : Type} [Fintype ι] [DecidableEq ι]
    (M N : Unit → ZMod 2 → Op ι) (ψ : EuclideanSpace ℂ ι) (hψ : ‖ψ‖ = 1)
    (hM : ∀ b : ZMod 2, (M () b)ᴴ * M () b ≤ 1)
    (hN : ∀ b : ZMod 2, (N () b)ᴴ * N () b ≤ 1) :
    opFamilyDistSq (uniformDistribution Unit) M N ψ ≤ 8 := by
  have hterm : ∀ b : ZMod 2, ‖applyOperatorToState (M () b - N () b) ψ‖ ^ 2 ≤ 4 := by
    intro b
    have h := norm_applyOperatorToState_sub_le (hM b) (hN b) ψ
    rw [hψ, mul_one] at h
    nlinarith [norm_nonneg (applyOperatorToState (M () b - N () b) ψ)]
  rw [opFamilyDistSq_uniform_unit, sum_zmod_two]
  linarith [hterm 0, hterm 1]

/-- Two contractions are at squared state-dependent distance at most four on a
unit vector, in the one-outcome convention of `def:povm-distance`. -/
theorem opDistSq_uniform_unit_le {ι : Type} [Fintype ι] [DecidableEq ι]
    (M N : Unit → Op ι) (ψ : EuclideanSpace ℂ ι) (hψ : ‖ψ‖ = 1)
    (hM : (M ())ᴴ * M () ≤ 1) (hN : (N ())ᴴ * N () ≤ 1) :
    opDistSq (uniformDistribution Unit) M N ψ ≤ 4 := by
  have h := norm_applyOperatorToState_sub_le hM hN ψ
  rw [hψ, mul_one] at h
  rw [opDistSq_uniform_unit]
  nlinarith [norm_nonneg (applyOperatorToState (M () - N ()) ψ)]

end

end MIPStarRE.QPBT.MagicSquareRigidity
