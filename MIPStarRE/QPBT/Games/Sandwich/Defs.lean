import MIPStarRE.QPBT.Games.Defs
import MIPStarRE.QPBT.Games.DistanceTheorems
import MIPStarRE.QPBT.Games.ErrorFunctions

/-! # Definitions for sandwiched measurements

This module defines the palindromic operator products and the conditional
collision predicate used by the sandwich and pasting lemmas.

## References

Blueprint `lem:ld-sandwich` and `lem:pasting`; paper
`references/qpbt-paper/06_nonlocal_games_and_mipstar.tex:465-525`.
-/

open scoped BigOperators MatrixOrder Matrix ComplexOrder

namespace MIPStarRE.QPBT

open MIPStarRE.LDT hiding Measurement
open MIPStarRE.Quantum
open DistanceCalculus

namespace SandwichProduct

/-- The ordered product of coordinate effects, defined recursively by placing
the final coordinate effect on both sides of the preceding product. This is the
palindromic product in `lem:ld-sandwich`; blueprint
`blueprint/src/chapter/ch12_qpbt_games.tex`, paper
`references/qpbt-paper/06_nonlocal_games_and_mipstar.tex:465-501`. -/
noncomputable def orderedCoordinateProduct {ι : Type*}
    [Fintype ι] [DecidableEq ι] :
    (k : ℕ) → (Γ : Fin k → Type*) →
      ((i : Fin k) → Γ i → Op ι) → ((i : Fin k) → Γ i) → Op ι
  | 0, _, _, _ => 1
  | 1, _, G, g => G 0 (g 0)
  | k + 2, Γ, G, g =>
      G (Fin.last (k + 1)) (g (Fin.last (k + 1))) *
        orderedCoordinateProduct (k + 1) (fun i => Γ i.castSucc)
          (fun i a => G i.castSucc a) (fun i => g i.castSucc) *
        G (Fin.last (k + 1)) (g (Fin.last (k + 1)))

end SandwichProduct

/-- The ordered product
`G^k_{g_k} ... G^1_{g_1} ... G^k_{g_k}` of `lem:ld-sandwich`.

**Local fix:** The source reverses the outcome indices, so the printed
expression is undefined when the outcome families differ. This definition uses
the pairing corrected in
`rem:ld-sandwich-indexing` and
`docs/paper-gaps/qpbt_ld-sandwich-indexing.tex`; blueprint statement
`lem:ld-sandwich` and remark `rem:ld-sandwich-indexing`, paper
`references/qpbt-paper/06_nonlocal_games_and_mipstar.tex:465-501`. Tracked in
issue #16. The empty product is `1`. -/
noncomputable def sandwichProduct {k : ℕ} {X ι : Type*}
    [Fintype ι] [DecidableEq ι] {Γ : Fin k → Type*}
    (G : (i : Fin k) → X → Γ i → Op ι) (x : X)
    (g : (i : Fin k) → Γ i) : Op ι :=
  SandwichProduct.orderedCoordinateProduct k Γ (fun i a => G i x a) g

/-- The two-family sandwiched product
`(G₂)_{g₂} (G₁)_{g₁} (G₂)_{g₂}` from blueprint
`eq:pasting-2a`, paper
`references/qpbt-paper/06_nonlocal_games_and_mipstar.tex:504-525`. -/
def pastedMeasurement {ι : Type*} [Fintype ι] [DecidableEq ι]
    {G₁ G₂ : Type*} (M₁ : G₁ → Op ι) (M₂ : G₂ → Op ι)
    (g₁ : G₁) (g₂ : G₂) : Op ι :=
  M₂ g₂ * M₁ g₁ * M₂ g₂

/-- Evaluating a tuple of codewords at a common point. This is a
formalization-only auxiliary for blueprint
`lem:ld-sandwich`, paper
`references/qpbt-paper/06_nonlocal_games_and_mipstar.tex:465-495`. -/
def evalFunctionTuple {k : ℕ} {Y : Type*} {R Γ : Fin k → Type*}
    (eval : (i : Fin k) → Γ i → Y → R i) (y : Y)
    (g : (i : Fin k) → Γ i) : (i : Fin k) → R i :=
  fun i => eval i (g i) y

/-- The positive-mass conditional collision bound used by `lem:pasting`.
This is a formalization-only spelling of the conditional probability in
`lem:pasting`, with paper origin
`references/qpbt-paper/06_nonlocal_games_and_mipstar.tex:504-525`. -/
def HasConditionalCollisionBound {X Y₁ Y₂ R₂ Γ₂ : Type*}
    [Fintype X] [DecidableEq X] [Fintype Y₁] [DecidableEq Y₁]
    [Fintype Y₂] [DecidableEq Y₂] [Fintype R₂] [DecidableEq R₂]
    [Fintype Γ₂]
    (D : Distribution ((X × Y₁) × Y₂)) (eval₂ : Γ₂ → Y₂ → R₂)
    (η : ℝ) : Prop :=
  ∀ x y₁, 0 < (D.map Prod.fst).weight (x, y₁) →
    ∀ g g' : Γ₂, g ≠ g' →
      (∑ y₂ : Y₂, D.weight ((x, y₁), y₂) *
        if eval₂ g y₂ = eval₂ g' y₂ then 1 else 0) ≤
        η * (D.map Prod.fst).weight (x, y₁)


/-! ### Tensor placements of measurements

The operator families compared in `lem:pasting` are placed on one factor of a
bipartite space. The two constructions below present such a placed family as a
measurement, so that the consistency calculus applies to it verbatim. -/

/-- An alias of `DistanceCalculus.leftPlacedMeasurement`, whose effects are the
left tensor placements of the effects of `M`. Formalization support for `lem:pasting`, blueprint
`ch12_qpbt_games.tex:960-990`. -/
noncomputable def Measurement.leftPlacement {α ιA ιB : Type*} [Fintype α]
    [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB]
    (M : Measurement α ιA) : Measurement α (ιA × ιB) :=
  DistanceCalculus.leftPlacedMeasurement M

/-- An alias of `DistanceCalculus.rightPlacedMeasurement`, whose effects are the
right tensor placements of the effects of `M`. Formalization support for `lem:pasting`, blueprint
`ch12_qpbt_games.tex:960-990`. -/
noncomputable def Measurement.rightPlacement {α ιA ιB : Type*} [Fintype α]
    [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB]
    (M : Measurement α ιB) : Measurement α (ιA × ιB) :=
  DistanceCalculus.rightPlacedMeasurement M

/-- The effects of the left placement. -/
@[simp] theorem Measurement.leftPlacement_effect {α ιA ιB : Type*} [Fintype α]
    [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB]
    (M : Measurement α ιA) (a : α) :
    (Measurement.leftPlacement (ιB := ιB) M).effect a = heteroKron (M.effect a) 1 := rfl

/-- The effects of the right placement. -/
@[simp] theorem Measurement.rightPlacement_effect {α ιA ιB : Type*} [Fintype α]
    [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB]
    (M : Measurement α ιB) (a : α) :
    (Measurement.rightPlacement (ιA := ιA) M).effect a = heteroKron 1 (M.effect a) := rfl

/-- The left placement of a projective measurement is projective.
Formalization support for `lem:pasting`, blueprint
`ch12_qpbt_games.tex:960-990`. -/
theorem Measurement.isProjective_leftPlacement {α ιA ιB : Type*} [Fintype α]
    [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB]
    (M : Measurement α ιA) (hM : MIPStarRE.QPBT.Measurement.IsProjective M) :
    MIPStarRE.QPBT.Measurement.IsProjective (Measurement.leftPlacement (ιB := ιB) M) := by
  intro a
  constructor
  · show heteroKron (M.effect a) 1 * heteroKron (M.effect a) 1 =
      heteroKron (M.effect a) 1
    rw [heteroKron_mul, (hM a).isIdempotentElem.eq, mul_one]
  · show (heteroKron (M.effect a) (1 : Op ιB))ᴴ = heteroKron (M.effect a) 1
    unfold heteroKron Matrix.kronecker
    rw [Matrix.conjTranspose_kronecker, measurement_effect_hermitian M a,
      Matrix.conjTranspose_one]

/-- The right placement of a projective measurement is projective. This is the
right-factor mirror of the preceding lemma and the second of the four
properties of the placement collected in the formalization-support node
`lem:pasting-tensor-placement`, blueprint `ch12_qpbt_games.tex:1063-1071`. -/
theorem Measurement.isProjective_rightPlacement {α ιA ιB : Type*} [Fintype α]
    [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB]
    (M : Measurement α ιB) (hM : MIPStarRE.QPBT.Measurement.IsProjective M) :
    MIPStarRE.QPBT.Measurement.IsProjective (Measurement.rightPlacement (ιA := ιA) M) := by
  intro a
  constructor
  · show heteroKron (1 : Op ιA) (M.effect a) * heteroKron 1 (M.effect a) =
      heteroKron 1 (M.effect a)
    rw [heteroKron_mul, (hM a).isIdempotentElem.eq, mul_one]
  · show (heteroKron (1 : Op ιA) (M.effect a))ᴴ = heteroKron 1 (M.effect a)
    unfold heteroKron Matrix.kronecker
    rw [Matrix.conjTranspose_kronecker, measurement_effect_hermitian M a,
      Matrix.conjTranspose_one]

/-- Postprocessing commutes with the left tensor placement. This is one of the
four properties of the placement collected in the formalization-support node
`lem:pasting-tensor-placement`, blueprint `ch12_qpbt_games.tex:1063-1071`; it
records the compatibility of the placement of `lem:pasting` with the outcome
coarse-grainings its statement applies, and is stated for the left factor
alongside its right-factor mirror below. -/
theorem Measurement.leftPlacement_postprocess {α β ιA ιB : Type*}
    [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB]
    (M : Measurement α ιA) (f : α → β) (b : β) :
    (Measurement.leftPlacement (ιB := ιB) (M.postprocess f)).effect b =
      ((Measurement.leftPlacement (ιB := ιB) M).postprocess f).effect b := by
  classical
  simp only [Measurement.leftPlacement_effect, Measurement.postprocess_effect,
    heteroKron_finset_sum_left]

/-- Postprocessing commutes with the right tensor placement. This is the
right-factor mirror of the preceding compatibility, the fourth of the four
properties of the placement collected in the formalization-support node
`lem:pasting-tensor-placement`, blueprint `ch12_qpbt_games.tex:1063-1071`. -/
theorem Measurement.rightPlacement_postprocess {α β ιA ιB : Type*}
    [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB]
    (M : Measurement α ιB) (f : α → β) (b : β) :
    (Measurement.rightPlacement (ιA := ιA) (M.postprocess f)).effect b =
      ((Measurement.rightPlacement (ιA := ιA) M).postprocess f).effect b := by
  classical
  simp only [Measurement.rightPlacement_effect, Measurement.postprocess_effect,
    heteroKron_finset_sum_right]


/-- The measurement obtained by relabelling the outcome set along a bijection.
Formalization support for `lem:pasting`, blueprint
`ch12_qpbt_games.tex:960-990`. -/
noncomputable def Measurement.congrAlphabet {α β ι : Type*} [Fintype α]
    [Fintype β] [Fintype ι] [DecidableEq ι] (e : β ≃ α) (M : Measurement α ι) :
    Measurement β ι :=
  Measurement.ofSumEqOne (fun b => M.effect (e b)) (fun b => M.pos (e b))
    ((e.sum_comp M.effect).trans M.sum_eq_one)

/-- The effects of a relabelled measurement. -/
@[simp] theorem Measurement.congrAlphabet_effect {α β ι : Type*} [Fintype α]
    [Fintype β] [Fintype ι] [DecidableEq ι] (e : β ≃ α) (M : Measurement α ι)
    (b : β) :
    (Measurement.congrAlphabet e M).effect b = M.effect (e b) := rfl

/-- Relabelling the outcome set preserves projectivity. Formalization support
for `lem:pasting`, blueprint `ch12_qpbt_games.tex:960-990`. -/
theorem Measurement.isProjective_congrAlphabet {α β ι : Type*} [Fintype α]
    [Fintype β] [Fintype ι] [DecidableEq ι] (e : β ≃ α) (M : Measurement α ι)
    (hM : MIPStarRE.QPBT.Measurement.IsProjective M) :
    MIPStarRE.QPBT.Measurement.IsProjective (Measurement.congrAlphabet e M) :=
  fun b => hM (e b)

/-- Postprocessing a relabelled measurement is the postprocessing of the
original measurement along the transported map. Formalization support for
`lem:pasting`, blueprint `ch12_qpbt_games.tex:960-990`. -/
theorem Measurement.postprocess_congrAlphabet {α β γ ι : Type*} [Fintype α]
    [DecidableEq α] [Fintype β] [DecidableEq β] [Fintype γ] [DecidableEq γ]
    [Fintype ι] [DecidableEq ι] (e : β ≃ α) (M : Measurement α ι)
    (f : β → γ) (c : γ) :
    ((Measurement.congrAlphabet e M).postprocess f).effect c =
      (M.postprocess (fun a => f (e.symm a))).effect c := by
  classical
  simp only [Measurement.postprocess_effect, Measurement.congrAlphabet_effect,
    Finset.sum_filter]
  rw [← Equiv.sum_comp e (fun a => if f (e.symm a) = c then M.effect a else 0)]
  simp

end MIPStarRE.QPBT
