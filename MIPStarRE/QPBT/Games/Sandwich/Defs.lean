import MIPStarRE.QPBT.Games.DistanceTheorems
import MIPStarRE.QPBT.Games.ErrorFunctions

/-! # Definitions for sandwiched measurements

This module defines the palindromic operator products and the conditional
collision predicate used by the sandwich and pasting lemmas.

## References

Blueprint `blueprint/src/chapter/ch12_qpbt_games.tex:454-546`; paper
`references/qpbt-paper/06_nonlocal_games_and_mipstar.tex:465-525`.
-/

open scoped BigOperators MatrixOrder Matrix ComplexOrder

namespace MIPStarRE.QPBT

open MIPStarRE.LDT hiding Measurement
open MIPStarRE.Quantum
open DistanceCalculus

namespace SandwichInternal

/-- Recursive form of the palindromic operator product, extending a tuple by
placing its final operator on both sides of the preceding product. -/
noncomputable def sandwichProductCore {ι : Type*}
    [Fintype ι] [DecidableEq ι] :
    (k : ℕ) → (Γ : Fin k → Type*) →
      ((i : Fin k) → Γ i → Op ι) → ((i : Fin k) → Γ i) → Op ι
  | 0, _, _, _ => 1
  | 1, _, G, g => G 0 (g 0)
  | k + 2, Γ, G, g =>
      G (Fin.last (k + 1)) (g (Fin.last (k + 1))) *
        sandwichProductCore (k + 1) (fun i => Γ i.castSucc)
          (fun i a => G i.castSucc a) (fun i => g i.castSucc) *
        G (Fin.last (k + 1)) (g (Fin.last (k + 1)))

end SandwichInternal

/-- The ordered product
`G^k_{g_k} ... G^1_{g_1} ... G^k_{g_k}` of `lem:ld-sandwich`.

**Local fix:** The source reverses the outcome indices, which is ill-typed when
the outcome families differ. This definition uses the pairing corrected in
`rem:ld-sandwich-indexing` and
`docs/paper-gaps/qpbt_ld-sandwich-indexing.tex`; blueprint statement
`ch12_qpbt_games.tex:454-480` and remark `ch12_qpbt_games.tex:485-487`, paper
`references/qpbt-paper/06_nonlocal_games_and_mipstar.tex:465-501`. Tracked in
issue #16. The empty product is `1`. -/
noncomputable def sandwichProduct {k : ℕ} {X ι : Type*}
    [Fintype ι] [DecidableEq ι] {Γ : Fin k → Type*}
    (G : (i : Fin k) → X → Γ i → Op ι) (x : X)
    (g : (i : Fin k) → Γ i) : Op ι :=
  SandwichInternal.sandwichProductCore k Γ (fun i a => G i x a) g

/-- The two-family sandwiched product
`(G₂)_{g₂} (G₁)_{g₁} (G₂)_{g₂}` from `eq:pasting-2a`; blueprint
`ch12_qpbt_games.tex:517-546`, paper
`references/qpbt-paper/06_nonlocal_games_and_mipstar.tex:504-525`. -/
def pastedMeasurement {ι : Type*} [Fintype ι] [DecidableEq ι]
    {G₁ G₂ : Type*} (M₁ : G₁ → Op ι) (M₂ : G₂ → Op ι)
    (g₁ : G₁) (g₂ : G₂) : Op ι :=
  M₂ g₂ * M₁ g₁ * M₂ g₂

/-- Evaluating a tuple of codewords at a common point. This is a
formalization-only auxiliary for `lem:ld-sandwich`, blueprint
`ch12_qpbt_games.tex:454-480`, paper
`references/qpbt-paper/06_nonlocal_games_and_mipstar.tex:465-495`. -/
def evalFunctionTuple {k : ℕ} {Y : Type*} {R Γ : Fin k → Type*}
    (eval : (i : Fin k) → Γ i → Y → R i) (y : Y)
    (g : (i : Fin k) → Γ i) : (i : Fin k) → R i :=
  fun i => eval i (g i) y

/-- The positive-mass conditional collision bound used by `lem:pasting`.
This is a formalization-only spelling of the conditional probability in
`blueprint/src/chapter/ch12_qpbt_games.tex:517-546`, with paper origin
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

end MIPStarRE.QPBT
