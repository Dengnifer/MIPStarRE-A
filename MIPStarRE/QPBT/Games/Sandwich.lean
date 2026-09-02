import MIPStarRE.QPBT.Games.DistanceTheorems
import MIPStarRE.QPBT.Games.ErrorFunctions

/-! # Sandwiched measurements and pasting

This module defines the ordered palindromic products used to combine
measurements and records the two quantitative consistency statements imported
by the QPBT analysis.

## References

The source results are `lem:ld-sandwich` and `lem:pasting` in
`blueprint/src/chapter/ch12_qpbt_games.tex:357-427`, with paper origin
`references/qpbt-paper/06_nonlocal_games_and_mipstar.tex:465-525`.
-/

open scoped BigOperators Matrix ComplexOrder

namespace MIPStarRE.QPBT

open MIPStarRE.LDT MIPStarRE.Quantum

/-- The ordered product
`G^k_{g_k} ... G^1_{g_1} ... G^k_{g_k}` of `lem:ld-sandwich`.

**Local fix:** The source reverses the outcome indices, which is ill-typed when
the outcome families differ. This definition uses the pairing corrected in
`rem:ld-sandwich-indexing`; blueprint `ch12_qpbt_games.tex:364-391`, paper
`references/qpbt-paper/06_nonlocal_games_and_mipstar.tex:465-501`.
The empty product is `1`. -/
noncomputable def sandwichProduct {k : ℕ} {X Y ι : Type*}
    [Fintype ι] [DecidableEq ι] {R : Fin k → Type*}
    (G : (i : Fin k) → X → (Y → R i) → Op ι) (x : X)
    (g : (i : Fin k) → Y → R i) : Op ι :=
  let operators := List.ofFn (fun i : Fin k => G i x (g i))
  operators.reverse.prod * operators.tail.prod

/-- The two-family sandwiched product
`(G₂)_{g₂} (G₁)_{g₁} (G₂)_{g₂}` from `eq:pasting-2a`; blueprint
`ch12_qpbt_games.tex:402-427`, paper
`references/qpbt-paper/06_nonlocal_games_and_mipstar.tex:504-525`. -/
def pastedMeasurement {ι : Type*} [Fintype ι] [DecidableEq ι]
    {G₁ G₂ : Type*} (M₁ : G₁ → Op ι) (M₂ : G₂ → Op ι)
    (g₁ : G₁) (g₂ : G₂) : Op ι :=
  M₂ g₂ * M₁ g₁ * M₂ g₂

/-- Evaluating a tuple of function outcomes at a common point. This is a
formalization-only auxiliary for `lem:ld-sandwich`, blueprint
`ch12_qpbt_games.tex:364-385`, paper
`references/qpbt-paper/06_nonlocal_games_and_mipstar.tex:465-495`. -/
def evalFunctionTuple {k : ℕ} {Y : Type*} {R : Fin k → Type*}
    (y : Y) (g : (i : Fin k) → Y → R i) : (i : Fin k) → R i :=
  fun i => g i y

/-- The sandwiched simultaneous-measurement estimate of `lem:ld-sandwich`.
The universal asymptotic constant is quantified before the distribution,
measurements, state, and error parameters. Blueprint
`ch12_qpbt_games.tex:364-391`, paper
`references/qpbt-paper/06_nonlocal_games_and_mipstar.tex:465-501`. -/
theorem consistencyDefect_sandwich_le {k : ℕ} {X Y ι : Type*}
    [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y] [Nonempty Y]
    [Fintype ι] [DecidableEq ι] {R : Fin k → Type*}
    [∀ i, Fintype (R i)] [∀ i, DecidableEq (R i)] :
    ∃ C₀ : ℝ, 1 ≤ C₀ ∧ ∀ (μ : Distribution X)
      (G : (i : Fin k) → X → Measurement (Y → R i) ι)
      (A : X → Measurement ((i : Fin k) → Y → R i) ι)
      (ψ : EuclideanSpace ℂ ι) (ε δ : ℝ),
      μ.IsProbability → 0 < ε →
      (∀ i x, MIPStarRE.QPBT.Measurement.IsProjective (G i x)) →
      (∀ x, MIPStarRE.QPBT.Measurement.IsProjective (A x)) →
      (∀ i (g g' : Y → R i), g ≠ g' →
        avgOver (uniformDistribution Y)
          (fun y => if g y = g' y then 1 else 0) ≤ ε) →
      (∀ i, consistencyDefect (Distribution.prod μ (uniformDistribution Y))
        (fun xy a => (((A xy.1).postprocess
          (fun g => g i xy.2)).effect a))
        (fun xy a => (((G i xy.1).postprocess
          (fun g => g xy.2)).effect a)) ψ ≤ δ) →
      consistencyDefect (Distribution.prod μ (uniformDistribution Y))
        (fun xy a => (((A xy.1).postprocess
          (evalFunctionTuple xy.2)).effect a))
        (fun xy a => ∑ g : (i : Fin k) → Y → R i,
          if evalFunctionTuple xy.2 g = a then
            sandwichProduct (fun i x h => (G i x).effect h) xy.1 g else 0) ψ ≤
        C₀ * (k : ℝ) * Real.sqrt (δ + ε) := by
  sorry

/-- The positive-mass conditional collision bound used by `lem:pasting`.
This is a formalization-only spelling of the conditional probability in
`blueprint/src/chapter/ch12_qpbt_games.tex:394-427`, with paper origin
`references/qpbt-paper/06_nonlocal_games_and_mipstar.tex:504-525`. -/
def HasConditionalCollisionBound {X Y₁ Y₂ R₂ : Type*}
    [Fintype X] [DecidableEq X] [Fintype Y₁] [DecidableEq Y₁]
    [Fintype Y₂] [DecidableEq Y₂] [Fintype R₂] [DecidableEq R₂]
    (D : Distribution ((X × Y₁) × Y₂)) (G₂ : Finset (Y₂ → R₂))
    (η : ℝ) : Prop :=
  ∀ x y₁, 0 < (D.map Prod.fst).weight (x, y₁) →
    ∀ g ∈ G₂, ∀ g' ∈ G₂, g ≠ g' →
      (∑ y₂ : Y₂, D.weight ((x, y₁), y₂) *
        if g y₂ = g' y₂ then 1 else 0) ≤
        η * (D.map Prod.fst).weight (x, y₁)

/-- Pasting two consistent measurements yields a polynomially small error.
The output error predicate is the shared two-variable contract, and all
operator families in the conclusion are the postprocessed source families.
This is `lem:pasting`, blueprint `ch12_qpbt_games.tex:402-427`, paper
`references/qpbt-paper/06_nonlocal_games_and_mipstar.tex:504-525`. -/
theorem exists_pasting_error :
    ∃ δp : ℝ → ℝ → ℝ, IsPolyErr2 δp ∧
      ∀ {X Y₁ Y₂ R₁ R₂ ι : Type*}
        [Fintype X] [DecidableEq X] [Fintype Y₁] [DecidableEq Y₁]
        [Fintype Y₂] [DecidableEq Y₂] [Fintype R₁] [DecidableEq R₁]
        [Fintype R₂] [DecidableEq R₂] [Fintype ι] [DecidableEq ι]
        (D : Distribution ((X × Y₁) × Y₂))
        (G₁ : X → Measurement (Y₁ → R₁) ι)
        (G₂ : X → Measurement (Y₂ → R₂) ι)
        (A : ((X × Y₁) × Y₂) → Measurement (R₁ × R₂) ι)
        (ψ : EuclideanSpace ℂ ι) (η δ : ℝ),
        D.IsProbability → 0 ≤ η → 0 ≤ δ →
        (∀ x, MIPStarRE.QPBT.Measurement.IsProjective (G₂ x)) →
        (∀ q, MIPStarRE.QPBT.Measurement.IsProjective (A q)) →
        HasConditionalCollisionBound D (Finset.univ : Finset (Y₂ → R₂)) η →
        consistencyDefect D
          (fun q a₁ => ((A q).postprocess Prod.fst).effect a₁)
          (fun q a₁ => ((G₁ q.1.1).postprocess
            (fun g => g q.1.2)).effect a₁) ψ ≤ δ →
        consistencyDefect D
          (fun q a₂ => ((A q).postprocess Prod.snd).effect a₂)
          (fun q a₂ => ((G₂ q.1.1).postprocess
            (fun g => g q.2)).effect a₂) ψ ≤ δ →
        consistencyDefect D (fun q a => (A q).effect a)
          (fun q a => (A q).effect a) ψ ≤ δ →
        consistencyDefect D (fun q a => (A q).effect a)
          (fun q a => ∑ g₁ : Y₁ → R₁, ∑ g₂ : Y₂ → R₂,
            if (g₁ q.1.2, g₂ q.2) = a then
              pastedMeasurement (fun g => (G₁ q.1.1).effect g)
                (fun g => (G₂ q.1.1).effect g) g₁ g₂ else 0) ψ ≤ δp η δ := by
  sorry

end MIPStarRE.QPBT
