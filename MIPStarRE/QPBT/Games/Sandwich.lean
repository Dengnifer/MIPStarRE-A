import MIPStarRE.QPBT.Games.DistanceTheorems
import MIPStarRE.QPBT.Games.ErrorFunctions

/-! # Sandwiched measurements and pasting

This module defines the ordered palindromic products used to combine
measurements and records the two quantitative consistency statements imported
by the QPBT analysis.

## References

The source results are blueprint `lem:ld-sandwich` and `lem:pasting`, with paper origin
`references/qpbt-paper/06_nonlocal_games_and_mipstar.tex:465-525`.
-/

open scoped BigOperators MatrixOrder Matrix ComplexOrder

namespace MIPStarRE.QPBT

open MIPStarRE.LDT hiding Measurement
open MIPStarRE.Quantum

/-- Recursive form of the palindromic operator product, extending a tuple by
placing its final operator on both sides of the preceding product. -/
private noncomputable def sandwichProductCore {ι : Type*}
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

/-- The ordered product
`G^k_{g_k} ... G^1_{g_1} ... G^k_{g_k}` of `lem:ld-sandwich`.

**Local fix:** The source reverses the outcome indices, which is ill-typed when
the outcome families differ. This definition uses the pairing corrected in
`rem:ld-sandwich-indexing` and
`docs/paper-gaps/qpbt_ld-sandwich-indexing.tex`; blueprint statement
`lem:ld-sandwich` and remark `rem:ld-sandwich-indexing`, paper
`references/qpbt-paper/06_nonlocal_games_and_mipstar.tex:465-501`. Tracked in
issue #16. The empty product is `1`. -/
noncomputable def sandwichProduct {k : ℕ} {X ι : Type*}
    [Fintype ι] [DecidableEq ι] {Γ : Fin k → Type*}
    (G : (i : Fin k) → X → Γ i → Op ι) (x : X)
    (g : (i : Fin k) → Γ i) : Op ι :=
  sandwichProductCore k Γ (fun i a => G i x a) g

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

/-- The palindromic effects form a POVM when each constituent measurement is
projective. This is `lem:ld-sandwich-measurement`, the measurement assertion
implicit in `lem:ld-sandwich`; blueprint `lem:ld-sandwich-measurement`, paper
`references/qpbt-paper/06_nonlocal_games_and_mipstar.tex:484-494`. -/
theorem sandwichProduct_isMeasurement {k : ℕ} {X ι : Type*}
    [Fintype ι] [DecidableEq ι] {Γ : Fin k → Type*}
    [∀ i, Fintype (Γ i)] (G : (i : Fin k) → X → Measurement (Γ i) ι)
    (hG : ∀ i x, MIPStarRE.QPBT.Measurement.IsProjective (G i x)) (x : X) :
    (∀ g : (i : Fin k) → Γ i,
      0 ≤ sandwichProduct (fun i x' a => (G i x').effect a) x g) ∧
      (∑ g : (i : Fin k) → Γ i,
        sandwichProduct (fun i x' a => (G i x').effect a) x g) = 1 := by
  classical
  induction k with
  | zero =>
      constructor
      · intro g
        change 0 ≤ (1 : Op ι)
        exact Matrix.PosSemidef.one.nonneg
      · simp [sandwichProduct, sandwichProductCore]
  | succ k ih =>
      cases k with
      | zero =>
          constructor
          · intro g
            change 0 ≤ (G 0 x).effect (g 0)
            exact (G 0 x).pos (g 0)
          · change
              (∑ g : (i : Fin 1) → Γ i,
                (G 0 x).effect (g 0)) = 1
            calc
              (∑ g : (i : Fin 1) → Γ i, (G 0 x).effect (g 0)) =
                  ∑ p : Γ 0 × ((i : Fin 0) → Γ i.castSucc),
                    (G 0 x).effect (((Fin.snocEquiv Γ) p) 0) := by
                exact Fintype.sum_equiv (Fin.snocEquiv Γ).symm _ _
                  (by intro g; rw [Equiv.apply_symm_apply])
              _ = ∑ a : Γ 0, (G 0 x).effect a := by
                rw [Fintype.sum_prod_type]
                apply Finset.sum_congr rfl
                intro a _
                simp only [Fintype.sum_unique]
                congr 1
              _ = 1 := (G 0 x).sum_eq_one
      | succ k =>
          have hprev := ih
            (G := fun i x' => G i.castSucc x')
            (hG := fun i x' => hG i.castSucc x')
          constructor
          · intro g
            change 0 ≤
              (G (Fin.last (k + 1)) x).effect (g (Fin.last (k + 1))) *
                sandwichProductCore (k + 1) (fun i => Γ i.castSucc)
                  (fun i a => (G i.castSucc x).effect a)
                  (fun i => g i.castSucc) *
                (G (Fin.last (k + 1)) x).effect (g (Fin.last (k + 1)))
            have hinner := hprev.1 (fun i => g i.castSucc)
            apply Matrix.nonneg_iff_posSemidef.mpr
            have hpos :
                (((G (Fin.last (k + 1)) x).effect (g (Fin.last (k + 1))))ᴴ *
                  sandwichProductCore (k + 1) (fun i => Γ i.castSucc)
                    (fun i a => (G i.castSucc x).effect a)
                    (fun i => g i.castSucc) *
                  (G (Fin.last (k + 1)) x).effect
                    (g (Fin.last (k + 1)))).PosSemidef :=
              (Matrix.nonneg_iff_posSemidef.mp hinner).conjTranspose_mul_mul_same _
            rw [MIPStarRE.QPBT.DistanceCalculus.measurement_effect_hermitian] at hpos
            exact hpos
          · change
              (∑ g : (i : Fin (k + 2)) → Γ i,
                sandwichProductCore (k + 2) Γ
                  (fun i a => (G i x).effect a) g) = 1
            calc
              (∑ g : (i : Fin (k + 2)) → Γ i,
                  sandwichProductCore (k + 2) Γ
                    (fun i a => (G i x).effect a) g) =
                  ∑ p : Γ (Fin.last (k + 1)) ×
                      ((i : Fin (k + 1)) → Γ i.castSucc),
                    sandwichProductCore (k + 2) Γ
                      (fun i a => (G i x).effect a) ((Fin.snocEquiv Γ) p) := by
                exact Fintype.sum_equiv (Fin.snocEquiv Γ).symm _ _
                  (by intro g; rw [Equiv.apply_symm_apply])
              _ = ∑ a : Γ (Fin.last (k + 1)),
                    ∑ g : (i : Fin (k + 1)) → Γ i.castSucc,
                      (G (Fin.last (k + 1)) x).effect a *
                        sandwichProductCore (k + 1) (fun i => Γ i.castSucc)
                          (fun i b => (G i.castSucc x).effect b) g *
                        (G (Fin.last (k + 1)) x).effect a := by
                rw [Fintype.sum_prod_type]
                apply Finset.sum_congr rfl
                intro a _
                apply Finset.sum_congr rfl
                intro g _
                simp [sandwichProductCore]
              _ = ∑ a : Γ (Fin.last (k + 1)),
                    (G (Fin.last (k + 1)) x).effect a *
                      (∑ g : (i : Fin (k + 1)) → Γ i.castSucc,
                        sandwichProductCore (k + 1) (fun i => Γ i.castSucc)
                          (fun i b => (G i.castSucc x).effect b) g) *
                      (G (Fin.last (k + 1)) x).effect a := by
                apply Finset.sum_congr rfl
                intro a _
                rw [Finset.mul_sum, Finset.sum_mul]
              _ = ∑ a : Γ (Fin.last (k + 1)),
                    (G (Fin.last (k + 1)) x).effect a := by
                have hprevSum := hprev.2
                change
                  (∑ g : (i : Fin (k + 1)) → Γ i.castSucc,
                    sandwichProductCore (k + 1) (fun i => Γ i.castSucc)
                      (fun i b => (G i.castSucc x).effect b) g) = 1 at hprevSum
                apply Finset.sum_congr rfl
                intro a _
                rw [hprevSum, mul_one,
                  (hG (Fin.last (k + 1)) x a).isIdempotentElem.eq]
              _ = 1 := (G (Fin.last (k + 1)) x).sum_eq_one

/-- The sandwiched simultaneous-measurement estimate of `lem:ld-sandwich`.
One universal asymptotic constant applies independently of the distribution,
measurements, state, and error parameters. Blueprint
`lem:ld-sandwich`, paper
`references/qpbt-paper/06_nonlocal_games_and_mipstar.tex:465-501`. -/
theorem consistencyDefect_sandwich_le :
    ∃ C₀ : ℝ, 1 ≤ C₀ ∧
      ∀ {k : ℕ} {X Y ιA ιB : Type*} {R Γ : Fin k → Type*}
        [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y] [Nonempty Y]
        [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB]
        [∀ i, Fintype (R i)] [∀ i, DecidableEq (R i)]
        [∀ i, Fintype (Γ i)] [∀ i, DecidableEq (Γ i)]
        (μ : Distribution X)
        (eval : (i : Fin k) → Γ i → Y → R i)
        (G : (i : Fin k) → X → Measurement (Γ i) ιB)
        (A : X → Measurement ((i : Fin k) → Γ i) ιA)
        (ψ : EuclideanSpace ℂ (ιA × ιB)) (ε δ : ℝ),
      μ.IsProbability → ‖ψ‖ = 1 → 0 < ε → 0 ≤ δ →
      (∀ i x, MIPStarRE.QPBT.Measurement.IsProjective (G i x)) →
      (∀ x, MIPStarRE.QPBT.Measurement.IsProjective (A x)) →
      (∀ i (g g' : Γ i), g ≠ g' →
        avgOver (uniformDistribution Y)
          (fun y => if eval i g y = eval i g' y then 1 else 0) ≤ ε) →
      (∀ i, consistencyDefect (Distribution.prod μ (uniformDistribution Y))
        (fun xy a => heteroKron (((A xy.1).postprocess
          (fun g => eval i (g i) xy.2)).effect a) 1)
        (fun xy a => heteroKron 1 (((G i xy.1).postprocess
          (fun g => eval i g xy.2)).effect a)) ψ ≤ δ) →
      consistencyDefect (Distribution.prod μ (uniformDistribution Y))
        (fun xy a => heteroKron (((A xy.1).postprocess
          (evalFunctionTuple eval xy.2)).effect a) 1)
        (fun xy a => heteroKron 1 (∑ g : (i : Fin k) → Γ i,
          if evalFunctionTuple eval xy.2 g = a then
            sandwichProduct (fun i x h => (G i x).effect h) xy.1 g else 0)) ψ ≤
        C₀ * (k : ℝ) * Real.sqrt (δ + ε) := by
  sorry

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

/-- The effects obtained by sandwiching one measurement with a projective
measurement form a POVM. This is `lem:pasting-measurement`, the measurement
assertion for `eq:pasting-2a`; blueprint `lem:pasting-measurement`, paper
`references/qpbt-paper/06_nonlocal_games_and_mipstar.tex:514-524`. -/
theorem pastedMeasurement_isMeasurement {Γ₁ Γ₂ ι : Type*}
    [Fintype Γ₁] [Fintype Γ₂] [Fintype ι] [DecidableEq ι]
    (G₁ : Measurement Γ₁ ι) (G₂ : Measurement Γ₂ ι)
    (hG₂ : MIPStarRE.QPBT.Measurement.IsProjective G₂) :
    (∀ g : Γ₁ × Γ₂,
      0 ≤ pastedMeasurement G₁.effect G₂.effect g.1 g.2) ∧
      (∑ g : Γ₁ × Γ₂,
        pastedMeasurement G₁.effect G₂.effect g.1 g.2) = 1 := by
  constructor
  · intro g
    unfold pastedMeasurement
    apply Matrix.nonneg_iff_posSemidef.mpr
    have hpos : ((G₂.effect g.2)ᴴ * G₁.effect g.1 * G₂.effect g.2).PosSemidef :=
      (Matrix.nonneg_iff_posSemidef.mp (G₁.pos g.1)).conjTranspose_mul_mul_same
        (G₂.effect g.2)
    rw [MIPStarRE.QPBT.DistanceCalculus.measurement_effect_hermitian G₂ g.2] at hpos
    exact hpos
  · classical
    unfold pastedMeasurement
    rw [Fintype.sum_prod_type, Finset.sum_comm]
    calc
      (∑ g₂ : Γ₂, ∑ g₁ : Γ₁,
          G₂.effect g₂ * G₁.effect g₁ * G₂.effect g₂) =
          ∑ g₂ : Γ₂,
            G₂.effect g₂ * (∑ g₁ : Γ₁, G₁.effect g₁) * G₂.effect g₂ := by
        apply Finset.sum_congr rfl
        intro g₂ _
        rw [Finset.mul_sum, Finset.sum_mul]
      _ = ∑ g₂ : Γ₂, G₂.effect g₂ := by
        apply Finset.sum_congr rfl
        intro g₂ _
        rw [G₁.sum_eq_one, mul_one, (hG₂ g₂).isIdempotentElem.eq]
      _ = 1 := G₂.sum_eq_one

/-- Pasting two consistent measurements yields a product-form polynomial
error. All operator families in the conclusion are the postprocessed source
families. This is blueprint `lem:pasting`, paper
`references/qpbt-paper/06_nonlocal_games_and_mipstar.tex:504-525`. -/
theorem exists_pasting_error :
    ∃ δp : ℝ → ℝ → ℝ, IsPolyErr₂ δp ∧
      ∀ {X Y₁ Y₂ R₁ R₂ Γ₁ Γ₂ ι : Type*}
        [Fintype X] [DecidableEq X] [Fintype Y₁] [DecidableEq Y₁]
        [Fintype Y₂] [DecidableEq Y₂] [Fintype R₁] [DecidableEq R₁]
        [Fintype R₂] [DecidableEq R₂]
        [Fintype Γ₁] [DecidableEq Γ₁] [Fintype Γ₂] [DecidableEq Γ₂]
        [Fintype ι] [DecidableEq ι]
        (D : Distribution ((X × Y₁) × Y₂))
        (eval₁ : Γ₁ → Y₁ → R₁) (eval₂ : Γ₂ → Y₂ → R₂)
        (G₁ : X → Measurement Γ₁ ι) (G₂ : X → Measurement Γ₂ ι)
        (A : ((X × Y₁) × Y₂) → Measurement (R₁ × R₂) ι)
        (ψ : EuclideanSpace ℂ (ι × ι)) (η δ : ℝ),
        D.IsProbability → ‖ψ‖ = 1 → 0 ≤ η → 0 ≤ δ →
        (∀ x, MIPStarRE.QPBT.Measurement.IsProjective (G₂ x)) →
        (∀ q, MIPStarRE.QPBT.Measurement.IsProjective (A q)) →
        HasConditionalCollisionBound D eval₂ η →
        consistencyDefect D
          (fun q a₁ => heteroKron (((A q).postprocess Prod.fst).effect a₁) 1)
          (fun q a₁ => heteroKron 1 (((G₁ q.1.1).postprocess
            (fun g => eval₁ g q.1.2)).effect a₁)) ψ ≤ δ →
        consistencyDefect D
          (fun q a₂ => heteroKron (((A q).postprocess Prod.snd).effect a₂) 1)
          (fun q a₂ => heteroKron 1 (((G₂ q.1.1).postprocess
            (fun g => eval₂ g q.2)).effect a₂)) ψ ≤ δ →
        consistencyDefect D (fun q a => heteroKron ((A q).effect a) 1)
          (fun q a => heteroKron 1 ((A q).effect a)) ψ ≤ δ →
        consistencyDefect D (fun q a => heteroKron ((A q).effect a) 1)
          (fun q a => heteroKron 1 (∑ g₁ : Γ₁, ∑ g₂ : Γ₂,
            if (eval₁ g₁ q.1.2, eval₂ g₂ q.2) = a then
              pastedMeasurement (fun g => (G₁ q.1.1).effect g)
                (fun g => (G₂ q.1.1).effect g) g₁ g₂ else 0)) ψ ≤ δp η δ := by
  sorry

end MIPStarRE.QPBT
