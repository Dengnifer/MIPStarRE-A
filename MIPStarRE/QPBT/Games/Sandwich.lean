import MIPStarRE.QPBT.Games.Sandwich.Pasting4

/-! # Sandwiched measurements and pasting

This module records the ordered palindromic products used to combine
measurements and the two quantitative consistency statements used in the QPBT
analysis.

## References

The source results are `lem:ld-sandwich` and `lem:pasting` in
`blueprint/src/chapter/ch12_qpbt_games.tex:469-1014`, with paper origin
`references/qpbt-paper/06_nonlocal_games_and_mipstar.tex:465-525`.
-/

open scoped BigOperators MatrixOrder Matrix ComplexOrder

namespace MIPStarRE.QPBT

open MIPStarRE.LDT hiding Measurement
open MIPStarRE.Quantum
open DistanceCalculus

/-- The palindromic effects form a POVM when each constituent measurement is
projective. This is `lem:ld-sandwich-measurement`, the measurement assertion
implicit in `lem:ld-sandwich`; blueprint `ch12_qpbt_games.tex:548-568`, paper
`references/qpbt-paper/06_nonlocal_games_and_mipstar.tex:484-494`. -/
theorem sandwichProduct_isMeasurement {k : ℕ} {X ι : Type*}
    [Fintype ι] [DecidableEq ι] {Γ : Fin k → Type*}
    [∀ i, Fintype (Γ i)] (G : (i : Fin k) → X → Measurement (Γ i) ι)
    (hG : ∀ i x, MIPStarRE.QPBT.Measurement.IsProjective (G i x)) (x : X) :
    (∀ g : (i : Fin k) → Γ i,
      0 ≤ sandwichProduct (fun i x' a => (G i x').effect a) x g) ∧
      (∑ g : (i : Fin k) → Γ i,
        sandwichProduct (fun i x' a => (G i x').effect a) x g) = 1 := by
  exact SandwichProduct.sandwichProduct_isMeasurement G hG x

/-- The sandwiched simultaneous-measurement estimate of `lem:ld-sandwich`.
One universal asymptotic constant applies independently of the distribution,
measurements, state, and error parameters. Blueprint
`ch12_qpbt_games.tex:469-496`, paper
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
  exact SandwichProduct.consistencyDefect_sandwich_le

/-- The effects obtained by sandwiching one measurement with a projective
measurement form a POVM. This is `lem:pasting-measurement`, the measurement
assertion for `eq:pasting-2a`; blueprint `ch12_qpbt_games.tex:995-1014`, paper
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
/-- Pasting two consistent measurements yields an additive polynomial error.
All operator families in the conclusion are the postprocessed source
families. This is `lem:pasting`, blueprint `ch12_qpbt_games.tex:960-990`, paper
`references/qpbt-paper/06_nonlocal_games_and_mipstar.tex:504-525`.

**Boundary hypothesis (ambient convention of the source):** the source states
the lemma for symmetric strategies
(`references/qpbt-paper/06_nonlocal_games_and_mipstar.tex:84-86,174-176`), and
the imported proof
(`references/neexp-paper/05_quantum_preliminaries.tex:1150-1175`) exchanges
the tensor factors of the second codeword measurement. The fourth comparison
hypothesis below, `eq:pasting-1-sym`, is that register exchange of the second
comparison in `eq:pasting-1`; it is the first symmetric equivalent of that
comparison in the sense of `def:symmetric-equivalents`, it holds verbatim for
a symmetric strategy, and it is the only consequence of the convention the
proof uses. Without it the statement is unattested; the reduction to the
pinched defect and the proof of the present form are recorded in
`docs/paper-gaps/qpbt_pasting-product-error.tex`. The lemma is proved with the
error function `δp η δ = (3 * C + 19) * (η ^ (1/4) + δ ^ (1/8))`, where `C`
is the constant of the coarse commutator estimate; on the unit square this
dominates the assembled bound `2 * δ + Real.sqrt K`, and elsewhere it exceeds
one, which bounds the defect of any two placed measurement families. -/
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
        consistencyDefect D
          (fun q a₂ => heteroKron (((G₂ q.1.1).postprocess
            (fun g => eval₂ g q.2)).effect a₂) 1)
          (fun q a₂ => heteroKron 1 (((A q).postprocess Prod.snd).effect a₂)) ψ ≤ δ →
        consistencyDefect D (fun q a => heteroKron ((A q).effect a) 1)
          (fun q a => heteroKron 1 (∑ g₁ : Γ₁, ∑ g₂ : Γ₂,
            if (eval₁ g₁ q.1.2, eval₂ g₂ q.2) = a then
              pastedMeasurement (fun g => (G₁ q.1.1).effect g)
                (fun g => (G₂ q.1.1).effect g) g₁ g₂ else 0)) ψ ≤ δp η δ := by
  classical
  obtain ⟨C, hC1, hCbound⟩ := exists_coarse_commutator_bound
  refine ⟨fun x y => (3 * C + 19) * (x ^ (1/4 : ℝ) + y ^ (1/8 : ℝ)), ?_, ?_⟩
  · refine ⟨3 * C + 19, 1/4, 1/8, by linarith, by norm_num, by norm_num, ?_⟩
    intro x y hx hy
    exact ⟨mul_nonneg (by linarith)
      (add_nonneg (Real.rpow_nonneg hx _) (Real.rpow_nonneg hy _)), le_rfl⟩
  intro X Y₁ Y₂ R₁ R₂ Γ₁ Γ₂ ι _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    D eval₁ eval₂ G₁ G₂ A ψ η δ hD hψ hη hδ hG₂ hA hcoll h₁ h₂ h₃ h₄
  have hpm : ∀ q : (X × Y₁) × Y₂,
      (∀ g : Γ₁ × Γ₂, 0 ≤ pastedMeasurement (fun g => (G₁ q.1.1).effect g)
          (fun g => (G₂ q.1.1).effect g) g.1 g.2) ∧
        (∑ g : Γ₁ × Γ₂, pastedMeasurement (fun g => (G₁ q.1.1).effect g)
          (fun g => (G₂ q.1.1).effect g) g.1 g.2) = 1 :=
    fun q => pastedMeasurement_isMeasurement (G₁ q.1.1) (G₂ q.1.1) (hG₂ q.1.1)
  set Bp : ((X × Y₁) × Y₂) → Measurement (R₁ × R₂) ι := fun q =>
    (Measurement.ofSumEqOne
      (fun g : Γ₁ × Γ₂ => pastedMeasurement (fun g => (G₁ q.1.1).effect g)
        (fun g => (G₂ q.1.1).effect g) g.1 g.2) (hpm q).1 (hpm q).2).postprocess
      (fun g => (eval₁ g.1 q.1.2, eval₂ g.2 q.2)) with hBpdef
  have heff : ∀ (q : (X × Y₁) × Y₂) (a : R₁ × R₂), (Bp q).effect a =
      ∑ g₁ : Γ₁, ∑ g₂ : Γ₂, if (eval₁ g₁ q.1.2, eval₂ g₂ q.2) = a then
        pastedMeasurement (fun g => (G₁ q.1.1).effect g)
          (fun g => (G₂ q.1.1).effect g) g₁ g₂ else 0 := by
    intro q a
    rw [hBpdef]
    simp only [Measurement.postprocess_effect, Measurement.ofSumEqOne]
    rw [Finset.sum_filter, Fintype.sum_prod_type]
  have hle1 := consistencyDefect_placed_le_one D A Bp ψ hD hψ
  have hfam : (fun (q : (X × Y₁) × Y₂) (a : R₁ × R₂) =>
        heteroKron (1 : Op ι) ((Bp q).effect a)) =
      fun (q : (X × Y₁) × Y₂) (a : R₁ × R₂) => heteroKron (1 : Op ι)
        (∑ g₁ : Γ₁, ∑ g₂ : Γ₂, if (eval₁ g₁ q.1.2, eval₂ g₂ q.2) = a then
          pastedMeasurement (fun g => (G₁ q.1.1).effect g)
            (fun g => (G₂ q.1.1).effect g) g₁ g₂ else 0) := by
    funext q a
    rw [heff q a]
  rw [hfam] at hle1
  rcases le_or_gt δ 1 with hδ1 | hδgt
  · rcases le_or_gt η 1 with hη1 | hηgt
    · refine le_trans (consistencyDefect_pasted_le_sqrt D eval₁ eval₂ G₁ G₂ A ψ
        η δ C hD hψ hη hG₂ hA hcoll h₁ h₂ h₃ h₄
        (hCbound D eval₁ eval₂ G₁ G₂ A ψ δ hA h₁ h₂)) ?_
      exact pasting_error_sqrt_le_rpow C δ η hC1 hδ hδ1 hη hη1
    · refine le_trans hle1 ?_
      have hb : (0:ℝ) ≤ δ ^ (1/8 : ℝ) := Real.rpow_nonneg hδ _
      have ha : (1:ℝ) ≤ η ^ (1/4 : ℝ) := by
        calc (1:ℝ) = (1:ℝ) ^ (1/4 : ℝ) := (Real.one_rpow _).symm
          _ ≤ η ^ (1/4 : ℝ) :=
            Real.rpow_le_rpow zero_le_one hηgt.le (by norm_num)
      nlinarith [mul_nonneg (sub_nonneg.mpr hC1) (sub_nonneg.mpr ha),
        mul_nonneg (show (0:ℝ) ≤ 3 * C + 19 by linarith) hb]
  · refine le_trans hle1 ?_
    have ha : (0:ℝ) ≤ η ^ (1/4 : ℝ) := Real.rpow_nonneg hη _
    have hb : (1:ℝ) ≤ δ ^ (1/8 : ℝ) := by
      calc (1:ℝ) = (1:ℝ) ^ (1/8 : ℝ) := (Real.one_rpow _).symm
        _ ≤ δ ^ (1/8 : ℝ) :=
          Real.rpow_le_rpow zero_le_one hδgt.le (by norm_num)
    nlinarith [mul_nonneg (sub_nonneg.mpr hC1) (sub_nonneg.mpr hb),
      mul_nonneg (show (0:ℝ) ≤ 3 * C + 19 by linarith) ha]

end MIPStarRE.QPBT
