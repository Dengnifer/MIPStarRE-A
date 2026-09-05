import MIPStarRE.QPBT.Games.Sandwich.Pasting

/-! # The pinched reduction of the pasting estimate

This module records step 1 of the proof of the adopted statement of
`lem:pasting`: the defect of the pasted family is at most the defect of the
second marginal comparison plus the pinched defect.

## References

`lem:pasting` in `blueprint/src/chapter/ch12_qpbt_games.tex:960-990`, with the
proof of the adopted statement in
`docs/paper-gaps/qpbt_pasting-product-error.tex`.
-/

open scoped BigOperators MatrixOrder Matrix ComplexOrder

namespace MIPStarRE.QPBT

open MIPStarRE.LDT hiding Measurement
open MIPStarRE.Quantum
open DistanceCalculus

/-- Conjugating a positive operator by an effect of a measurement is positive.
Formalization-only auxiliary step for `lem:pasting`; the effects of a
measurement are self-adjoint, so the conjugation is a congruence. -/
private theorem conj_effect_nonneg {α ι : Type*} [Fintype α] [Fintype ι]
    [DecidableEq ι] (M : Measurement α ι) (a : α) {N : Op ι} (hN : 0 ≤ N) :
    0 ≤ M.effect a * N * M.effect a := by
  apply Matrix.nonneg_iff_posSemidef.mpr
  have hpos : ((M.effect a)ᴴ * N * M.effect a).PosSemidef :=
    (Matrix.nonneg_iff_posSemidef.mp hN).conjTranspose_mul_mul_same (M.effect a)
  rwa [measurement_effect_hermitian M a] at hpos

/-- The pinched first codeword family of `lem:pasting`: the coarse first
codeword effects conjugated by the fine second codeword effects. -/
private theorem pinched_sum_eq_one {Γ₂ R₁ ι : Type*} [Fintype Γ₂]
    [DecidableEq Γ₂] [Fintype R₁] [DecidableEq R₁] [Fintype ι] [DecidableEq ι]
    (G : Measurement Γ₂ ι) (P : Measurement R₁ ι)
    (hG : MIPStarRE.QPBT.Measurement.IsProjective G) :
    (∑ a : R₁, ∑ g : Γ₂, G.effect g * P.effect a * G.effect g) = 1 := by
  classical
  rw [Finset.sum_comm]
  calc
    (∑ g : Γ₂, ∑ a : R₁, G.effect g * P.effect a * G.effect g) =
        ∑ g : Γ₂, G.effect g * (∑ a : R₁, P.effect a) * G.effect g := by
      refine Finset.sum_congr rfl fun g _ => ?_
      rw [Finset.mul_sum, Finset.sum_mul]
    _ = ∑ g : Γ₂, G.effect g := by
      refine Finset.sum_congr rfl fun g _ => ?_
      rw [P.sum_eq_one, mul_one, (hG g).isIdempotentElem.eq]
    _ = 1 := G.sum_eq_one

/-- Tensor placement is additive in the right factor. The identity is inlined
here because the shared copy lives with the Magic Square rigidity development;
see issue #204. -/
private theorem heteroKron_add_right' {ιA ιB : Type*} (A : Op ιA) (B C : Op ιB) :
    heteroKron A (B + C) = heteroKron A B + heteroKron A C := by
  ext p q
  simp [heteroKron, Matrix.kronecker, mul_add]

/-- Tensor placement respects differences in the right factor. The identity is
inlined here because the shared copy lives with the Magic Square rigidity
development; see issue #204. -/
private theorem heteroKron_sub_right' {ιA ιB : Type*} (A : Op ιA) (B C : Op ιB) :
    heteroKron A (B - C) = heteroKron A B - heteroKron A C := by
  ext p q
  simp [heteroKron, Matrix.kronecker, mul_sub]
/-- The pinched reduction of `lem:pasting`. The defect of the pasted family is
at most the defect of the second marginal comparison plus the pinched defect,
the defect of the first marginal comparison against the first codeword family
conjugated by the fine second codeword effects. This is step 1 of the proof of
the adopted statement in `docs/paper-gaps/qpbt_pasting-product-error.tex`;
blueprint `ch12_qpbt_games.tex:960-990`. -/
theorem consistencyDefect_pasted_le_marginal_add_pinched
    {X Y₁ Y₂ R₁ R₂ Γ₁ Γ₂ ι : Type*}
    [Fintype X] [DecidableEq X] [Fintype Y₁] [DecidableEq Y₁]
    [Fintype Y₂] [DecidableEq Y₂] [Fintype R₁] [DecidableEq R₁]
    [Fintype R₂] [DecidableEq R₂] [Fintype Γ₁] [DecidableEq Γ₁]
    [Fintype Γ₂] [DecidableEq Γ₂] [Fintype ι] [DecidableEq ι]
    (D : Distribution ((X × Y₁) × Y₂))
    (eval₁ : Γ₁ → Y₁ → R₁) (eval₂ : Γ₂ → Y₂ → R₂)
    (G₁ : X → Measurement Γ₁ ι) (G₂ : X → Measurement Γ₂ ι)
    (A : ((X × Y₁) × Y₂) → Measurement (R₁ × R₂) ι)
    (ψ : EuclideanSpace ℂ (ι × ι)) (hψ : ‖ψ‖ = 1)
    (hG₂ : ∀ x, MIPStarRE.QPBT.Measurement.IsProjective (G₂ x)) :
    consistencyDefect D (fun q a => heteroKron ((A q).effect a) 1)
        (fun q a => heteroKron 1 (∑ g₁ : Γ₁, ∑ g₂ : Γ₂,
          if (eval₁ g₁ q.1.2, eval₂ g₂ q.2) = a then
            pastedMeasurement (fun g => (G₁ q.1.1).effect g)
              (fun g => (G₂ q.1.1).effect g) g₁ g₂ else 0)) ψ ≤
      consistencyDefect D
        (fun q a₂ => heteroKron (((A q).postprocess Prod.snd).effect a₂) 1)
        (fun q a₂ => heteroKron 1 (((G₂ q.1.1).postprocess
          (fun g => eval₂ g q.2)).effect a₂)) ψ +
      consistencyDefect D
        (fun q a₁ => heteroKron (((A q).postprocess Prod.fst).effect a₁) 1)
        (fun q a₁ => heteroKron 1 (∑ g : Γ₂, (G₂ q.1.1).effect g *
          ((G₁ q.1.1).postprocess (fun g' => eval₁ g' q.1.2)).effect a₁ *
          (G₂ q.1.1).effect g)) ψ := by
  classical
  set Pm : ((X × Y₁) × Y₂) → Measurement R₁ ι :=
    fun q => (G₁ q.1.1).postprocess (fun g => eval₁ g q.1.2) with hPm
  set Qm : ((X × Y₁) × Y₂) → Measurement R₂ ι :=
    fun q => (G₂ q.1.1).postprocess (fun g => eval₂ g q.2) with hQm
  set paste : ((X × Y₁) × Y₂) → (R₁ × R₂) → Op ι := fun q a =>
    ∑ g₁ : Γ₁, ∑ g₂ : Γ₂,
      if (eval₁ g₁ q.1.2, eval₂ g₂ q.2) = a then
        pastedMeasurement (fun g => (G₁ q.1.1).effect g)
          (fun g => (G₂ q.1.1).effect g) g₁ g₂ else 0 with hpaste
  set pinch : ((X × Y₁) × Y₂) → R₁ → Op ι := fun q a₁ =>
    ∑ g : Γ₂, (G₂ q.1.1).effect g * (Pm q).effect a₁ * (G₂ q.1.1).effect g
    with hpinch
  -- the pasted family, restricted to a fixed pair, is a conjugated coarse effect
  have hpasteEq : ∀ (q : (X × Y₁) × Y₂) (a₁ : R₁) (a₂ : R₂),
      paste q (a₁, a₂) =
        ∑ g ∈ Finset.univ.filter (fun g => eval₂ g q.2 = a₂),
          (G₂ q.1.1).effect g * (Pm q).effect a₁ * (G₂ q.1.1).effect g := by
    intro q a₁ a₂
    simp only [hpaste, pastedMeasurement, hPm, Measurement.postprocess_effect]
    rw [Finset.sum_comm, Finset.sum_filter]
    refine Finset.sum_congr rfl fun g₂ _ => ?_
    by_cases h2 : eval₂ g₂ q.2 = a₂
    · simp only [h2, if_true]
      rw [Finset.mul_sum, Finset.sum_mul, Finset.sum_filter]
      refine Finset.sum_congr rfl fun g₁ _ => ?_
      by_cases h1 : eval₁ g₁ q.1.2 = a₁ <;> simp [h1, Prod.ext_iff]
    · simp [h2, Prod.ext_iff]
  -- the pinched family is a measurement
  have hpinchPos : ∀ (q : (X × Y₁) × Y₂) (a₁ : R₁), 0 ≤ pinch q a₁ := by
    intro q a₁
    exact Finset.sum_nonneg fun g _ =>
      conj_effect_nonneg (G₂ q.1.1) g ((Pm q).pos a₁)
  have hpinchSum : ∀ q : (X × Y₁) × Y₂, (∑ a₁ : R₁, pinch q a₁) = 1 := by
    intro q
    exact pinched_sum_eq_one (G₂ q.1.1) (Pm q) (hG₂ q.1.1)
  have hpasteSum : ∀ q : (X × Y₁) × Y₂, (∑ a : R₁ × R₂, paste q a) = 1 := by
    intro q
    rw [Fintype.sum_prod_type]
    have h : ∀ a₁ : R₁, (∑ a₂ : R₂, paste q (a₁, a₂)) = pinch q a₁ := by
      intro a₁
      simp only [hpinch]
      rw [← Finset.sum_fiberwise Finset.univ (fun g => eval₂ g q.2)
        (fun g => (G₂ q.1.1).effect g * (Pm q).effect a₁ * (G₂ q.1.1).effect g)]
      exact Finset.sum_congr rfl fun a₂ _ => hpasteEq q a₁ a₂
    rw [Finset.sum_congr rfl fun a₁ (_ : a₁ ∈ Finset.univ) => h a₁]
    exact hpinchSum q
  have hpastePos : ∀ (q : (X × Y₁) × Y₂) (a : R₁ × R₂), 0 ≤ paste q a := by
    intro q a
    obtain ⟨a₁, a₂⟩ := a
    rw [hpasteEq q a₁ a₂]
    exact Finset.sum_nonneg fun g _ =>
      conj_effect_nonneg (G₂ q.1.1) g ((Pm q).pos a₁)
  -- the exact operator identity of the reduction
  have hdiff : ∀ (q : (X × Y₁) × Y₂) (a₁ : R₁) (a₂ : R₂),
      (1 : Op ι) + paste q (a₁, a₂) - ((Qm q).effect a₂ + pinch q a₁) =
        ∑ g ∈ Finset.univ.filter (fun g => ¬ eval₂ g q.2 = a₂),
          (G₂ q.1.1).effect g * (1 - (Pm q).effect a₁) * (G₂ q.1.1).effect g := by
    intro q a₁ a₂
    have hsplit1 : (1 : Op ι) =
        (∑ g ∈ Finset.univ.filter (fun g => eval₂ g q.2 = a₂), (G₂ q.1.1).effect g) +
        ∑ g ∈ Finset.univ.filter (fun g => ¬ eval₂ g q.2 = a₂), (G₂ q.1.1).effect g := by
      rw [Finset.sum_filter_add_sum_filter_not]
      exact ((G₂ q.1.1).sum_eq_one).symm
    have hQ : (Qm q).effect a₂ =
        ∑ g ∈ Finset.univ.filter (fun g => eval₂ g q.2 = a₂), (G₂ q.1.1).effect g := by
      simp only [hQm]
      exact Measurement.postprocess_effect (G₂ q.1.1) (fun g => eval₂ g q.2) a₂
    have hpi : pinch q a₁ =
        (∑ g ∈ Finset.univ.filter (fun g => eval₂ g q.2 = a₂),
          (G₂ q.1.1).effect g * (Pm q).effect a₁ * (G₂ q.1.1).effect g) +
        ∑ g ∈ Finset.univ.filter (fun g => ¬ eval₂ g q.2 = a₂),
          (G₂ q.1.1).effect g * (Pm q).effect a₁ * (G₂ q.1.1).effect g := by
      simp only [hpinch]
      rw [Finset.sum_filter_add_sum_filter_not]
    have hrhs : (∑ g ∈ Finset.univ.filter (fun g => ¬ eval₂ g q.2 = a₂),
          (G₂ q.1.1).effect g * (1 - (Pm q).effect a₁) * (G₂ q.1.1).effect g) =
        (∑ g ∈ Finset.univ.filter (fun g => ¬ eval₂ g q.2 = a₂), (G₂ q.1.1).effect g) -
        ∑ g ∈ Finset.univ.filter (fun g => ¬ eval₂ g q.2 = a₂),
          (G₂ q.1.1).effect g * (Pm q).effect a₁ * (G₂ q.1.1).effect g := by
      rw [← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun g _ => ?_
      have hexp : (G₂ q.1.1).effect g * (1 - (Pm q).effect a₁) * (G₂ q.1.1).effect g =
          (G₂ q.1.1).effect g * (G₂ q.1.1).effect g -
            (G₂ q.1.1).effect g * (Pm q).effect a₁ * (G₂ q.1.1).effect g := by
        rw [mul_sub, sub_mul, mul_one]
      rw [hexp, (hG₂ q.1.1 g).isIdempotentElem.eq]
    rw [hpasteEq q a₁ a₂, hrhs, hQ, hpi]
    nth_rewrite 1 [hsplit1]
    abel
  -- the pointwise comparison of the quadratic forms
  have hmono : ∀ (q : (X × Y₁) × Y₂) (a₁ : R₁) (a₂ : R₂),
      stateQForm ψ (heteroKron ((A q).effect (a₁, a₂))
          ((Qm q).effect a₂ + pinch q a₁)) ≤
        stateQForm ψ (heteroKron ((A q).effect (a₁, a₂)) (1 + paste q (a₁, a₂))) := by
    intro q a₁ a₂
    refine quadratic_form_mono ?_ ψ
    refine Matrix.le_iff.mpr ?_
    rw [← heteroKron_sub_right', hdiff q a₁ a₂]
    refine Matrix.nonneg_iff_posSemidef.mp
      (MIPStarRE.Quantum.kronecker_nonneg ((A q).pos (a₁, a₂)) ?_)
    refine Finset.sum_nonneg fun g _ => conj_effect_nonneg (G₂ q.1.1) g ?_
    exact Matrix.nonneg_iff_posSemidef.mpr
      (Matrix.le_iff.mp (measurement_effect_le_one (Pm q) a₁))
  -- assembly
  have hone : stateQForm ψ (1 : Op (ι × ι)) = ‖ψ‖ ^ 2 := by
    have hid : applyOperatorToState (1 : Op (ι × ι)) ψ = ψ := by
      simp [applyOperatorToState]
    rw [stateQForm, hid]
    simpa using (inner_self_eq_norm_sq (𝕜 := ℂ) ψ)
  have hA1 : ∀ (q : (X × Y₁) × Y₂) (a₁ : R₁),
      ((A q).postprocess Prod.fst).effect a₁ = ∑ a₂ : R₂, (A q).effect (a₁, a₂) := by
    intro q a₁
    rw [Measurement.postprocess_effect, Finset.sum_filter, Fintype.sum_prod_type]
    have hin : ∀ b₁ : R₁,
        (∑ b₂ : R₂, if (b₁, b₂).1 = a₁ then (A q).effect (b₁, b₂) else 0) =
          if b₁ = a₁ then ∑ b₂ : R₂, (A q).effect (b₁, b₂) else 0 := by
      intro b₁
      by_cases h : b₁ = a₁ <;> simp [h]
    rw [Finset.sum_congr rfl fun b₁ (_ : b₁ ∈ Finset.univ) => hin b₁, Finset.sum_ite_eq']
    simp
  have hA2 : ∀ (q : (X × Y₁) × Y₂) (a₂ : R₂),
      ((A q).postprocess Prod.snd).effect a₂ = ∑ a₁ : R₁, (A q).effect (a₁, a₂) := by
    intro q a₂
    rw [Measurement.postprocess_effect, Finset.sum_filter, Fintype.sum_prod_type]
    exact Finset.sum_congr rfl fun b₁ _ => by simp
  let pasteM : ((X × Y₁) × Y₂) → Measurement (R₁ × R₂) ι := fun q =>
    MIPStarRE.Quantum.Measurement.ofSumEqOne (paste q) (hpastePos q) (hpasteSum q)
  let pinchM : ((X × Y₁) × Y₂) → Measurement R₁ ι := fun q =>
    MIPStarRE.Quantum.Measurement.ofSumEqOne (pinch q) (hpinchPos q) (hpinchSum q)
  have hL := SandwichProduct.consistencyDefect_placed_eq_avg_point D A pasteM ψ
  simp only [pasteM, MIPStarRE.Quantum.Measurement.ofSumEqOne] at hL
  have hR1 := SandwichProduct.consistencyDefect_placed_eq_avg_point D
    (fun q => (A q).postprocess Prod.snd) Qm ψ
  have hR2 := SandwichProduct.consistencyDefect_placed_eq_avg_point D
    (fun q => (A q).postprocess Prod.fst) pinchM ψ
  simp only [pinchM, MIPStarRE.Quantum.Measurement.ofSumEqOne] at hR2
  have hmain : consistencyDefect D (fun q a => heteroKron ((A q).effect a) 1)
      (fun q a => heteroKron 1 (paste q a)) ψ ≤
      consistencyDefect D
        (fun q a₂ => heteroKron (((A q).postprocess Prod.snd).effect a₂) 1)
        (fun q a₂ => heteroKron 1 ((Qm q).effect a₂)) ψ +
      consistencyDefect D
        (fun q a₁ => heteroKron (((A q).postprocess Prod.fst).effect a₁) 1)
        (fun q a₁ => heteroKron 1 (pinch q a₁)) ψ := by
    rw [hL, hR1, hR2, ← avgOver_add]
    refine avgOver_mono _ _ _ fun q => ?_
    have e0 := point_defect_eq (leftPlacedMeasurement (ιB := ι) (A q))
      (rightPlacedMeasurement (ιA := ι) (pasteM q)) ψ
    simp only [leftPlacedMeasurement, rightPlacedMeasurement, pasteM,
      MIPStarRE.Quantum.Measurement.ofSumEqOne] at e0
    simp_rw [placed_product_stateQForm_eq] at e0
    have e1 := point_defect_eq
      (leftPlacedMeasurement (ιB := ι) ((A q).postprocess Prod.snd))
      (rightPlacedMeasurement (ιA := ι) (Qm q)) ψ
    simp only [leftPlacedMeasurement, rightPlacedMeasurement,
      MIPStarRE.Quantum.Measurement.ofSumEqOne] at e1
    simp_rw [placed_product_stateQForm_eq] at e1
    have e2 := point_defect_eq
      (leftPlacedMeasurement (ιB := ι) ((A q).postprocess Prod.fst))
      (rightPlacedMeasurement (ιA := ι) (pinchM q)) ψ
    simp only [leftPlacedMeasurement, rightPlacedMeasurement, pinchM,
      MIPStarRE.Quantum.Measurement.ofSumEqOne] at e2
    simp_rw [placed_product_stateQForm_eq] at e2
    rw [e0, e1, e2, hψ, one_pow]
    have hunit : (∑ a : R₁ × R₂, stateQForm ψ (heteroKron ((A q).effect a) 1)) = 1 := by
      rw [← stateQForm_finset_sum, ← heteroKron_finset_sum_left, (A q).sum_eq_one,
        heteroKron_one_one, hone, hψ, one_pow]
    have hpair : ∀ F : R₁ → R₂ → Op ι,
        (∑ a : R₁ × R₂, stateQForm ψ (heteroKron ((A q).effect a) (F a.1 a.2))) =
          ∑ a₁ : R₁, ∑ a₂ : R₂,
            stateQForm ψ (heteroKron ((A q).effect (a₁, a₂)) (F a₁ a₂)) := by
      intro F
      rw [Fintype.sum_prod_type]
    have hs1 : (∑ a₂ : R₂, stateQForm ψ
        (heteroKron (((A q).postprocess Prod.snd).effect a₂) ((Qm q).effect a₂))) =
        ∑ a₁ : R₁, ∑ a₂ : R₂,
          stateQForm ψ (heteroKron ((A q).effect (a₁, a₂)) ((Qm q).effect a₂)) := by
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun a₂ _ => ?_
      rw [hA2 q a₂, heteroKron_finset_sum_left, stateQForm_finset_sum]
    have hs2 : (∑ a₁ : R₁, stateQForm ψ
        (heteroKron (((A q).postprocess Prod.fst).effect a₁) (pinch q a₁))) =
        ∑ a₁ : R₁, ∑ a₂ : R₂,
          stateQForm ψ (heteroKron ((A q).effect (a₁, a₂)) (pinch q a₁)) := by
      refine Finset.sum_congr rfl fun a₁ _ => ?_
      rw [hA1 q a₁, heteroKron_finset_sum_left, stateQForm_finset_sum]
    have hterm : ∀ (a₁ : R₁) (a₂ : R₂),
        stateQForm ψ (heteroKron ((A q).effect (a₁, a₂)) ((Qm q).effect a₂)) +
          stateQForm ψ (heteroKron ((A q).effect (a₁, a₂)) (pinch q a₁)) ≤
        stateQForm ψ (heteroKron ((A q).effect (a₁, a₂)) 1) +
          stateQForm ψ (heteroKron ((A q).effect (a₁, a₂)) (paste q (a₁, a₂))) := by
      intro a₁ a₂
      have hl := hmono q a₁ a₂
      rw [heteroKron_add_right', stateQForm_add, heteroKron_add_right',
        stateQForm_add] at hl
      exact hl
    have hsum : (∑ a₁ : R₁, ∑ a₂ : R₂,
          stateQForm ψ (heteroKron ((A q).effect (a₁, a₂)) ((Qm q).effect a₂))) +
        (∑ a₁ : R₁, ∑ a₂ : R₂,
          stateQForm ψ (heteroKron ((A q).effect (a₁, a₂)) (pinch q a₁))) ≤
        (∑ a₁ : R₁, ∑ a₂ : R₂,
          stateQForm ψ (heteroKron ((A q).effect (a₁, a₂)) 1)) +
        (∑ a₁ : R₁, ∑ a₂ : R₂,
          stateQForm ψ (heteroKron ((A q).effect (a₁, a₂)) (paste q (a₁, a₂)))) := by
      rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
      refine Finset.sum_le_sum fun a₁ _ => ?_
      rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
      exact Finset.sum_le_sum fun a₂ _ => hterm a₁ a₂
    rw [hs1, hs2]
    rw [hpair (fun _ _ => 1)] at hunit
    rw [hpair (fun a₁ a₂ => paste q (a₁, a₂))]
    linarith
  exact hmain

end MIPStarRE.QPBT
