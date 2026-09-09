import MIPStarRE.QPBT.Games.Sandwich.Pasting.CodewordConsistency

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
    rw [← heteroKron_sub_right, hdiff q a₁ a₂]
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
      rw [heteroKron_add_right, stateQForm_add, heteroKron_add_right,
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

/-- The Cauchy--Schwarz step of `lem:pasting` at a fixed question: the gap
between the overlap of a projective measurement with a first codeword family
and its overlap with the pinching of that family by a projective family on the
same factor is at most the square root of the summed commutator mass of the two
families. This is step 2 of the proof of the adopted statement in
`docs/paper-gaps/qpbt_pasting-product-error.tex`; blueprint
`ch12_qpbt_games.tex:960-990`. -/
private theorem abs_pinch_overlap_gap_le_sqrt {R₁ Γ₂ ι : Type*}
    [Fintype R₁] [DecidableEq R₁] [Fintype Γ₂] [DecidableEq Γ₂]
    [Fintype ι] [DecidableEq ι]
    (A P : Measurement R₁ ι) (G : Measurement Γ₂ ι)
    (ψ : EuclideanSpace ℂ (ι × ι)) (hψ : ‖ψ‖ = 1)
    (hA : MIPStarRE.QPBT.Measurement.IsProjective A)
    (hG : MIPStarRE.QPBT.Measurement.IsProjective G) :
    |∑ a : R₁, (stateQForm ψ (heteroKron (A.effect a) (P.effect a)) -
        stateQForm ψ (heteroKron (A.effect a)
          (∑ g : Γ₂, G.effect g * P.effect a * G.effect g)))| ≤
      Real.sqrt (∑ a : R₁, ∑ g : Γ₂,
        ‖applyOperatorToState (heteroKron 1
          (P.effect a * G.effect g - G.effect g * P.effect a)) ψ‖ ^ 2) := by
  classical
  -- the two inlined identities of the distance calculus; see issue #204
  have happ : ∀ (M N : Op (ι × ι)) (v : EuclideanSpace ℂ (ι × ι)),
      applyOperatorToState (M * N) v =
        applyOperatorToState M (applyOperatorToState N v) := by
    intro M N v
    unfold applyOperatorToState
    simp [Matrix.toEuclideanLin, Matrix.toLpLin_mul_same]
  have hqf : ∀ M N : Op (ι × ι), stateQForm ψ (M * N) =
      (inner ℂ (applyOperatorToState Mᴴ ψ) (applyOperatorToState N ψ)).re := by
    intro M N
    have hadj : (Matrix.toEuclideanLin M).adjoint = Matrix.toEuclideanLin Mᴴ := by
      rw [← Matrix.toEuclideanLin_conjTranspose_eq_adjoint]
    have h1 : (inner ℂ ((Matrix.toEuclideanLin M).adjoint ψ)
        (applyOperatorToState N ψ) : ℂ) =
        inner ℂ ψ (Matrix.toEuclideanLin M (applyOperatorToState N ψ)) :=
      LinearMap.adjoint_inner_left _ _ _
    rw [stateQForm, happ]
    rw [show applyOperatorToState Mᴴ ψ = (Matrix.toEuclideanLin M).adjoint ψ by
      rw [hadj]; rfl]
    rw [h1]
    rfl
  have hct : ∀ (M N : Op ι), (heteroKron M N)ᴴ = heteroKron Mᴴ Nᴴ := by
    intro M N
    unfold heteroKron
    exact Matrix.conjTranspose_kronecker M N
  have hqsub : ∀ M N : Op (ι × ι),
      stateQForm ψ (M - N) = stateQForm ψ M - stateQForm ψ N := by
    intro M N
    simp [stateQForm, applyOperatorToState]
  -- the commutator rearrangement of the pinching defect
  have hterm : ∀ a : R₁, P.effect a -
      (∑ g : Γ₂, G.effect g * P.effect a * G.effect g) =
      ∑ g : Γ₂, (P.effect a * G.effect g - G.effect g * P.effect a) * G.effect g := by
    intro a
    have h1 : (∑ g : Γ₂, P.effect a * G.effect g) = P.effect a := by
      rw [← Finset.mul_sum, G.sum_eq_one, mul_one]
    calc P.effect a - ∑ g : Γ₂, G.effect g * P.effect a * G.effect g
        = (∑ g : Γ₂, P.effect a * G.effect g) -
            ∑ g : Γ₂, G.effect g * P.effect a * G.effect g := by rw [h1]
      _ = ∑ g : Γ₂, (P.effect a * G.effect g - G.effect g * P.effect a * G.effect g) := by
            rw [← Finset.sum_sub_distrib]
      _ = ∑ g : Γ₂, (P.effect a * G.effect g - G.effect g * P.effect a) * G.effect g := by
            refine Finset.sum_congr rfl fun g _ => ?_
            rw [sub_mul, mul_assoc (P.effect a), (hG g).isIdempotentElem.eq]
  -- the summand as a product of two placed operators
  have hfac : ∀ (a : R₁) (g : Γ₂),
      heteroKron (A.effect a)
          ((P.effect a * G.effect g - G.effect g * P.effect a) * G.effect g) =
        heteroKron (A.effect a) (P.effect a * G.effect g - G.effect g * P.effect a) *
          heteroKron (A.effect a) (G.effect g) := by
    intro a g
    rw [heteroKron_mul, (hA a).isIdempotentElem.eq]
  -- the two mass estimates
  have hone1 : applyOperatorToState (1 : Op (ι × ι)) ψ = ψ := by
    simp [applyOperatorToState]
  let M : Measurement (R₁ × Γ₂) (ι × ι) :=
    MIPStarRE.Quantum.Measurement.ofSumEqOne
      (fun p => heteroKron (A.effect p.1) (G.effect p.2))
      (fun p => kronecker_nonneg (A.pos p.1) (G.pos p.2))
      (by
        rw [Fintype.sum_prod_type]
        rw [show (∑ a : R₁, ∑ g : Γ₂, heteroKron (A.effect a) (G.effect g)) =
            ∑ a : R₁, heteroKron (A.effect a) (1 : Op ι) from
          Finset.sum_congr rfl fun a _ => by
            rw [← heteroKron_finset_sum_right, G.sum_eq_one]]
        rw [← heteroKron_finset_sum_left, A.sum_eq_one, heteroKron_one_one])
  have hmass : (∑ p : R₁ × Γ₂,
      ‖applyOperatorToState (heteroKron (A.effect p.1) (G.effect p.2)) ψ‖ ^ 2) ≤ 1 := by
    have h := sum_norm_mul_apply_le (fun p : R₁ × Γ₂ => M.effect p) (1 : Op (ι × ι)) ψ
      (MIPStarRE.QPBT.measurement_sum_adjoint_mul_le_one M)
    simp only [M, MIPStarRE.Quantum.Measurement.ofSumEqOne, mul_one] at h
    rw [hone1, hψ, one_pow] at h
    exact h
  have hcontract : ∀ (a : R₁) (g : Γ₂),
      ‖applyOperatorToState (heteroKron (A.effect a)
          (P.effect a * G.effect g - G.effect g * P.effect a)) ψ‖ ^ 2 ≤
        ‖applyOperatorToState (heteroKron 1
          (P.effect a * G.effect g - G.effect g * P.effect a)) ψ‖ ^ 2 := by
    intro a g
    have hpr : IsProj (heteroKron (A.effect a) (1 : Op ι)) :=
      Measurement.isProjective_leftPlacement (ιB := ι) A hA a
    have hle : (heteroKron (A.effect a) (1 : Op ι))ᴴ *
        heteroKron (A.effect a) (1 : Op ι) ≤ 1 := by
      rw [hpr.isSelfAdjoint.isHermitian.eq, hpr.isIdempotentElem.eq]
      exact measurement_effect_le_one (Measurement.leftPlacement (ιB := ι) A) a
    have hsplit : heteroKron (A.effect a)
        (P.effect a * G.effect g - G.effect g * P.effect a) =
        heteroKron (A.effect a) 1 *
          heteroKron 1 (P.effect a * G.effect g - G.effect g * P.effect a) := by
      rw [heteroKron_mul, mul_one, one_mul]
    rw [hsplit]
    have h := sum_norm_mul_apply_le
      (fun _ : Unit => heteroKron (A.effect a) (1 : Op ι))
      (heteroKron 1 (P.effect a * G.effect g - G.effect g * P.effect a)) ψ
      (by simpa using hle)
    simpa using h
  have hXH : ∀ (a : R₁) (g : Γ₂),
      (heteroKron (A.effect a) (P.effect a * G.effect g - G.effect g * P.effect a))ᴴ =
        - heteroKron (A.effect a)
          (P.effect a * G.effect g - G.effect g * P.effect a) := by
    intro a g
    rw [hct, measurement_effect_hermitian A a, Matrix.conjTranspose_sub,
      Matrix.conjTranspose_mul, Matrix.conjTranspose_mul,
      measurement_effect_hermitian P a, measurement_effect_hermitian G g,
      ← heteroKron_neg_right]
    congr 1
    abel
  have hnormXH : ∀ (a : R₁) (g : Γ₂),
      ‖applyOperatorToState (heteroKron (A.effect a)
          (P.effect a * G.effect g - G.effect g * P.effect a))ᴴ ψ‖ =
        ‖applyOperatorToState (heteroKron (A.effect a)
          (P.effect a * G.effect g - G.effect g * P.effect a)) ψ‖ := by
    intro a g
    rw [hXH a g, show applyOperatorToState (-(heteroKron (A.effect a)
        (P.effect a * G.effect g - G.effect g * P.effect a))) ψ =
        -applyOperatorToState (heteroKron (A.effect a)
          (P.effect a * G.effect g - G.effect g * P.effect a)) ψ by
      simp [applyOperatorToState], norm_neg]
  -- the pointwise expansion of the gap
  have hexpand : (∑ a : R₁, (stateQForm ψ (heteroKron (A.effect a) (P.effect a)) -
      stateQForm ψ (heteroKron (A.effect a)
        (∑ g : Γ₂, G.effect g * P.effect a * G.effect g)))) =
      ∑ p : R₁ × Γ₂, stateQForm ψ (heteroKron (A.effect p.1)
        ((P.effect p.1 * G.effect p.2 - G.effect p.2 * P.effect p.1) *
          G.effect p.2)) := by
    rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [← hqsub, ← heteroKron_sub_right, hterm a, heteroKron_finset_sum_right,
      stateQForm_finset_sum]
  set u : R₁ × Γ₂ → EuclideanSpace ℂ (ι × ι) := fun p =>
    applyOperatorToState (heteroKron (A.effect p.1)
      (P.effect p.1 * G.effect p.2 - G.effect p.2 * P.effect p.1)) ψ with hu
  set v : R₁ × Γ₂ → EuclideanSpace ℂ (ι × ι) := fun p =>
    applyOperatorToState (heteroKron (A.effect p.1) (G.effect p.2)) ψ with hv
  have hpoint : ∀ p : R₁ × Γ₂,
      |stateQForm ψ (heteroKron (A.effect p.1)
        ((P.effect p.1 * G.effect p.2 - G.effect p.2 * P.effect p.1) *
          G.effect p.2))| ≤ ‖u p‖ * ‖v p‖ := by
    intro p
    rw [hfac p.1 p.2, hqf]
    refine le_trans (Complex.abs_re_le_norm _) ?_
    refine le_trans (norm_inner_le_norm _ _) ?_
    rw [hu, hv, hnormXH p.1 p.2]
  rw [hexpand]
  have hsum2 : (∑ a : R₁, ∑ g : Γ₂, ‖applyOperatorToState (heteroKron 1
      (P.effect a * G.effect g - G.effect g * P.effect a)) ψ‖ ^ 2) =
      ∑ p : R₁ × Γ₂, ‖applyOperatorToState (heteroKron 1
        (P.effect p.1 * G.effect p.2 - G.effect p.2 * P.effect p.1)) ψ‖ ^ 2 := by
    rw [Fintype.sum_prod_type]
  rw [hsum2]
  calc |∑ p : R₁ × Γ₂, stateQForm ψ (heteroKron (A.effect p.1)
          ((P.effect p.1 * G.effect p.2 - G.effect p.2 * P.effect p.1) *
            G.effect p.2))| ≤
        ∑ p : R₁ × Γ₂, |stateQForm ψ (heteroKron (A.effect p.1)
          ((P.effect p.1 * G.effect p.2 - G.effect p.2 * P.effect p.1) *
            G.effect p.2))| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ p : R₁ × Γ₂, ‖u p‖ * ‖v p‖ := Finset.sum_le_sum fun p _ => hpoint p
    _ ≤ Real.sqrt (∑ p : R₁ × Γ₂, ‖u p‖ ^ 2) *
          Real.sqrt (∑ p : R₁ × Γ₂, ‖v p‖ ^ 2) := by
        simpa using Real.sum_mul_le_sqrt_mul_sqrt
          (Finset.univ : Finset (R₁ × Γ₂)) (fun p => ‖u p‖) (fun p => ‖v p‖)
    _ ≤ Real.sqrt (∑ p : R₁ × Γ₂, ‖applyOperatorToState (heteroKron 1
          (P.effect p.1 * G.effect p.2 - G.effect p.2 * P.effect p.1)) ψ‖ ^ 2) * 1 := by
        refine mul_le_mul ?_ ?_ (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
        · exact Real.sqrt_le_sqrt
            (Finset.sum_le_sum fun p _ => hcontract p.1 p.2)
        · rw [show (1 : ℝ) = Real.sqrt 1 by rw [Real.sqrt_one]]
          exact Real.sqrt_le_sqrt hmass
    _ = Real.sqrt (∑ p : R₁ × Γ₂, ‖applyOperatorToState (heteroKron 1
          (P.effect p.1 * G.effect p.2 - G.effect p.2 * P.effect p.1)) ψ‖ ^ 2) := by
        rw [mul_one]

/-- Step 2 of the proof of the adopted statement of `lem:pasting`: the pinched
defect is at most the defect of the first marginal comparison plus the square
root of the averaged commutator mass of the first codeword family against the
fine second codeword family, by the Cauchy--Schwarz estimate over the pairs of a
first answer and a second codeword. Blueprint `ch12_qpbt_games.tex:960-990`,
proof of the adopted statement in
`docs/paper-gaps/qpbt_pasting-product-error.tex`. -/
theorem consistencyDefect_pinched_le_marginal_add_sqrt
    {X Y₁ Y₂ R₁ Γ₂ ι : Type*}
    [Fintype X] [DecidableEq X] [Fintype Y₁] [DecidableEq Y₁]
    [Fintype Y₂] [DecidableEq Y₂] [Fintype R₁] [DecidableEq R₁]
    [Fintype Γ₂] [DecidableEq Γ₂] [Fintype ι] [DecidableEq ι]
    (D : Distribution ((X × Y₁) × Y₂)) (G₂ : X → Measurement Γ₂ ι)
    (P A : ((X × Y₁) × Y₂) → Measurement R₁ ι)
    (ψ : EuclideanSpace ℂ (ι × ι)) (K : ℝ)
    (hD : D.IsProbability) (hψ : ‖ψ‖ = 1)
    (hA : ∀ q, MIPStarRE.QPBT.Measurement.IsProjective (A q))
    (hG₂ : ∀ x, MIPStarRE.QPBT.Measurement.IsProjective (G₂ x))
    (hK : avgOver D (fun q => ∑ a : R₁, ∑ g : Γ₂,
      ‖applyOperatorToState (heteroKron 1 ((P q).effect a * (G₂ q.1.1).effect g -
        (G₂ q.1.1).effect g * (P q).effect a)) ψ‖ ^ 2) ≤ K) :
    consistencyDefect D (fun q a => heteroKron ((A q).effect a) 1)
        (fun q a => heteroKron 1 (∑ g : Γ₂, (G₂ q.1.1).effect g * (P q).effect a *
          (G₂ q.1.1).effect g)) ψ ≤
      consistencyDefect D (fun q a => heteroKron ((A q).effect a) 1)
        (fun q a => heteroKron 1 ((P q).effect a)) ψ + Real.sqrt K := by
  classical
  let pinchM : ((X × Y₁) × Y₂) → Measurement R₁ ι := fun q =>
    MIPStarRE.Quantum.Measurement.ofSumEqOne
      (fun a => ∑ g : Γ₂, (G₂ q.1.1).effect g * (P q).effect a * (G₂ q.1.1).effect g)
      (fun a => Finset.sum_nonneg fun g _ =>
        conj_effect_nonneg (G₂ q.1.1) g ((P q).pos a))
      (pinched_sum_eq_one (G₂ q.1.1) (P q) (hG₂ q.1.1))
  have e1 := consistencyDefect_eq_one_sub_overlap D
    (fun q => Measurement.leftPlacement (ιB := ι) (A q))
    (fun q => Measurement.rightPlacement (ιA := ι) (pinchM q)) ψ hD hψ
  have e2 := consistencyDefect_eq_one_sub_overlap D
    (fun q => Measurement.leftPlacement (ιB := ι) (A q))
    (fun q => Measurement.rightPlacement (ιA := ι) (P q)) ψ hD hψ
  simp only [Measurement.leftPlacement_effect, Measurement.rightPlacement_effect,
    pinchM, MIPStarRE.Quantum.Measurement.ofSumEqOne] at e1 e2
  simp_rw [placed_product_stateQForm_eq] at e1 e2
  rw [e1, e2]
  set OP : ((X × Y₁) × Y₂) → ℝ := fun q =>
    ∑ a : R₁, stateQForm ψ (heteroKron ((A q).effect a) ((P q).effect a)) with hOP
  set OQ : ((X × Y₁) × Y₂) → ℝ := fun q =>
    ∑ a : R₁, stateQForm ψ (heteroKron ((A q).effect a)
      (∑ g : Γ₂, (G₂ q.1.1).effect g * (P q).effect a * (G₂ q.1.1).effect g)) with hOQ
  set CM : ((X × Y₁) × Y₂) → ℝ := fun q => ∑ a : R₁, ∑ g : Γ₂,
    ‖applyOperatorToState (heteroKron 1 ((P q).effect a * (G₂ q.1.1).effect g -
      (G₂ q.1.1).effect g * (P q).effect a)) ψ‖ ^ 2 with hCM
  have hf : ∀ q, |OP q - OQ q| ≤ Real.sqrt (CM q) := by
    intro q
    have hpt := abs_pinch_overlap_gap_le_sqrt (A q) (P q) (G₂ q.1.1) ψ hψ
      (hA q) (hG₂ q.1.1)
    rw [hOP, hOQ, hCM]
    rw [show (∑ a : R₁, stateQForm ψ (heteroKron ((A q).effect a) ((P q).effect a))) -
        ∑ a : R₁, stateQForm ψ (heteroKron ((A q).effect a)
          (∑ g : Γ₂, (G₂ q.1.1).effect g * (P q).effect a * (G₂ q.1.1).effect g)) =
        ∑ a : R₁, (stateQForm ψ (heteroKron ((A q).effect a) ((P q).effect a)) -
          stateQForm ψ (heteroKron ((A q).effect a)
            (∑ g : Γ₂, (G₂ q.1.1).effect g * (P q).effect a *
              (G₂ q.1.1).effect g))) by rw [Finset.sum_sub_distrib]]
    exact hpt
  have hg : ∀ q, 0 ≤ CM q := by
    intro q
    exact Finset.sum_nonneg fun a _ => Finset.sum_nonneg fun g _ => sq_nonneg _
  have hjensen : |avgOver D (fun q => OP q - OQ q)| ≤ Real.sqrt (avgOver D CM) :=
    MIPStarRE.LDT.Preliminaries.avgOver_abs_le_sqrt_of_pointwise D
      (fun q => OP q - OQ q) CM hf hg (by rw [hD.weight_sum_eq_one])
  have hfinal : avgOver D OP - avgOver D OQ ≤ Real.sqrt K := by
    rw [← avgOver_sub]
    refine le_trans (le_abs_self _) (le_trans hjensen ?_)
    exact Real.sqrt_le_sqrt hK
  linarith

end MIPStarRE.QPBT
