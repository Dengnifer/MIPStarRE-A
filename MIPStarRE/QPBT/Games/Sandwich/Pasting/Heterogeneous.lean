import MIPStarRE.QPBT.Games.Sandwich.Pasting.Assembly
import MIPStarRE.QPBT.Games.ErrorFunctions

/-! # Pasting on independent local spaces

The two local spaces are realized in a common product space by adjoining fixed
basis vectors. Tensor placement supplies the corresponding
measurements, with projectivity and postprocessing preserved.

## References

Paper `lem:pasting`,
`references/qpbt-paper/06_nonlocal_games_and_mipstar.tex:504-525`, and its use in
`lem:qld-xz-lines`, `14_analysis_of_the_pauli_basis_test.tex:882-963`.
The common-space realization is a formalization-only auxiliary; see issue #495.
-/

open scoped BigOperators MatrixOrder Matrix ComplexOrder

namespace MIPStarRE.QPBT

open MIPStarRE.LDT hiding Measurement
open MIPStarRE.Quantum
open DistanceCalculus

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

namespace Pasting

variable {ιA ιB : Type*}
  [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB]

/-- Adjoin a fixed basis vector to each local register. Alice's original
coordinate is first and Bob's original coordinate is last. This is the
common-carrier realization used for the heterogeneous pasting estimate;
blueprint `def:pasting-product-state`. -/
noncomputable def productPaddedState (a₀ : ιA) (b₀ : ιB)
    (ψ : EuclideanSpace ℂ (ιA × ιB)) :
    EuclideanSpace ℂ ((ιA × ιB) × (ιA × ιB)) :=
  WithLp.toLp 2 (fun p => if p.1.2 = b₀ then
    if p.2.1 = a₀ then ψ (p.1.1, p.2.2) else 0 else 0)

/-- Adjoining unit basis vectors preserves the state norm. Formalization-only
auxiliary, blueprint `lem:pasting-product-state-preservation`. -/
theorem productPaddedState_norm (a₀ : ιA) (b₀ : ιB)
    (ψ : EuclideanSpace ℂ (ιA × ιB)) :
    ‖productPaddedState a₀ b₀ ψ‖ = ‖ψ‖ := by
  rw [← sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)]
  simp [EuclideanSpace.norm_sq_eq, productPaddedState, Fintype.sum_prod_type, apply_ite]

/-- Local tensor padding preserves every bipartite quadratic form. This exact
identity is independent of positivity and of normalization of the state.
Formalization-only auxiliary, blueprint `lem:pasting-product-state-preservation`. -/
theorem stateQForm_productPaddedState (a₀ : ιA) (b₀ : ιB)
    (ψ : EuclideanSpace ℂ (ιA × ιB)) (A : Op ιA) (B : Op ιB) :
    stateQForm (productPaddedState a₀ b₀ ψ)
        (heteroKron (heteroKron A (1 : Op ιB)) (heteroKron (1 : Op ιA) B)) =
      stateQForm ψ (heteroKron A B) := by
  unfold stateQForm applyOperatorToState
  rw [EuclideanSpace.inner_eq_star_dotProduct, EuclideanSpace.inner_eq_star_dotProduct]
  apply congrArg Complex.re
  simp [productPaddedState, Matrix.toEuclideanLin, Matrix.mulVec, dotProduct,
    heteroKron, Matrix.kronecker, Matrix.kroneckerMap_apply, Fintype.sum_prod_type,
    Matrix.one_apply, Finset.sum_mul, apply_ite]

/-- Tensor padding preserves the off-diagonal consistency defect for arbitrary
operator families. No measurement or probability assumption is required.
Formalization-only auxiliary, blueprint `lem:pasting-product-state-preservation`. -/
theorem consistencyDefect_productPaddedState {X α : Type*}
    [Fintype X] [DecidableEq X] [Fintype α] [DecidableEq α]
    (D : Distribution X) (A : X → α → Op ιA) (B : X → α → Op ιB)
    (a₀ : ιA) (b₀ : ιB) (ψ : EuclideanSpace ℂ (ιA × ιB)) :
    consistencyDefect D
        (fun x a => heteroKron (heteroKron (A x a) (1 : Op ιB)) (1 : Op (ιA × ιB)))
        (fun x a => heteroKron (1 : Op (ιA × ιB)) (heteroKron (1 : Op ιA) (B x a)))
        (productPaddedState a₀ b₀ ψ) =
      consistencyDefect D (fun x a => heteroKron (A x a) (1 : Op ιB))
        (fun x a => heteroKron (1 : Op ιA) (B x a)) ψ := by
  unfold consistencyDefect
  simp_rw [consistency_term_eq_stateQForm, heteroKron_mul, mul_one, one_mul,
    stateQForm_productPaddedState]

end Pasting

/-- A stronger homogeneous auxiliary for paper `lem:pasting`: the two forward
marginal comparisons already imply the pasted conclusion. The paper-facing
`exists_pasting_error` retains the printed self-consistency hypothesis.
This auxiliary isolates its existing Schmidt-mirror proof, which does not use
that hypothesis. See issue #495 and paper
`references/qpbt-paper/06_nonlocal_games_and_mipstar.tex:504-525`;
blueprint `lem:pasting-forward-comparisons`.

**Local fix:** the additive interpretation of `IsPolyErr₂` is documented in
`docs/paper-gaps/qpbt_pasting-product-error.tex`, issue #201. -/
theorem exists_pasting_error_of_marginal_consistency :
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
    D eval₁ eval₂ G₁ G₂ A ψ η δ hD hψ hη hδ hG₂ hA hcoll h₁ h₂
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
    · refine le_trans (consistencyDefect_pasted_le_sqrt_one_sided D eval₁ eval₂ G₁ G₂ A ψ
        η δ C hD hψ hη hG₂ hA hcoll h₁ h₂ hδ hδ1
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

/-- The one-sided pasting estimate on independent Alice and Bob spaces.
This is a stronger Lean-only auxiliary for paper `lem:pasting`,
`references/qpbt-paper/06_nonlocal_games_and_mipstar.tex:504-525`: only its two
forward marginal comparisons are required. The paper-facing
`exists_pasting_error` continues to retain all three printed hypotheses.

The two spaces embed isometrically into a common product carrier by adjoining
fixed unit basis vectors. Tensor placement preserves the measurements and their
projectivity; `Pasting.consistencyDefect_productPaddedState` preserves the input
and output defects. The unit state internally excludes empty local carriers;
no nonemptiness assumption on outcomes is needed. See issue #495 and blueprint
`lem:pasting-heterogeneous`.

**Local fix:** the additive interpretation of `IsPolyErr₂` is documented in
`docs/paper-gaps/qpbt_pasting-product-error.tex`, issue #201. -/
theorem exists_pasting_error_heterogeneous :
    ∃ δp : ℝ → ℝ → ℝ, IsPolyErr₂ δp ∧
      ∀ {X Y₁ Y₂ R₁ R₂ Γ₁ Γ₂ ιA ιB : Type*}
        [Fintype X] [DecidableEq X] [Fintype Y₁] [DecidableEq Y₁]
        [Fintype Y₂] [DecidableEq Y₂] [Fintype R₁] [DecidableEq R₁]
        [Fintype R₂] [DecidableEq R₂]
        [Fintype Γ₁] [DecidableEq Γ₁] [Fintype Γ₂] [DecidableEq Γ₂]
        [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB]
        (D : Distribution ((X × Y₁) × Y₂))
        (eval₁ : Γ₁ → Y₁ → R₁) (eval₂ : Γ₂ → Y₂ → R₂)
        (G₁ : X → Measurement Γ₁ ιB) (G₂ : X → Measurement Γ₂ ιB)
        (A : ((X × Y₁) × Y₂) → Measurement (R₁ × R₂) ιA)
        (ψ : EuclideanSpace ℂ (ιA × ιB)) (η δ : ℝ),
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
          (fun q a => heteroKron 1 (∑ g₁ : Γ₁, ∑ g₂ : Γ₂,
            if (eval₁ g₁ q.1.2, eval₂ g₂ q.2) = a then
              pastedMeasurement (fun g => (G₁ q.1.1).effect g)
                (fun g => (G₂ q.1.1).effect g) g₁ g₂ else 0)) ψ ≤ δp η δ := by
  classical
  obtain ⟨δp, hpoly, hbound⟩ := exists_pasting_error_of_marginal_consistency
  refine ⟨δp, hpoly, ?_⟩
  intro X Y₁ Y₂ R₁ R₂ Γ₁ Γ₂ ιA ιB _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    D eval₁ eval₂ G₁ G₂ A ψ η δ hD hψ hη hδ hG₂ hA hcoll h₁ h₂
  have hnonempty : Nonempty (ιA × ιB) := by
    rcases isEmpty_or_nonempty (ιA × ιB) with h | h
    · letI := h
      have hz : ψ = 0 := Subsingleton.elim _ _
      simp [hz] at hψ
    · exact h
  obtain ⟨⟨a₀, b₀⟩⟩ := hnonempty
  let A' := fun q => Measurement.leftPlacement (ιB := ιB) (A q)
  let G₁' := fun x => Measurement.rightPlacement (ιA := ιA) (G₁ x)
  let G₂' := fun x => Measurement.rightPlacement (ιA := ιA) (G₂ x)
  let ψ' := Pasting.productPaddedState a₀ b₀ ψ
  have hψ' : ‖ψ'‖ = 1 := (Pasting.productPaddedState_norm a₀ b₀ ψ).trans hψ
  have h₁' : consistencyDefect D
      (fun q a₁ => heteroKron (((A' q).postprocess Prod.fst).effect a₁) 1)
      (fun q a₁ => heteroKron 1 (((G₁' q.1.1).postprocess
        (fun g => eval₁ g q.1.2)).effect a₁)) ψ' ≤ δ := by
    simpa only [A', G₁', ψ', ← Measurement.leftPlacement_postprocess,
      ← Measurement.rightPlacement_postprocess, Measurement.leftPlacement_effect,
      Measurement.rightPlacement_effect, Pasting.consistencyDefect_productPaddedState] using h₁
  have h₂' : consistencyDefect D
      (fun q a₂ => heteroKron (((A' q).postprocess Prod.snd).effect a₂) 1)
      (fun q a₂ => heteroKron 1 (((G₂' q.1.1).postprocess
        (fun g => eval₂ g q.2)).effect a₂)) ψ' ≤ δ := by
    simpa only [A', G₂', ψ', ← Measurement.leftPlacement_postprocess,
      ← Measurement.rightPlacement_postprocess, Measurement.leftPlacement_effect,
      Measurement.rightPlacement_effect, Pasting.consistencyDefect_productPaddedState] using h₂
  have hpadded := hbound D eval₁ eval₂ G₁' G₂' A' ψ' η δ hD hψ' hη hδ
    (fun x => Measurement.isProjective_rightPlacement (G₂ x) (hG₂ x))
    (fun q => Measurement.isProjective_leftPlacement (A q) (hA q)) hcoll h₁' h₂'
  have hpaste (q : (X × Y₁) × Y₂) (a : R₁ × R₂) :
      (∑ g₁ : Γ₁, ∑ g₂ : Γ₂,
        if (eval₁ g₁ q.1.2, eval₂ g₂ q.2) = a then
          pastedMeasurement (fun g => (G₁' q.1.1).effect g)
            (fun g => (G₂' q.1.1).effect g) g₁ g₂ else 0) =
        heteroKron (1 : Op ιA) (∑ g₁ : Γ₁, ∑ g₂ : Γ₂,
          if (eval₁ g₁ q.1.2, eval₂ g₂ q.2) = a then
            pastedMeasurement (fun g => (G₁ q.1.1).effect g)
              (fun g => (G₂ q.1.1).effect g) g₁ g₂ else 0) := by
    simp only [G₁', G₂', Measurement.rightPlacement_effect, pastedMeasurement,
      heteroKron_mul, one_mul]
    simp_rw [heteroKron_finset_sum_right]
    apply Finset.sum_congr rfl
    intro g₁ _
    apply Finset.sum_congr rfl
    intro g₂ _
    split_ifs <;> simp [heteroKron, Matrix.kronecker]
  simp_rw [hpaste] at hpadded
  simpa only [A', ψ', Measurement.leftPlacement_effect,
    Pasting.consistencyDefect_productPaddedState] using hpadded

end MIPStarRE.QPBT
