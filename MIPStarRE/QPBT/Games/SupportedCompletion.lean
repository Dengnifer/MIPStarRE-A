import MIPStarRE.QPBT.Games.Sandwich.Support

/-!
# Completion on a prescribed set of outcomes

This formalization-only auxiliary constructs a complete measurement supported on
the good outcomes of a finite measurement, by sending every bad outcome to a
specified good outcome. For projective measurements this adds the complementary
projection to the default effect and preserves projectivity. The consistency
estimates charge changes of outcome labels only to the state mass of that
complementary projection, on either of two possibly different player spaces.

The source-specific estimate on the mass outside the image of the polynomial
combining map is the unimplemented target `global_polynomial_bad_mass_le`,
specified in `audits/2026-09-06_supported-projective-completion.md` under issue #279.
No result here asserts the global polynomial-pair theorem or derives that estimate.

## References

* `references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1364-1402`,
  the completion step after `eq:qld-sgg-mhat-sandwich` in `lem:qld-4-7`.
* Blueprint `lem:qld-4-7`, whose source theorem remains separate from this auxiliary.
-/

open scoped BigOperators MatrixOrder Matrix ComplexOrder

namespace MIPStarRE.QPBT.SupportedCompletion

open MIPStarRE.LDT hiding Measurement
open MIPStarRE.Quantum
open DistanceCalculus

variable {α β X ι ιA ιB : Type*}
variable [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
variable [Fintype X] [DecidableEq X]
variable [Fintype ι] [DecidableEq ι]
variable [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB]

/-- Retain every good outcome and send every other outcome to the specified
good outcome. The default is actual domain data, with its membership proof. -/
def toGood (good : α → Prop) [DecidablePred good]
    (a₀ : {a // good a}) (a : α) : {a // good a} :=
  if h : good a then ⟨a, h⟩ else a₀

omit [Fintype α] [DecidableEq α] in
@[simp] theorem toGood_coe (good : α → Prop) [DecidablePred good]
    (a₀ a : {a // good a}) : toGood good a₀ a = a := by
  simp [toGood, a.property]

/-- The omitted effects. When the measurement is projective, their sum is the
projection complementary to the sum of good effects. -/
noncomputable def badEffect (M : Measurement α ι)
    (good : α → Prop) [DecidablePred good] : Op ι :=
  ∑ a ∈ Finset.univ.filter (fun a => ¬ good a), M.effect a

/-- Complete the restriction to good outcomes by adding all bad effects to
`a₀`. This is an outcome postprocessing of the original complete measurement. -/
noncomputable def complete (M : Measurement α ι)
    (good : α → Prop) [DecidablePred good] (a₀ : {a // good a}) :
    Measurement {a // good a} ι :=
  M.postprocess (toGood good a₀)

/-- The completion is projective whenever the original measurement is
projective, by projectivity of outcome postprocessing. -/
theorem complete_isProjective (M : Measurement α ι)
    (hM : Measurement.IsProjective M) (good : α → Prop) [DecidablePred good]
    (a₀ : {a // good a}) : Measurement.IsProjective (complete M good a₀) :=
  SandwichProduct.postprocess_isProjective M hM (toGood good a₀)

omit [DecidableEq α] in
/-- The bad effect is precisely the complement of the restricted total. -/
theorem badEffect_eq_one_sub (M : Measurement α ι)
    (good : α → Prop) [DecidablePred good] :
    badEffect M good = 1 - ∑ a : {a // good a}, M.effect a := by
  have hsplit := Fintype.sum_subtype_add_sum_subtype good M.effect
  have hbad : badEffect M good = ∑ a : {a // ¬ good a}, M.effect a := by
    exact Finset.sum_subtype _ (by simp) M.effect
  rw [hbad]
  rw [M.sum_eq_one] at hsplit
  exact eq_sub_of_add_eq' hsplit

omit [DecidableEq α] in
/-- The sum of the omitted effects is positive semidefinite. -/
theorem badEffect_nonneg (M : Measurement α ι)
    (good : α → Prop) [DecidablePred good] : 0 ≤ badEffect M good :=
  Finset.sum_nonneg fun a _ => M.pos a

/-- The submeasurement obtained by retaining only the good outcomes. -/
noncomputable def restrict (M : Measurement α ι)
    (good : α → Prop) [DecidablePred good] : Submeasurement {a // good a} ι where
  effect a := M.effect a
  pos a := M.pos a
  sum_le_one := by
    have h := badEffect_nonneg M good
    rw [badEffect_eq_one_sub] at h
    exact sub_nonneg.mp h

/-- The bad effect is itself a projection: it is one effect of the binary
postprocessing recording whether an outcome is bad. -/
theorem badEffect_isStarProjection (M : Measurement α ι)
    (hM : Measurement.IsProjective M) (good : α → Prop) [DecidablePred good] :
    IsStarProjection (badEffect M good) := by
  have h := SandwichProduct.postprocess_isProjective M hM
    (fun a => decide (¬ good a)) true
  change IsStarProjection (∑ a ∈ Finset.univ.filter
    (fun a => decide (¬ good a) = true), M.effect a) at h
  simpa only [decide_eq_true_eq, badEffect] using h

/-- The completed default effect absorbs exactly the omitted projection;
all other good effects are retained. -/
theorem complete_effect (M : Measurement α ι)
    (good : α → Prop) [DecidablePred good] (a₀ a : {a // good a}) :
    (complete M good a₀).effect a =
      M.effect a + if a = a₀ then badEffect M good else 0 := by
  classical
  rw [complete, Measurement.postprocess_effect, Finset.sum_filter]
  have hterm (b : α) :
      (if toGood good a₀ b = a then M.effect b else 0) =
        (if b = a.val then M.effect b else 0) +
          if a = a₀ then (if ¬ good b then M.effect b else 0) else 0 := by
    by_cases hb : good b
    · have heq : toGood good a₀ b = a ↔ b = a.val := by
        simp [toGood, hb, Subtype.ext_iff]
      simp [heq, hb]
    · have hba : b ≠ a.val := by
        rintro rfl
        exact hb a.property
      simp [toGood, hb, hba, eq_comm]
  simp_rw [hterm]
  rw [Finset.sum_add_distrib]
  simp [badEffect, Finset.sum_filter, Finset.sum_ite_irrel]

/-- Relabeling the completed measurement adds the bad effect to exactly the
label of the chosen default outcome, relative to the relabeled restriction. -/
theorem complete_postprocess_effect (M : Measurement α ι)
    (good : α → Prop) [DecidablePred good] (a₀ : {a // good a})
    (g : {a // good a} → β) (b : β) :
    ((complete M good a₀).postprocess g).effect b =
      ((restrict M good).postprocess g).effect b +
        if b = g a₀ then badEffect M good else 0 := by
  rw [MIPStarRE.Quantum.Measurement.postprocess_effect]
  simp_rw [complete_effect]
  rw [Finset.sum_add_distrib]
  congr 1
  simp [eq_comm]

private theorem postprocess_overlap (M : Measurement α ι) (N : Measurement β ι)
    (f : α → β) (ψ : EuclideanSpace ℂ ι) :
    (∑ b, stateQForm ψ ((M.postprocess f).effect b * N.effect b)) =
      ∑ a, stateQForm ψ (M.effect a * N.effect (f a)) := by
  simp only [MIPStarRE.Quantum.Measurement.postprocess_effect, Finset.sum_mul,
    stateQForm_finset_sum]
  calc
    (∑ b, ∑ a ∈ Finset.univ.filter (fun a => f a = b),
        stateQForm ψ (M.effect a * N.effect b)) =
      ∑ b, ∑ a ∈ Finset.univ.filter (fun a => f a = b),
        stateQForm ψ (M.effect a * N.effect (f a)) := by
          apply Finset.sum_congr rfl
          intro b _
          apply Finset.sum_congr rfl
          intro a ha
          rw [(Finset.mem_filter.mp ha).2]
    _ = _ := Finset.sum_fiberwise Finset.univ f _

private theorem postprocess_defect (μ : Distribution X) (M : Measurement α ι)
    (N : X → Measurement β ι) (f : X → α → β) (ψ : EuclideanSpace ℂ ι) :
    consistencyDefect μ (fun x a => (M.postprocess (f x)).effect a)
        (fun x a => (N x).effect a) ψ =
      avgOver μ (fun x => ‖ψ‖ ^ 2 -
        ∑ a, stateQForm ψ (M.effect a * (N x).effect (f x a))) := by
  unfold consistencyDefect
  simp_rw [consistency_term_eq_stateQForm, point_defect_eq, postprocess_overlap]

private theorem leftPlaced_postprocess (M : Measurement α ιA) (f : α → β) :
    leftPlacedMeasurement (ιB := ιB) (M.postprocess f) =
      (leftPlacedMeasurement (ιB := ιB) M).postprocess f := by
  apply MIPStarRE.Quantum.Measurement.ext
  intro b
  exact heteroKron_finset_sum_left _ _ _

private theorem rightPlaced_postprocess (M : Measurement α ιB) (f : α → β) :
    rightPlacedMeasurement (ιA := ιA) (M.postprocess f) =
      (rightPlacedMeasurement (ιA := ιA) M).postprocess f := by
  apply MIPStarRE.Quantum.Measurement.ext
  intro b
  exact heteroKron_finset_sum_right _ _ _

private theorem left_postprocess_defect (μ : Distribution X) (M : Measurement α ιA)
    (N : X → Measurement β ιB) (f : X → α → β)
    (ψ : EuclideanSpace ℂ (ιA × ιB)) :
    consistencyDefect μ (fun x a => heteroKron ((M.postprocess (f x)).effect a) 1)
        (fun x a => heteroKron 1 ((N x).effect a)) ψ =
      avgOver μ (fun x => ‖ψ‖ ^ 2 -
        ∑ a, stateQForm ψ (heteroKron (M.effect a) ((N x).effect (f x a)))) := by
  change consistencyDefect μ
    (fun x a => (leftPlacedMeasurement (M.postprocess (f x))).effect a)
    (fun x a => (rightPlacedMeasurement (N x)).effect a) ψ = _
  simp_rw [leftPlaced_postprocess]
  rw [postprocess_defect]
  simp only [leftPlacedMeasurement, rightPlacedMeasurement,
    MIPStarRE.Quantum.Measurement.ofSumEqOne, placed_product_stateQForm_eq]

private theorem right_postprocess_defect (μ : Distribution X) (M : Measurement α ιB)
    (N : X → Measurement β ιA) (f : X → α → β)
    (ψ : EuclideanSpace ℂ (ιA × ιB)) :
    consistencyDefect μ (fun x a => heteroKron 1 ((M.postprocess (f x)).effect a))
        (fun x a => heteroKron ((N x).effect a) 1) ψ =
      avgOver μ (fun x => ‖ψ‖ ^ 2 -
        ∑ a, stateQForm ψ (heteroKron ((N x).effect (f x a)) (M.effect a))) := by
  change consistencyDefect μ
    (fun x a => (rightPlacedMeasurement (M.postprocess (f x))).effect a)
    (fun x a => (leftPlacedMeasurement (N x)).effect a) ψ = _
  simp_rw [rightPlaced_postprocess]
  rw [postprocess_defect]
  simp only [leftPlacedMeasurement, rightPlacedMeasurement,
    MIPStarRE.Quantum.Measurement.ofSumEqOne, heteroKron_mul, one_mul, mul_one]

omit [DecidableEq α] [Fintype X] [DecidableEq X] in
/-- Equal good-outcome contributions cancel; the remaining averaged change
is bounded by the sum of the bad-outcome upper bounds. -/
private theorem abs_avg_sum_change_le (μ : Distribution X) (hμ : μ.IsProbability)
    (good : α → Prop) [DecidablePred good] (u v : X → α → ℝ) (r : α → ℝ)
    (hu : ∀ x a, 0 ≤ u x a ∧ u x a ≤ r a)
    (hv : ∀ x a, 0 ≤ v x a ∧ v x a ≤ r a)
    (huv : ∀ x a, good a → u x a = v x a) (c : ℝ) :
    |avgOver μ (fun x => c - ∑ a, u x a) -
        avgOver μ (fun x => c - ∑ a, v x a)| ≤
      ∑ a ∈ Finset.univ.filter (fun a => ¬ good a), r a := by
  have hpoint (x : X) :
      |(c - ∑ a, u x a) - (c - ∑ a, v x a)| ≤
        ∑ a ∈ Finset.univ.filter (fun a => ¬ good a), r a := by
    have hterm (a : α) : |v x a - u x a| ≤ if ¬ good a then r a else 0 := by
      by_cases ha : good a
      · simp [ha, huv x a ha]
      · rw [if_pos ha]
        exact abs_le.mpr ⟨by linarith [(hu x a).2, (hv x a).1],
          by linarith [(hv x a).2, (hu x a).1]⟩
    calc
      _ = |∑ a, (v x a - u x a)| := by
        rw [Finset.sum_sub_distrib]
        congr 1
        ring
      _ ≤ ∑ a, |v x a - u x a| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ a, if ¬ good a then r a else 0 :=
        Finset.sum_le_sum fun a _ => hterm a
      _ = _ := (Finset.sum_filter _ _).symm
  rw [← avgOver_sub]
  calc
    _ ≤ avgOver μ (fun x => |(c - ∑ a, u x a) - (c - ∑ a, v x a)|) := by
      unfold avgOver
      refine (Finset.abs_sum_le_sum_abs _ _).trans_eq ?_
      apply Finset.sum_congr rfl
      intro x _
      rw [abs_mul, abs_of_nonneg (μ.nonnegative x)]
    _ ≤ avgOver μ (fun _ =>
        ∑ a ∈ Finset.univ.filter (fun a => ¬ good a), r a) :=
      avgOver_mono μ _ _ hpoint
    _ = _ := avgOver_const_of_isProbability μ hμ _

/-- Relabelings that agree on good outcomes change Alice-first cross-player
consistency by at most Alice's bad-outcome state mass. The spaces may differ,
the other measurement need not be projective, and the state may be unnormalized.
This auxiliary isolates the quantitative content of the source completion step. -/
theorem abs_postprocess_consistency_left_sub_le
    (μ : Distribution X) (hμ : μ.IsProbability) (M : Measurement α ιA)
    (N : X → Measurement β ιB) (good : α → Prop) [DecidablePred good]
    (f g : X → α → β) (hfg : ∀ x a, good a → f x a = g x a)
    (ψ : EuclideanSpace ℂ (ιA × ιB)) :
    |consistencyDefect μ
        (fun x a => heteroKron ((M.postprocess (f x)).effect a) 1)
        (fun x a => heteroKron 1 ((N x).effect a)) ψ -
      consistencyDefect μ
        (fun x a => heteroKron ((M.postprocess (g x)).effect a) 1)
        (fun x a => heteroKron 1 ((N x).effect a)) ψ| ≤
      stateQForm ψ (heteroKron (badEffect M good) (1 : Op ιB)) := by
  rw [left_postprocess_defect, left_postprocess_defect]
  simp only [badEffect, heteroKron_finset_sum_left, stateQForm_finset_sum]
  have hbound (x : X) (a : α) (b : β) :
      0 ≤ stateQForm ψ (heteroKron (M.effect a) ((N x).effect b)) ∧
        stateQForm ψ (heteroKron (M.effect a) ((N x).effect b)) ≤
          stateQForm ψ (heteroKron (M.effect a) (1 : Op ιB)) :=
    ⟨stateQForm_nonneg ψ (kronecker_nonneg (M.pos a) ((N x).pos b)),
      quadratic_form_mono
        (kronecker_le_kronecker_right_one (M.pos a) (measurement_effect_le_one (N x) b)) ψ⟩
  exact abs_avg_sum_change_le μ hμ good _ _ _
    (fun x a => hbound x a (f x a)) (fun x a => hbound x a (g x a))
    (fun x a ha => by rw [hfg x a ha]) _

/-- Relabelings that agree on good outcomes change Bob-first cross-player
consistency by at most Bob's bad-outcome state mass. The completed measurement
is the first consistency argument, although it acts on the right tensor factor;
this is the orientation of the Bob conclusion of `lem:qld-4-7`. -/
theorem abs_postprocess_consistency_right_sub_le
    (μ : Distribution X) (hμ : μ.IsProbability) (M : Measurement α ιB)
    (N : X → Measurement β ιA) (good : α → Prop) [DecidablePred good]
    (f g : X → α → β) (hfg : ∀ x a, good a → f x a = g x a)
    (ψ : EuclideanSpace ℂ (ιA × ιB)) :
    |consistencyDefect μ
        (fun x a => heteroKron 1 ((M.postprocess (f x)).effect a))
        (fun x a => heteroKron ((N x).effect a) 1) ψ -
      consistencyDefect μ
        (fun x a => heteroKron 1 ((M.postprocess (g x)).effect a))
        (fun x a => heteroKron ((N x).effect a) 1) ψ| ≤
      stateQForm ψ (heteroKron (1 : Op ιA) (badEffect M good)) := by
  rw [right_postprocess_defect, right_postprocess_defect]
  simp only [badEffect, heteroKron_finset_sum_right, stateQForm_finset_sum]
  have hbound (x : X) (a : α) (b : β) :
      0 ≤ stateQForm ψ (heteroKron ((N x).effect b) (M.effect a)) ∧
        stateQForm ψ (heteroKron ((N x).effect b) (M.effect a)) ≤
          stateQForm ψ (heteroKron (1 : Op ιA) (M.effect a)) :=
    ⟨stateQForm_nonneg ψ (kronecker_nonneg ((N x).pos b) (M.pos a)),
      quadratic_form_mono
        (kronecker_mono_left (measurement_effect_le_one (N x) b) (M.pos a)) ψ⟩
  exact abs_avg_sum_change_le μ hμ good _ _ _
    (fun x a => hbound x a (f x a)) (fun x a => hbound x a (g x a))
    (fun x a ha => by rw [hfg x a ha]) _

/-- After any outcome maps agreeing on the good outcomes, the constructed
completion changes Alice-first consistency by at most the bad projection's
state mass. Together with `complete_isProjective`, this is the finite-measurement
adapter for the completion step of `lem:qld-4-7`, not its source mass estimate. -/
theorem abs_complete_consistency_left_sub_le
    (μ : Distribution X) (hμ : μ.IsProbability) (M : Measurement α ιA)
    (N : X → Measurement β ιB) (good : α → Prop) [DecidablePred good]
    (a₀ : {a // good a}) (f : X → α → β) (g : X → {a // good a} → β)
    (hgf : ∀ x a, g x a = f x a) (ψ : EuclideanSpace ℂ (ιA × ιB)) :
    |consistencyDefect μ
        (fun x a => heteroKron (((complete M good a₀).postprocess (g x)).effect a) 1)
        (fun x a => heteroKron 1 ((N x).effect a)) ψ -
      consistencyDefect μ
        (fun x a => heteroKron ((M.postprocess (f x)).effect a) 1)
        (fun x a => heteroKron 1 ((N x).effect a)) ψ| ≤
      stateQForm ψ (heteroKron (badEffect M good) (1 : Op ιB)) := by
  simp only [complete, MIPStarRE.Quantum.Measurement.postprocess_comp]
  apply abs_postprocess_consistency_left_sub_le μ hμ M N good _ f _ ψ
  intro x a ha
  simpa only [toGood, dif_pos ha] using hgf x ⟨a, ha⟩

/-- The same completion estimate with the completed measurement on Bob's
space, still as the first argument of consistency. Both player spaces and the
order of the tensor factors remain explicit. -/
theorem abs_complete_consistency_right_sub_le
    (μ : Distribution X) (hμ : μ.IsProbability) (M : Measurement α ιB)
    (N : X → Measurement β ιA) (good : α → Prop) [DecidablePred good]
    (a₀ : {a // good a}) (f : X → α → β) (g : X → {a // good a} → β)
    (hgf : ∀ x a, g x a = f x a) (ψ : EuclideanSpace ℂ (ιA × ιB)) :
    |consistencyDefect μ
        (fun x a => heteroKron 1 (((complete M good a₀).postprocess (g x)).effect a))
        (fun x a => heteroKron ((N x).effect a) 1) ψ -
      consistencyDefect μ
        (fun x a => heteroKron 1 ((M.postprocess (f x)).effect a))
        (fun x a => heteroKron ((N x).effect a) 1) ψ| ≤
      stateQForm ψ (heteroKron (1 : Op ιA) (badEffect M good)) := by
  simp only [complete, MIPStarRE.Quantum.Measurement.postprocess_comp]
  apply abs_postprocess_consistency_right_sub_le μ hμ M N good _ f _ ψ
  intro x a ha
  simpa only [toGood, dif_pos ha] using hgf x ⟨a, ha⟩

/-- Adding one fixed operator at a question-dependent outcome changes the
defect by its total state mass minus the overlap at that outcome. -/
private theorem add_at_outcome_defect (μ : Distribution X)
    (A : X → β → Op ι) (N : X → Measurement β ι)
    (R : Op ι) (k : X → β) (ψ : EuclideanSpace ℂ ι) :
    consistencyDefect μ (fun x a => A x a + if a = k x then R else 0)
        (fun x a => (N x).effect a) ψ =
      consistencyDefect μ A (fun x a => (N x).effect a) ψ +
        avgOver μ (fun x => stateQForm ψ R - stateQForm ψ (R * (N x).effect (k x))) := by
  unfold consistencyDefect
  simp_rw [consistency_term_eq_stateQForm]
  have hpoint (x : X) :
      (∑ a, ∑ b, if a = b then 0 else
        stateQForm ψ ((A x a + if a = k x then R else 0) * (N x).effect b)) =
      (∑ a, ∑ b, if a = b then 0 else stateQForm ψ (A x a * (N x).effect b)) +
        (stateQForm ψ R - stateQForm ψ (R * (N x).effect (k x))) := by
    have hterm (a b : β) :
        (if a = b then 0 else
          stateQForm ψ ((A x a + if a = k x then R else 0) * (N x).effect b)) =
        (if a = b then 0 else stateQForm ψ (A x a * (N x).effect b)) +
          if a = k x then
            (if a = b then 0 else stateQForm ψ (R * (N x).effect b)) else 0 := by
      by_cases hab : a = b
      · simp only [hab, if_true, ite_self, add_zero]
      · simp only [hab, if_false]
        by_cases ha : a = k x <;> simp [ha, add_mul, stateQForm_add]
    simp_rw [hterm, Finset.sum_add_distrib]
    congr 1
    rw [Finset.sum_comm]
    simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true]
    rw [Finset.sum_ite]
    simp only [Finset.sum_const_zero, zero_add]
    rw [show Finset.univ.filter (fun b => ¬ k x = b) = Finset.univ.erase (k x) by
      ext b
      simp [ne_comm]]
    rw [Finset.sum_erase_eq_sub (Finset.mem_univ _),
      ← stateQForm_finset_sum, ← Finset.mul_sum,
      (N x).sum_eq_one, mul_one]
  simp_rw [hpoint]
  exact avgOver_add μ _ _

/-- Completing the good restriction and then relabeling increases Alice-first
consistency by at most the bad-effect mass. This directly applies to the
submeasurement relation preceding completion in the source; projectivity of the
constructed complete measurement is supplied by `complete_isProjective`. -/
theorem complete_restrict_consistency_left_le
    (μ : Distribution X) (hμ : μ.IsProbability) (M : Measurement α ιA)
    (N : X → Measurement β ιB) (good : α → Prop) [DecidablePred good]
    (a₀ : {a // good a}) (g : X → {a // good a} → β)
    (ψ : EuclideanSpace ℂ (ιA × ιB)) :
    consistencyDefect μ
        (fun x a => heteroKron (((complete M good a₀).postprocess (g x)).effect a) 1)
        (fun x a => heteroKron 1 ((N x).effect a)) ψ ≤
      consistencyDefect μ
        (fun x a => heteroKron (((restrict M good).postprocess (g x)).effect a) 1)
        (fun x a => heteroKron 1 ((N x).effect a)) ψ +
      stateQForm ψ (heteroKron (badEffect M good) (1 : Op ιB)) := by
  have heffect (x : X) (a : β) :
      heteroKron (((complete M good a₀).postprocess (g x)).effect a) (1 : Op ιB) =
        heteroKron (((restrict M good).postprocess (g x)).effect a) 1 +
          if a = g x a₀ then heteroKron (badEffect M good) 1 else 0 := by
    rw [complete_postprocess_effect, heteroKron_add_left]
    by_cases h : a = g x a₀ <;> simp [h, heteroKron]
  simp_rw [heffect]
  have hdefect := add_at_outcome_defect μ
    (fun x a => heteroKron (((restrict M good).postprocess (g x)).effect a) 1)
    (fun x => rightPlacedMeasurement (N x))
    (heteroKron (badEffect M good) 1) (fun x => g x a₀) ψ
  dsimp only [rightPlacedMeasurement, MIPStarRE.Quantum.Measurement.ofSumEqOne] at hdefect
  rw [hdefect]
  apply add_le_add le_rfl
  calc
    _ ≤ avgOver μ (fun _ => stateQForm ψ
        (heteroKron (badEffect M good) (1 : Op ιB))) := by
      apply avgOver_mono
      intro x
      apply sub_le_self
      change 0 ≤ stateQForm ψ
        (heteroKron (badEffect M good) 1 * heteroKron 1 ((N x).effect (g x a₀)))
      rw [placed_product_stateQForm_eq]
      exact stateQForm_nonneg ψ (kronecker_nonneg (badEffect_nonneg M good) ((N x).pos _))
    _ = _ := avgOver_const_of_isProbability μ hμ _

/-- The direct restriction-to-completion estimate with the completed
measurement on Bob's space and first in the consistency relation. -/
theorem complete_restrict_consistency_right_le
    (μ : Distribution X) (hμ : μ.IsProbability) (M : Measurement α ιB)
    (N : X → Measurement β ιA) (good : α → Prop) [DecidablePred good]
    (a₀ : {a // good a}) (g : X → {a // good a} → β)
    (ψ : EuclideanSpace ℂ (ιA × ιB)) :
    consistencyDefect μ
        (fun x a => heteroKron 1 (((complete M good a₀).postprocess (g x)).effect a))
        (fun x a => heteroKron ((N x).effect a) 1) ψ ≤
      consistencyDefect μ
        (fun x a => heteroKron 1 (((restrict M good).postprocess (g x)).effect a))
        (fun x a => heteroKron ((N x).effect a) 1) ψ +
      stateQForm ψ (heteroKron (1 : Op ιA) (badEffect M good)) := by
  have heffect (x : X) (a : β) :
      heteroKron (1 : Op ιA) (((complete M good a₀).postprocess (g x)).effect a) =
        heteroKron 1 (((restrict M good).postprocess (g x)).effect a) +
          if a = g x a₀ then heteroKron 1 (badEffect M good) else 0 := by
    rw [complete_postprocess_effect, heteroKron_add_right]
    by_cases h : a = g x a₀ <;> simp [h, heteroKron]
  simp_rw [heffect]
  have hdefect := add_at_outcome_defect μ
    (fun x a => heteroKron 1 (((restrict M good).postprocess (g x)).effect a))
    (fun x => leftPlacedMeasurement (N x))
    (heteroKron 1 (badEffect M good)) (fun x => g x a₀) ψ
  dsimp only [leftPlacedMeasurement, MIPStarRE.Quantum.Measurement.ofSumEqOne] at hdefect
  rw [hdefect]
  apply add_le_add le_rfl
  calc
    _ ≤ avgOver μ (fun _ => stateQForm ψ
        (heteroKron (1 : Op ιA) (badEffect M good))) := by
      apply avgOver_mono
      intro x
      apply sub_le_self
      change 0 ≤ stateQForm ψ
        (heteroKron 1 (badEffect M good) * heteroKron ((N x).effect (g x a₀)) 1)
      rw [heteroKron_mul, one_mul, mul_one]
      exact stateQForm_nonneg ψ (kronecker_nonneg ((N x).pos _) (badEffect_nonneg M good))
    _ = _ := avgOver_const_of_isProbability μ hμ _

end MIPStarRE.QPBT.SupportedCompletion
