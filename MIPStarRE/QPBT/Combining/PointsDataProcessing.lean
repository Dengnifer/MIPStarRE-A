import MIPStarRE.QPBT.Combining.Witnesses

/-!
# Averaged affine coarse-graining of complete operator families

Uniform scalar coefficients give collision probability `1 / card K` for
distinct pairs over a finite field. Expanding the squared state-dependent
distance therefore proves contraction when the two operator families have
the same total operator. The placement lemmas apply this identity to the
complete point measurements and to both ordered measurement products.

## References

This is the finite-dimensional calculation used for the coarse-graining in
`lem:qld-4-12`, `references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:993-1018`.
The operator-family contraction is a formalization-only auxiliary lemma.
-/

open scoped BigOperators

namespace MIPStarRE.QPBT

open MIPStarRE.LDT hiding Measurement
open MIPStarRE.Quantum

noncomputable section

private theorem avgOver_uniform_eq_indicator {K : Type*}
    [Fintype K] [DecidableEq K] [Nonempty K] (x : K) :
    avgOver (uniformDistribution K) (fun y => if y = x then (1 : ℝ) else 0) =
      (Fintype.card K : ℝ)⁻¹ := by
  rw [avgOver_uniform_eq_inv_card_mul_sum]
  simp

private theorem affine_collision_average {K : Type*}
    [Field K] [Fintype K] [DecidableEq K]
    (p p' : K × K) :
    avgOver (uniformDistribution (K × K)) (fun coefficients =>
      if coefficients.1 * p.1 + coefficients.2 * p.2 =
          coefficients.1 * p'.1 + coefficients.2 * p'.2 then (1 : ℝ) else 0) =
      if p = p' then 1 else (Fintype.card K : ℝ)⁻¹ := by
  classical
  calc
    avgOver (uniformDistribution (K × K)) (fun coefficients =>
        if coefficients.1 * p.1 + coefficients.2 * p.2 =
            coefficients.1 * p'.1 + coefficients.2 * p'.2 then (1 : ℝ) else 0) =
        avgOver (uniformDistribution K) (fun alpha =>
          avgOver (uniformDistribution K) (fun beta =>
            if alpha * p.1 + beta * p.2 = alpha * p'.1 + beta * p'.2 then
              (1 : ℝ) else 0)) := by
                simpa only using
                  (avgOver_uniform_prod (α := K) (β := K) (fun alpha beta =>
                    if alpha * p.1 + beta * p.2 = alpha * p'.1 + beta * p'.2 then
                      (1 : ℝ) else 0))
    _ = if p = p' then 1 else (Fintype.card K : ℝ)⁻¹ := by
      by_cases hp : p = p'
      · subst p'
        simp [avgOver_uniform_const]
      · rw [if_neg hp]
        by_cases hfirst : p.1 = p'.1
        · have hsecond : p.2 ≠ p'.2 := by
            intro h
            exact hp (Prod.ext hfirst h)
          have hdiff : p.2 - p'.2 ≠ 0 := sub_ne_zero.mpr hsecond
          calc
        avgOver (uniformDistribution K) (fun alpha =>
            avgOver (uniformDistribution K) (fun beta =>
              if alpha * p.1 + beta * p.2 = alpha * p'.1 + beta * p'.2 then
                (1 : ℝ) else 0)) =
            avgOver (uniformDistribution K) (fun _ =>
              avgOver (uniformDistribution K) (fun beta =>
                if beta = 0 then (1 : ℝ) else 0)) := by
              apply avgOver_congr
              intro alpha
              apply avgOver_congr
              intro beta
              congr 1
              apply propext
              constructor
              · intro h
                rw [hfirst] at h
                have : beta * (p.2 - p'.2) = 0 := by
                  linear_combination h
                exact (mul_eq_zero.mp this).resolve_right hdiff
              · intro h
                subst beta
                simp [hfirst]
            _ = _ := by rw [avgOver_uniform_eq_indicator, avgOver_uniform_const]
        · have hdiff : p.1 - p'.1 ≠ 0 := sub_ne_zero.mpr hfirst
          calc
        avgOver (uniformDistribution K) (fun alpha =>
            avgOver (uniformDistribution K) (fun beta =>
              if alpha * p.1 + beta * p.2 = alpha * p'.1 + beta * p'.2 then
                (1 : ℝ) else 0)) =
            avgOver (uniformDistribution K) (fun beta =>
              avgOver (uniformDistribution K) (fun alpha =>
                if alpha = beta * (p'.2 - p.2) / (p.1 - p'.1) then
                  (1 : ℝ) else 0)) := by
              rw [avgOver_uniform_comm]
              apply avgOver_congr
              intro beta
              apply avgOver_congr
              intro alpha
              congr 1
              apply propext
              exact calc
                alpha * p.1 + beta * p.2 = alpha * p'.1 + beta * p'.2 ↔
                    alpha * (p.1 - p'.1) = beta * (p'.2 - p.2) := by
                      constructor <;> intro h <;> linear_combination h
                _ ↔ alpha = beta * (p'.2 - p.2) / (p.1 - p'.1) :=
                  (eq_div_iff hdiff).symm
            _ = _ := by
              calc
                avgOver (uniformDistribution K) (fun beta =>
                    avgOver (uniformDistribution K) (fun alpha =>
                      if alpha = beta * (p'.2 - p.2) / (p.1 - p'.1) then
                        (1 : ℝ) else 0)) =
                    avgOver (uniformDistribution K)
                      (fun _ => (Fintype.card K : ℝ)⁻¹) := by
                        apply avgOver_congr
                        intro beta
                        exact avgOver_uniform_eq_indicator _
                _ = _ := avgOver_uniform_const _

private theorem sum_fiber_norm_sq_eq_pair_sum
    {Γ R ι : Type*} [Fintype Γ] [Fintype R] [DecidableEq R]
    [Fintype ι] [DecidableEq ι]
    (f : Γ → R) (v : Γ → EuclideanSpace ℂ ι) :
    (∑ r : R, ‖∑ g ∈ Finset.univ.filter (fun g => f g = r), v g‖ ^ 2) =
      ∑ g : Γ, ∑ g' : Γ,
        if f g = f g' then (inner ℂ (v g) (v g')).re else 0 := by
  classical
  calc
    (∑ r : R, ‖∑ g ∈ Finset.univ.filter (fun g => f g = r), v g‖ ^ 2) =
        ∑ r : R, ∑ g ∈ Finset.univ.filter (fun g => f g = r),
          ∑ g' ∈ Finset.univ.filter (fun g' => f g' = r),
            (inner ℂ (v g) (v g')).re := by
              apply Finset.sum_congr rfl
              intro r _
              simp only [@norm_sq_eq_re_inner ℂ, sum_inner, inner_sum, map_sum]
              apply Finset.sum_congr rfl
              intro g _
              apply Finset.sum_congr rfl
              intro g' _
              exact inner_re_symm _ _
    _ = ∑ r : R, ∑ g : Γ, ∑ g' : Γ,
        if f g = r ∧ f g' = r then (inner ℂ (v g) (v g')).re else 0 := by
          apply Finset.sum_congr rfl
          intro r _
          rw [Finset.sum_filter]
          apply Finset.sum_congr rfl
          intro g _
          by_cases hg : f g = r
          · rw [if_pos hg, Finset.sum_filter]
            apply Finset.sum_congr rfl
            intro g' _
            by_cases hg' : f g' = r <;> simp [hg, hg']
          · simp [hg]
    _ = ∑ g : Γ, ∑ r : R, ∑ g' : Γ,
        if f g = r ∧ f g' = r then (inner ℂ (v g) (v g')).re else 0 := by
          rw [Finset.sum_comm]
    _ = ∑ g : Γ, ∑ g' : Γ, ∑ r : R,
        if f g = r ∧ f g' = r then (inner ℂ (v g) (v g')).re else 0 := by
          apply Finset.sum_congr rfl
          intro g _
          rw [Finset.sum_comm]
    _ = ∑ g : Γ, ∑ g' : Γ,
        if f g = f g' then (inner ℂ (v g) (v g')).re else 0 := by
          apply Finset.sum_congr rfl
          intro g _
          apply Finset.sum_congr rfl
          intro g' _
          by_cases hgg' : f g = f g'
          · rw [if_pos hgg', Fintype.sum_eq_single (f g)]
            · simp [hgg']
            · intro r hr
              simp [Ne.symm hr]
          · rw [if_neg hgg']
            apply Finset.sum_eq_zero
            intro r _
            simp only [ite_eq_right_iff]
            intro h
            exact (hgg' (h.1.trans h.2.symm)).elim

private theorem avg_affine_fiber_norm_sq_le
    {K ι : Type*} [Field K] [Fintype K] [DecidableEq K]
    [Fintype ι] [DecidableEq ι]
    (v : K × K → EuclideanSpace ℂ ι) (hsum : ∑ p, v p = 0) :
    avgOver (uniformDistribution (K × K)) (fun coefficients =>
        ∑ c : K,
          ‖∑ p ∈ Finset.univ.filter (fun p =>
            coefficients.1 * p.1 + coefficients.2 * p.2 = c), v p‖ ^ 2) ≤
      ∑ p, ‖v p‖ ^ 2 := by
  classical
  let w : (K × K) → (K × K) → ℝ := fun p p' => (inner ℂ (v p) (v p')).re
  let qinv : ℝ := (Fintype.card K : ℝ)⁻¹
  have hall : (∑ p, ∑ p', w p p') = 0 := by
    have h := sum_fiber_norm_sq_eq_pair_sum (fun _ : K × K => ()) v
    simpa [w, hsum] using h.symm
  have hdiag : (∑ p, w p p) = ∑ p, ‖v p‖ ^ 2 := by
    apply Finset.sum_congr rfl
    intro p _
    exact (@norm_sq_eq_re_inner ℂ _ _ _ _ (v p)).symm
  have hnonneg : 0 ≤ ∑ p, ‖v p‖ ^ 2 :=
    Finset.sum_nonneg fun p _ => sq_nonneg _
  have hqinv : 0 ≤ qinv := by positivity
  calc
    avgOver (uniformDistribution (K × K)) (fun coefficients =>
        ∑ c : K,
          ‖∑ p ∈ Finset.univ.filter (fun p =>
            coefficients.1 * p.1 + coefficients.2 * p.2 = c), v p‖ ^ 2) =
        avgOver (uniformDistribution (K × K)) (fun coefficients =>
          ∑ p, ∑ p', if
            coefficients.1 * p.1 + coefficients.2 * p.2 =
              coefficients.1 * p'.1 + coefficients.2 * p'.2 then w p p' else 0) := by
            apply avgOver_congr
            intro coefficients
            exact sum_fiber_norm_sq_eq_pair_sum _ v
    _ = ∑ p, ∑ p', avgOver (uniformDistribution (K × K)) (fun coefficients =>
          if coefficients.1 * p.1 + coefficients.2 * p.2 =
              coefficients.1 * p'.1 + coefficients.2 * p'.2 then w p p' else 0) := by
            rw [avgOver_sum]
            apply Finset.sum_congr rfl
            intro p _
            rw [avgOver_sum]
    _ = ∑ p, ∑ p', if p = p' then w p p' else qinv * w p p' := by
            apply Finset.sum_congr rfl
            intro p _
            apply Finset.sum_congr rfl
            intro p' _
            calc
              avgOver (uniformDistribution (K × K)) (fun coefficients =>
                  if coefficients.1 * p.1 + coefficients.2 * p.2 =
                      coefficients.1 * p'.1 + coefficients.2 * p'.2 then
                    w p p' else 0) =
                  avgOver (uniformDistribution (K × K)) (fun coefficients =>
                    (if coefficients.1 * p.1 + coefficients.2 * p.2 =
                        coefficients.1 * p'.1 + coefficients.2 * p'.2 then
                      (1 : ℝ) else 0) * w p p') := by
                        apply avgOver_congr
                        intro coefficients
                        split <;> simp_all
              _ = (if p = p' then 1 else qinv) * w p p' := by
                    rw [avgOver_mul_const, affine_collision_average]
              _ = if p = p' then w p p' else qinv * w p p' := by
                    split <;> simp_all
    _ = (1 - qinv) * ∑ p, ‖v p‖ ^ 2 := by
          calc
            (∑ p, ∑ p', if p = p' then w p p' else qinv * w p p') =
                qinv * (∑ p, ∑ p', w p p') + (1 - qinv) * ∑ p, w p p := by
                  rw [Finset.mul_sum, Finset.mul_sum]
                  rw [← Finset.sum_add_distrib]
                  apply Finset.sum_congr rfl
                  intro p _
                  calc
                    (∑ p', if p = p' then w p p' else qinv * w p p') =
                        ∑ p', (qinv * w p p' +
                          if p = p' then (1 - qinv) * w p p' else 0) := by
                            apply Finset.sum_congr rfl
                            intro p' _
                            by_cases h : p = p' <;> simp [h]
                            ring
                    _ = qinv * ∑ p', w p p' + (1 - qinv) * w p p := by
                          rw [Finset.sum_add_distrib, ← Finset.mul_sum]
                          congr 1
                          rw [Fintype.sum_eq_single p]
                          · simp
                          · intro p' hp'
                            simp [Ne.symm hp']
            _ = (1 - qinv) * ∑ p, ‖v p‖ ^ 2 := by rw [hall, hdiag]; ring
    _ ≤ ∑ p, ‖v p‖ ^ 2 := by nlinarith

/-- Uniform affine scalar coarse-graining does not increase the squared
state-dependent distance of complete operator families. -/
theorem opFamilyDistSq_uniform_affine_postprocess_le
    {X K ι : Type} [Fintype X] [DecidableEq X] [Nonempty X]
    [Field K] [Fintype K] [DecidableEq K]
    [Fintype ι] [DecidableEq ι]
    (A B : X → K × K → Op ι) (ψ : EuclideanSpace ℂ ι)
    (hsum : ∀ x, ∑ p, A x p = ∑ p, B x p) :
    opFamilyDistSq (uniformDistribution (X × (K × K)))
        (fun question c =>
          ∑ p ∈ Finset.univ.filter (fun p =>
            question.2.1 * p.1 + question.2.2 * p.2 = c), A question.1 p)
        (fun question c =>
          ∑ p ∈ Finset.univ.filter (fun p =>
            question.2.1 * p.1 + question.2.2 * p.2 = c), B question.1 p)
        ψ ≤ opFamilyDistSq (uniformDistribution X) A B ψ := by
  classical
  unfold opFamilyDistSq
  calc
    avgOver (uniformDistribution (X × (K × K))) (fun question =>
        ∑ c : K,
          ‖applyOperatorToState
            ((∑ p ∈ Finset.univ.filter (fun p =>
                question.2.1 * p.1 + question.2.2 * p.2 = c), A question.1 p) -
              ∑ p ∈ Finset.univ.filter (fun p =>
                question.2.1 * p.1 + question.2.2 * p.2 = c), B question.1 p) ψ‖ ^ 2) =
        avgOver (uniformDistribution X) (fun x =>
          avgOver (uniformDistribution (K × K)) (fun coefficients =>
            ∑ c : K,
              ‖applyOperatorToState
                ((∑ p ∈ Finset.univ.filter (fun p =>
                    coefficients.1 * p.1 + coefficients.2 * p.2 = c), A x p) -
                  ∑ p ∈ Finset.univ.filter (fun p =>
                    coefficients.1 * p.1 + coefficients.2 * p.2 = c), B x p) ψ‖ ^ 2)) := by
          simpa only using (avgOver_uniform_prod (α := X) (β := K × K)
            (fun x coefficients =>
              ∑ c : K,
                ‖applyOperatorToState
                  ((∑ p ∈ Finset.univ.filter (fun p =>
                      coefficients.1 * p.1 + coefficients.2 * p.2 = c), A x p) -
                    ∑ p ∈ Finset.univ.filter (fun p =>
                      coefficients.1 * p.1 + coefficients.2 * p.2 = c), B x p) ψ‖ ^ 2))
    _ ≤ avgOver (uniformDistribution X) (fun x =>
        ∑ p, ‖applyOperatorToState (A x p - B x p) ψ‖ ^ 2) := by
      apply avgOver_mono
      intro x
      let v : K × K → EuclideanSpace ℂ ι := fun p =>
        applyOperatorToState (A x p - B x p) ψ
      have hvsum : ∑ p, v p = 0 := by
        simp only [v]
        calc
          (∑ p, applyOperatorToState (A x p - B x p) ψ) =
              applyOperatorToState (∑ p, (A x p - B x p)) ψ :=
                (MagicSquareRigidity.applyOperatorToState_sum
                  (fun p => A x p - B x p) ψ).symm
          _ = 0 := by
            rw [Finset.sum_sub_distrib, hsum x, sub_self]
            simp [applyOperatorToState]
      calc
        avgOver (uniformDistribution (K × K)) (fun coefficients =>
            ∑ c : K,
              ‖applyOperatorToState
                ((∑ p ∈ Finset.univ.filter (fun p =>
                    coefficients.1 * p.1 + coefficients.2 * p.2 = c), A x p) -
                  ∑ p ∈ Finset.univ.filter (fun p =>
                    coefficients.1 * p.1 + coefficients.2 * p.2 = c), B x p) ψ‖ ^ 2) =
            avgOver (uniformDistribution (K × K)) (fun coefficients =>
              ∑ c : K,
                ‖∑ p ∈ Finset.univ.filter (fun p =>
                  coefficients.1 * p.1 + coefficients.2 * p.2 = c), v p‖ ^ 2) := by
                  apply avgOver_congr
                  intro coefficients
                  apply Finset.sum_congr rfl
                  intro c _
                  congr 2
                  simp only [v, applyOperatorToState, map_sub, LinearMap.sub_apply,
                    map_sum, LinearMap.sum_apply, Finset.sum_sub_distrib]
        _ ≤ ∑ p, ‖v p‖ ^ 2 := avg_affine_fiber_norm_sq_le v hvsum
        _ = ∑ p, ‖applyOperatorToState (A x p - B x p) ψ‖ ^ 2 := rfl

/-- Register placement preserves the total of a finite operator family. -/
theorem place_sum {P : AdmissibleParams} {ε : ℝ}
    (S : ProjectiveSetting P ε) (p : Placement) {α : Type*} [Fintype α]
    (A : α → Op (S.ExpandedLocalSpace p.side)) :
    S.place p (∑ a, A a) = ∑ a, S.place p (A a) := by
  classical
  ext i j
  cases p <;> simp [ProjectiveSetting.place, Matrix.sum_apply,
    Finset.sum_mul, Finset.mul_sum]

private theorem place_one {P : AdmissibleParams} {ε : ℝ}
    (S : ProjectiveSetting P ε) (p : Placement) :
    S.place p (1 : Op (S.ExpandedLocalSpace p.side)) = 1 := by
  ext i j
  cases p <;> simp only [ProjectiveSetting.place, Matrix.one_apply, Prod.ext_iff]
  all_goals split_ifs <;> aesop

/-- A complete measurement remains complete after register placement. -/
theorem sum_placed_measurement_eq_one {P : AdmissibleParams} {ε : ℝ}
    (S : ProjectiveSetting P ε) (p : Placement) {α : Type*} [Fintype α]
    (M : Measurement α (S.ExpandedLocalSpace p.side)) :
    (∑ a, S.place p (M.effect a)) = 1 := by
  rw [← place_sum, M.sum_eq_one, place_one]

/-- Ordered products of two complete measurements have total identity after placement. -/
theorem sum_placed_measurement_products_eq_one
    {P : AdmissibleParams} {ε : ℝ}
    (S : ProjectiveSetting P ε) (p : Placement)
    {α β : Type*} [Fintype α] [Fintype β]
    (M : Measurement α (S.ExpandedLocalSpace p.side))
    (N : Measurement β (S.ExpandedLocalSpace p.side)) :
    (∑ ab : α × β, S.place p (M.effect ab.1 * N.effect ab.2)) = 1 := by
  rw [← place_sum, Fintype.sum_prod_type]
  have hlocal : (∑ a : α, ∑ b : β, M.effect a * N.effect b) = 1 := by
    calc
    (∑ a : α, ∑ b : β, M.effect a * N.effect b) =
        ∑ a : α, M.effect a * ∑ b : β, N.effect b := by
          apply Finset.sum_congr rfl
          intro a _
          rw [Finset.mul_sum]
    _ = (∑ a : α, M.effect a) * ∑ b : β, N.effect b := by rw [Finset.sum_mul]
    _ = 1 := by rw [M.sum_eq_one, N.sum_eq_one, one_mul]
  rw [hlocal, place_one]

end

end MIPStarRE.QPBT
