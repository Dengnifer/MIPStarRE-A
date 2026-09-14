import MIPStarRE.QPBT.Combining.DirectPassingErrorBounds
import MIPStarRE.QPBT.Combining.RootErrorBounds

/-! # Absorption of the actual rounded polynomial-pair error

The point and line errors both enter low-degree soundness. The actual
projective rounding then incurs an eighth root. The unit cap is applied only
to the final consistency defect.

## References

Paper `lem:qld-4-7`,
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1267-1404`.
The direct passing estimate is recovered from PR545; square-root closure is
recovered from issue #529. This module proves their quantitative composition.
-/

namespace MIPStarRE.QPBT

/-- On the unit interval, all actual rounding terms are bounded by an eighth
root. The point error is controlled through its square root, as in the saved
direct passing bound. The cap uses the independent unit bound on defects. -/
theorem actual_rounding_error_le_root {delta point ratio t : ℝ}
    (hd : 0 ≤ delta) (hp : 0 ≤ point)
    (hdt : delta ≤ t) (hpt : Real.sqrt point ≤ t) (hrt : ratio ≤ t) :
    min 1 (32 * delta + 32 * Real.sqrt (220 * delta ^ (1 / 4 : ℝ)) +
      64 * Real.sqrt (2 * delta) + 64 * point + 30 * ratio) ≤
      1024 * Real.sqrt (Real.sqrt (Real.sqrt (min 1 t))) := by
  have ht : 0 ≤ t := hd.trans hdt
  by_cases ht1 : t ≤ 1
  · rw [min_eq_right ht1]
    have hroot : Real.sqrt (Real.sqrt (Real.sqrt t)) = t ^ (1 / 8 : ℝ) := by
      simp only [Real.sqrt_eq_rpow]
      rw [← Real.rpow_mul ht, ← Real.rpow_mul ht]
      norm_num
    rw [hroot]
    have h18 : t ≤ t ^ (1 / 8 : ℝ) := by
      simpa using Real.rpow_le_rpow_of_exponent_ge' ht ht1
        (by norm_num : (0 : ℝ) ≤ 1 / 8) (by norm_num : (1 / 8 : ℝ) ≤ 1)
    have h14 : t ≤ t ^ (1 / 4 : ℝ) := by
      simpa using Real.rpow_le_rpow_of_exponent_ge' ht ht1
        (by norm_num : (0 : ℝ) ≤ 1 / 4) (by norm_num : (1 / 4 : ℝ) ≤ 1)
    have hsqrt : Real.sqrt (t ^ (1 / 4 : ℝ)) = t ^ (1 / 8 : ℝ) := by
      rw [Real.sqrt_eq_rpow, ← Real.rpow_mul ht]
      norm_num
    have hround : Real.sqrt (220 * delta ^ (1 / 4 : ℝ)) ≤
        15 * t ^ (1 / 8 : ℝ) := by
      calc
        _ ≤ Real.sqrt (225 * t ^ (1 / 4 : ℝ)) := Real.sqrt_le_sqrt
          (mul_le_mul (by norm_num) (Real.rpow_le_rpow hd hdt (by norm_num))
            (Real.rpow_nonneg hd _) (by norm_num))
        _ = _ := by rw [Real.sqrt_mul (by norm_num), hsqrt]; norm_num
    have hsecond : Real.sqrt (2 * delta) ≤ 2 * t ^ (1 / 8 : ℝ) := by
      calc
        _ ≤ Real.sqrt (4 * t ^ (1 / 4 : ℝ)) :=
          Real.sqrt_le_sqrt (by nlinarith [Real.rpow_nonneg ht (1 / 4 : ℝ)])
        _ = _ := by rw [Real.sqrt_mul (by norm_num), hsqrt]; norm_num
    have hpoint : point ≤ t := by
      nlinarith [Real.sq_sqrt hp, Real.sqrt_nonneg point]
    refine (min_le_right _ _).trans ?_
    nlinarith [Real.rpow_nonneg ht (1 / 8 : ℝ)]
  · rw [min_eq_left (le_of_not_ge ht1)]
    norm_num

/-- A fixed positive coefficient can be absorbed by increasing the universal
prefactor exponent, for every nonnegative strategy error. -/
theorem scale_deltaQld_le {P : AdmissibleParams} {a b epsilon K : ℝ}
    (ha : 1 ≤ a) (he : 0 ≤ epsilon) (hK : 1 ≤ K) :
    K * deltaQld a b epsilon P.m P.d P.q ≤
      deltaQld (K * a) b epsilon P.m P.d P.q := by
  have hmd : (1 : ℝ) ≤ ((P.m * P.d : ℕ) : ℝ) :=
    Nat.one_le_cast.mpr (Nat.mul_pos P.one_le_m P.hd)
  have haK : a ≤ K * a := le_mul_of_one_le_left (by linarith) hK
  have ha0 : 0 ≤ a := by linarith
  have hK0 : 0 ≤ K := by linarith
  have hsum : 0 ≤ Real.rpow epsilon b + Real.rpow (P.q : ℝ) (-b) +
      Real.rpow 2 (-(b * ((P.m * P.d : ℕ) : ℝ))) :=
    add_nonneg (add_nonneg (Real.rpow_nonneg he _) (Real.rpow_nonneg (by positivity) _))
      (Real.rpow_nonneg (by norm_num) _)
  unfold deltaQld
  rw [← mul_assoc, ← mul_assoc]
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le hmd haK) (mul_nonneg hK0 ha0)) hsum

/-- Universal absorption of the actual rounded pair error, including the
point and line errors in the passing envelope and the eighth-root rounding
loss. The constants precede all admissible parameters and nonnegative errors.
This is the final scalar substitution for paper `lem:qld-4-7`. -/
theorem exists_actual_rounded_global_pair_error_bound (pointError : ℝ → ℝ)
    (hpoint : IsPolyErr pointError) (lineError : ℝ → ℝ → ℝ)
    (hline : IsPolyErr₂ lineError) (C a b : ℝ) (hC : 0 ≤ C)
    (ha : 1 ≤ a) (hb : 0 < b) (hb1 : b ≤ 1) :
    ∃ A B : ℝ, 1 < A ∧ 0 < B ∧ B < 1 ∧
      ∀ (P : AdmissibleParams) (epsilon : ℝ), 0 ≤ epsilon →
        let delta := deltaLd a b
          (directPassingErrorEnvelope
            (pointError epsilon + C * (P.m : ℝ) *
              lineError epsilon ((P.m * P.d : ℕ) / (P.q : ℝ)))
            ((P.m * P.d : ℕ) / (P.q : ℝ))) P.q (2 * P.m + 2) P.d 1
        let eta := delta + Real.sqrt (220 * delta ^ (1 / 4 : ℝ)) +
          2 * Real.sqrt (2 * delta)
        min 1 (8 * (4 * eta + 8 * pointError epsilon) +
          (((12 * P.m * P.d + 4 * P.d + 14 : ℕ) : ℝ) / P.q)) ≤
          deltaQld A B epsilon P.m P.d P.q := by
  obtain ⟨A, B, hA, hB, hB1, hbound⟩ :=
    exists_direct_global_pair_error_bound pointError hpoint lineError hline
      C a b 1 hC ha hb hb1 (by norm_num)
  refine ⟨1024 * A, B / 2 / 2 / 2, by linarith, by positivity, by linarith, ?_⟩
  intro P epsilon he delta eta
  let ratio : ℝ := ((P.m * P.d : ℕ) : ℝ) / P.q
  let passing := directPassingErrorEnvelope
    (pointError epsilon + C * (P.m : ℝ) * lineError epsilon ratio) ratio
  let slack := deltaLd a b (passing + epsilon) P.q (2 * P.m + 2) P.d 1
  let t := slack + Real.sqrt (pointError epsilon) + ratio
  have hr : 0 ≤ ratio := by dsimp [ratio]; positivity
  have hpass : 0 ≤ passing := by dsimp [passing, directPassingErrorEnvelope]; positivity
  have hp : 0 ≤ pointError epsilon := by
    obtain ⟨_, _, _, _, h⟩ := hpoint
    exact (h epsilon he).1
  have hs : 0 ≤ slack := by dsimp [slack, deltaLd]; positivity
  have hd : 0 ≤ delta := by dsimp [delta, deltaLd, directPassingErrorEnvelope]; positivity
  have hds : delta ≤ slack := by
    change deltaLd a b passing P.q (2 * P.m + 2) P.d 1 ≤ _
    dsimp [slack, deltaLd]
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    exact add_le_add (add_le_add
      (Real.rpow_le_rpow hpass (by linarith) hb.le) le_rfl) le_rfl
  have hdt : delta ≤ t := by dsimp [t]; linarith [Real.sqrt_nonneg (pointError epsilon)]
  have hpt : Real.sqrt (pointError epsilon) ≤ t := by dsimp [t]; linarith
  have hrt : ratio ≤ t := by dsimp [t]; linarith [Real.sqrt_nonneg (pointError epsilon)]
  have hratio : (((12 * P.m * P.d + 4 * P.d + 14 : ℕ) : ℝ) / P.q) ≤ 30 * ratio := by
    have hm : (1 : ℝ) ≤ P.m := by exact_mod_cast P.one_le_m
    have hd' : (1 : ℝ) ≤ P.d := by exact_mod_cast P.hd
    dsimp [ratio]
    rw [← mul_div_assoc]
    apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
    push_cast
    nlinarith
  have hcap : min 1 t ≤ deltaQld A B epsilon P.m P.d P.q := by
    simpa only [one_mul] using hbound P epsilon he
  have hroot := Real.sqrt_le_sqrt (Real.sqrt_le_sqrt (Real.sqrt_le_sqrt hcap))
  have hrootBound := (Real.sqrt_le_sqrt (Real.sqrt_le_sqrt
    (sqrt_deltaQld_le (P := P) hA.le he))).trans
      ((Real.sqrt_le_sqrt (sqrt_deltaQld_le (P := P) (b := B / 2) hA.le he)).trans
        (sqrt_deltaQld_le (P := P) (b := B / 2 / 2) hA.le he))
  refine (min_le_min_left 1 ?_).trans
    ((actual_rounding_error_le_root hd hp hdt hpt hrt).trans
      ((mul_le_mul_of_nonneg_left (hroot.trans hrootBound) (by norm_num)).trans
        (scale_deltaQld_le hA.le he (by norm_num : (1 : ℝ) ≤ 1024))))
  dsimp [eta]
  linarith

end MIPStarRE.QPBT
