import MIPStarRE.QPBT.Combining.ErrorBounds
import MIPStarRE.QPBT.Combining.PassingError
import MIPStarRE.QPBT.Combining.DirectLowDegree.Transport.Error

/-!
# Absorbing both errors of the directly indexed game

The conversion from combined measurements to a low-degree strategy has passing
error `3 * (sqrt (deltaQ + deltaL) + m * d / q)`. This module bounds its cap by
one while retaining the point error and the dimension factor in the line error.
It then absorbs low-degree soundness at that capped error into `deltaQld`.
These scalar estimates do not construct either measurement witness.

## References

* `references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1279-1288,1402`
* Blueprint `lem:qld-4-7`
* Issue #513
-/

namespace MIPStarRE.QPBT

/-- The capped passing error of the directly indexed game is bounded by the
dimension times a polynomial error. Both the point error `pointError error`
and the line error `C * dimension * lineError error ratio` are retained.
This is a scalar auxiliary for paper `lem:qld-4-7`, not an existence assertion
for the measurements used to construct that game. -/
theorem exists_direct_passing_polynomial_bound (pointError : ℝ → ℝ)
    (hpoint : IsPolyErr pointError) (lineError : ℝ → ℝ → ℝ)
    (hline : IsPolyErr₂ lineError) (C : ℝ) (hC : 0 ≤ C) :
    ∃ passingError : ℝ → ℝ → ℝ, IsPolyErr₂ passingError ∧
      ∀ error ratio dimension : ℝ, 0 ≤ error → 0 ≤ ratio → 1 ≤ dimension →
        min 1 (directPassingErrorEnvelope
          (pointError error + C * dimension * lineError error ratio) ratio) ≤
            dimension * passingError error ratio := by
  obtain ⟨A, p, hA, hp, hpoint⟩ := hpoint
  obtain ⟨B, r, s, hB, hr, hs, hline⟩ := hline
  let t := min p r
  let u := min s 2
  let K := A + C * B
  let D := 3 * (Real.sqrt K + 1) + 1
  have ht : 0 < t := lt_min hp hr
  have hu : 0 < u := lt_min hs (by norm_num)
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hD : 1 ≤ D := by dsimp [D]; nlinarith [Real.sqrt_nonneg K]
  refine ⟨fun error ratio => D * (error ^ (t / 2) + ratio ^ (u / 2)),
    ⟨D, t / 2, u / 2, hD, by positivity, by positivity, ?_⟩, ?_⟩
  · intro error ratio herror hratio
    exact ⟨by positivity, le_rfl⟩
  intro error ratio dimension herror hratio hdimension
  have hdim : 0 ≤ dimension := by linarith
  have he : 0 ≤ error ^ (t / 2) := Real.rpow_nonneg herror _
  have hy : 0 ≤ ratio ^ (u / 2) := Real.rpow_nonneg hratio _
  have hlarge (h : 1 ≤ error ^ (t / 2) + ratio ^ (u / 2)) :
      min 1 (directPassingErrorEnvelope
        (pointError error + C * dimension * lineError error ratio) ratio) ≤
          dimension * (D * (error ^ (t / 2) + ratio ^ (u / 2))) := by
    refine (min_le_left _ _).trans ?_
    exact one_le_mul_of_one_le_of_one_le hdimension
      (one_le_mul_of_one_le_of_one_le hD h)
  by_cases herrorOne : error ≤ 1
  · by_cases hratioOne : ratio ≤ 1
    · have hpointBound : pointError error ≤ A * error ^ t :=
        (hpoint error herror).2.trans (mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow_of_exponent_ge' herror herrorOne ht.le
            (min_le_left _ _)) (by linarith))
      have hlineBound : lineError error ratio ≤ B * (error ^ t + ratio ^ u) :=
        (hline error ratio herror hratio).2.trans (mul_le_mul_of_nonneg_left
          (add_le_add
            (Real.rpow_le_rpow_of_exponent_ge' herror herrorOne ht.le
              (min_le_right _ _))
            (Real.rpow_le_rpow_of_exponent_ge' hratio hratioOne hu.le
              (min_le_left _ _))) (by linarith))
      have heFull : 0 ≤ error ^ t := Real.rpow_nonneg herror _
      have hyFull : 0 ≤ ratio ^ u := Real.rpow_nonneg hratio _
      have hsum : pointError error + C * dimension * lineError error ratio ≤
          dimension * K * (error ^ t + ratio ^ u) := by
        have hpDim : A * error ^ t ≤ dimension * (A * error ^ t) :=
          le_mul_of_one_le_left (by positivity) hdimension
        have hlDim := mul_le_mul_of_nonneg_left hlineBound
          (mul_nonneg hC hdim)
        dsimp [K]
        nlinarith [mul_nonneg (mul_nonneg hdim (by linarith : 0 ≤ A)) hyFull]
      have heSq : (error ^ (t / 2)) ^ (2 : ℕ) = error ^ t := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul herror]
        congr 1
        ring
      have hySq : (ratio ^ (u / 2)) ^ (2 : ℕ) = ratio ^ u := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hratio]
        congr 1
        ring
      have hrootSum : Real.sqrt (error ^ t + ratio ^ u) ≤
          error ^ (t / 2) + ratio ^ (u / 2) := by
        apply (Real.sqrt_le_left (add_nonneg he hy)).mpr
        nlinarith [mul_nonneg he hy]
      have hrootDim : Real.sqrt dimension ≤ dimension := by
        apply (Real.sqrt_le_left hdim).mpr
        nlinarith
      have hroot : Real.sqrt
          (pointError error + C * dimension * lineError error ratio) ≤
          dimension * Real.sqrt K * (error ^ (t / 2) + ratio ^ (u / 2)) := by
        calc
          _ ≤ Real.sqrt (dimension * K * (error ^ t + ratio ^ u)) :=
            Real.sqrt_le_sqrt hsum
          _ = Real.sqrt dimension * Real.sqrt K *
              Real.sqrt (error ^ t + ratio ^ u) := by
            rw [Real.sqrt_mul (mul_nonneg hdim hK), Real.sqrt_mul hdim]
          _ ≤ _ := mul_le_mul
            (mul_le_mul_of_nonneg_right hrootDim (Real.sqrt_nonneg K)) hrootSum
            (Real.sqrt_nonneg _) (mul_nonneg hdim (Real.sqrt_nonneg K))
      have hratioSmall : ratio ≤ ratio ^ (u / 2) := by
        simpa using Real.rpow_le_rpow_of_exponent_ge' hratio hratioOne
          (by positivity : 0 ≤ u / 2) (by
            have : u ≤ 2 := min_le_right _ _
            linarith : u / 2 ≤ 1)
      have hratioDim : ratio ≤ dimension * ratio ^ (u / 2) :=
        hratioSmall.trans (le_mul_of_one_le_left hy hdimension)
      refine (min_le_right _ _).trans ?_
      dsimp [directPassingErrorEnvelope, D]
      nlinarith [mul_nonneg hdim he, mul_nonneg hdim hy]
    · exact hlarge (by
        have := Real.one_le_rpow (le_of_not_ge hratioOne) (by positivity : 0 ≤ u / 2)
        linarith)
  · exact hlarge (by
      have := Real.one_le_rpow (le_of_not_ge herrorOne) (by positivity : 0 ≤ t / 2)
      linarith)

/-- Low-degree soundness applied at the capped direct-game passing error has
the global polynomial-pair error form. The positive slack `error` permits a
soundness application even when the capped passing error is zero. The point
error occurs both in the passing error and in the subsequent square-root loss.

This auxiliary proves only the numerical substitution at paper `lem:qld-4-7`,
lines 1279--1288 and 1402. Constructing the strategy and the projective pair
measurement remains the obligation `exists_globalPairWitness`. -/
private theorem exists_capped_direct_global_pair_error_bound (pointError : ℝ → ℝ)
    (hpoint : IsPolyErr pointError) (lineError : ℝ → ℝ → ℝ)
    (hline : IsPolyErr₂ lineError)
    (C a b scale : ℝ) (hC : 0 ≤ C) (ha : 1 ≤ a)
    (hb : 0 < b) (hbOne : b ≤ 1) (hscale : 0 ≤ scale) :
    ∃ A B : ℝ, 1 < A ∧ 0 < B ∧ B < 1 ∧
      ∀ (P : AdmissibleParams) (error : ℝ), 0 ≤ error →
        min 1 (scale *
          (deltaLd a b
            (min 1 (directPassingErrorEnvelope
              (pointError error + C * (P.m : ℝ) *
                lineError error ((P.m * P.d : ℕ) / (P.q : ℝ)))
              ((P.m * P.d : ℕ) / (P.q : ℝ))) + error)
            P.q (2 * P.m + 2) P.d 1 + Real.sqrt (pointError error) +
              ((P.m * P.d : ℕ) / (P.q : ℝ)))) ≤
          deltaQld A B error P.m P.d P.q := by
  obtain ⟨passingError, hpassing, hbound⟩ :=
    exists_direct_passing_polynomial_bound pointError hpoint lineError hline C hC
  obtain ⟨A, B, hA, hB, hBOne, habs⟩ :=
    exists_global_pair_error_bound pointError hpoint passingError hpassing
      1 a b scale (by norm_num) ha hb hbOne hscale
  refine ⟨A, B, hA, hB, hBOne, ?_⟩
  intro P error herror
  have haNonneg : 0 ≤ a := by linarith
  have hratio : 0 ≤ ((P.m * P.d : ℕ) : ℝ) / (P.q : ℝ) := by positivity
  have hpassNonneg : 0 ≤ min 1 (directPassingErrorEnvelope
      (pointError error + C * (P.m : ℝ) *
        lineError error ((P.m * P.d : ℕ) / (P.q : ℝ)))
      ((P.m * P.d : ℕ) / (P.q : ℝ))) := by
    unfold directPassingErrorEnvelope
    positivity
  have hpass := hbound error _ (P.m : ℝ) herror hratio
    (by exact_mod_cast P.one_le_m)
  refine le_trans ?_ (habs P error herror)
  apply min_le_min_left
  apply mul_le_mul_of_nonneg_left _ hscale
  refine add_le_add (add_le_add ?_ le_rfl) le_rfl
  unfold deltaLd
  apply mul_le_mul_of_nonneg_left _
    (mul_nonneg haNonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _))
  refine add_le_add (add_le_add ?_ le_rfl) le_rfl
  apply Real.rpow_le_rpow (add_nonneg hpassNonneg herror) _ hb.le
  simpa only [one_mul] using add_le_add hpass (le_refl error)

/-- The full direct-game passing error, including both point and line errors,
can be substituted in low-degree soundness and absorbed into the error form of
paper `lem:qld-4-7`. The universal constants are chosen before the admissible
parameters and the nonnegative test error. Only the final consistency error is
capped; the input to `deltaLd` is the actual passing envelope, with slack.

This is numerical support for paper lines 1279--1288 and 1402. It constructs no
line witness, global polynomial measurement, or projective pair measurement. -/
theorem exists_direct_global_pair_error_bound (pointError : ℝ → ℝ)
    (hpoint : IsPolyErr pointError) (lineError : ℝ → ℝ → ℝ)
    (hline : IsPolyErr₂ lineError)
    (C a b scale : ℝ) (hC : 0 ≤ C) (ha : 1 ≤ a)
    (hb : 0 < b) (hbOne : b ≤ 1) (hscale : 0 ≤ scale) :
    ∃ A B : ℝ, 1 < A ∧ 0 < B ∧ B < 1 ∧
      ∀ (P : AdmissibleParams) (error : ℝ), 0 ≤ error →
        min 1 (scale *
          (deltaLd a b
            (directPassingErrorEnvelope
              (pointError error + C * (P.m : ℝ) *
                lineError error ((P.m * P.d : ℕ) / (P.q : ℝ)))
              ((P.m * P.d : ℕ) / (P.q : ℝ)) + error)
            P.q (2 * P.m + 2) P.d 1 + Real.sqrt (pointError error) +
              ((P.m * P.d : ℕ) / (P.q : ℝ)))) ≤
          deltaQld A B error P.m P.d P.q := by
  obtain ⟨A, B, hA, hB, hBOne, habs⟩ :=
    exists_capped_direct_global_pair_error_bound pointError hpoint lineError hline
      C a b (scale + 1) hC ha hb hbOne (by linarith)
  refine ⟨A, B, hA, hB, hBOne, ?_⟩
  intro P error herror
  have haNonneg : 0 ≤ a := by linarith
  let ratio : ℝ := ((P.m * P.d : ℕ) : ℝ) / (P.q : ℝ)
  let passing := directPassingErrorEnvelope
    (pointError error + C * (P.m : ℝ) * lineError error ratio) ratio
  have hratio : 0 ≤ ratio := by dsimp [ratio]; positivity
  have hpassing : 0 ≤ passing := by dsimp [passing, directPassingErrorEnvelope]; positivity
  have hbound := habs P error herror
  change min 1 ((scale + 1) *
    (deltaLd a b (min 1 passing + error) P.q (2 * P.m + 2) P.d 1 +
      Real.sqrt (pointError error) + ratio)) ≤ _ at hbound
  change min 1 (scale *
    (deltaLd a b (passing + error) P.q (2 * P.m + 2) P.d 1 +
      Real.sqrt (pointError error) + ratio)) ≤ _
  by_cases hsmall : passing ≤ 1
  · rw [min_eq_right hsmall] at hbound
    refine le_trans (min_le_min_left 1 ?_) hbound
    apply mul_le_mul_of_nonneg_right (by linarith)
    unfold deltaLd
    exact add_nonneg (add_nonneg
      (mul_nonneg (mul_nonneg haNonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _))
        (add_nonneg (add_nonneg (Real.rpow_nonneg (add_nonneg hpassing herror) _)
          (Real.rpow_nonneg (Nat.cast_nonneg _) _))
          (Real.rpow_nonneg (by norm_num) _))) (Real.sqrt_nonneg _)) hratio
  · rw [min_eq_left (le_of_not_ge hsmall)] at hbound
    have hld : 1 ≤ deltaLd a b (1 + error) P.q (2 * P.m + 2) P.d 1 :=
      one_le_deltaLd_of_one_le_error ha hb.le (by linarith) (by omega) P.hd le_rfl
    have hsum : 1 ≤ deltaLd a b (1 + error) P.q (2 * P.m + 2) P.d 1 +
        Real.sqrt (pointError error) + ratio := by
      linarith [Real.sqrt_nonneg (pointError error)]
    rw [min_eq_left (one_le_mul_of_one_le_of_one_le (by linarith) hsum)] at hbound
    exact (min_le_left _ _).trans hbound

end MIPStarRE.QPBT
