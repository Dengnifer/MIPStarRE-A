import MIPStarRE.QPBT.Test.SoundnessDefs

/-!
# Square roots of the Pauli soundness error

The state-extraction estimate bounds a squared norm. Taking its square root
preserves the Pauli soundness error family after halving the exponent.

## References

Blueprint `rem:pauli-robustness-form`; the source states the squared bound at
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1868-1876`,
whereas `thm:pauli` bounds the unsquared norm.
-/

namespace MIPStarRE.QPBT

/-- Taking the square root of the Pauli error is bounded by halving its
exponent. This formalization-only scalar estimate supports the passage from
the squared extraction bound to the norm bound in blueprint
`rem:pauli-robustness-form`; it is stated as `thm:pauli-error-square-root-support`.
It holds for all nonnegative errors. -/
theorem sqrt_deltaQld_le {P : AdmissibleParams} {a b epsilon : ℝ}
    (ha : 1 ≤ a) (hepsilon : 0 ≤ epsilon) :
    Real.sqrt (deltaQld a b epsilon P.m P.d P.q) ≤
      deltaQld a (b / 2) epsilon P.m P.d P.q := by
  let degree : ℝ := ((P.m * P.d : ℕ) : ℝ)
  have hdegree : 1 ≤ degree :=
    Nat.one_le_cast.mpr (Nat.mul_pos P.one_le_m P.hd)
  have ha0 : 0 ≤ a := zero_le_one.trans ha
  have hdegree0 : 0 ≤ degree := zero_le_one.trans hdegree
  have hprefactor : 1 ≤ a * degree ^ a :=
    one_le_mul_of_one_le_of_one_le ha (Real.one_le_rpow hdegree ha0)
  have hq : (0 : ℝ) ≤ P.q := Nat.cast_nonneg _
  have htwo : (0 : ℝ) ≤ 2 := by norm_num
  have hroot_sum {x y z : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 ≤ z) :
      (x + y + z) ^ (1 / 2 : ℝ) ≤
        x ^ (1 / 2 : ℝ) + y ^ (1 / 2 : ℝ) + z ^ (1 / 2 : ℝ) :=
    (Real.rpow_add_le_add_rpow (add_nonneg hx hy) hz (by norm_num) (by norm_num)).trans
      (add_le_add (Real.rpow_add_le_add_rpow hx hy (by norm_num) (by norm_num)) le_rfl)
  have hrate :
      (epsilon ^ b + (P.q : ℝ) ^ (-b) + (2 : ℝ) ^ (-(b * degree))) ^ (1 / 2 : ℝ) ≤
        epsilon ^ (b / 2) + (P.q : ℝ) ^ (-(b / 2)) +
          (2 : ℝ) ^ (-((b / 2) * degree)) := by
    have h := hroot_sum (Real.rpow_nonneg hepsilon b) (Real.rpow_nonneg hq (-b))
      (Real.rpow_nonneg htwo (-(b * degree)))
    rw [← Real.rpow_mul hepsilon, ← Real.rpow_mul hq, ← Real.rpow_mul htwo] at h
    simpa only [div_eq_mul_inv, one_mul, neg_mul, mul_assoc, mul_comm, mul_left_comm] using h
  unfold deltaQld
  simp only [Real.rpow_eq_pow, Real.sqrt_eq_rpow]
  change (a * degree ^ a *
      (epsilon ^ b + (P.q : ℝ) ^ (-b) + (2 : ℝ) ^ (-(b * degree)))) ^ (1 / 2 : ℝ) ≤ _
  rw [Real.mul_rpow (zero_le_one.trans hprefactor) (by positivity)]
  exact mul_le_mul
    (Real.rpow_le_self_of_one_le hprefactor (by norm_num)) hrate
    (by positivity) (zero_le_one.trans hprefactor)

end MIPStarRE.QPBT
