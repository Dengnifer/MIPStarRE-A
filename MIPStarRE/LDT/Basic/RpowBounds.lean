import MIPStarRE.LDT.Basic.ParametersBase

/-!
# A real power against exponential decay

A small reusable envelope bound: a fixed real power of `x` is dominated by an
exponential in `x`, with an explicit constant depending only on the exponent
and on the decay rate.
-/

namespace MIPStarRE.LDT

/-- Formalization-only auxiliary: a fixed real power is dominated by an
exponential.  For `x ≥ 1` and `t > 0`, the product `x ^ s * 2 ^ (-t x)` is at
most `⌈s⌉! / (t log 2) ^ ⌈s⌉`, a constant depending only on `s` and `t`.

Taking `x = m`, `s = a + b` and `t = b`, this bounds the third term in the
proof of `lem:delta-bound` (blueprint node `lem:delta-bound-envelope-support`)
by an explicit constant.  It is obtained from the Taylor lower bound
`y ^ n / n! ≤ exp y` on the exponential. -/
theorem rpow_mul_two_rpow_neg_le {s t x : ℝ} (ht : 0 < t) (hx : 1 ≤ x) :
    x ^ s * (2 : ℝ) ^ (-(t * x)) ≤
      (Nat.factorial ⌈s⌉₊ : ℝ) / (t * Real.log 2) ^ ⌈s⌉₊ := by
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hK : 0 < (t * Real.log 2) ^ ⌈s⌉₊ := by positivity
  have hE : 0 < Real.exp (Real.log 2 * (t * x)) := Real.exp_pos _
  have hxs : x ^ s ≤ x ^ ⌈s⌉₊ := by
    rw [← Real.rpow_natCast]
    exact Real.rpow_le_rpow_of_exponent_le hx (Nat.le_ceil s)
  have hexp : (t * Real.log 2) ^ ⌈s⌉₊ * x ^ ⌈s⌉₊ ≤
      (Nat.factorial ⌈s⌉₊ : ℝ) * Real.exp (Real.log 2 * (t * x)) := by
    have h := Real.pow_div_factorial_le_exp (x := Real.log 2 * (t * x))
      (mul_nonneg hlog.le (mul_nonneg ht.le (by linarith))) ⌈s⌉₊
    rw [div_le_iff₀ (by positivity)] at h
    calc (t * Real.log 2) ^ ⌈s⌉₊ * x ^ ⌈s⌉₊
        = (Real.log 2 * (t * x)) ^ ⌈s⌉₊ := by ring
      _ ≤ _ := le_of_le_of_eq h (mul_comm _ _)
  rw [Real.rpow_neg (show (0 : ℝ) ≤ 2 by norm_num),
    Real.rpow_def_of_pos (show (0 : ℝ) < 2 by norm_num), le_div_iff₀ hK]
  calc x ^ s * (Real.exp (Real.log 2 * (t * x)))⁻¹ * (t * Real.log 2) ^ ⌈s⌉₊
      ≤ x ^ ⌈s⌉₊ * (Real.exp (Real.log 2 * (t * x)))⁻¹ *
          (t * Real.log 2) ^ ⌈s⌉₊ := by
        gcongr
    _ = (t * Real.log 2) ^ ⌈s⌉₊ * x ^ ⌈s⌉₊ *
          (Real.exp (Real.log 2 * (t * x)))⁻¹ := by ring
    _ ≤ (Nat.factorial ⌈s⌉₊ : ℝ) * Real.exp (Real.log 2 * (t * x)) *
          (Real.exp (Real.log 2 * (t * x)))⁻¹ :=
        mul_le_mul_of_nonneg_right hexp (inv_nonneg.mpr hE.le)
    _ = Nat.factorial ⌈s⌉₊ := mul_inv_cancel_right₀ hE.ne' _

end MIPStarRE.LDT
