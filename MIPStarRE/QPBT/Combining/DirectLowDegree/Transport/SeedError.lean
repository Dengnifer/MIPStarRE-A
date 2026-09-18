import MIPStarRE.QPBT.Combining.DirectLowDegree.Transport.Error

/-!
# Error absorption for seed compression

The recovery of global polynomial consistency after seed compression costs a
square root of the direct soundness error. Halving its exponent preserves the
error function of blueprint `lem:ld-soundness`.

## References

* `references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:413-458`
-/

namespace MIPStarRE.QPBT

/-- The square-root loss from seed compression is absorbed by enlarging the
universal prefactor and halving the error exponent in `lem:ld-soundness`. -/
theorem ten_sqrt_deltaLd_le (D : DirectLdParams) {a b ε : ℝ}
    (ha : 1 ≤ a) (hε : 0 ≤ ε) :
    10 * Real.sqrt (deltaLd a b ε D.q D.m D.d D.k) ≤
      deltaLd (10 * a) (b / 2) ε D.q D.m D.d D.k := by
  let N : ℝ := (D.d * D.m * D.k : ℕ)
  have hN : 1 ≤ N := by
    change (1 : ℝ) ≤ ((D.d * D.m * D.k : ℕ) : ℝ)
    exact_mod_cast (show 1 ≤ D.d * D.m * D.k from
      Nat.mul_pos (Nat.mul_pos D.hd D.hm) D.hk)
  have hNa : 1 ≤ N ^ a := Real.one_le_rpow hN (by linarith)
  have hP : 1 ≤ a * N ^ a := by nlinarith
  have hP0 : 0 ≤ a * N ^ a := by linarith
  have hsP : Real.sqrt (a * N ^ a) ≤ a * N ^ a :=
    Real.sqrt_le_self_iff.mpr (Or.inr hP)
  have hs (x r : ℝ) (hx : 0 ≤ x) : Real.sqrt (x ^ r) = x ^ (r / 2) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hx]
    congr 1
    ring
  have hx : 0 ≤ (ε ^ b : ℝ) := Real.rpow_nonneg hε _
  have hy : 0 ≤ ((D.q : ℝ) ^ (-b)) := Real.rpow_nonneg (by positivity) _
  have hz : 0 ≤ (2 : ℝ) ^ (-(b * (D.m * D.d : ℕ))) :=
    Real.rpow_nonneg (by norm_num) _
  have hsum : Real.sqrt (ε ^ b + (D.q : ℝ) ^ (-b) +
      (2 : ℝ) ^ (-(b * (D.m * D.d : ℕ)))) ≤
      ε ^ (b / 2) + (D.q : ℝ) ^ (-(b / 2)) +
        (2 : ℝ) ^ (-((b / 2) * (D.m * D.d : ℕ))) := by
    calc
      _ ≤ Real.sqrt (ε ^ b) + Real.sqrt ((D.q : ℝ) ^ (-b)) +
          Real.sqrt ((2 : ℝ) ^ (-(b * (D.m * D.d : ℕ)))) :=
        MIPStarRE.LDT.sqrt_add3_le_add3_sqrt hx hy hz
      _ = _ := by
        rw [hs ε b hε, hs (D.q : ℝ) (-b) (by positivity),
          hs 2 (-(b * (D.m * D.d : ℕ))) (by norm_num)]
        congr 2 <;> congr 1 <;> ring
  have hmono : a * N ^ a ≤ a * N ^ (10 * a) := by
    apply mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le hN (by linarith)) (by linarith)
  unfold deltaLd
  simp only [Real.rpow_eq_pow]
  change 10 * Real.sqrt (a * N ^ a * _) ≤ 10 * a * N ^ (10 * a) * _
  rw [Real.sqrt_mul hP0]
  have hbound := mul_le_mul (hsP.trans hmono) hsum (Real.sqrt_nonneg _)
    (by positivity : 0 ≤ a * N ^ (10 * a))
  nlinarith

/-- For errors at most one, `deltaLd` dominates the rejection probability and
the polynomial collision probability needed after seed compression. -/
theorem error_and_collision_le_deltaLd (D : DirectLdParams) {a b ε : ℝ}
    (ha : 1 ≤ a) (hb : b ≤ 1) (hε : 0 < ε) (hε1 : ε ≤ 1) :
    ε ≤ deltaLd a b ε D.q D.m D.d D.k ∧
      (D.m : ℝ) * D.d / D.q ≤ deltaLd a b ε D.q D.m D.d D.k := by
  let N : ℝ := (D.d * D.m * D.k : ℕ)
  have hN : 1 ≤ N := by
    change (1 : ℝ) ≤ ((D.d * D.m * D.k : ℕ) : ℝ)
    exact_mod_cast (show 1 ≤ D.d * D.m * D.k from
      Nat.mul_pos (Nat.mul_pos D.hd D.hm) D.hk)
  have hNa : N ≤ N ^ a := by
    simpa using Real.rpow_le_rpow_of_exponent_le hN ha
  have hP : N ≤ a * N ^ a := hNa.trans
    (le_mul_of_one_le_left (by positivity) ha)
  have hmd : (D.m : ℝ) * D.d ≤ N := by
    dsimp [N]
    push_cast
    nlinarith [le_mul_of_one_le_right (by positivity : 0 ≤ (D.d : ℝ) * D.m)
      (show (1 : ℝ) ≤ D.k by exact_mod_cast D.hk)]
  have he : ε ≤ ε ^ b := by
    simpa using Real.rpow_le_rpow_of_exponent_ge hε hε1 hb
  have hq1 : (1 : ℝ) ≤ D.q := by exact_mod_cast D.toLDTParameters.hq
  have hq : (D.q : ℝ)⁻¹ ≤ (D.q : ℝ) ^ (-b) := by
    simpa only [Real.rpow_neg_one] using
      Real.rpow_le_rpow_of_exponent_le hq1 (neg_le_neg hb)
  have hx : 0 ≤ (ε ^ b : ℝ) := Real.rpow_nonneg hε.le _
  have hy : 0 ≤ ((D.q : ℝ) ^ (-b)) := Real.rpow_nonneg (by positivity) _
  have hz : 0 ≤ (2 : ℝ) ^ (-(b * (D.m * D.d : ℕ))) :=
    Real.rpow_nonneg (by norm_num) _
  unfold deltaLd
  simp only [Real.rpow_eq_pow]
  change ε ≤ a * N ^ a * _ ∧ (D.m : ℝ) * D.d / D.q ≤ a * N ^ a * _
  constructor
  · nlinarith [mul_nonneg (sub_nonneg.mpr (hN.trans hP)) hx,
      mul_nonneg (by linarith : 0 ≤ a * N ^ a) (add_nonneg hy hz)]
  · have hprod := mul_le_mul (hmd.trans hP) hq (by positivity)
      (by linarith : 0 ≤ a * N ^ a)
    rw [div_eq_mul_inv]
    nlinarith [mul_nonneg (by linarith : 0 ≤ a * N ^ a) (add_nonneg hx hz)]

end MIPStarRE.QPBT
