import MIPStarRE.QPBT.Test.SoundnessDefs

/-!
# Scalar absorption of the Naimark transfer constants

Transferring the Pauli operator distances from a Naimark dilation back to the
original spaces produces bounds of the shape `3 * δ + 6 * δ ^ 2`, where `δ` is
the Pauli soundness error `deltaQld`. This module records the purely scalar
fact that such a combination is again a Pauli soundness error, after enlarging
the universal prefactor. No strategy, measurement, or state content enters
here; the module only depends on `MIPStarRE.QPBT.Test.SoundnessDefs`.

## References

Blueprint `lem:delta-qld-scalar-absorption-support`. The source performs the
same constant bookkeeping inline when it records the error form of
`thm:pauli` at
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1862-1876`.
The companion constant adjustments are `deltaQld_mono`
(`MIPStarRE/QPBT/Test/SoundnessDefs.lean`) and `sqrt_deltaQld_le`
(`MIPStarRE/QPBT/Combining/RootErrorBounds.lean`).
-/

namespace MIPStarRE.QPBT

/-- The Pauli soundness error is nonnegative whenever its prefactor and its
error argument are. The remaining two summands of the error bracket are
`rpow`s of nonnegative bases, so no admissibility hypothesis is needed. -/
theorem deltaQld_nonneg {P : AdmissibleParams} {a b epsilon : ℝ}
    (ha : 0 ≤ a) (hepsilon : 0 ≤ epsilon) :
    0 ≤ deltaQld a b epsilon P.m P.d P.q := by
  have hdegree0 : (0 : ℝ) ≤ ((P.m * P.d : ℕ) : ℝ) := Nat.cast_nonneg _
  have h1 := Real.rpow_nonneg hepsilon b
  have h2 := Real.rpow_nonneg (Nat.cast_nonneg P.q) (-b)
  have h3 := Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 2)
    (-(b * ((P.m * P.d : ℕ) : ℝ)))
  unfold deltaQld
  simp only [Real.rpow_eq_pow]
  exact mul_nonneg (mul_nonneg ha (Real.rpow_nonneg hdegree0 a)) (by linarith)

/-- The shape of the absorption once the error bracket has been separated:
doubling the `rpow` exponent is dominated by raising it to `21 * a ^ 2`. -/
private theorem rpow_absorb_aux {degree tail a : ℝ}
    (hdegree : 1 ≤ degree) (htail : 0 ≤ tail) (ha : 1 ≤ a) :
    21 * (a * degree ^ a) * (a * degree ^ a * tail) ≤
      21 * a ^ 2 * degree ^ (21 * a ^ 2) * tail := by
  have hdegree0 : (0 : ℝ) < degree := lt_of_lt_of_le zero_lt_one hdegree
  have hexp : a + a ≤ 21 * a ^ 2 := by nlinarith
  have hsplit : degree ^ (a + a) = degree ^ a * degree ^ a :=
    Real.rpow_add hdegree0 a a
  have hpow : degree ^ (a + a) ≤ degree ^ (21 * a ^ 2) :=
    Real.rpow_le_rpow_of_exponent_le hdegree hexp
  have hcoeff : (0 : ℝ) ≤ 21 * a ^ 2 := by positivity
  calc 21 * (a * degree ^ a) * (a * degree ^ a * tail)
      = 21 * a ^ 2 * (degree ^ a * degree ^ a) * tail := by ring
    _ = 21 * a ^ 2 * degree ^ (a + a) * tail := by rw [hsplit]
    _ ≤ 21 * a ^ 2 * degree ^ (21 * a ^ 2) * tail :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hpow hcoeff) htail

/-- **Scalar absorption.** On the source parameter domain the combination
`3 * δ + 6 * δ ^ 2` of the Pauli soundness error `δ = deltaQld a b ε m d q` is
again a Pauli soundness error, with the universal prefactor enlarged from `a`
to `21 * a ^ 2` and the exponent `b` unchanged.

This is the arithmetic step that returns the Naimark operator-transfer bound
`3 * dilatedDistance + 6 * stateError ^ 2` to the source error form. It is a
Lean-only constant-bookkeeping helper, not an additional hypothesis of
`thm:pauli`: the source absorbs the same universal constants inline at
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1862-1876`.
It is stated as blueprint `lem:delta-qld-scalar-absorption-support`. -/
theorem three_add_six_sq_deltaQld_le {P : AdmissibleParams} {a b epsilon : ℝ}
    (ha : 1 ≤ a) (hb : 0 < b) (hepsilon : 0 ≤ epsilon) (hepsilon1 : epsilon ≤ 1) :
    3 * deltaQld a b epsilon P.m P.d P.q +
        6 * deltaQld a b epsilon P.m P.d P.q ^ 2 ≤
      deltaQld (21 * a ^ 2) b epsilon P.m P.d P.q := by
  have hdegree : (1 : ℝ) ≤ ((P.m * P.d : ℕ) : ℝ) :=
    Nat.one_le_cast.mpr (Nat.mul_pos P.one_le_m P.hd)
  have hdegree0 : (0 : ℝ) ≤ ((P.m * P.d : ℕ) : ℝ) := zero_le_one.trans hdegree
  have hq : (1 : ℝ) ≤ (P.q : ℝ) := by
    obtain ⟨k, -, hk⟩ := P.hq
    rw [hk]
    exact_mod_cast Nat.one_le_pow _ _ (by norm_num)
  have ha0 : (0 : ℝ) ≤ a := zero_le_one.trans ha
  have hprefactor : (1 : ℝ) ≤ a * ((P.m * P.d : ℕ) : ℝ) ^ a :=
    one_le_mul_of_one_le_of_one_le ha (Real.one_le_rpow hdegree ha0)
  have hprefactor0 : (0 : ℝ) ≤ a * ((P.m * P.d : ℕ) : ℝ) ^ a :=
    zero_le_one.trans hprefactor
  -- The error bracket lies in `[0, 3]`: each summand is an `rpow` bounded by
  -- one on the source parameter domain.
  have htail0 : (0 : ℝ) ≤ epsilon ^ b + (P.q : ℝ) ^ (-b) +
      (2 : ℝ) ^ (-(b * ((P.m * P.d : ℕ) : ℝ))) := by
    have h1 := Real.rpow_nonneg hepsilon b
    have h2 := Real.rpow_nonneg (Nat.cast_nonneg P.q) (-b)
    have h3 := Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 2)
      (-(b * ((P.m * P.d : ℕ) : ℝ)))
    linarith
  have htail3 : epsilon ^ b + (P.q : ℝ) ^ (-b) +
      (2 : ℝ) ^ (-(b * ((P.m * P.d : ℕ) : ℝ))) ≤ 3 := by
    have h1 : epsilon ^ b ≤ 1 := Real.rpow_le_one hepsilon hepsilon1 hb.le
    have h2 : (P.q : ℝ) ^ (-b) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos hq (neg_nonpos.mpr hb.le)
    have h3 : (2 : ℝ) ^ (-(b * ((P.m * P.d : ℕ) : ℝ))) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos (by norm_num)
        (neg_nonpos.mpr (mul_nonneg hb.le hdegree0))
    linarith
  have hnonneg : 0 ≤ deltaQld a b epsilon P.m P.d P.q :=
    deltaQld_nonneg ha0 hepsilon
  have hub : deltaQld a b epsilon P.m P.d P.q ≤
      3 * (a * ((P.m * P.d : ℕ) : ℝ) ^ a) := by
    unfold deltaQld
    simp only [Real.rpow_eq_pow]
    nlinarith [mul_nonneg hprefactor0 (sub_nonneg.mpr htail3)]
  calc 3 * deltaQld a b epsilon P.m P.d P.q +
        6 * deltaQld a b epsilon P.m P.d P.q ^ 2
      ≤ 21 * (a * ((P.m * P.d : ℕ) : ℝ) ^ a) *
          deltaQld a b epsilon P.m P.d P.q := by
        nlinarith [mul_nonneg hnonneg (sub_nonneg.mpr hub),
          mul_nonneg hnonneg (sub_nonneg.mpr hprefactor)]
    _ ≤ deltaQld (21 * a ^ 2) b epsilon P.m P.d P.q := by
        unfold deltaQld
        simp only [Real.rpow_eq_pow]
        exact rpow_absorb_aux hdegree htail0 ha

end MIPStarRE.QPBT
