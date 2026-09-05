import MIPStarRE.QPBT.Test.SoundnessDefs

/-!
# Canonical Pauli basis test parameters

This file defines the canonical admissible parameter tuple as a function of
the target register size and states its quantitative soundness estimate.

## References

The definitions and estimate correspond to `def:introparams` and
`lem:delta-bound` in
`blueprint/src/chapter/ch13_qpbt_test.tex:546-567`, from
`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:1503-1562`.
-/

namespace MIPStarRE.QPBT

noncomputable section

/-- The admissibility predicate for a parameter tuple `(q, m, d)`. -/
def IsAdmissibleTuple (t : ℕ × ℕ × ℕ) : Prop :=
  IsAdmissibleSize t.1 ∧ 1 ≤ t.2.1 ∧ 1 ≤ t.2.2 ∧ t.2.1 ∣ t.1

/-- Convert an admissible tuple to the parameter structure used by the
Pauli basis game. -/
def AdmissibleParams.ofTuple (t : ℕ × ℕ × ℕ)
    (h : IsAdmissibleTuple t) : AdmissibleParams where
  q := t.1
  m := t.2.1
  d := t.2.2
  hd := h.2.2.1
  hq := h.1
  hdvd := h.2.2.2

/-- The smallest even natural number represented by the ceiling prescription
in `def:introparams`. -/
noncomputable def introParamsC (a b : ℝ) : ℕ :=
  2 * ⌈(b + a) / (2 * b)⌉₊

/-- The canonical `(q, m, d)` tuple of `def:introparams`. -/
def introParamsTuple (c R : ℕ) : ℕ × ℕ × ℕ :=
  (2 ^ (c * Nat.clog 2 (Nat.clog 2 R) + 1),
    2 ^ Nat.log 2 (c * Nat.clog 2 R + 1), 1)

/-- Formalization-only auxiliary: a numerical comparison of the two exponents
appearing in the canonical tuple.  If `s` is positive and `r` is at most
`2 ^ s`, then the base-two logarithm of `c * r + 1` does not exceed
`c * s + 1`. -/
private theorem log_two_le_mul_add_one (c r s : ℕ) (hs : 1 ≤ s)
    (hrs : r ≤ 2 ^ s) : Nat.log 2 (c * r + 1) ≤ c * s + 1 := by
  have hkey : c * r + 1 ≤ 2 ^ (c * s + 1) := by
    rcases Nat.eq_zero_or_pos c with hc | hc
    · subst hc
      simp
    · obtain ⟨d, rfl⟩ : ∃ d, c = d + 1 := ⟨c - 1, by omega⟩
      have h1 : d + 1 ≤ 2 ^ d := Nat.lt_two_pow_self
      have h2 : (d + 1) * r ≤ 2 ^ d * 2 ^ s := Nat.mul_le_mul h1 hrs
      have h3 : 1 ≤ 2 ^ d * 2 ^ s := by
        have hp : 0 < 2 ^ d * 2 ^ s := by positivity
        omega
      have h4 : 2 ^ (d + 1 + s) = 2 ^ d * 2 ^ s + 2 ^ d * 2 ^ s := by
        rw [pow_add, pow_succ]
        ring
      have h5 : d + 1 + s ≤ (d + 1) * s + 1 := by
        have hds : d ≤ d * s := by
          simpa using Nat.mul_le_mul (le_refl d) hs
        have hexp : (d + 1) * s = d * s + s := by ring
        omega
      calc (d + 1) * r + 1 ≤ 2 ^ d * 2 ^ s + 2 ^ d * 2 ^ s :=
            Nat.add_le_add h2 h3
        _ = 2 ^ (d + 1 + s) := h4.symm
        _ ≤ 2 ^ ((d + 1) * s + 1) := Nat.pow_le_pow_right (by norm_num) h5
  calc Nat.log 2 (c * r + 1) ≤ Nat.log 2 (2 ^ (c * s + 1)) :=
        Nat.log_mono_right hkey
    _ = c * s + 1 := Nat.log_pow (by norm_num) _

/-- The canonical tuple is admissible. This is the numerical
admissibility part of `lem:delta-bound`, blueprint
`ch13_qpbt_test.tex:559-567`, paper
`08_classical_and_quantum_low_degree_tests.tex:1520-1562`. -/
theorem introParamsTuple_isAdmissible (a b : ℝ) (R : ℕ) (hR : 4 ≤ R) :
    IsAdmissibleTuple (introParamsTuple (introParamsC a b) R) := by
  have hEven : Even (introParamsC a b) := ⟨⌈(b + a) / (2 * b)⌉₊, two_mul _⟩
  have hpow : Nat.clog 2 (2 ^ 2) ≤ Nat.clog 2 R :=
    Nat.clog_mono_right 2 (by simpa using hR)
  have hr2 : 2 ≤ Nat.clog 2 R := by
    rwa [Nat.clog_pow 2 2 (by norm_num)] at hpow
  have hs1 : 1 ≤ Nat.clog 2 (Nat.clog 2 R) := Nat.clog_pos (by norm_num) hr2
  have hrs : Nat.clog 2 R ≤ 2 ^ Nat.clog 2 (Nat.clog 2 R) :=
    Nat.le_pow_clog (by norm_num) _
  exact ⟨⟨introParamsC a b * Nat.clog 2 (Nat.clog 2 R) + 1,
      (hEven.mul_right _).add_one, rfl⟩,
    Nat.one_le_pow _ _ (by norm_num), le_rfl,
    pow_dvd_pow 2 (log_two_le_mul_add_one _ _ _ hs1 hrs)⟩

/-- The canonical admissible parameter structure of `def:introparams`,
blueprint `ch13_qpbt_test.tex:546-557`, paper
`08_classical_and_quantum_low_degree_tests.tex:1503-1514`. -/
noncomputable def introParams (a b : ℝ) (R : ℕ) (hR : 4 ≤ R) :
    AdmissibleParams :=
  AdmissibleParams.ofTuple _ (introParamsTuple_isAdmissible a b R hR)

/-- The canonical parameter dimension supplies at least `R` encoded
coordinates, as asserted in `lem:delta-bound`. -/
theorem le_two_pow_introParams_m (a b : ℝ) (ha : 1 ≤ a) (hb : 0 < b)
    (R : ℕ) (hR : 4 ≤ R) :
    R ≤ 2 ^ (introParams a b R hR).m := by
  have hc2 : 2 ≤ introParamsC a b := by
    have hceil : 0 < ⌈(b + a) / (2 * b)⌉₊ :=
      Nat.ceil_pos.mpr (div_pos (by linarith) (by linarith))
    show 2 ≤ 2 * ⌈(b + a) / (2 * b)⌉₊
    omega
  have hlt : introParamsC a b * Nat.clog 2 R + 1 <
      2 ^ Nat.log 2 (introParamsC a b * Nat.clog 2 R + 1) * 2 := by
    simpa [pow_succ] using
      Nat.lt_pow_succ_log_self (b := 2) (by norm_num)
        (introParamsC a b * Nat.clog 2 R + 1)
  have hmul : 2 * Nat.clog 2 R ≤ introParamsC a b * Nat.clog 2 R :=
    Nat.mul_le_mul hc2 (le_refl _)
  have key : Nat.clog 2 R ≤
      2 ^ Nat.log 2 (introParamsC a b * Nat.clog 2 R + 1) := by
    omega
  calc R ≤ 2 ^ Nat.clog 2 R := Nat.le_pow_clog (by norm_num) R
    _ ≤ 2 ^ (2 ^ Nat.log 2 (introParamsC a b * Nat.clog 2 R + 1)) :=
        Nat.pow_le_pow_right (by norm_num) key
    _ = 2 ^ (introParams a b R hR).m := rfl

/-- `lem:delta-bound`: the Pauli soundness error at the canonical parameters
has polylogarithmic dependence on `R`. Blueprint
`ch13_qpbt_test.tex:559-567`, paper
`08_classical_and_quantum_low_degree_tests.tex:1520-1562`.

The explicit nonnegativity premise records the failure-probability domain
inherited from `thm:pauli`; fractional powers of a negative real do not express
the source's error parameter.

**Local fix:** The third error term is bounded directly using the lower bound
on `m`, rather than the source's false intermediate comparison between the
field exponent and `m`. This discrepancy is documented in issue #16 and
`docs/paper-gaps/qpbt_delta-bound-exponent-comparison.tex`; see also
`rem:delta-bound-exponent-comparison`. -/
theorem exists_deltaQld_introParams_bound (a b : ℝ) (ha : 1 ≤ a)
    (hb : 0 < b) (hb' : b < 1) :
    ∃ a' b' : ℝ, 1 ≤ a' ∧ 0 < b' ∧ b' ≤ 1 ∧
      ∀ (R : ℕ) (hR : 4 ≤ R) (ε : ℝ),
        0 ≤ ε → deltaQld a b ε (introParams a b R hR).m
            (introParams a b R hR).d (introParams a b R hR).q ≤
          a' * (Real.rpow (Real.logb 2 R) a' * Real.rpow ε b' +
            Real.rpow (Real.logb 2 R) (-b')) := by
  sorry

end

end MIPStarRE.QPBT
