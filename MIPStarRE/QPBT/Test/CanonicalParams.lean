import MIPStarRE.LDT.Basic.RpowBounds
import MIPStarRE.QPBT.Test.SoundnessDefs

/-!
# Canonical Pauli basis test parameters

This file defines the canonical admissible parameter tuple as a function of
the target register size and states its quantitative soundness estimate.

## References

The definitions and estimate correspond to `def:introparams` and
`lem:delta-bound` in
`blueprint/src/chapter/ch13_qpbt_test.tex`, from
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

/-- Formalization-only auxiliary: for `R ≥ 4` the base-two ceiling logarithm
of `R` is at least `2`.  This is the lower bound on `⌈log R⌉` used throughout
the analysis of the canonical tuple of `def:introparams`. -/
private theorem two_le_clog_two (R : ℕ) (hR : 4 ≤ R) : 2 ≤ Nat.clog 2 R := by
  have hpow : Nat.clog 2 (2 ^ 2) ≤ Nat.clog 2 R :=
    Nat.clog_mono_right 2 (by simpa using hR)
  rwa [Nat.clog_pow 2 2 (by norm_num)] at hpow

/-- The canonical tuple is admissible. This is the numerical
admissibility part of `lem:delta-bound`, blueprint
`ch13_qpbt_test.tex`, paper
`08_classical_and_quantum_low_degree_tests.tex:1520-1562`. -/
theorem introParamsTuple_isAdmissible (a b : ℝ) (R : ℕ) (hR : 4 ≤ R) :
    IsAdmissibleTuple (introParamsTuple (introParamsC a b) R) := by
  have hEven : Even (introParamsC a b) := ⟨⌈(b + a) / (2 * b)⌉₊, two_mul _⟩
  have hr2 : 2 ≤ Nat.clog 2 R := two_le_clog_two R hR
  have hs1 : 1 ≤ Nat.clog 2 (Nat.clog 2 R) := Nat.clog_pos (by norm_num) hr2
  have hrs : Nat.clog 2 R ≤ 2 ^ Nat.clog 2 (Nat.clog 2 R) :=
    Nat.le_pow_clog (by norm_num) _
  exact ⟨⟨introParamsC a b * Nat.clog 2 (Nat.clog 2 R) + 1,
      (hEven.mul_right _).add_one, rfl⟩,
    Nat.one_le_pow _ _ (by norm_num), le_rfl,
    pow_dvd_pow 2 (log_two_le_mul_add_one _ _ _ hs1 hrs)⟩

/-- The canonical admissible parameter structure of `def:introparams`,
blueprint `ch13_qpbt_test.tex`, paper
`08_classical_and_quantum_low_degree_tests.tex:1503-1514`. -/
noncomputable def introParams (a b : ℝ) (R : ℕ) (hR : 4 ≤ R) :
    AdmissibleParams :=
  AdmissibleParams.ofTuple _ (introParamsTuple_isAdmissible a b R hR)

/-- Formalization-only auxiliary: the canonical even integer `c` of
`def:introparams` is at least `2`, since `(b + a) / b > 1` for `a ≥ 1` and
`b > 0`. -/
private theorem two_le_introParamsC (a b : ℝ) (ha : 1 ≤ a) (hb : 0 < b) :
    2 ≤ introParamsC a b := by
  have hceil : 0 < ⌈(b + a) / (2 * b)⌉₊ :=
    Nat.ceil_pos.mpr (div_pos (by linarith) (by linarith))
  change 2 ≤ 2 * ⌈(b + a) / (2 * b)⌉₊
  omega

/-- The canonical parameter dimension supplies at least `R` encoded
coordinates, as asserted in `lem:delta-bound`. -/
theorem le_two_pow_introParams_m (a b : ℝ) (ha : 1 ≤ a) (hb : 0 < b)
    (R : ℕ) (hR : 4 ≤ R) :
    R ≤ 2 ^ (introParams a b R hR).m := by
  have hc2 : 2 ≤ introParamsC a b := two_le_introParamsC a b ha hb
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

/-- Formalization-only auxiliary: the defining inequality `c ≥ (b + a) / b` of
the canonical even integer of `def:introparams`, in the form `a + b ≤ c b`
used in the proof of `lem:delta-bound`. -/
private theorem add_le_introParamsC_mul (a b : ℝ) (hb : 0 < b) :
    a + b ≤ (introParamsC a b : ℝ) * b := by
  have hceil := Nat.le_ceil ((b + a) / (2 * b))
  have hb2 : (0 : ℝ) < 2 * b := by linarith
  calc a + b = (b + a) / (2 * b) * (2 * b) := by
        rw [div_mul_cancel₀ _ hb2.ne', add_comm]
    _ ≤ (⌈(b + a) / (2 * b)⌉₊ : ℝ) * (2 * b) :=
        mul_le_mul_of_nonneg_right hceil hb2.le
    _ = (introParamsC a b : ℝ) * b := by
        unfold introParamsC
        push_cast
        ring

/-- `lem:delta-bound`: the Pauli soundness error at the canonical parameters
has polylogarithmic dependence on `R`. Blueprint
`ch13_qpbt_test.tex`, paper
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
  have ha0 : 0 ≤ a := by linarith
  set c := introParamsC a b
  set C : ℝ := (Nat.factorial ⌈a + b⌉₊ : ℝ) / (b * Real.log 2) ^ ⌈a + b⌉₊
  have hc2 : (2 : ℝ) ≤ c := by exact_mod_cast two_le_introParamsC a b ha hb
  have hcb : a + b ≤ (c : ℝ) * b := add_le_introParamsC_mul a b hb
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hC0 : 0 ≤ C := by positivity
  have h2c : (1 : ℝ) ≤ (2 * (c : ℝ)) ^ a := Real.one_le_rpow (by linarith) ha0
  have haa' : a ≤ a * ((2 * (c : ℝ)) ^ a + C) := by nlinarith
  refine ⟨a * ((2 * (c : ℝ)) ^ a + C), b, by linarith, hb, hb'.le, ?_⟩
  intro R hR ε hε
  -- The canonical parameters, unfolded.
  have hm_def : (introParams a b R hR).m =
      2 ^ Nat.log 2 (c * Nat.clog 2 R + 1) := rfl
  have hq_def : (introParams a b R hR).q =
      2 ^ (c * Nat.clog 2 (Nat.clog 2 R) + 1) := rfl
  have hd_def : (introParams a b R hR).d = 1 := rfl
  unfold deltaQld
  rw [hm_def, hq_def, hd_def, Nat.mul_one]
  simp only [Real.rpow_eq_pow]
  -- Integer bounds on the canonical parameters.
  have hR0 : (0 : ℝ) < R := by exact_mod_cast (by omega : 0 < R)
  have hR4 : (4 : ℝ) ≤ (R : ℝ) := by exact_mod_cast hR
  have hn2 : 2 ≤ Nat.clog 2 R := two_le_clog_two R hR
  have hpred : 2 ^ (Nat.clog 2 R - 1) < R :=
    Nat.pow_pred_clog_lt_self (by norm_num) (by omega)
  have hRn : R ≤ 2 ^ Nat.clog 2 R := Nat.le_pow_clog (by norm_num) R
  have hm_up : 2 ^ Nat.log 2 (c * Nat.clog 2 R + 1) ≤ c * Nat.clog 2 R + 1 :=
    Nat.pow_log_le_self 2 (by omega)
  have hm_lo : c * Nat.clog 2 R + 1 <
      2 * 2 ^ Nat.log 2 (c * Nat.clog 2 R + 1) := by
    have h := Nat.lt_pow_succ_log_self (b := 2) (by norm_num)
      (c * Nat.clog 2 R + 1)
    rw [pow_succ] at h
    linarith
  have hq_nat : Nat.clog 2 R ^ c ≤ 2 ^ (c * Nat.clog 2 (Nat.clog 2 R) + 1) := by
    calc Nat.clog 2 R ^ c ≤ (2 ^ Nat.clog 2 (Nat.clog 2 R)) ^ c :=
          Nat.pow_le_pow_left (Nat.le_pow_clog (by norm_num) _) c
      _ = 2 ^ (c * Nat.clog 2 (Nat.clog 2 R)) := by rw [← pow_mul, mul_comm]
      _ ≤ 2 ^ (c * Nat.clog 2 (Nat.clog 2 R) + 1) :=
          Nat.pow_le_pow_right (by norm_num) (Nat.le_succ _)
  set n := Nat.clog 2 R
  set m := 2 ^ Nat.log 2 (c * n + 1) with hm
  set q := 2 ^ (c * Nat.clog 2 n + 1)
  set L := Real.logb 2 (R : ℝ) with hL
  -- Real bounds: `2 ≤ L ≤ m ≤ 2 c L` and `L ^ c ≤ q`.
  have hrpow2 : (2 : ℝ) ^ (2 : ℝ) = 4 := by
    rw [Real.rpow_two]
    norm_num
  have hL2 : (2 : ℝ) ≤ L := by
    rw [hL, Real.le_logb_iff_rpow_le (by norm_num) hR0, hrpow2]
    exact hR4
  have hL0 : 0 ≤ L := by linarith
  have hL1 : 1 ≤ L := by linarith
  have hLpos : 0 < L := by linarith
  have hLn : L ≤ n := by
    rw [hL, Real.logb_le_iff_le_rpow (by norm_num) hR0, Real.rpow_natCast]
    exact_mod_cast hRn
  have hnL : (n : ℝ) ≤ L + 1 := by
    have h1 : ((n - 1 : ℕ) : ℝ) ≤ L := by
      rw [hL, Real.le_logb_iff_rpow_le (by norm_num) hR0, Real.rpow_natCast]
      exact_mod_cast hpred.le
    have h2 : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by
      rw [Nat.cast_sub (by omega), Nat.cast_one]
    linarith
  have hm1 : (1 : ℝ) ≤ m := by
    rw [hm]
    exact_mod_cast Nat.one_le_pow _ _ (by norm_num)
  have hm0 : (0 : ℝ) ≤ m := by linarith
  have hmpos : (0 : ℝ) < m := by linarith
  have hm_up' : (m : ℝ) ≤ c * n + 1 := by exact_mod_cast hm_up
  have hm_lo' : (c : ℝ) * n + 1 < 2 * m := by exact_mod_cast hm_lo
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hcn : (2 : ℝ) * n ≤ c * n := mul_le_mul_of_nonneg_right hc2 hn0
  have hLm : L ≤ m := by linarith
  have hm2cL : (m : ℝ) ≤ 2 * c * L := by
    have h1 : (c : ℝ) * n ≤ c * (L + 1) :=
      mul_le_mul_of_nonneg_left hnL (by linarith)
    have h2 : (c : ℝ) * 2 ≤ c * L := mul_le_mul_of_nonneg_left hL2 (by linarith)
    linarith
  have hma : (m : ℝ) ^ a ≤ (2 * (c : ℝ)) ^ a * L ^ a := by
    rw [← Real.mul_rpow (by linarith) hL0]
    exact Real.rpow_le_rpow hm0 hm2cL ha0
  have hq_lo : L ^ c ≤ (q : ℝ) := by
    calc L ^ c ≤ (n : ℝ) ^ c := pow_le_pow_left₀ hL0 hLn c
      _ ≤ (q : ℝ) := by exact_mod_cast hq_nat
  -- The three summands of the soundness function.
  have hq2 : (q : ℝ) ^ (-b) ≤ L ^ (-(a + b)) := by
    calc (q : ℝ) ^ (-b) ≤ (L ^ c) ^ (-b) :=
          Real.rpow_le_rpow_of_nonpos (by positivity) hq_lo (by linarith)
      _ = L ^ ((c : ℝ) * (-b)) := by rw [Real.rpow_mul hL0, Real.rpow_natCast]
      _ ≤ L ^ (-(a + b)) := Real.rpow_le_rpow_of_exponent_le hL1 (by linarith)
  have hLa : L ^ a ≤ L ^ (a * ((2 * (c : ℝ)) ^ a + C)) :=
    Real.rpow_le_rpow_of_exponent_le hL1 haa'
  have hεb : 0 ≤ ε ^ b := Real.rpow_nonneg hε _
  have hT1 : a * (m : ℝ) ^ a * ε ^ b ≤
      a * ((2 * (c : ℝ)) ^ a + C) *
        (L ^ (a * ((2 * (c : ℝ)) ^ a + C)) * ε ^ b) := by
    have h1 : (m : ℝ) ^ a ≤
        ((2 * (c : ℝ)) ^ a + C) * L ^ (a * ((2 * (c : ℝ)) ^ a + C)) := by
      calc (m : ℝ) ^ a ≤ (2 * (c : ℝ)) ^ a * L ^ a := hma
        _ ≤ (2 * (c : ℝ)) ^ a * L ^ (a * ((2 * (c : ℝ)) ^ a + C)) :=
            mul_le_mul_of_nonneg_left hLa (by positivity)
        _ ≤ ((2 * (c : ℝ)) ^ a + C) * L ^ (a * ((2 * (c : ℝ)) ^ a + C)) :=
            mul_le_mul_of_nonneg_right (by linarith) (by positivity)
    calc a * (m : ℝ) ^ a * ε ^ b
        ≤ a * (((2 * (c : ℝ)) ^ a + C) * L ^ (a * ((2 * (c : ℝ)) ^ a + C))) *
            ε ^ b :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h1 ha0) hεb
      _ = _ := by ring
  have hT2 : a * (m : ℝ) ^ a * (q : ℝ) ^ (-b) ≤
      a * (2 * (c : ℝ)) ^ a * L ^ (-b) := by
    have hLL : L ^ a * L ^ (-(a + b)) = L ^ (-b) := by
      rw [← Real.rpow_add hLpos]
      congr 1
      ring
    calc a * (m : ℝ) ^ a * (q : ℝ) ^ (-b)
        ≤ a * ((2 * (c : ℝ)) ^ a * L ^ a) * L ^ (-(a + b)) :=
          mul_le_mul (mul_le_mul_of_nonneg_left hma ha0) hq2
            (Real.rpow_nonneg (Nat.cast_nonneg q) _) (by positivity)
      _ = a * (2 * (c : ℝ)) ^ a * (L ^ a * L ^ (-(a + b))) := by ring
      _ = a * (2 * (c : ℝ)) ^ a * L ^ (-b) := by rw [hLL]
  have hT3 : a * (m : ℝ) ^ a * (2 : ℝ) ^ (-(b * m)) ≤ a * C * L ^ (-b) := by
    have hsplit : (m : ℝ) ^ a = (m : ℝ) ^ (a + b) * (m : ℝ) ^ (-b) := by
      rw [← Real.rpow_add hmpos]
      congr 1
      ring
    have h1 : (m : ℝ) ^ (a + b) * (2 : ℝ) ^ (-(b * m)) ≤ C :=
      MIPStarRE.LDT.rpow_mul_two_rpow_neg_le hb hm1
    have h2 : (m : ℝ) ^ (-b) ≤ L ^ (-b) :=
      Real.rpow_le_rpow_of_nonpos hLpos hLm (by linarith)
    calc a * (m : ℝ) ^ a * (2 : ℝ) ^ (-(b * m))
        = a * (((m : ℝ) ^ (a + b) * (2 : ℝ) ^ (-(b * m))) * (m : ℝ) ^ (-b)) := by
          rw [hsplit]
          ring
      _ ≤ a * (C * L ^ (-b)) :=
          mul_le_mul_of_nonneg_left
            (mul_le_mul h1 h2 (Real.rpow_nonneg hm0 _) hC0) ha0
      _ = a * C * L ^ (-b) := by ring
  calc a * (m : ℝ) ^ a * (ε ^ b + (q : ℝ) ^ (-b) + (2 : ℝ) ^ (-(b * m)))
      = a * (m : ℝ) ^ a * ε ^ b + a * (m : ℝ) ^ a * (q : ℝ) ^ (-b) +
          a * (m : ℝ) ^ a * (2 : ℝ) ^ (-(b * m)) := by ring
    _ ≤ a * ((2 * (c : ℝ)) ^ a + C) *
          (L ^ (a * ((2 * (c : ℝ)) ^ a + C)) * ε ^ b) +
        a * (2 * (c : ℝ)) ^ a * L ^ (-b) + a * C * L ^ (-b) :=
        add_le_add (add_le_add hT1 hT2) hT3
    _ = a * ((2 * (c : ℝ)) ^ a + C) *
          (L ^ (a * ((2 * (c : ℝ)) ^ a + C)) * ε ^ b + L ^ (-b)) := by ring

end

end MIPStarRE.QPBT
