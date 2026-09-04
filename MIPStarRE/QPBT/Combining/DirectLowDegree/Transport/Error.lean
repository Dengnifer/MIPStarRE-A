import MIPStarRE.QPBT.Combining.DirectLowDegree.Game
import MIPStarRE.QPBT.Combining.DirectLowDegree.Transport.Correspondence
import MIPStarRE.QPBT.Games.DistanceTheorems.Support
import MIPStarRE.LDT.Test.MainTheorem.ScalarBounds.EnvelopeBounds

/-!
# The scalar error of the low-degree soundness transport

This module supplies the scalar half of the soundness transport for the
directly indexed low-degree game.  Its content is purely arithmetic: the
auxiliary sampling parameter with which the mature low individual degree
theorem is applied to a coordinate strategy, the resulting bounds on the three
terms of the mature error `mainFormalError`, and the absorption of the
simultaneous-measurement estimate into the error function `deltaLd` of
`lem:ld-soundness`.

## Main definitions

* `directLdAuxParameter D = 2560000 m³ d` is the sampling parameter handed to
  `MIPStarRE.LDT.Test.mainFormal`.  It is the multiple of the exponential scale
  `2560000 m²` of `mainFormalError` with quotient `m d`, so that the
  exponential term of the mature error is exactly `exp (-m d)`.

## Main results

* `directLdAuxParameter_pos` and `four_hundred_mul_le_directLdAuxParameter` are
  the two hypotheses `0 < k` and `400 m d ≤ k` of `mainFormal`, proved from the
  positivity of the dimension and of the degree alone.
* `directLd_test_term_le`, `directLd_field_term_le` and
  `directLd_exponential_term_le` bound the three terms of
  `mainFormalError D.toLDTParameters (directLdAuxParameter D) (3 ε)`: the test
  term by `3 ε^(1/40000)`, the field term by `d q^(-1/40000)`, and the
  exponential term by `2^(-b m d)` for every `0 ≤ b ≤ 1`.
* `exists_directLdTransportConstants` exhibits, for a sandwich constant
  `C₀ ≥ 1`, the explicit universal constants `a = 2500000000 C₀` and
  `b = 1/80000` for which `C₀ k √(mainFormalError + m d / q + ε)` is at most
  `deltaLd a b ε q m d k` in the regime `0 < ε ≤ 1`.
* `one_le_deltaLd_of_one_le_error` and
  `one_le_deltaLd_of_fieldSize_le_degree` bound `deltaLd` below by one in the
  two degenerate regimes `1 ≤ ε` and `q ≤ d`, and
  `consistencyDefect_heteroKron_le_one` bounds every bipartite consistency
  defect on a unit state above by one.  Together they close both degenerate
  regimes, where the conclusion of `lem:ld-soundness` carries no information.

The exponent `b = 1/80000` is half the exponent `1/40000` carried by
`mainFormalError`; the halving is exactly what the square root of the
simultaneous-measurement estimate costs.

## References

* `references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:413-458`
* `blueprint/src/chapter/ch13_qpbt_test.tex:139-167`
* `MIPStarRE/LDT/Test/MainTheorem/MainFormal.lean:288-327`
* `MIPStarRE/LDT/Test/MainTheorem/ScalarBounds/Definitions.lean:28-36`
* `references/ldt-paper/test_definition.tex:180-202`
* `docs/paper-gaps/qpbt_ld-dimension-divisibility.tex`
-/

open scoped BigOperators MatrixOrder Matrix ComplexOrder

namespace MIPStarRE.QPBT

open MIPStarRE.LDT MIPStarRE.Quantum

/-! ## The auxiliary sampling parameter -/

/-- The auxiliary sampling parameter of the low-degree soundness transport.

The mature low individual degree theorem is applied to each coordinate
strategy of a directly indexed strategy with `k = 2560000 m³ d` samples.  This
is the multiple of the exponential scale `2560000 m²` of `mainFormalError`
whose quotient is `m d`, and it dominates the corrected large-sampling
hypothesis `400 m d ≤ k` of `MIPStarRE.LDT.Test.mainFormal` uniformly in the
parameters.  Blueprint `ch13_qpbt_test.tex:139-167`; paper
`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:413-458`. -/
def directLdAuxParameter (D : DirectLdParams) : ℕ := 2560000 * D.m ^ 3 * D.d

/-- The auxiliary sampling parameter is positive, which is the boundary
hypothesis `0 < k` of `MIPStarRE.LDT.Test.mainFormal`. -/
theorem directLdAuxParameter_pos (D : DirectLdParams) : 0 < directLdAuxParameter D := by
  have hm : 0 < D.m := D.hm
  have hd : 0 < D.d := D.hd
  have hpow : 0 < D.m ^ 3 := pow_pos hm 3
  exact Nat.mul_pos (Nat.mul_pos (by norm_num) hpow) hd

/-- The auxiliary sampling parameter satisfies the corrected large-sampling
hypothesis `400 m d ≤ k` of `MIPStarRE.LDT.Test.mainFormal`, documented in
`docs/paper-gaps/issue-906-main-formal-k-bound.tex`. -/
theorem four_hundred_mul_le_directLdAuxParameter (D : DirectLdParams) :
    400 * D.toLDTParameters.m * D.toLDTParameters.d ≤ directLdAuxParameter D := by
  have hcube : D.m ≤ D.m ^ 3 := Nat.le_self_pow (by norm_num) D.m
  change 400 * D.m * D.d ≤ 2560000 * D.m ^ 3 * D.d
  exact Nat.mul_le_mul (Nat.mul_le_mul (by norm_num) hcube) le_rfl

/-! ## Elementary positivity of the parameters

The four lemmas below are formalization-only conveniences: they record the
positivity fields of `DirectLdParams` in the real numbers, where all the
scalar estimates of this module take place. -/

private theorem directLd_one_le_m (D : DirectLdParams) : (1 : ℝ) ≤ (D.m : ℝ) := by
  have h : 1 ≤ D.m := D.hm
  exact_mod_cast h

private theorem directLd_one_le_d (D : DirectLdParams) : (1 : ℝ) ≤ (D.d : ℝ) := by
  have h : 1 ≤ D.d := D.hd
  exact_mod_cast h

private theorem directLd_one_le_k (D : DirectLdParams) : (1 : ℝ) ≤ (D.k : ℝ) := by
  have h : 1 ≤ D.k := D.hk
  exact_mod_cast h

private theorem directLd_one_le_q (D : DirectLdParams) : (1 : ℝ) ≤ (D.q : ℝ) := by
  have h : 1 ≤ D.q := D.toLDTParameters.hq
  exact_mod_cast h

/-! ## The three terms of the mature error -/

/-- With the auxiliary sampling parameter the exponential scale of
`mainFormalError` collapses: the argument of its exponential term is exactly
`m d`.

Formalization-only scalar identity for the error function displayed in
`MIPStarRE/LDT/Test/MainTheorem/ScalarBounds/Definitions.lean:28-36`. -/
theorem directLdAuxParameter_exp_arg (D : DirectLdParams) :
    (directLdAuxParameter D : ℝ) / (2560000 * ((D.m : ℝ) ^ (2 : ℕ))) =
      (D.m : ℝ) * (D.d : ℝ) := by
  have hm : (0 : ℝ) < (D.m : ℝ) := lt_of_lt_of_le zero_lt_one (directLd_one_le_m D)
  have hpow : (0 : ℝ) < (D.m : ℝ) ^ (2 : ℕ) := pow_pos hm 2
  have hne : (2560000 : ℝ) * ((D.m : ℝ) ^ (2 : ℕ)) ≠ 0 :=
    ne_of_gt (mul_pos (by norm_num) hpow)
  unfold directLdAuxParameter
  push_cast
  rw [div_eq_iff hne]
  ring

/-- The test term of `mainFormalError` at the incoming error `3 ε`, bounded by
the constant `3` times `ε^(1/40000)`.

Formalization-only scalar bound on the first term of the error function
displayed in `MIPStarRE/LDT/Test/MainTheorem/ScalarBounds/Definitions.lean:28-36`,
used for the error of `lem:ld-soundness`, blueprint
`ch13_qpbt_test.tex:139-167`. -/
theorem directLd_test_term_le {ε : ℝ} (hε : 0 ≤ ε) :
    Real.rpow (3 * ε) (1 / 40000) ≤ 3 * Real.rpow ε (1 / 40000) := by
  simp only [Real.rpow_eq_pow]
  rw [Real.mul_rpow (by norm_num) hε]
  have h3 : (3 : ℝ) ^ ((1 : ℝ) / 40000) ≤ 3 := by
    calc (3 : ℝ) ^ ((1 : ℝ) / 40000) ≤ (3 : ℝ) ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
      _ = 3 := Real.rpow_one 3
  exact mul_le_mul_of_nonneg_right h3 (Real.rpow_nonneg hε _)

/-- The field term of `mainFormalError`, bounded by the polynomial `d` times
`q^(-1/40000)`.

Formalization-only scalar bound on the second term of the error function
displayed in `MIPStarRE/LDT/Test/MainTheorem/ScalarBounds/Definitions.lean:28-36`,
used for the error of `lem:ld-soundness`, blueprint
`ch13_qpbt_test.tex:139-167`. -/
theorem directLd_field_term_le (D : DirectLdParams) :
    Real.rpow ((D.d : ℝ) / (D.q : ℝ)) (1 / 40000) ≤
      (D.d : ℝ) * Real.rpow (D.q : ℝ) (-(1 / 40000)) := by
  have hd1 := directLd_one_le_d D
  have hq1 := directLd_one_le_q D
  simp only [Real.rpow_eq_pow]
  rw [Real.div_rpow (by linarith) (by linarith), div_eq_mul_inv,
    ← Real.rpow_neg (by linarith : (0 : ℝ) ≤ (D.q : ℝ))]
  have hd : (D.d : ℝ) ^ ((1 : ℝ) / 40000) ≤ (D.d : ℝ) := by
    calc (D.d : ℝ) ^ ((1 : ℝ) / 40000) ≤ (D.d : ℝ) ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le hd1 (by norm_num)
      _ = (D.d : ℝ) := Real.rpow_one _
  exact mul_le_mul_of_nonneg_right hd (Real.rpow_nonneg (by linarith) _)

/-- The exponential term of `mainFormalError` at the auxiliary sampling
parameter is `exp (-m d)`, hence at most `2^(-b m d)` for every exponent
`0 ≤ b ≤ 1`.

Formalization-only scalar bound on the third term of the error function
displayed in `MIPStarRE/LDT/Test/MainTheorem/ScalarBounds/Definitions.lean:28-36`;
the exponential of `deltaLd` is the base-two decay of `lem:ld-soundness`,
blueprint `ch13_qpbt_test.tex:139-167`. -/
theorem directLd_exponential_term_le (D : DirectLdParams) {b : ℝ}
    (hb0 : 0 ≤ b) (hb1 : b ≤ 1) :
    Real.exp (-((directLdAuxParameter D : ℝ) / (2560000 * ((D.m : ℝ) ^ (2 : ℕ))))) ≤
      Real.rpow 2 (-(b * ((D.m * D.d : ℕ) : ℝ))) := by
  have hlog : Real.log 2 ≤ 1 := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    linarith
  have hlog0 : (0 : ℝ) ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hmd : (0 : ℝ) ≤ (D.m : ℝ) * (D.d : ℝ) := by positivity
  have hcast : ((D.m * D.d : ℕ) : ℝ) = (D.m : ℝ) * (D.d : ℝ) := by push_cast; ring
  rw [directLdAuxParameter_exp_arg D, hcast]
  simp only [Real.rpow_eq_pow]
  rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2)]
  apply Real.exp_le_exp.mpr
  nlinarith [mul_le_mul_of_nonneg_right hlog hmd,
    mul_le_mul_of_nonneg_right hb1 hmd, mul_nonneg hlog0 hb0]

/-! ## The transport envelope

The three scalar quantities `ε^b`, `q^(-b)` and `2^(-b m d)` at the transport
exponent `b = 1/80000` are the inner factor of `deltaLd`; the abbreviation
below names their sum. -/

/-- The inner factor of `deltaLd` at the transport exponent `b = 1/80000`.
This is a formalization-only abbreviation. -/
private noncomputable def transportEnvelope (D : DirectLdParams) (ε : ℝ) : ℝ :=
  Real.rpow ε (1 / 80000) + Real.rpow (D.q : ℝ) (-(1 / 80000)) +
    Real.rpow 2 (-((1 / 80000) * ((D.m * D.d : ℕ) : ℝ)))

private theorem transportEnvelope_rpow_eps_le (D : DirectLdParams) (ε : ℝ) :
    Real.rpow ε (1 / 80000) ≤ transportEnvelope D ε := by
  have hy : (0 : ℝ) ≤ Real.rpow (D.q : ℝ) (-(1 / 80000)) :=
    Real.rpow_nonneg (by positivity) _
  have hz : (0 : ℝ) ≤ Real.rpow 2 (-((1 / 80000) * ((D.m * D.d : ℕ) : ℝ))) :=
    Real.rpow_nonneg (by norm_num) _
  unfold transportEnvelope
  linarith

private theorem transportEnvelope_rpow_q_le (D : DirectLdParams) {ε : ℝ} (hε : 0 ≤ ε) :
    Real.rpow (D.q : ℝ) (-(1 / 80000)) ≤ transportEnvelope D ε := by
  have hx : (0 : ℝ) ≤ Real.rpow ε (1 / 80000) := Real.rpow_nonneg hε _
  have hz : (0 : ℝ) ≤ Real.rpow 2 (-((1 / 80000) * ((D.m * D.d : ℕ) : ℝ))) :=
    Real.rpow_nonneg (by norm_num) _
  unfold transportEnvelope
  linarith

private theorem transportEnvelope_nonneg (D : DirectLdParams) {ε : ℝ} (hε : 0 ≤ ε) :
    0 ≤ transportEnvelope D ε := by
  have hx : (0 : ℝ) ≤ Real.rpow ε (1 / 80000) := Real.rpow_nonneg hε _
  exact le_trans hx (transportEnvelope_rpow_eps_le D ε)

/-! ## The mature error at the auxiliary sampling parameter -/

/-- The mature error at the auxiliary sampling parameter, written out in the
parameters of the directly indexed game. -/
private theorem mainFormalError_direct_eq (D : DirectLdParams) (ε : ℝ) :
    Test.mainFormalError D.toLDTParameters (directLdAuxParameter D) (3 * ε) =
      100000 * ((directLdAuxParameter D : ℝ) ^ (2 : ℕ)) * ((D.m : ℝ) ^ (4 : ℕ)) *
        (Real.rpow (3 * ε) (1 / 40000) +
          Real.rpow ((D.d : ℝ) / (D.q : ℝ)) (1 / 40000) +
          Real.exp (-((directLdAuxParameter D : ℝ) /
            (2560000 * ((D.m : ℝ) ^ (2 : ℕ)))))) := rfl

private theorem directLdEnvelope_nonneg (D : DirectLdParams) {ε : ℝ} (hε : 0 ≤ ε) :
    0 ≤ Real.rpow (3 * ε) (1 / 40000) +
      Real.rpow ((D.d : ℝ) / (D.q : ℝ)) (1 / 40000) +
      Real.exp (-((directLdAuxParameter D : ℝ) / (2560000 * ((D.m : ℝ) ^ (2 : ℕ))))) := by
  have h1 : (0 : ℝ) ≤ Real.rpow (3 * ε) (1 / 40000) := Real.rpow_nonneg (by linarith) _
  have h2 : (0 : ℝ) ≤ Real.rpow ((D.d : ℝ) / (D.q : ℝ)) (1 / 40000) :=
    Real.rpow_nonneg (by positivity) _
  have h3 : (0 : ℝ) ≤
      Real.exp (-((directLdAuxParameter D : ℝ) / (2560000 * ((D.m : ℝ) ^ (2 : ℕ))))) :=
    (Real.exp_pos _).le
  linarith

private theorem mainFormalError_direct_nonneg (D : DirectLdParams) {ε : ℝ} (hε : 0 ≤ ε) :
    0 ≤ Test.mainFormalError D.toLDTParameters (directLdAuxParameter D) (3 * ε) := by
  rw [mainFormalError_direct_eq]
  exact mul_nonneg (by positivity) (directLdEnvelope_nonneg D hε)

/-- The square root of the polynomial prefactor of the mature error at the
auxiliary sampling parameter. -/
private theorem sqrt_directLdPrefactor_le (D : DirectLdParams) :
    Real.sqrt (100000 * ((directLdAuxParameter D : ℝ) ^ (2 : ℕ)) * ((D.m : ℝ) ^ (4 : ℕ))) ≤
      820000000 * (D.m : ℝ) ^ (5 : ℕ) * (D.d : ℝ) := by
  have hm1 := directLd_one_le_m D
  have hd1 := directLd_one_le_d D
  have hK : (directLdAuxParameter D : ℝ) = 2560000 * (D.m : ℝ) ^ (3 : ℕ) * (D.d : ℝ) := by
    unfold directLdAuxParameter
    push_cast
    ring
  have hX : (0 : ℝ) ≤ (D.m : ℝ) ^ (10 : ℕ) * (D.d : ℝ) ^ (2 : ℕ) := by positivity
  have hC : (0 : ℝ) ≤ 820000000 * (D.m : ℝ) ^ (5 : ℕ) * (D.d : ℝ) := by positivity
  have hlhs : 100000 * ((directLdAuxParameter D : ℝ) ^ (2 : ℕ)) * ((D.m : ℝ) ^ (4 : ℕ)) =
      655360000000000000 * ((D.m : ℝ) ^ (10 : ℕ) * (D.d : ℝ) ^ (2 : ℕ)) := by
    rw [hK]; ring
  have hrhs : (820000000 * (D.m : ℝ) ^ (5 : ℕ) * (D.d : ℝ)) ^ (2 : ℕ) =
      672400000000000000 * ((D.m : ℝ) ^ (10 : ℕ) * (D.d : ℝ) ^ (2 : ℕ)) := by ring
  calc Real.sqrt (100000 * ((directLdAuxParameter D : ℝ) ^ (2 : ℕ)) * ((D.m : ℝ) ^ (4 : ℕ)))
      ≤ Real.sqrt ((820000000 * (D.m : ℝ) ^ (5 : ℕ) * (D.d : ℝ)) ^ (2 : ℕ)) := by
        apply Real.sqrt_le_sqrt
        rw [hlhs, hrhs]
        exact mul_le_mul_of_nonneg_right (by norm_num) hX
    _ = 820000000 * (D.m : ℝ) ^ (5 : ℕ) * (D.d : ℝ) := Real.sqrt_sq hC

/-- Halving the exponents: the square root of the mature envelope at the
auxiliary sampling parameter is at most `3 d` times the transport envelope. -/
private theorem sqrt_directLdEnvelope_le (D : DirectLdParams) {ε : ℝ} (hε0 : 0 < ε) :
    Real.sqrt (Real.rpow (3 * ε) (1 / 40000) +
        Real.rpow ((D.d : ℝ) / (D.q : ℝ)) (1 / 40000) +
        Real.exp (-((directLdAuxParameter D : ℝ) / (2560000 * ((D.m : ℝ) ^ (2 : ℕ)))))) ≤
      3 * (D.d : ℝ) * transportEnvelope D ε := by
  have hd1 := directLd_one_le_d D
  have hq1 := directLd_one_le_q D
  have h1n : (0 : ℝ) ≤ Real.rpow (3 * ε) (1 / 40000) := Real.rpow_nonneg (by linarith) _
  have h2n : (0 : ℝ) ≤ Real.rpow ((D.d : ℝ) / (D.q : ℝ)) (1 / 40000) :=
    Real.rpow_nonneg (by positivity) _
  have h3n : (0 : ℝ) ≤
      Real.exp (-((directLdAuxParameter D : ℝ) / (2560000 * ((D.m : ℝ) ^ (2 : ℕ))))) :=
    (Real.exp_pos _).le
  have hb1 : Real.sqrt (Real.rpow (3 * ε) (1 / 40000)) ≤ 3 * Real.rpow ε (1 / 80000) := by
    have e : Real.sqrt (Real.rpow (3 * ε) (1 / 40000)) = Real.rpow (3 * ε) (1 / 80000) := by
      rw [Test.sqrt_rpow_one_div (by linarith : (0 : ℝ) ≤ 3 * ε)
        (by norm_num : (0 : ℝ) < 40000)]
      norm_num
    rw [e]
    simp only [Real.rpow_eq_pow]
    rw [Real.mul_rpow (by norm_num) hε0.le]
    have h3 : (3 : ℝ) ^ ((1 : ℝ) / 80000) ≤ 3 := by
      calc (3 : ℝ) ^ ((1 : ℝ) / 80000) ≤ (3 : ℝ) ^ (1 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
        _ = 3 := Real.rpow_one 3
    exact mul_le_mul_of_nonneg_right h3 (Real.rpow_nonneg hε0.le _)
  have hb2 : Real.sqrt (Real.rpow ((D.d : ℝ) / (D.q : ℝ)) (1 / 40000)) ≤
      (D.d : ℝ) * Real.rpow (D.q : ℝ) (-(1 / 80000)) := by
    have e : Real.sqrt (Real.rpow ((D.d : ℝ) / (D.q : ℝ)) (1 / 40000)) =
        Real.rpow ((D.d : ℝ) / (D.q : ℝ)) (1 / 80000) := by
      rw [Test.sqrt_rpow_one_div (by positivity : (0 : ℝ) ≤ (D.d : ℝ) / (D.q : ℝ))
        (by norm_num : (0 : ℝ) < 40000)]
      norm_num
    rw [e]
    simp only [Real.rpow_eq_pow]
    rw [Real.div_rpow (by linarith) (by linarith), div_eq_mul_inv,
      ← Real.rpow_neg (by linarith : (0 : ℝ) ≤ (D.q : ℝ))]
    have hd : (D.d : ℝ) ^ ((1 : ℝ) / 80000) ≤ (D.d : ℝ) := by
      calc (D.d : ℝ) ^ ((1 : ℝ) / 80000) ≤ (D.d : ℝ) ^ (1 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le hd1 (by norm_num)
        _ = (D.d : ℝ) := Real.rpow_one _
    exact mul_le_mul_of_nonneg_right hd (Real.rpow_nonneg (by linarith) _)
  have hb3 : Real.sqrt
      (Real.exp (-((directLdAuxParameter D : ℝ) / (2560000 * ((D.m : ℝ) ^ (2 : ℕ)))))) ≤
      Real.rpow 2 (-((1 / 80000) * ((D.m * D.d : ℕ) : ℝ))) := by
    have hlog : Real.log 2 ≤ 1 := by
      have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
      linarith
    have hmd : (0 : ℝ) ≤ (D.m : ℝ) * (D.d : ℝ) := by positivity
    have hcast : ((D.m * D.d : ℕ) : ℝ) = (D.m : ℝ) * (D.d : ℝ) := by push_cast; ring
    rw [directLdAuxParameter_exp_arg D, ← Real.exp_half, hcast]
    simp only [Real.rpow_eq_pow]
    rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2)]
    apply Real.exp_le_exp.mpr
    nlinarith [mul_le_mul_of_nonneg_right hlog hmd]
  have hx := Real.rpow_nonneg hε0.le (1 / 80000 : ℝ)
  have hy := Real.rpow_nonneg (by linarith : (0 : ℝ) ≤ (D.q : ℝ)) (-(1 / 80000) : ℝ)
  have hz := Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ (2 : ℝ))
    (-((1 / 80000) * ((D.m * D.d : ℕ) : ℝ)))
  have p1 : (0 : ℝ) ≤ ((D.d : ℝ) - 1) * Real.rpow ε (1 / 80000) :=
    mul_nonneg (by linarith) hx
  have p2 : (0 : ℝ) ≤ (D.d : ℝ) * Real.rpow (D.q : ℝ) (-(1 / 80000)) :=
    mul_nonneg (by linarith) hy
  have p3 : (0 : ℝ) ≤ (3 * (D.d : ℝ) - 1) *
      Real.rpow 2 (-((1 / 80000) * ((D.m * D.d : ℕ) : ℝ))) := mul_nonneg (by linarith) hz
  calc Real.sqrt (Real.rpow (3 * ε) (1 / 40000) +
        Real.rpow ((D.d : ℝ) / (D.q : ℝ)) (1 / 40000) +
        Real.exp (-((directLdAuxParameter D : ℝ) / (2560000 * ((D.m : ℝ) ^ (2 : ℕ))))))
      ≤ Real.sqrt (Real.rpow (3 * ε) (1 / 40000)) +
          Real.sqrt (Real.rpow ((D.d : ℝ) / (D.q : ℝ)) (1 / 40000)) +
          Real.sqrt
            (Real.exp (-((directLdAuxParameter D : ℝ) /
              (2560000 * ((D.m : ℝ) ^ (2 : ℕ)))))) :=
        MIPStarRE.LDT.sqrt_add3_le_add3_sqrt h1n h2n h3n
    _ ≤ 3 * Real.rpow ε (1 / 80000) + (D.d : ℝ) * Real.rpow (D.q : ℝ) (-(1 / 80000)) +
          Real.rpow 2 (-((1 / 80000) * ((D.m * D.d : ℕ) : ℝ))) := by
        linarith
    _ ≤ 3 * (D.d : ℝ) * transportEnvelope D ε := by
        unfold transportEnvelope
        nlinarith [p1, p2, p3]

/-- The square root of the whole scalar error of the transport, bounded by an
explicit polynomial in the parameters times the transport envelope. -/
private theorem sqrt_directLdTransportError_le (D : DirectLdParams) {ε : ℝ}
    (hε0 : 0 < ε) (hε1 : ε ≤ 1) :
    Real.sqrt (Test.mainFormalError D.toLDTParameters (directLdAuxParameter D) (3 * ε) +
        ((D.m : ℝ) * (D.d : ℝ)) / (D.q : ℝ) + ε) ≤
      2500000000 * (D.m : ℝ) ^ (5 : ℕ) * (D.d : ℝ) ^ (2 : ℕ) * transportEnvelope D ε := by
  have hm1 := directLd_one_le_m D
  have hd1 := directLd_one_le_d D
  have hq1 := directLd_one_le_q D
  have hT := transportEnvelope_nonneg D hε0.le
  have hE := mainFormalError_direct_nonneg D hε0.le
  have hmdq : (0 : ℝ) ≤ ((D.m : ℝ) * (D.d : ℝ)) / (D.q : ℝ) := by positivity
  have hsE : Real.sqrt
      (Test.mainFormalError D.toLDTParameters (directLdAuxParameter D) (3 * ε)) ≤
      820000000 * (D.m : ℝ) ^ (5 : ℕ) * (D.d : ℝ) *
        (3 * (D.d : ℝ) * transportEnvelope D ε) := by
    rw [mainFormalError_direct_eq, Real.sqrt_mul (by positivity)]
    exact mul_le_mul (sqrt_directLdPrefactor_le D) (sqrt_directLdEnvelope_le D hε0)
      (Real.sqrt_nonneg _) (by positivity)
  have hsmd : Real.sqrt (((D.m : ℝ) * (D.d : ℝ)) / (D.q : ℝ)) ≤
      (D.m : ℝ) * (D.d : ℝ) * Real.rpow (D.q : ℝ) (-(1 / 80000)) := by
    have hmd1 : (1 : ℝ) ≤ (D.m : ℝ) * (D.d : ℝ) := by nlinarith
    simp only [Real.rpow_eq_pow]
    rw [Real.sqrt_eq_rpow, Real.div_rpow (by linarith) (by linarith), div_eq_mul_inv,
      ← Real.rpow_neg (by linarith : (0 : ℝ) ≤ (D.q : ℝ))]
    have h1 : ((D.m : ℝ) * (D.d : ℝ)) ^ ((1 : ℝ) / 2) ≤ (D.m : ℝ) * (D.d : ℝ) := by
      calc ((D.m : ℝ) * (D.d : ℝ)) ^ ((1 : ℝ) / 2)
          ≤ ((D.m : ℝ) * (D.d : ℝ)) ^ (1 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le hmd1 (by norm_num)
        _ = (D.m : ℝ) * (D.d : ℝ) := Real.rpow_one _
    have h2 : (D.q : ℝ) ^ (-((1 : ℝ) / 2)) ≤ (D.q : ℝ) ^ (-((1 : ℝ) / 80000)) :=
      Real.rpow_le_rpow_of_exponent_le hq1 (by norm_num)
    exact mul_le_mul h1 h2 (Real.rpow_nonneg (by linarith) _) (by nlinarith)
  have hsε : Real.sqrt ε ≤ Real.rpow ε (1 / 80000) := by
    simp only [Real.rpow_eq_pow]
    rw [Real.sqrt_eq_rpow]
    exact Real.rpow_le_rpow_of_exponent_ge hε0 hε1 (by norm_num)
  have hqT : (D.m : ℝ) * (D.d : ℝ) * Real.rpow (D.q : ℝ) (-(1 / 80000)) ≤
      (D.m : ℝ) * (D.d : ℝ) * transportEnvelope D ε :=
    mul_le_mul_of_nonneg_left (transportEnvelope_rpow_q_le D hε0.le) (by positivity)
  have hεT : Real.rpow ε (1 / 80000) ≤ 1 * transportEnvelope D ε := by
    rw [one_mul]
    exact transportEnvelope_rpow_eps_le D ε
  have hP : (D.m : ℝ) * (D.d : ℝ) ≤ (D.m : ℝ) ^ (5 : ℕ) * (D.d : ℝ) ^ (2 : ℕ) := by
    have e1 : (D.m : ℝ) ≤ (D.m : ℝ) ^ (5 : ℕ) := by
      simpa using pow_le_pow_right₀ hm1 (by norm_num : 1 ≤ 5)
    have e2 : (D.d : ℝ) ≤ (D.d : ℝ) ^ (2 : ℕ) := by
      simpa using pow_le_pow_right₀ hd1 (by norm_num : 1 ≤ 2)
    exact mul_le_mul e1 e2 (by linarith) (by positivity)
  have hP1 : (1 : ℝ) ≤ (D.m : ℝ) ^ (5 : ℕ) * (D.d : ℝ) ^ (2 : ℕ) := by
    have e1 : (1 : ℝ) ≤ (D.m : ℝ) ^ (5 : ℕ) := one_le_pow₀ hm1
    have e2 : (1 : ℝ) ≤ (D.d : ℝ) ^ (2 : ℕ) := one_le_pow₀ hd1
    nlinarith
  have hcoef : 2460000000 * ((D.m : ℝ) ^ (5 : ℕ) * (D.d : ℝ) ^ (2 : ℕ)) +
      (D.m : ℝ) * (D.d : ℝ) + 1 ≤
      2500000000 * ((D.m : ℝ) ^ (5 : ℕ) * (D.d : ℝ) ^ (2 : ℕ)) := by linarith
  have hkey : 820000000 * (D.m : ℝ) ^ (5 : ℕ) * (D.d : ℝ) *
        (3 * (D.d : ℝ) * transportEnvelope D ε) +
      (D.m : ℝ) * (D.d : ℝ) * transportEnvelope D ε + 1 * transportEnvelope D ε ≤
      2500000000 * (D.m : ℝ) ^ (5 : ℕ) * (D.d : ℝ) ^ (2 : ℕ) * transportEnvelope D ε := by
    nlinarith [mul_le_mul_of_nonneg_right hcoef hT]
  calc Real.sqrt (Test.mainFormalError D.toLDTParameters (directLdAuxParameter D) (3 * ε) +
        ((D.m : ℝ) * (D.d : ℝ)) / (D.q : ℝ) + ε)
      ≤ Real.sqrt
            (Test.mainFormalError D.toLDTParameters (directLdAuxParameter D) (3 * ε)) +
          Real.sqrt (((D.m : ℝ) * (D.d : ℝ)) / (D.q : ℝ)) + Real.sqrt ε :=
        MIPStarRE.LDT.sqrt_add3_le_add3_sqrt hE hmdq hε0.le
    _ ≤ 820000000 * (D.m : ℝ) ^ (5 : ℕ) * (D.d : ℝ) *
            (3 * (D.d : ℝ) * transportEnvelope D ε) +
          (D.m : ℝ) * (D.d : ℝ) * transportEnvelope D ε + 1 * transportEnvelope D ε := by
        linarith
    _ ≤ 2500000000 * (D.m : ℝ) ^ (5 : ℕ) * (D.d : ℝ) ^ (2 : ℕ) * transportEnvelope D ε :=
        hkey

/-! ## Absorption into the error function of `lem:ld-soundness` -/

/-- Absorption of the simultaneous-measurement estimate into `deltaLd`.

For every universal constant `C₀ ≥ 1` of the sandwiched simultaneous
measurement estimate `consistencyDefect_sandwich_le`, the explicit universal
constants `a = 2500000000 C₀` and `b = 1/80000` satisfy the side conditions of
`lem:ld-soundness` and absorb

  `C₀ k √(mainFormalError (2560000 m³ d) (3 ε) + m d / q + ε)`

into `deltaLd a b ε q m d k` in the nontrivial regime `0 < ε ≤ 1`.  Blueprint
`ch13_qpbt_test.tex:139-167`; paper
`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:413-458`. -/
theorem exists_directLdTransportConstants (C₀ : ℝ) (hC₀ : 1 ≤ C₀) :
    ∃ a b : ℝ, 1 ≤ a ∧ 0 < b ∧ b ≤ 1 ∧
      ∀ (D : DirectLdParams) (ε : ℝ), 0 < ε → ε ≤ 1 →
        C₀ * (D.k : ℝ) *
            Real.sqrt
              (Test.mainFormalError D.toLDTParameters (directLdAuxParameter D) (3 * ε) +
                ((D.m : ℝ) * (D.d : ℝ)) / (D.q : ℝ) + ε) ≤
          deltaLd a b ε D.q D.m D.d D.k := by
  refine ⟨2500000000 * C₀, 1 / 80000, by linarith, by norm_num, by norm_num, ?_⟩
  intro D ε hε0 hε1
  have hm1 := directLd_one_le_m D
  have hd1 := directLd_one_le_d D
  have hk1 := directLd_one_le_k D
  have hT := transportEnvelope_nonneg D hε0.le
  have hdelta : deltaLd (2500000000 * C₀) (1 / 80000) ε D.q D.m D.d D.k =
      2500000000 * C₀ * Real.rpow ((D.d * D.m * D.k : ℕ) : ℝ) (2500000000 * C₀) *
        transportEnvelope D ε := rfl
  have hbase : (1 : ℝ) ≤ ((D.d * D.m * D.k : ℕ) : ℝ) := by
    have hn : 1 ≤ D.d * D.m * D.k := Nat.mul_pos (Nat.mul_pos D.hd D.hm) D.hk
    exact_mod_cast hn
  have hpow : ((D.d * D.m * D.k : ℕ) : ℝ) ^ (8 : ℕ) ≤
      Real.rpow ((D.d * D.m * D.k : ℕ) : ℝ) (2500000000 * C₀) := by
    simp only [Real.rpow_eq_pow]
    rw [← Real.rpow_natCast (((D.d * D.m * D.k : ℕ) : ℝ)) 8]
    exact Real.rpow_le_rpow_of_exponent_le hbase (by push_cast; linarith)
  have hmono : (D.k : ℝ) * (D.m : ℝ) ^ (5 : ℕ) * (D.d : ℝ) ^ (2 : ℕ) ≤
      ((D.d * D.m * D.k : ℕ) : ℝ) ^ (8 : ℕ) := by
    have e1 : (D.k : ℝ) ≤ (D.k : ℝ) ^ (8 : ℕ) := by
      simpa using pow_le_pow_right₀ hk1 (by norm_num : 1 ≤ 8)
    have e2 : (D.m : ℝ) ^ (5 : ℕ) ≤ (D.m : ℝ) ^ (8 : ℕ) :=
      pow_le_pow_right₀ hm1 (by norm_num)
    have e3 : (D.d : ℝ) ^ (2 : ℕ) ≤ (D.d : ℝ) ^ (8 : ℕ) :=
      pow_le_pow_right₀ hd1 (by norm_num)
    push_cast
    calc (D.k : ℝ) * (D.m : ℝ) ^ (5 : ℕ) * (D.d : ℝ) ^ (2 : ℕ)
        ≤ (D.k : ℝ) ^ (8 : ℕ) * (D.m : ℝ) ^ (8 : ℕ) * (D.d : ℝ) ^ (8 : ℕ) :=
          mul_le_mul (mul_le_mul e1 e2 (by positivity) (by positivity)) e3
            (by positivity) (by positivity)
      _ = ((D.d : ℝ) * (D.m : ℝ) * (D.k : ℝ)) ^ (8 : ℕ) := by ring
  have hstep := sqrt_directLdTransportError_le D hε0 hε1
  rw [hdelta]
  calc C₀ * (D.k : ℝ) *
        Real.sqrt (Test.mainFormalError D.toLDTParameters (directLdAuxParameter D) (3 * ε) +
          ((D.m : ℝ) * (D.d : ℝ)) / (D.q : ℝ) + ε)
      ≤ C₀ * (D.k : ℝ) *
          (2500000000 * (D.m : ℝ) ^ (5 : ℕ) * (D.d : ℝ) ^ (2 : ℕ) *
            transportEnvelope D ε) :=
        mul_le_mul_of_nonneg_left hstep (mul_nonneg (by linarith) (by positivity))
    _ = 2500000000 * C₀ *
          ((D.k : ℝ) * (D.m : ℝ) ^ (5 : ℕ) * (D.d : ℝ) ^ (2 : ℕ)) *
          transportEnvelope D ε := by ring
    _ ≤ 2500000000 * C₀ * Real.rpow ((D.d * D.m * D.k : ℕ) : ℝ) (2500000000 * C₀) *
          transportEnvelope D ε := by
        apply mul_le_mul_of_nonneg_right _ hT
        exact mul_le_mul_of_nonneg_left (le_trans hmono hpow) (by linarith)

/-! ## The degenerate regimes

In the two regimes `1 ≤ ε` and `q ≤ d` the error function `deltaLd` is at
least one, so the consistency conclusions of `lem:ld-soundness` hold for any
witnesses; the low-degree test carries no information there. -/

/-- In the regime `1 ≤ ε` the error function `deltaLd` is at least one.

Formalization-only scalar bound closing the trivial regime of
`lem:ld-soundness`, blueprint `ch13_qpbt_test.tex:139-167`, paper
`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:413-458`. -/
theorem one_le_deltaLd_of_one_le_error {a b ε : ℝ} (ha : 1 ≤ a) (hb : 0 ≤ b)
    (hε : 1 ≤ ε) {q m d k : ℕ} (hm : 1 ≤ m) (hd : 1 ≤ d) (hk : 1 ≤ k) :
    1 ≤ deltaLd a b ε q m d k := by
  have hbase : (1 : ℝ) ≤ ((d * m * k : ℕ) : ℝ) := by
    have hn : 1 ≤ d * m * k := Nat.mul_pos (Nat.mul_pos hd hm) hk
    exact_mod_cast hn
  have hX : (1 : ℝ) ≤ Real.rpow ((d * m * k : ℕ) : ℝ) a := by
    simp only [Real.rpow_eq_pow]
    calc (1 : ℝ) = (1 : ℝ) ^ a := (Real.one_rpow a).symm
      _ ≤ ((d * m * k : ℕ) : ℝ) ^ a := Real.rpow_le_rpow (by norm_num) hbase (by linarith)
  have hY : (1 : ℝ) ≤ Real.rpow ε b := by
    simp only [Real.rpow_eq_pow]
    calc (1 : ℝ) = (1 : ℝ) ^ b := (Real.one_rpow b).symm
      _ ≤ ε ^ b := Real.rpow_le_rpow (by norm_num) hε hb
  have hZ : (0 : ℝ) ≤ Real.rpow (q : ℝ) (-b) := Real.rpow_nonneg (by positivity) _
  have hW : (0 : ℝ) ≤ Real.rpow 2 (-(b * ((m * d : ℕ) : ℝ))) :=
    Real.rpow_nonneg (by norm_num) _
  have hax : (1 : ℝ) ≤ a * Real.rpow ((d * m * k : ℕ) : ℝ) a := by nlinarith
  have hsum : (1 : ℝ) ≤ Real.rpow ε b + Real.rpow (q : ℝ) (-b) +
      Real.rpow 2 (-(b * ((m * d : ℕ) : ℝ))) := by linarith
  unfold deltaLd
  calc (1 : ℝ) = 1 * 1 := by norm_num
    _ ≤ a * Real.rpow ((d * m * k : ℕ) : ℝ) a *
        (Real.rpow ε b + Real.rpow (q : ℝ) (-b) +
          Real.rpow 2 (-(b * ((m * d : ℕ) : ℝ)))) :=
      mul_le_mul hax hsum (by norm_num) (by linarith)

/-- In the degenerate regime `q ≤ d`, where the degree bound is at least the
field size, the error function `deltaLd` is at least one.

Formalization-only scalar bound closing the regime in which the low individual
degree test carries no information; the error of `lem:ld-soundness` is
blueprint `ch13_qpbt_test.tex:139-167`, paper
`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:413-458`. -/
theorem one_le_deltaLd_of_fieldSize_le_degree {a b ε : ℝ} (ha : 1 ≤ a) (hb1 : b ≤ 1)
    (hε : 0 ≤ ε) {q m d k : ℕ} (hq : 1 ≤ q) (hqd : q ≤ d) (hm : 1 ≤ m) (hk : 1 ≤ k) :
    1 ≤ deltaLd a b ε q m d k := by
  have hq1 : (1 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
  have hqpos : (0 : ℝ) < (q : ℝ) := by linarith
  have hdmk : d ≤ d * m * k := by
    calc d = d * 1 * 1 := by ring
      _ ≤ d * m * k := Nat.mul_le_mul (Nat.mul_le_mul le_rfl hm) hk
  have hbase : (q : ℝ) ≤ ((d * m * k : ℕ) : ℝ) := by
    have hn : q ≤ d * m * k := le_trans hqd hdmk
    exact_mod_cast hn
  have hX : (q : ℝ) ≤ Real.rpow ((d * m * k : ℕ) : ℝ) a := by
    simp only [Real.rpow_eq_pow]
    calc (q : ℝ) ≤ ((d * m * k : ℕ) : ℝ) := hbase
      _ = ((d * m * k : ℕ) : ℝ) ^ (1 : ℝ) := (Real.rpow_one _).symm
      _ ≤ ((d * m * k : ℕ) : ℝ) ^ a :=
          Real.rpow_le_rpow_of_exponent_le (le_trans hq1 hbase) ha
  have hqb : Real.rpow (q : ℝ) b ≤ (q : ℝ) := by
    simp only [Real.rpow_eq_pow]
    calc (q : ℝ) ^ b ≤ (q : ℝ) ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le hq1 hb1
      _ = (q : ℝ) := Real.rpow_one _
  have hqbpos : (0 : ℝ) < Real.rpow (q : ℝ) b := Real.rpow_pos_of_pos hqpos b
  have hinv : (q : ℝ)⁻¹ ≤ Real.rpow (q : ℝ) (-b) := by
    simp only [Real.rpow_eq_pow]
    rw [Real.rpow_neg hqpos.le]
    exact inv_anti₀ hqbpos hqb
  have hY : (0 : ℝ) ≤ Real.rpow ε b := Real.rpow_nonneg hε _
  have hW : (0 : ℝ) ≤ Real.rpow 2 (-(b * ((m * d : ℕ) : ℝ))) :=
    Real.rpow_nonneg (by norm_num) _
  have hsum : (q : ℝ)⁻¹ ≤ Real.rpow ε b + Real.rpow (q : ℝ) (-b) +
      Real.rpow 2 (-(b * ((m * d : ℕ) : ℝ))) := by linarith
  have hax : 1 * (q : ℝ) ≤ a * Real.rpow ((d * m * k : ℕ) : ℝ) a :=
    mul_le_mul ha hX (by linarith) (by linarith)
  unfold deltaLd
  calc (1 : ℝ) = 1 * (q : ℝ) * (q : ℝ)⁻¹ := by field_simp
    _ ≤ a * Real.rpow ((d * m * k : ℕ) : ℝ) a *
        (Real.rpow ε b + Real.rpow (q : ℝ) (-b) +
          Real.rpow 2 (-(b * ((m * d : ℕ) : ℝ)))) :=
      mul_le_mul hax hsum (by positivity) (by linarith)

/-! ## A coarse universal bound on the consistency defect

The consistency defect compared with `deltaLd` in `lem:ld-soundness` is the
off-diagonal Born mass of a pair of measurement families acting on the two
tensor factors of a unit bipartite state.  Since the joint Born weights are
nonnegative and sum to one, that mass is at most one; combined with the two
lower bounds on `deltaLd` above this closes the regimes `1 ≤ ε` and `q ≤ d`.

The three lemmas of this section are formalization-only.  They are generic
statements about `consistencyDefect` rather than about the low-degree game,
and would naturally live in `MIPStarRE/QPBT/Games/DistanceTheorems.lean`. -/

private theorem sum_heteroKron_one_right {α ιA ιB : Type*} [Fintype α]
    [Fintype ιA] [DecidableEq ιA] [DecidableEq ιB]
    (M : Quantum.Measurement α ιA) :
    (∑ a : α, heteroKron (M.effect a) (1 : Op ιB)) = 1 := by
  ext i j
  simp only [Matrix.sum_apply, heteroKron, Matrix.kronecker,
    Matrix.kroneckerMap_apply]
  rw [← Finset.sum_mul]
  rw [show (∑ a : α, M.effect a i.1 j.1) = (1 : Op ιA) i.1 j.1 by
    simpa only [Matrix.sum_apply] using congrFun (congrFun M.sum_eq_one i.1) j.1]
  exact congrFun (congrFun
    (Matrix.one_kronecker_one (m := ιA) (n := ιB) (α := ℂ)) i) j

private theorem sum_heteroKron_one_left {α ιA ιB : Type*} [Fintype α]
    [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB]
    (N : Quantum.Measurement α ιB) :
    (∑ a : α, heteroKron (1 : Op ιA) (N.effect a)) = 1 := by
  ext i j
  simp only [Matrix.sum_apply, heteroKron, Matrix.kronecker,
    Matrix.kroneckerMap_apply]
  rw [← Finset.mul_sum]
  rw [show (∑ a : α, N.effect a i.2 j.2) = (1 : Op ιB) i.2 j.2 by
    simpa only [Matrix.sum_apply] using congrFun (congrFun N.sum_eq_one i.2) j.2]
  exact congrFun (congrFun
    (Matrix.one_kronecker_one (m := ιA) (n := ιB) (α := ℂ)) i) j

/-- Alice's measurement seen on the bipartite space, by tensoring with the
identity on Bob's space.  Formalization-only. -/
private noncomputable def leftKronMeasurement {α ιA ιB : Type*} [Fintype α]
    [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB]
    (M : Quantum.Measurement α ιA) : Quantum.Measurement α (ιA × ιB) where
  effect a := heteroKron (M.effect a) 1
  pos a := kronecker_nonneg (M.pos a)
    (Matrix.nonneg_iff_posSemidef.mpr Matrix.PosSemidef.one)
  sum_le_one := le_of_eq (sum_heteroKron_one_right M)
  sum_eq_one := sum_heteroKron_one_right M

/-- Bob's measurement seen on the bipartite space, by tensoring with the
identity on Alice's space.  Formalization-only. -/
private noncomputable def rightKronMeasurement {α ιA ιB : Type*} [Fintype α]
    [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB]
    (N : Quantum.Measurement α ιB) : Quantum.Measurement α (ιA × ιB) where
  effect a := heteroKron 1 (N.effect a)
  pos a := kronecker_nonneg
    (Matrix.nonneg_iff_posSemidef.mpr Matrix.PosSemidef.one) (N.pos a)
  sum_le_one := le_of_eq (sum_heteroKron_one_left N)
  sum_eq_one := sum_heteroKron_one_left N

/-- Coarse bound on the consistency defect of a bipartite pair of measurement
families on a unit state: the off-diagonal Born mass is at most one.

This is the trivial estimate that closes the degenerate regimes of
`lem:ld-soundness`, where `deltaLd` is at least one by
`one_le_deltaLd_of_one_le_error` or by
`one_le_deltaLd_of_fieldSize_le_degree`.  Formalization-only support for
`blueprint/src/chapter/ch13_qpbt_test.tex:139-167`. -/
theorem consistencyDefect_heteroKron_le_one {X α ιA ιB : Type*}
    [Fintype X] [DecidableEq X] [Fintype α] [DecidableEq α]
    [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB]
    (μ : Distribution X) (hμ : μ.IsProbability)
    (A : X → Quantum.Measurement α ιA) (B : X → Quantum.Measurement α ιB)
    (ψ : EuclideanSpace ℂ (ιA × ιB)) (hψ : ‖ψ‖ = 1) :
    consistencyDefect μ (fun x a => heteroKron ((A x).effect a) 1)
        (fun x a => heteroKron 1 ((B x).effect a)) ψ ≤ 1 := by
  have hEq : consistencyDefect μ (fun x a => heteroKron ((A x).effect a) 1)
      (fun x a => heteroKron 1 ((B x).effect a)) ψ =
      1 - avgOver μ (fun x => ∑ a : α,
        DistanceCalculus.stateQForm ψ
          (heteroKron ((A x).effect a) 1 * heteroKron 1 ((B x).effect a))) :=
    DistanceCalculus.consistencyDefect_eq_one_sub_overlap μ
      (fun x => leftKronMeasurement (A x)) (fun x => rightKronMeasurement (B x))
      ψ hμ hψ
  have hnn : 0 ≤ avgOver μ (fun x => ∑ a : α,
      DistanceCalculus.stateQForm ψ
        (heteroKron ((A x).effect a) 1 * heteroKron 1 ((B x).effect a))) := by
    refine avgOver_nonneg μ _ (fun x => Finset.sum_nonneg (fun a _ => ?_))
    have hprod : heteroKron ((A x).effect a) (1 : Op ιB) *
        heteroKron (1 : Op ιA) ((B x).effect a) =
        heteroKron ((A x).effect a) ((B x).effect a) := by
      change Matrix.kroneckerMap (fun x1 x2 => x1 * x2) ((A x).effect a)
            (1 : Op ιB) *
          Matrix.kroneckerMap (fun x1 x2 => x1 * x2) (1 : Op ιA)
            ((B x).effect a) =
          Matrix.kroneckerMap (fun x1 x2 => x1 * x2) ((A x).effect a)
            ((B x).effect a)
      rw [← Matrix.mul_kronecker_mul, mul_one, one_mul]
    rw [hprod]
    unfold DistanceCalculus.stateQForm applyOperatorToState heteroKron
    exact
      (Matrix.isPositive_toEuclideanLin_iff.mpr
        (Matrix.nonneg_iff_posSemidef.mp
          (kronecker_nonneg ((A x).pos a) ((B x).pos a)))).re_inner_nonneg_right ψ
  rw [hEq]
  linarith

end MIPStarRE.QPBT
