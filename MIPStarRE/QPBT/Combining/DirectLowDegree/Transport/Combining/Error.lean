import MIPStarRE.QPBT.Combining.DirectLowDegree.Transport.Combining.Parameters
import MIPStarRE.QPBT.Combining.DirectLowDegree.Transport.Error

/-!
# The scalar error of the simultaneity reduction

`prop:ld-simultaneous-general-k` produces the three consistency relations of
`lem:ld-soundness` with the error of `thm:main-formal` at the combined
parameters of `def:ld-combining-parameters`, at the pass bound `30 ε`, together
with the recovery loss `(m + k) d / q` of `lem:ld-combining-recovery`.  This
module absorbs that error into the error function `deltaLd` of
`lem:ld-soundness` at the original parameters `(q, m, d, k)`.

The absorption is the estimate

  `mainFormalError (q, m + k, d) (2560000 (m + k)³ d) (30 ε) + (m + k) d / q`
  `  ≤ deltaLd a b ε q m d k`

for `0 < ε ≤ 1`, with the universal constants `a = 10^23` and `b = 1/80000`.
The exponent is the transport exponent of `exists_directLdTransportConstants`,
half the exponent `1/40000` carried by `mainFormalError`; the constant is
obtained from the prefactor `655360000000000000 (m + k)^{10} d²` of the mature
error at the combined parameters, the factor `30 d` by which the three envelope
terms of that error exceed the corresponding terms of `deltaLd`, and the bound
`m + k ≤ 2 d m k`.

## Main results

* `exists_directCombinedTransportConstants` — the absorption, with the explicit
  universal constants `a = 10^23` and `b = 1/80000`.

## References

* `references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:413-458`
* `blueprint/src/chapter/ch13_qpbt_test.tex:693-722`
* `MIPStarRE/LDT/Test/MainTheorem/ScalarBounds/Definitions.lean:28-36`
-/

open scoped BigOperators

namespace MIPStarRE.QPBT

open MIPStarRE.LDT MIPStarRE.Quantum

/-! ## The mature error at the combined parameters -/

/-- The auxiliary sampling parameter at the combined parameters, in the
parameters of the original directly indexed game. -/
private theorem directCombinedAux_cast (D : DirectLdParams) :
    (directLdAuxParameter D.combined : ℝ) =
      2560000 * (((D.m + D.k : ℕ) : ℝ) ^ (3 : ℕ)) * (D.d : ℝ) := by
  unfold directLdAuxParameter
  simp only [DirectLdParams.combined_m, DirectLdParams.combined_d]
  push_cast
  ring

/-- The mature error at the combined parameters and the pass bound `30 ε`,
written out in the parameters of the original directly indexed game. -/
private theorem mainFormalError_combined_eq (D : DirectLdParams) (ε : ℝ) :
    Test.mainFormalError D.combined.toLDTParameters
        (directLdAuxParameter D.combined) (3 * (10 * ε)) =
      100000 * ((directLdAuxParameter D.combined : ℝ) ^ (2 : ℕ)) *
          (((D.m + D.k : ℕ) : ℝ) ^ (4 : ℕ)) *
        (Real.rpow (3 * (10 * ε)) (1 / 40000) +
          Real.rpow ((D.d : ℝ) / (D.q : ℝ)) (1 / 40000) +
          Real.exp (-((directLdAuxParameter D.combined : ℝ) /
            (2560000 * (((D.m + D.k : ℕ) : ℝ) ^ (2 : ℕ)))))) := rfl

/-- The polynomial prefactor of the mature error at the combined parameters. -/
private theorem directCombinedPrefactor_eq (D : DirectLdParams) :
    100000 * ((directLdAuxParameter D.combined : ℝ) ^ (2 : ℕ)) *
        (((D.m + D.k : ℕ) : ℝ) ^ (4 : ℕ)) =
      655360000000000000 * (((D.m + D.k : ℕ) : ℝ) ^ (10 : ℕ)) * ((D.d : ℝ) ^ (2 : ℕ)) := by
  rw [directCombinedAux_cast]
  ring

/-- With the auxiliary sampling parameter of the combined parameters the
exponential scale of the mature error collapses: the argument of its
exponential term is exactly `(m + k) d`. -/
private theorem directCombinedAux_exp_arg (D : DirectLdParams) :
    (directLdAuxParameter D.combined : ℝ) /
        (2560000 * (((D.m + D.k : ℕ) : ℝ) ^ (2 : ℕ))) =
      ((D.m + D.k : ℕ) : ℝ) * (D.d : ℝ) := by
  have hM : (1 : ℝ) ≤ ((D.m + D.k : ℕ) : ℝ) := by
    have h : 1 ≤ D.m + D.k := le_trans D.hm (Nat.le_add_right D.m D.k)
    exact_mod_cast h
  have hMpos : (0 : ℝ) < ((D.m + D.k : ℕ) : ℝ) := lt_of_lt_of_le zero_lt_one hM
  have hne : (2560000 : ℝ) * (((D.m + D.k : ℕ) : ℝ) ^ (2 : ℕ)) ≠ 0 := ne_of_gt (by positivity)
  rw [directCombinedAux_cast, div_eq_iff hne]
  ring

/-! ## The three terms of the mature error at the combined parameters -/

/-- The test term of the mature error at the pass bound `30 ε`, bounded by the
constant `30` times `ε^(1/80000)` in the regime `0 < ε ≤ 1`. -/
private theorem directCombined_test_term_le {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε ≤ 1) :
    Real.rpow (3 * (10 * ε)) (1 / 40000) ≤ 30 * Real.rpow ε (1 / 80000) := by
  have h30 : (3 : ℝ) * (10 * ε) = 30 * ε := by ring
  rw [h30]
  simp only [Real.rpow_eq_pow]
  rw [Real.mul_rpow (by norm_num) hε0.le]
  have hc : (30 : ℝ) ^ ((1 : ℝ) / 40000) ≤ 30 := by
    calc (30 : ℝ) ^ ((1 : ℝ) / 40000) ≤ (30 : ℝ) ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
      _ = 30 := Real.rpow_one 30
  have he : ε ^ ((1 : ℝ) / 40000) ≤ ε ^ ((1 : ℝ) / 80000) :=
    Real.rpow_le_rpow_of_exponent_ge hε0 hε1 (by norm_num)
  exact mul_le_mul hc he (Real.rpow_nonneg hε0.le _) (by norm_num)

/-- The field term of the mature error, bounded by the polynomial `d` times
`q^(-1/80000)`. -/
private theorem directCombined_field_term_le (D : DirectLdParams) :
    Real.rpow ((D.d : ℝ) / (D.q : ℝ)) (1 / 40000) ≤
      (D.d : ℝ) * Real.rpow (D.q : ℝ) (-(1 / 80000)) := by
  have hd1 : (1 : ℝ) ≤ (D.d : ℝ) := by exact_mod_cast D.hd
  have hqn : 1 ≤ D.q := D.toLDTParameters.hq
  have hq1 : (1 : ℝ) ≤ (D.q : ℝ) := by exact_mod_cast hqn
  simp only [Real.rpow_eq_pow]
  rw [Real.div_rpow (by linarith) (by linarith), div_eq_mul_inv,
    ← Real.rpow_neg (by linarith : (0 : ℝ) ≤ (D.q : ℝ))]
  have hd : (D.d : ℝ) ^ ((1 : ℝ) / 40000) ≤ (D.d : ℝ) := by
    calc (D.d : ℝ) ^ ((1 : ℝ) / 40000) ≤ (D.d : ℝ) ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le hd1 (by norm_num)
      _ = (D.d : ℝ) := Real.rpow_one _
  have hq : (D.q : ℝ) ^ (-((1 : ℝ) / 40000)) ≤ (D.q : ℝ) ^ (-((1 : ℝ) / 80000)) :=
    Real.rpow_le_rpow_of_exponent_le hq1 (by norm_num)
  exact mul_le_mul hd hq (Real.rpow_nonneg (by linarith) _) (by linarith)

/-- The exponential term of the mature error at the auxiliary sampling
parameter of the combined parameters is `exp (-(m + k) d)`, hence at most the
base-two decay `2^(-m d/80000)` of `deltaLd`. -/
private theorem directCombined_exponential_term_le (D : DirectLdParams) :
    Real.exp (-(((D.m + D.k : ℕ) : ℝ) * (D.d : ℝ))) ≤
      Real.rpow 2 (-((1 / 80000) * ((D.m * D.d : ℕ) : ℝ))) := by
  have hlog : Real.log 2 ≤ 1 := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    linarith
  have hm0 : (0 : ℝ) ≤ (D.m : ℝ) := by positivity
  have hd0 : (0 : ℝ) ≤ (D.d : ℝ) := by positivity
  have hMm : (D.m : ℝ) ≤ ((D.m + D.k : ℕ) : ℝ) := by
    have hk0 : (0 : ℝ) ≤ (D.k : ℝ) := by positivity
    push_cast
    linarith
  have hcast : ((D.m * D.d : ℕ) : ℝ) = (D.m : ℝ) * (D.d : ℝ) := by push_cast; ring
  rw [hcast]
  simp only [Real.rpow_eq_pow]
  rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2)]
  apply Real.exp_le_exp.mpr
  nlinarith [mul_le_mul_of_nonneg_right hMm hd0,
    mul_le_mul_of_nonneg_left hlog (mul_nonneg hm0 hd0), mul_nonneg hm0 hd0]

/-! ## The two contributions of the reduction -/

/-- The mature error at the combined parameters and the pass bound `30 ε`,
bounded by an explicit polynomial in the parameters times the inner factor of
`deltaLd` at the transport exponent `b = 1/80000`. -/
private theorem mainFormalError_combined_le (D : DirectLdParams) {ε : ℝ}
    (hε0 : 0 < ε) (hε1 : ε ≤ 1) :
    Test.mainFormalError D.combined.toLDTParameters
        (directLdAuxParameter D.combined) (3 * (10 * ε)) ≤
      19660800000000000000 * (((D.m + D.k : ℕ) : ℝ) ^ (10 : ℕ)) * ((D.d : ℝ) ^ (3 : ℕ)) *
        transportEnvelope D ε := by
  have hd1 : (1 : ℝ) ≤ (D.d : ℝ) := by exact_mod_cast D.hd
  have hX : (0 : ℝ) ≤ Real.rpow ε (1 / 80000) := Real.rpow_nonneg hε0.le _
  have hY : (0 : ℝ) ≤ Real.rpow (D.q : ℝ) (-(1 / 80000)) := Real.rpow_nonneg (by positivity) _
  have hZ : (0 : ℝ) ≤ Real.rpow 2 (-((1 / 80000) * ((D.m * D.d : ℕ) : ℝ))) :=
    Real.rpow_nonneg (by norm_num) _
  have hsum : Real.rpow (3 * (10 * ε)) (1 / 40000) +
      Real.rpow ((D.d : ℝ) / (D.q : ℝ)) (1 / 40000) +
      Real.exp (-((directLdAuxParameter D.combined : ℝ) /
        (2560000 * (((D.m + D.k : ℕ) : ℝ) ^ (2 : ℕ))))) ≤
      30 * (D.d : ℝ) * transportEnvelope D ε := by
    rw [directCombinedAux_exp_arg D]
    unfold transportEnvelope
    linarith [directCombined_test_term_le hε0 hε1, directCombined_field_term_le D,
      directCombined_exponential_term_le D, mul_nonneg (sub_nonneg.mpr hd1) hX,
      mul_nonneg (sub_nonneg.mpr hd1) hY, mul_nonneg (sub_nonneg.mpr hd1) hZ, hX, hY, hZ]
  rw [mainFormalError_combined_eq, directCombinedPrefactor_eq]
  have hpre : (0 : ℝ) ≤ 655360000000000000 * (((D.m + D.k : ℕ) : ℝ) ^ (10 : ℕ)) *
      ((D.d : ℝ) ^ (2 : ℕ)) := by positivity
  refine le_trans (mul_le_mul_of_nonneg_left hsum hpre) (le_of_eq ?_)
  ring

/-- The recovery loss of `lem:ld-combining-recovery`, bounded by the polynomial
`(m + k) d` times the inner factor of `deltaLd` at the transport exponent
`b = 1/80000`. -/
private theorem directCombinedRecoveryLoss_le (D : DirectLdParams) {ε : ℝ} (hε0 : 0 < ε) :
    ((D.combined.m * D.d : ℕ) : ℝ) / (D.q : ℝ) ≤
      ((D.m + D.k : ℕ) : ℝ) * (D.d : ℝ) * transportEnvelope D ε := by
  have hqn : 1 ≤ D.q := D.toLDTParameters.hq
  have hq1 : (1 : ℝ) ≤ (D.q : ℝ) := by exact_mod_cast hqn
  have hqpos : (0 : ℝ) < (D.q : ℝ) := by linarith
  have hcast : ((D.combined.m * D.d : ℕ) : ℝ) = ((D.m + D.k : ℕ) : ℝ) * (D.d : ℝ) := by
    simp only [DirectLdParams.combined_m]
    push_cast
    ring
  have hqb : Real.rpow (D.q : ℝ) (1 / 80000) ≤ (D.q : ℝ) := by
    simp only [Real.rpow_eq_pow]
    calc (D.q : ℝ) ^ ((1 : ℝ) / 80000) ≤ (D.q : ℝ) ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le hq1 (by norm_num)
      _ = (D.q : ℝ) := Real.rpow_one _
  have hqbpos : (0 : ℝ) < Real.rpow (D.q : ℝ) (1 / 80000) := Real.rpow_pos_of_pos hqpos _
  have hinv : (D.q : ℝ)⁻¹ ≤ Real.rpow (D.q : ℝ) (-(1 / 80000)) := by
    simp only [Real.rpow_eq_pow]
    rw [Real.rpow_neg hqpos.le]
    exact inv_anti₀ hqbpos hqb
  have hstep : (D.q : ℝ)⁻¹ ≤ transportEnvelope D ε := by
    have hX : (0 : ℝ) ≤ Real.rpow ε (1 / 80000) := Real.rpow_nonneg hε0.le _
    have hZ : (0 : ℝ) ≤ Real.rpow 2 (-((1 / 80000) * ((D.m * D.d : ℕ) : ℝ))) :=
      Real.rpow_nonneg (by norm_num) _
    unfold transportEnvelope
    linarith
  have hMd : (0 : ℝ) ≤ ((D.m + D.k : ℕ) : ℝ) * (D.d : ℝ) := by positivity
  rw [hcast, div_eq_mul_inv]
  exact mul_le_mul_of_nonneg_left hstep hMd

/-! ## Absorption into the error function of `lem:ld-soundness` -/

/-- Absorption of the error of `prop:ld-simultaneous-general-k` into the error
function of `lem:ld-soundness`.

The explicit universal constants `a = 10^23` and `b = 1/80000` satisfy the side
conditions of `lem:ld-soundness` and absorb the error of `thm:main-formal` at
the combined parameters of `def:ld-combining-parameters`, at the pass bound
`30 ε`, together with the recovery loss `(m + k) d / q` of
`lem:ld-combining-recovery`, into `deltaLd a b ε q m d k` in the nontrivial
regime `0 < ε ≤ 1`.  Blueprint `ch13_qpbt_test.tex:693-722`; paper
`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:413-458`. -/
theorem exists_directCombinedTransportConstants :
    ∃ a b : ℝ, 1 ≤ a ∧ 0 < b ∧ b ≤ 1 ∧
      ∀ (D : DirectLdParams) (ε : ℝ), 0 < ε → ε ≤ 1 →
        Test.mainFormalError D.combined.toLDTParameters
              (directLdAuxParameter D.combined) (3 * (10 * ε)) +
            ((D.combined.m * D.d : ℕ) : ℝ) / (D.q : ℝ) ≤
          deltaLd a b ε D.q D.m D.d D.k := by
  refine ⟨100000000000000000000000, 1 / 80000, by norm_num, by norm_num, by norm_num, ?_⟩
  intro D ε hε0 hε1
  have hm1 : (1 : ℝ) ≤ (D.m : ℝ) := by exact_mod_cast D.hm
  have hd1 : (1 : ℝ) ≤ (D.d : ℝ) := by exact_mod_cast D.hd
  have hk1 : (1 : ℝ) ≤ (D.k : ℝ) := by exact_mod_cast D.hk
  have hM1 : (1 : ℝ) ≤ ((D.m + D.k : ℕ) : ℝ) := by
    have h : 1 ≤ D.m + D.k := le_trans D.hm (Nat.le_add_right D.m D.k)
    exact_mod_cast h
  have hN1 : (1 : ℝ) ≤ ((D.d * D.m * D.k : ℕ) : ℝ) := by
    have h : 1 ≤ D.d * D.m * D.k := Nat.mul_pos (Nat.mul_pos D.hd D.hm) D.hk
    exact_mod_cast h
  have hT : (0 : ℝ) ≤ transportEnvelope D ε := transportEnvelope_nonneg D hε0.le
  have hE := mainFormalError_combined_le D hε0 hε1
  have hL := directCombinedRecoveryLoss_le D hε0
  -- The combined dimension is dominated by the polynomial scale of `deltaLd`.
  have hmk : (D.m : ℝ) + (D.k : ℝ) ≤ 2 * ((D.m : ℝ) * (D.k : ℝ)) := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hm1) (sub_nonneg.mpr hk1)]
  have hmkd : 2 * ((D.m : ℝ) * (D.k : ℝ)) ≤ 2 * ((D.d : ℝ) * (D.m : ℝ) * (D.k : ℝ)) := by
    nlinarith [mul_nonneg (mul_nonneg (sub_nonneg.mpr hd1) (by linarith : (0 : ℝ) ≤ (D.m : ℝ)))
      (by linarith : (0 : ℝ) ≤ (D.k : ℝ))]
  have hMN : ((D.m + D.k : ℕ) : ℝ) ≤ 2 * ((D.d * D.m * D.k : ℕ) : ℝ) := by
    push_cast
    linarith
  have hdN : (D.d : ℝ) ≤ ((D.d * D.m * D.k : ℕ) : ℝ) := by
    have hdm : (D.d : ℝ) ≤ (D.d : ℝ) * (D.m : ℝ) := le_mul_of_one_le_right (by linarith) hm1
    have hdmk : (D.d : ℝ) * (D.m : ℝ) ≤ (D.d : ℝ) * (D.m : ℝ) * (D.k : ℝ) :=
      le_mul_of_one_le_right (by positivity) hk1
    push_cast
    linarith
  have hpoly : ((D.m + D.k : ℕ) : ℝ) ^ (10 : ℕ) * (D.d : ℝ) ^ (3 : ℕ) ≤
      1024 * ((D.d * D.m * D.k : ℕ) : ℝ) ^ (13 : ℕ) := by
    have e1 : ((D.m + D.k : ℕ) : ℝ) ^ (10 : ℕ) ≤
        (2 * ((D.d * D.m * D.k : ℕ) : ℝ)) ^ (10 : ℕ) := by gcongr
    have e2 : (D.d : ℝ) ^ (3 : ℕ) ≤ ((D.d * D.m * D.k : ℕ) : ℝ) ^ (3 : ℕ) := by gcongr
    calc ((D.m + D.k : ℕ) : ℝ) ^ (10 : ℕ) * (D.d : ℝ) ^ (3 : ℕ)
        ≤ (2 * ((D.d * D.m * D.k : ℕ) : ℝ)) ^ (10 : ℕ) *
            ((D.d * D.m * D.k : ℕ) : ℝ) ^ (3 : ℕ) :=
          mul_le_mul e1 e2 (by positivity) (by positivity)
      _ = 1024 * ((D.d * D.m * D.k : ℕ) : ℝ) ^ (13 : ℕ) := by ring
  have hMdle : ((D.m + D.k : ℕ) : ℝ) * (D.d : ℝ) ≤
      ((D.m + D.k : ℕ) : ℝ) ^ (10 : ℕ) * (D.d : ℝ) ^ (3 : ℕ) := by
    have e1 : ((D.m + D.k : ℕ) : ℝ) ≤ ((D.m + D.k : ℕ) : ℝ) ^ (10 : ℕ) := by
      simpa using pow_le_pow_right₀ hM1 (by norm_num : 1 ≤ 10)
    have e2 : (D.d : ℝ) ≤ (D.d : ℝ) ^ (3 : ℕ) := by
      simpa using pow_le_pow_right₀ hd1 (by norm_num : 1 ≤ 3)
    exact mul_le_mul e1 e2 (by linarith) (by positivity)
  have hN13 : ((D.d * D.m * D.k : ℕ) : ℝ) ^ (13 : ℕ) ≤
      Real.rpow ((D.d * D.m * D.k : ℕ) : ℝ) 100000000000000000000000 := by
    simp only [Real.rpow_eq_pow]
    rw [← Real.rpow_natCast (((D.d * D.m * D.k : ℕ) : ℝ)) 13]
    exact Real.rpow_le_rpow_of_exponent_le hN1 (by push_cast; norm_num)
  have hR0 : (0 : ℝ) ≤ Real.rpow ((D.d * D.m * D.k : ℕ) : ℝ) 100000000000000000000000 :=
    Real.rpow_nonneg (by linarith) _
  have hdelta : deltaLd 100000000000000000000000 (1 / 80000) ε D.q D.m D.d D.k =
      100000000000000000000000 *
          Real.rpow ((D.d * D.m * D.k : ℕ) : ℝ) 100000000000000000000000 *
        transportEnvelope D ε := rfl
  rw [hdelta]
  have step1 : ((D.m + D.k : ℕ) : ℝ) * (D.d : ℝ) * transportEnvelope D ε ≤
      ((D.m + D.k : ℕ) : ℝ) ^ (10 : ℕ) * (D.d : ℝ) ^ (3 : ℕ) * transportEnvelope D ε :=
    mul_le_mul_of_nonneg_right hMdle hT
  have step2 : ((D.m + D.k : ℕ) : ℝ) ^ (10 : ℕ) * (D.d : ℝ) ^ (3 : ℕ) *
      transportEnvelope D ε ≤
      1024 * ((D.d * D.m * D.k : ℕ) : ℝ) ^ (13 : ℕ) * transportEnvelope D ε :=
    mul_le_mul_of_nonneg_right hpoly hT
  have step3 : ((D.d * D.m * D.k : ℕ) : ℝ) ^ (13 : ℕ) * transportEnvelope D ε ≤
      Real.rpow ((D.d * D.m * D.k : ℕ) : ℝ) 100000000000000000000000 *
        transportEnvelope D ε :=
    mul_le_mul_of_nonneg_right hN13 hT
  linarith [hE, hL, step1, step2, step3, mul_nonneg hR0 hT]

end MIPStarRE.QPBT
