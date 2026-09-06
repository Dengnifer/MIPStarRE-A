import MIPStarRE.QPBT.Games.ErrorFunctions
import MIPStarRE.QPBT.Test.LowDegreeGameTheorems
import MIPStarRE.QPBT.Test.SoundnessDefs
import Mathlib.Analysis.MeanInequalitiesPow

/-! # Scalar error bounds for combining polynomial measurements

This module proves three formalization-only scalar estimates: polynomial
bounds after conditioning, composition with the dimension factor retained, and
absorption into the global polynomial-pair error scale. The estimates quantify
over error functions and numerical parameters; they do not construct measurements.

## References

The auxiliary blueprint statements are `thm:qld-conditioned-polynomial-bound`,
`thm:qld-combining-polynomial-bound`, and `thm:qld-global-pair-error-bound` in
`blueprint/src/chapter/ch15_qpbt_combining.tex`. They support the calculations
in `lem:qld-xz-lines`, `lem:qld-4-13`, and `lem:qld-4-7` of
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:950-963,1134-1246`
and `:1278-1288,1402`. The corrected error notation and the retained dimension
factor are documented in `docs/paper-gaps/qpbt_combined-lines-error-term.tex`.
-/

namespace MIPStarRE.QPBT

/-- Additive polynomial errors remain polynomial after conditioning and insertion
of a polynomially small point error. The minimum uses the independent unit bound
for normalized POVM consistency, not a replacement measurement. This scalar lemma
supports `lem:qld-xz-lines`, paper lines 950--963; see issue #118 and
`docs/paper-gaps/qpbt_combined-lines-error-term.tex`. -/
theorem exists_conditioned_polynomial_bound (pointError : ℝ → ℝ)
    (hpoint : IsPolyErr pointError) (constant : ℝ) (hconstant : 1 ≤ constant)
    (pastingError : ℝ → ℝ → ℝ) (hpasting : IsPolyErr₂ pastingError) :
    ∃ lineError : ℝ → ℝ → ℝ, IsPolyErr₂ lineError ∧
      ∀ error ratio mass : ℝ, 0 ≤ error → 0 ≤ ratio →
        1 / 2 ≤ mass → mass ≤ 1 →
        min 1 (mass * pastingError ratio
          ((8 * pointError error + constant * (error + Real.sqrt error)) / mass) + ratio) ≤
          lineError error ratio := by
  obtain ⟨pointConstant, pointPower, hpointConstant, hpointPower, hpointBound⟩ := hpoint
  obtain ⟨pastingConstant, ratioPower, marginalPower, hpastingConstant,
    hratioPower, hmarginalPower, hpastingBound⟩ := hpasting
  let smallPower := min pointPower (1 / 2 : ℝ)
  let finalRatioPower := min ratioPower 1
  let marginalConstant := 8 * pointConstant + 2 * constant
  let powerConstant := (2 * marginalConstant) ^ marginalPower
  let finalConstant := pastingConstant * (1 + powerConstant) + 1
  have hsmall : 0 < smallPower := lt_min hpointPower (by norm_num)
  have hfinalRatio : 0 < finalRatioPower := lt_min hratioPower zero_lt_one
  have hmarginalConstant : 0 ≤ marginalConstant := by dsimp [marginalConstant]; linarith
  have hpowerConstant : 0 ≤ powerConstant := Real.rpow_nonneg (by positivity) _
  have hfinalConstant : 1 ≤ finalConstant := by
    dsimp [finalConstant]
    nlinarith
  refine ⟨fun error ratio => finalConstant *
    (error ^ (smallPower * marginalPower) + ratio ^ finalRatioPower),
    ⟨finalConstant, smallPower * marginalPower, finalRatioPower, hfinalConstant,
      mul_pos hsmall hmarginalPower, hfinalRatio, ?_⟩, ?_⟩
  · intro error ratio herror hratio
    exact ⟨mul_nonneg (by linarith) (add_nonneg (Real.rpow_nonneg herror _)
      (Real.rpow_nonneg hratio _)), le_rfl⟩
  intro error ratio mass herror hratio hmass hmassOne
  have hmassPos : 0 < mass := by linarith
  have herrorPower : 0 ≤ error ^ (smallPower * marginalPower) :=
    Real.rpow_nonneg herror _
  have hratioPowerNonneg : 0 ≤ ratio ^ finalRatioPower := Real.rpow_nonneg hratio _
  have hlarge (hlarge : 1 ≤ error ^ (smallPower * marginalPower) +
      ratio ^ finalRatioPower) :
      min 1 (mass * pastingError ratio
        ((8 * pointError error + constant * (error + Real.sqrt error)) / mass) + ratio) ≤
        finalConstant * (error ^ (smallPower * marginalPower) +
          ratio ^ finalRatioPower) := by
    refine (min_le_left _ _).trans ?_
    nlinarith [mul_nonneg (show 0 ≤ finalConstant - 1 by linarith)
      (add_nonneg herrorPower hratioPowerNonneg)]
  by_cases herrorOne : error ≤ 1
  · by_cases hratioOne : ratio ≤ 1
    · have hpointValue := hpointBound error herror
      have hpointSmall : pointError error ≤ pointConstant * error ^ smallPower :=
        hpointValue.2.trans (mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow_of_exponent_ge' herror herrorOne hsmall.le
            (min_le_left _ _)) (by linarith))
      have herrorSmall : error ≤ error ^ smallPower := by
        simpa using Real.rpow_le_rpow_of_exponent_ge' herror herrorOne hsmall.le
          (show smallPower ≤ 1 by exact (min_le_right _ _).trans (by norm_num))
      have hsqrtSmall : Real.sqrt error ≤ error ^ smallPower := by
        rw [Real.sqrt_eq_rpow]
        exact Real.rpow_le_rpow_of_exponent_ge' herror herrorOne hsmall.le
          (min_le_right _ _)
      have hmarginalNonneg : 0 ≤ 8 * pointError error +
          constant * (error + Real.sqrt error) :=
        add_nonneg (mul_nonneg (by norm_num) hpointValue.1)
          (mul_nonneg (by linarith) (add_nonneg herror (Real.sqrt_nonneg _)))
      have hmarginalSmall : 8 * pointError error +
          constant * (error + Real.sqrt error) ≤ marginalConstant * error ^ smallPower := by
        dsimp [marginalConstant]
        nlinarith [mul_le_mul_of_nonneg_left (add_le_add herrorSmall hsqrtSmall)
          (show 0 ≤ constant by linarith)]
      have hdivSmall : (8 * pointError error + constant * (error + Real.sqrt error)) /
          mass ≤ (2 * marginalConstant) * error ^ smallPower := by
        apply (div_le_iff₀ hmassPos).mpr
        exact hmarginalSmall.trans (by
          nlinarith [mul_nonneg hmarginalConstant (Real.rpow_nonneg herror smallPower),
            mul_nonneg (show 0 ≤ mass - 1 / 2 by linarith)
              (mul_nonneg hmarginalConstant (Real.rpow_nonneg herror smallPower))])
      have hdivPower : ((8 * pointError error + constant *
          (error + Real.sqrt error)) / mass) ^ marginalPower ≤
          powerConstant * error ^ (smallPower * marginalPower) := by
        calc
          _ ≤ ((2 * marginalConstant) * error ^ smallPower) ^ marginalPower :=
            Real.rpow_le_rpow (div_nonneg hmarginalNonneg hmassPos.le)
              hdivSmall hmarginalPower.le
          _ = _ := by rw [Real.mul_rpow (by positivity) (Real.rpow_nonneg herror _),
            ← Real.rpow_mul herror]
      have hratioSmall : ratio ^ ratioPower ≤ ratio ^ finalRatioPower :=
        Real.rpow_le_rpow_of_exponent_ge' hratio hratioOne hfinalRatio.le
          (min_le_left _ _)
      have hratioLinear : ratio ≤ ratio ^ finalRatioPower := by
        simpa using Real.rpow_le_rpow_of_exponent_ge' hratio hratioOne hfinalRatio.le
          (min_le_right _ _)
      have hpastingValue := hpastingBound ratio _ hratio
        (div_nonneg hmarginalNonneg hmassPos.le)
      refine (min_le_right _ _).trans ?_
      calc
        _ ≤ pastingError ratio
            ((8 * pointError error + constant * (error + Real.sqrt error)) / mass) +
            ratio := add_le_add (mul_le_of_le_one_left hpastingValue.1 hmassOne) le_rfl
        _ ≤ pastingConstant * (ratio ^ finalRatioPower +
            powerConstant * error ^ (smallPower * marginalPower)) +
            ratio ^ finalRatioPower :=
          add_le_add (hpastingValue.2.trans (mul_le_mul_of_nonneg_left
            (add_le_add hratioSmall hdivPower) (by linarith))) hratioLinear
        _ ≤ _ := by
          dsimp [finalConstant]
          nlinarith [mul_nonneg
            (mul_nonneg (show 0 ≤ pastingConstant by linarith) hpowerConstant)
            hratioPowerNonneg,
            mul_nonneg (show 0 ≤ pastingConstant by linarith) herrorPower]
    · apply hlarge
      linarith [Real.one_le_rpow (le_of_not_ge hratioOne) hfinalRatio.le]
  · apply hlarge
    linarith [Real.one_le_rpow (le_of_not_ge herrorOne)
      (mul_pos hsmall hmarginalPower).le]

/-- Polynomial absorption for the first combining route, including large errors.
The independent unit bound on consistency accounts for the minimum. The factor
`dimension` is retained, as required by the correction to `lem:qld-4-13` in
`docs/paper-gaps/qpbt_combined-lines-error-term.tex`, paper lines 1134--1246. -/
theorem exists_combining_polynomial_bound (pointError : ℝ → ℝ)
    (hpoint : IsPolyErr pointError) (lineError : ℝ → ℝ → ℝ)
    (hline : IsPolyErr₂ lineError) (constant : ℝ) (hconstant : 0 ≤ constant) :
    ∃ combinedError : ℝ → ℝ → ℝ, IsPolyErr₂ combinedError ∧
      ∀ error ratio dimension : ℝ, 0 ≤ error → 0 ≤ ratio → 1 ≤ dimension →
        min 1 (constant * ((pointError error) ^ (1 / 2 : ℝ) + Real.sqrt dimension *
          ((lineError error ratio) ^ (1 / 4 : ℝ) + (pointError error) ^ (1 / 4 : ℝ) +
            error ^ (1 / 4 : ℝ)))) ≤ dimension * combinedError error ratio := by
  obtain ⟨pointConstant, pointPower, hpointConstant, hpointPower, hpointBound⟩ := hpoint
  obtain ⟨lineConstant, errorPower, ratioPower, hlineConstant,
    herrorPower, hratioPower, hlineBound⟩ := hline
  let finalPower := min (pointPower / 4) (min (errorPower / 4) (1 / 4 : ℝ))
  let coefficient := pointConstant ^ (1 / 2 : ℝ) + lineConstant ^ (1 / 4 : ℝ) +
    pointConstant ^ (1 / 4 : ℝ) + 1
  let finalConstant := 1 + constant * coefficient
  have hfinalPower : 0 < finalPower := by dsimp [finalPower]; positivity
  have hcoefficient : 0 ≤ coefficient := by dsimp [coefficient]; positivity
  have hfinalConstant : 1 ≤ finalConstant := by
    dsimp [finalConstant]
    linarith [mul_nonneg hconstant hcoefficient]
  refine ⟨fun error ratio => finalConstant *
    (error ^ finalPower + ratio ^ (ratioPower / 4)),
    ⟨finalConstant, finalPower, ratioPower / 4, hfinalConstant, hfinalPower,
      by positivity, ?_⟩, ?_⟩
  · intro error ratio herror hratio
    exact ⟨mul_nonneg (by linarith) (add_nonneg (Real.rpow_nonneg herror _)
      (Real.rpow_nonneg hratio _)), le_rfl⟩
  intro error ratio dimension herror hratio hdimension
  have hdimensionNonneg : 0 ≤ dimension := by linarith
  have herrorTerm : 0 ≤ error ^ finalPower := Real.rpow_nonneg herror _
  have hratioTerm : 0 ≤ ratio ^ (ratioPower / 4) := Real.rpow_nonneg hratio _
  by_cases herrorOne : error ≤ 1
  · have hpointValue := hpointBound error herror
    have hlineValue := hlineBound error ratio herror hratio
    have hpointRoot (power : ℝ) (hpower : 0 ≤ power)
        (hsmall : finalPower ≤ pointPower * power) :
        (pointError error) ^ power ≤ pointConstant ^ power * error ^ finalPower := by
      calc
        _ ≤ (pointConstant * error ^ pointPower) ^ power :=
          Real.rpow_le_rpow hpointValue.1 hpointValue.2 hpower
        _ = pointConstant ^ power * error ^ (pointPower * power) := by
          rw [Real.mul_rpow (by linarith) (Real.rpow_nonneg herror _),
            ← Real.rpow_mul herror]
        _ ≤ _ := mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow_of_exponent_ge' herror herrorOne hfinalPower.le hsmall)
          (Real.rpow_nonneg (by linarith) _)
    have hpointQuarter := hpointRoot (1 / 4) (by norm_num)
      (by
        have := min_le_left (pointPower / 4) (min (errorPower / 4) (1 / 4 : ℝ))
        dsimp [finalPower]
        linarith)
    have hpointHalf := hpointRoot (1 / 2) (by norm_num)
      (by
        have := min_le_left (pointPower / 4) (min (errorPower / 4) (1 / 4 : ℝ))
        dsimp [finalPower]
        linarith)
    have hlineQuarter : (lineError error ratio) ^ (1 / 4 : ℝ) ≤
        lineConstant ^ (1 / 4 : ℝ) * (error ^ finalPower + ratio ^ (ratioPower / 4)) := by
      calc
        _ ≤ (lineConstant * (error ^ errorPower + ratio ^ ratioPower)) ^ (1 / 4 : ℝ) :=
          Real.rpow_le_rpow hlineValue.1 hlineValue.2 (by norm_num)
        _ = lineConstant ^ (1 / 4 : ℝ) *
            (error ^ errorPower + ratio ^ ratioPower) ^ (1 / 4 : ℝ) := by
          rw [Real.mul_rpow (by linarith) (by positivity)]
        _ ≤ lineConstant ^ (1 / 4 : ℝ) *
            ((error ^ errorPower) ^ (1 / 4 : ℝ) +
              (ratio ^ ratioPower) ^ (1 / 4 : ℝ)) :=
          mul_le_mul_of_nonneg_left
            (Real.rpow_add_le_add_rpow (Real.rpow_nonneg herror _)
              (Real.rpow_nonneg hratio _) (by norm_num) (by norm_num))
            (Real.rpow_nonneg (by linarith) _)
        _ ≤ _ := by
          rw [← Real.rpow_mul herror, ← Real.rpow_mul hratio]
          apply mul_le_mul_of_nonneg_left _ (Real.rpow_nonneg (by linarith) _)
          apply add_le_add _ (by simp [div_eq_mul_inv])
          apply Real.rpow_le_rpow_of_exponent_ge' herror herrorOne hfinalPower.le
          have hsmall : finalPower ≤ errorPower / 4 :=
            (min_le_right _ _).trans (min_le_left _ _)
          linarith
    have herrorQuarter : error ^ (1 / 4 : ℝ) ≤ error ^ finalPower :=
      Real.rpow_le_rpow_of_exponent_ge' herror herrorOne hfinalPower.le
        ((min_le_right _ _).trans (min_le_right _ _))
    have hsqrt : Real.sqrt dimension ≤ dimension := by
      nlinarith [Real.sq_sqrt hdimensionNonneg, Real.sqrt_nonneg dimension]
    have hsum : (pointError error) ^ (1 / 2 : ℝ) + Real.sqrt dimension *
        ((lineError error ratio) ^ (1 / 4 : ℝ) + (pointError error) ^ (1 / 4 : ℝ) +
          error ^ (1 / 4 : ℝ)) ≤
        dimension * (coefficient * (error ^ finalPower + ratio ^ (ratioPower / 4))) := by
      have hrootNonneg : 0 ≤ (lineError error ratio) ^ (1 / 4 : ℝ) +
          (pointError error) ^ (1 / 4 : ℝ) + error ^ (1 / 4 : ℝ) :=
        add_nonneg (add_nonneg (Real.rpow_nonneg hlineValue.1 _)
          (Real.rpow_nonneg hpointValue.1 _)) (Real.rpow_nonneg herror _)
      have hrootSum := add_le_add (add_le_add hlineQuarter hpointQuarter) herrorQuarter
      have hscaled := mul_le_mul hsqrt hrootSum hrootNonneg hdimensionNonneg
      have hpointScaled := mul_le_mul_of_nonneg_right hdimension
        (Real.rpow_nonneg hpointValue.1 (1 / 2 : ℝ))
      dsimp [coefficient]
      nlinarith [mul_nonneg hdimensionNonneg
        (mul_nonneg (Real.rpow_nonneg (by linarith : 0 ≤ pointConstant) (1 / 2 : ℝ))
          hratioTerm),
        mul_nonneg hdimensionNonneg
          (mul_nonneg (Real.rpow_nonneg (by linarith : 0 ≤ pointConstant) (1 / 4 : ℝ))
            hratioTerm),
        mul_le_mul_of_nonneg_left hpointHalf hdimensionNonneg,
        mul_nonneg hdimensionNonneg hratioTerm]
    refine (min_le_right _ _).trans ((mul_le_mul_of_nonneg_left hsum hconstant).trans ?_)
    dsimp [finalConstant]
    nlinarith [mul_nonneg hdimensionNonneg (add_nonneg herrorTerm hratioTerm)]
  · refine (min_le_left _ _).trans ?_
    have hone := Real.one_le_rpow (le_of_not_ge herrorOne) hfinalPower.le
    have hsumOne : 1 ≤ finalConstant * (error ^ finalPower + ratio ^ (ratioPower / 4)) := by
      nlinarith [mul_nonneg (show 0 ≤ finalConstant - 1 by linarith)
        (add_nonneg herrorTerm hratioTerm)]
    nlinarith [mul_nonneg (show 0 ≤ dimension - 1 by linarith)
      (show 0 ≤ finalConstant * (error ^ finalPower + ratio ^ (ratioPower / 4)) by linarith)]

set_option maxHeartbeats 800000 in
/-- Scalar sufficiency of the established first route for the global-pair error.
The input of low-degree soundness includes `error` as a positive slack when
`error > 0`. The cap uses the independent unit bound on a consistency defect.
This is the numerical substitution at paper `lem:qld-4-7`, lines 1278--1288
and 1402, not a construction of its measurements or a game transport theorem.
See `docs/paper-gaps/qpbt_combined-lines-error-term.tex`. -/
theorem exists_globalPair_error_bound (pointError : ℝ → ℝ)
    (hpoint : IsPolyErr pointError) (combinedError : ℝ → ℝ → ℝ)
    (hcombined : IsPolyErr₂ combinedError)
    (combineConstant soundnessConstant soundnessPower finalScale : ℝ)
    (hcombineConstant : 0 ≤ combineConstant) (hsoundnessConstant : 1 ≤ soundnessConstant)
    (hsoundnessPower : 0 < soundnessPower) (hsoundnessPowerOne : soundnessPower ≤ 1)
    (hfinalScale : 0 ≤ finalScale) :
    ∃ finalConstant finalPower : ℝ, 1 < finalConstant ∧ 0 < finalPower ∧ finalPower < 1 ∧
      ∀ (params : AdmissibleParams) (error : ℝ), 0 ≤ error →
        min 1 (finalScale *
          (deltaLd soundnessConstant soundnessPower
              (combineConstant * (params.m : ℝ) *
                combinedError error ((params.m * params.d : ℕ) / (params.q : ℝ)) + error)
              params.q (2 * params.m + 2) params.d 1 +
            Real.sqrt (pointError error) + ((params.m * params.d : ℕ) / (params.q : ℝ)))) ≤
          deltaQld finalConstant finalPower error params.m params.d params.q := by
  obtain ⟨pointConstant, pointPower, hpointConstant, hpointPower, hpointBound⟩ := hpoint
  obtain ⟨lineConstant, errorPower, ratioPower, hlineConstant,
    herrorPower, hratioPower, hlineBound⟩ := hcombined
  let finalPower := min (1 / 2 : ℝ) (min soundnessPower
    (min (errorPower * soundnessPower)
      (min (ratioPower * soundnessPower) (pointPower / 2))))
  have hfinalPower : 0 < finalPower := by
    dsimp [finalPower]
    positivity
  have hhalf : finalPower ≤ 1 / 2 := min_le_left _ _
  have hpower : finalPower ≤ soundnessPower :=
    (min_le_right _ _).trans (min_le_left _ _)
  have herrorExponent : finalPower ≤ errorPower * soundnessPower :=
    (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hratioExponent : finalPower ≤ ratioPower * soundnessPower :=
    (min_le_right _ _).trans ((min_le_right _ _).trans
      ((min_le_right _ _).trans (min_le_left _ _)))
  have hpointExponent : finalPower ≤ pointPower / 2 :=
    (min_le_right _ _).trans ((min_le_right _ _).trans
      ((min_le_right _ _).trans (min_le_right _ _)))
  let lineGrowth := soundnessPower + ratioPower * soundnessPower
  let growth := soundnessConstant + lineGrowth + 1
  let lineCoefficient := soundnessConstant * (4 : ℝ) ^ soundnessConstant *
    ((combineConstant * lineConstant) ^ soundnessPower + 2)
  let coefficient := finalScale * (lineCoefficient + Real.sqrt pointConstant + 1)
  let finalConstant := coefficient + growth + 2
  have hlineGrowth : 0 ≤ lineGrowth := by dsimp [lineGrowth]; positivity
  have hgrowth : 1 ≤ growth := by dsimp [growth]; linarith
  have hlineCoefficient : 0 ≤ lineCoefficient := by dsimp [lineCoefficient]; positivity
  have hcoefficient : 0 ≤ coefficient := by dsimp [coefficient]; positivity
  have hfinalConstant : 1 < finalConstant := by dsimp [finalConstant]; linarith
  have hcoefficient_le : coefficient ≤ finalConstant := by dsimp [finalConstant]; linarith
  have hgrowth_le : growth ≤ finalConstant := by dsimp [finalConstant]; linarith
  refine ⟨finalConstant, finalPower, hfinalConstant, hfinalPower, by linarith, ?_⟩
  intro params error herror
  let size : ℝ := ((params.m * params.d : ℕ) : ℝ)
  let extendedSize : ℝ := (((2 * params.m + 2) * params.d : ℕ) : ℝ)
  let ratio : ℝ := size / (params.q : ℝ)
  let envelope := error ^ finalPower + (params.q : ℝ) ^ (-finalPower) +
    (2 : ℝ) ^ (-(finalPower * size))
  have hm : (1 : ℝ) ≤ (params.m : ℝ) := by exact_mod_cast params.one_le_m
  have hd : (1 : ℝ) ≤ (params.d : ℝ) := by exact_mod_cast params.hd
  have hsize : 1 ≤ size := by
    dsimp [size]
    exact_mod_cast Nat.mul_pos params.one_le_m params.hd
  have hsize0 : 0 ≤ size := by linarith
  have hsizePos : 0 < size := by linarith
  have hmSize : (params.m : ℝ) ≤ size := by dsimp [size]; push_cast; nlinarith
  have hq : (1 : ℝ) ≤ (params.q : ℝ) := by
    obtain ⟨power, _, hq⟩ := params.hq
    rw [hq]
    exact_mod_cast Nat.one_le_pow _ _ (by norm_num)
  have hq0 : 0 ≤ (params.q : ℝ) := by linarith
  have hratio : 0 ≤ ratio := by dsimp [ratio]; positivity
  have henv : 0 ≤ envelope := by dsimp [envelope]; positivity
  have henvError : error ^ finalPower ≤ envelope := by
    dsimp [envelope]
    linarith [Real.rpow_nonneg hq0 (-finalPower),
      Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 2) (-(finalPower * size))]
  have henvField : (params.q : ℝ) ^ (-finalPower) ≤ envelope := by
    dsimp [envelope]
    linarith [Real.rpow_nonneg herror finalPower,
      Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 2) (-(finalPower * size))]
  change min 1 (finalScale *
    (deltaLd soundnessConstant soundnessPower
      (combineConstant * (params.m : ℝ) * combinedError error ratio + error)
      params.q (2 * params.m + 2) params.d 1 + Real.sqrt (pointError error) + ratio)) ≤
    finalConstant * size ^ finalConstant * envelope
  by_cases herrorOne : error ≤ 1
  · have herrorMono (power : ℝ) (hpower : finalPower ≤ power) :
        error ^ power ≤ error ^ finalPower :=
      Real.rpow_le_rpow_of_exponent_ge' herror herrorOne hfinalPower.le hpower
    have hfieldMono (power : ℝ) (hpower : finalPower ≤ power) :
        (params.q : ℝ) ^ (-power) ≤ (params.q : ℝ) ^ (-finalPower) :=
      Real.rpow_le_rpow_of_exponent_le hq (neg_le_neg hpower)
    have hsizeRatio : 1 ≤ size ^ (ratioPower * soundnessPower) :=
      Real.one_le_rpow hsize (mul_nonneg hratioPower.le hsoundnessPower.le)
    have hsizeLine : 1 ≤ size ^ lineGrowth := Real.one_le_rpow hsize hlineGrowth
    have hpolySum : error ^ (errorPower * soundnessPower) +
        ratio ^ (ratioPower * soundnessPower) ≤
        size ^ (ratioPower * soundnessPower) * envelope := by
      have hratioEq : ratio ^ (ratioPower * soundnessPower) =
          size ^ (ratioPower * soundnessPower) *
            (params.q : ℝ) ^ (-(ratioPower * soundnessPower)) := by
        dsimp [ratio]
        rw [Real.div_rpow hsize0 hq0, div_eq_mul_inv, Real.rpow_neg hq0]
      rw [hratioEq]
      have hfirst := (herrorMono _ herrorExponent).trans
        (le_mul_of_one_le_left (Real.rpow_nonneg herror _) hsizeRatio)
      have hsecond := mul_le_mul_of_nonneg_left (hfieldMono _ hratioExponent)
        (Real.rpow_nonneg hsize0 (ratioPower * soundnessPower))
      have hsum := add_le_add hfirst hsecond
      refine hsum.trans ?_
      dsimp [envelope]
      nlinarith [mul_nonneg (Real.rpow_nonneg hsize0 (ratioPower * soundnessPower))
        (Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 2) (-(finalPower * size)))]
    have hcombinedValue := hlineBound error ratio herror hratio
    have hbaseNonneg : 0 ≤
        combineConstant * (params.m : ℝ) * combinedError error ratio :=
      mul_nonneg (mul_nonneg hcombineConstant (by positivity)) hcombinedValue.1
    have hpoly : (combinedError error ratio) ^ soundnessPower ≤
        lineConstant ^ soundnessPower *
          (size ^ (ratioPower * soundnessPower) * envelope) := by
      calc
        _ ≤ (lineConstant * (error ^ errorPower + ratio ^ ratioPower)) ^ soundnessPower :=
          Real.rpow_le_rpow hcombinedValue.1 hcombinedValue.2 hsoundnessPower.le
        _ = lineConstant ^ soundnessPower *
            (error ^ errorPower + ratio ^ ratioPower) ^ soundnessPower := by
          rw [Real.mul_rpow (by linarith) (by positivity)]
        _ ≤ lineConstant ^ soundnessPower *
            (error ^ (errorPower * soundnessPower) + ratio ^ (ratioPower * soundnessPower)) := by
          refine mul_le_mul_of_nonneg_left ?_ (Real.rpow_nonneg (by linarith) _)
          simpa only [← Real.rpow_mul herror, ← Real.rpow_mul hratio] using
            Real.rpow_add_le_add_rpow (Real.rpow_nonneg herror errorPower)
              (Real.rpow_nonneg hratio ratioPower) hsoundnessPower.le hsoundnessPowerOne
        _ ≤ _ := mul_le_mul_of_nonneg_left hpolySum (Real.rpow_nonneg (by linarith) _)
    have hproduct : (combineConstant * (params.m : ℝ) * combinedError error ratio) ^
        soundnessPower ≤ (combineConstant * lineConstant) ^ soundnessPower *
          size ^ lineGrowth * envelope := by
      rw [Real.mul_rpow (by positivity) hcombinedValue.1]
      calc
        _ ≤ (combineConstant * size) ^ soundnessPower *
            (lineConstant ^ soundnessPower *
              (size ^ (ratioPower * soundnessPower) * envelope)) :=
          mul_le_mul (Real.rpow_le_rpow (by positivity)
            (mul_le_mul_of_nonneg_left hmSize hcombineConstant) hsoundnessPower.le)
            hpoly (Real.rpow_nonneg hcombinedValue.1 _) (by positivity)
        _ = _ := by
          dsimp [lineGrowth]
          rw [Real.mul_rpow hcombineConstant hsize0,
            Real.mul_rpow hcombineConstant (by linarith), Real.rpow_add hsizePos]
          ring
    have hinput : (combineConstant * (params.m : ℝ) * combinedError error ratio + error) ^
        soundnessPower ≤ ((combineConstant * lineConstant) ^ soundnessPower + 1) *
          size ^ lineGrowth * envelope := by
      have hsplit := Real.rpow_add_le_add_rpow
        hbaseNonneg herror
        hsoundnessPower.le hsoundnessPowerOne
      have hsum := hsplit.trans (add_le_add hproduct
        ((herrorMono _ hpower).trans henvError))
      refine hsum.trans ?_
      nlinarith [mul_le_mul_of_nonneg_right hsizeLine henv]
    have hextended : size ≤ extendedSize ∧ extendedSize ≤ 4 * size := by
      dsimp [size, extendedSize]
      push_cast
      constructor <;> nlinarith
    have hextended0 : 0 ≤ extendedSize := hsize0.trans hextended.1
    have hexponential : (2 : ℝ) ^ (-(soundnessPower * extendedSize)) ≤
        (2 : ℝ) ^ (-(finalPower * size)) := by
      apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
      exact neg_le_neg ((mul_le_mul_of_nonneg_right hpower hsize0).trans
        (mul_le_mul_of_nonneg_left hextended.1 hsoundnessPower.le))
    have hrest : (params.q : ℝ) ^ (-soundnessPower) +
        (2 : ℝ) ^ (-(soundnessPower * extendedSize)) ≤ envelope := by
      have hsum := add_le_add (hfieldMono _ hpower) hexponential
      dsimp [envelope]
      linarith [Real.rpow_nonneg herror finalPower]
    have hbracket :
        (combineConstant * (params.m : ℝ) * combinedError error ratio + error) ^ soundnessPower +
          (params.q : ℝ) ^ (-soundnessPower) +
          (2 : ℝ) ^ (-(soundnessPower * extendedSize)) ≤
        ((combineConstant * lineConstant) ^ soundnessPower + 2) *
          size ^ lineGrowth * envelope := by
      have hsum := add_le_add hinput hrest
      nlinarith [mul_le_mul_of_nonneg_right hsizeLine henv]
    have hprefactor : soundnessConstant * extendedSize ^ soundnessConstant ≤
        soundnessConstant * ((4 : ℝ) ^ soundnessConstant * size ^ soundnessConstant) := by
      apply mul_le_mul_of_nonneg_left _ (by linarith)
      calc
        _ ≤ (4 * size) ^ soundnessConstant :=
          Real.rpow_le_rpow hextended0 hextended.2 (by linarith)
        _ = _ := Real.mul_rpow (by norm_num) hsize0
    have hld : deltaLd soundnessConstant soundnessPower
        (combineConstant * (params.m : ℝ) * combinedError error ratio + error)
        params.q (2 * params.m + 2) params.d 1 ≤
        lineCoefficient * size ^ (soundnessConstant + lineGrowth) * envelope := by
      have heq : deltaLd soundnessConstant soundnessPower
          (combineConstant * (params.m : ℝ) * combinedError error ratio + error)
          params.q (2 * params.m + 2) params.d 1 =
          soundnessConstant * extendedSize ^ soundnessConstant *
            ((combineConstant * (params.m : ℝ) * combinedError error ratio + error) ^
              soundnessPower + (params.q : ℝ) ^ (-soundnessPower) +
              (2 : ℝ) ^ (-(soundnessPower * extendedSize))) := by
        simp only [deltaLd, extendedSize, Nat.mul_one, Real.rpow_eq_pow,
          Nat.mul_comm params.d (2 * params.m + 2)]
      rw [heq]
      refine (mul_le_mul hprefactor hbracket (by positivity) (by positivity)).trans_eq ?_
      dsimp [lineCoefficient]
      rw [Real.rpow_add hsizePos soundnessConstant lineGrowth]
      ring
    have hroot : Real.sqrt (pointError error) ≤ Real.sqrt pointConstant * envelope := by
      calc
        _ ≤ Real.sqrt (pointConstant * error ^ pointPower) :=
          Real.sqrt_le_sqrt (hpointBound error herror).2
        _ = Real.sqrt pointConstant * error ^ (pointPower / 2) := by
          rw [Real.sqrt_mul (by linarith)]
          congr 1
          rw [Real.sqrt_eq_rpow, ← Real.rpow_mul herror]
          congr 1
          ring
        _ ≤ _ := mul_le_mul_of_nonneg_left
          ((herrorMono _ hpointExponent).trans henvError) (Real.sqrt_nonneg _)
    have hratioBound : ratio ≤ size * envelope := by
      dsimp [ratio]
      rw [div_eq_mul_inv, ← Real.rpow_neg_one]
      exact mul_le_mul_of_nonneg_left
        ((hfieldMono 1 (by linarith)).trans henvField) hsize0
    have hsizePower : size ^ (soundnessConstant + lineGrowth) ≤ size ^ growth :=
      Real.rpow_le_rpow_of_exponent_le hsize (by dsimp [growth]; linarith)
    have hsizeGrowth : size ≤ size ^ growth := by
      simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hsize hgrowth
    have honeGrowth : 1 ≤ size ^ growth := Real.one_le_rpow hsize (by linarith)
    have hldBound := hld.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hsizePower hlineCoefficient) henv)
    have hrootBound := hroot.trans (le_mul_of_one_le_left
      (mul_nonneg (Real.sqrt_nonneg _) henv) honeGrowth)
    have hratioGrowth := hratioBound.trans (mul_le_mul_of_nonneg_right hsizeGrowth henv)
    have hsum := mul_le_mul_of_nonneg_left
      (add_le_add (add_le_add hldBound hrootBound) hratioGrowth) hfinalScale
    have hfinal : finalScale *
        (deltaLd soundnessConstant soundnessPower
          (combineConstant * (params.m : ℝ) * combinedError error ratio + error)
          params.q (2 * params.m + 2) params.d 1 + Real.sqrt (pointError error) + ratio) ≤
        coefficient * size ^ growth * envelope := by
      exact hsum.trans_eq (by dsimp [coefficient]; ring)
    refine (min_le_right _ _).trans (hfinal.trans ?_)
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul hcoefficient_le
        (Real.rpow_le_rpow_of_exponent_le hsize hgrowth_le)
        (Real.rpow_nonneg hsize0 growth) (by linarith)) henv
  · have herrorLarge : 1 ≤ error := le_of_not_ge herrorOne
    have henvOne : 1 ≤ envelope :=
      (Real.one_le_rpow herrorLarge hfinalPower.le).trans henvError
    have hsizeOne : 1 ≤ size ^ finalConstant :=
      Real.one_le_rpow hsize (by linarith)
    have hprefactorOne : 1 ≤ finalConstant * size ^ finalConstant := by
      simpa only [one_mul] using mul_le_mul hfinalConstant.le hsizeOne
        (by norm_num : (0 : ℝ) ≤ 1) (by linarith : 0 ≤ finalConstant)
    refine (min_le_left _ _).trans ?_
    simpa only [one_mul] using mul_le_mul hprefactorOne henvOne
      (by norm_num : (0 : ℝ) ≤ 1) (zero_le_one.trans hprefactorOne)

end MIPStarRE.QPBT
