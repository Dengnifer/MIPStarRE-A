import MIPStarRE.QPBT.Games.ErrorFunctions
import MIPStarRE.QPBT.Test.PauliBasisTest
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity

/-! # Obstruction to absorbing the combined-line dimension factor

The first estimate in the printed combined-line proof contains the term
`m * epsilon ^ (1 / 4)`. Even capped by one, this term cannot be bounded by
a polynomial error in `m ^ 2 * epsilon` and `m * d / q`, uniformly over
admissible parameters. This is a scalar obstruction to that proof route,
not a counterexample to the existence of extended-line measurements.

## References

Paper `references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1134-1137`,
`eq:qld-combined-lines-consistency`, and blueprint `rem:qld-4-13-source-defects`.
The scaling argument is recorded in
`docs/paper-gaps/qpbt_combined-lines-error-term.tex`; issue #510 checks it on
the numerical domain of `exists_extendedLinesWitness`.
-/

namespace MIPStarRE.QPBT

open Filter Topology

/-- No polynomial error in the two printed arguments dominates even the capped
`m * epsilon ^ (1 / 4)` term of `eq:qld-combined-lines-consistency`.

This formalization-only obstruction uses admissible parameters
`m = 2 ^ (2 * n + 1)`, `d = 1`, `q = m ^ 3`, and `epsilon = m ^ (-4)`.
Both error arguments then equal `m ^ (-2)` and tend to zero, whereas the
capped term equals one. It does not assert that `lem:qld-4-13` is false:
an upper bound on a defect need not be attained by any strategy. See
`docs/paper-gaps/qpbt_combined-lines-error-term.tex` and issue #510. -/
theorem not_exists_combining_quarter_power_bound :
    ¬ ∃ f : ℝ → ℝ → ℝ, IsPolyErr₂ f ∧
      ∀ (P : AdmissibleParams) (ε : ℝ), 0 ≤ ε →
        min 1 ((P.m : ℝ) * ε ^ (1 / 4 : ℝ)) ≤
          f ((P.m : ℝ) ^ 2 * ε) ((P.m * P.d : ℕ) / (P.q : ℝ)) := by
  rintro ⟨f, ⟨C, r, s, _, hr, hs, hf⟩, hbound⟩
  let params (n : ℕ) : AdmissibleParams :=
    { m := 2 ^ (2 * n + 1)
      d := 1
      q := (2 ^ (2 * n + 1)) ^ 3
      hd := le_rfl
      hq := ⟨(2 * n + 1) * 3, ⟨3 * n + 1, by omega⟩, by rw [pow_mul]⟩
      hdvd := dvd_pow_self _ (by norm_num : 3 ≠ 0) }
  let dimension (n : ℕ) : ℝ := (params n).m
  have hdimension (n : ℕ) : 0 < dimension n := by
    dsimp [dimension, params]
    positivity
  have hdimensionTop : Tendsto dimension atTop atTop := by
    have hexponent : Tendsto (fun n : ℕ => 2 * n + 1) atTop atTop :=
      tendsto_atTop_mono (fun n => by change n ≤ 2 * n + 1; omega) tendsto_id
    simpa [dimension, params, Function.comp_def] using
      (tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1 : ℝ) < 2)).comp hexponent
  have hinv : Tendsto (fun n => (dimension n)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp hdimensionTop
  have hsmall : Tendsto (fun n => ((dimension n)⁻¹) ^ 2) atTop (𝓝 0) := by
    simpa using hinv.pow 2
  have hlimit : Tendsto
      (fun n => C * ((((dimension n)⁻¹) ^ 2) ^ r + (((dimension n)⁻¹) ^ 2) ^ s))
      atTop (𝓝 0) := by
    simpa using (hsmall.rpow_const_nhds_zero hr).add
      (hsmall.rpow_const_nhds_zero hs) |>.const_mul C
  have hone (n : ℕ) :
      1 ≤ C * ((((dimension n)⁻¹) ^ 2) ^ r + (((dimension n)⁻¹) ^ 2) ^ s) := by
    have hpos := hdimension n
    have hne := ne_of_gt hpos
    have hquarter : ((((dimension n)⁻¹) ^ 4) : ℝ) ^ (1 / 4 : ℝ) =
        (dimension n)⁻¹ := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (inv_nonneg.mpr hpos.le)]
      norm_num
    have hfirst : (dimension n) ^ 2 * ((dimension n)⁻¹) ^ 4 =
        ((dimension n)⁻¹) ^ 2 := by
      field_simp
    have hratio : (((params n).m * (params n).d : ℕ) : ℝ) / (params n).q =
        ((dimension n)⁻¹) ^ 2 := by
      simp only [params, dimension, mul_one, Nat.cast_pow]
      field_simp
    have h := hbound (params n) (((dimension n)⁻¹) ^ 4) (by positivity)
    change min 1 (dimension n * _) ≤ f (dimension n ^ 2 * _) _ at h
    rw [hquarter, mul_inv_cancel₀ hne, min_self, hfirst, hratio] at h
    exact h.trans (hf _ _ (sq_nonneg _) (sq_nonneg _)).2
  have : (1 : ℝ) ≤ 0 := ge_of_tendsto hlimit (Eventually.of_forall hone)
  norm_num at this

end MIPStarRE.QPBT
