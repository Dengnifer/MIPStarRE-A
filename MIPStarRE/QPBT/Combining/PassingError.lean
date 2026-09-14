import MIPStarRE.QPBT.Games.ErrorFunctions

/-! # Capped scalar envelope for direct-game error bounds

This module gives a concrete polynomial envelope for a scalar expression assembled from
seven prospective rejection bounds in the directly indexed extended-line game. It is a
formalization-only arithmetic auxiliary: it does not prove that any game branch satisfies
one of these bounds, nor does it prove a passing-value theorem.

The cap by one records the independent fact that a rejection probability is at most one.
It is essential for the polynomial-error contract: the uncapped function
`2 * x + Real.sqrt x + y` cannot be bounded by one positive power of `x` both near zero
and at infinity.

## References

- `references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1279-1288`
- Parent issue #119 and arithmetic issue #326
-/

namespace MIPStarRE.QPBT

/-- The concrete two-variable polynomial envelope for the capped scalar bound. -/
noncomputable def directPassingErrorEnvelope (x y : ℝ) : ℝ :=
  3 * (Real.sqrt x + y)

/-- The direct passing-error envelope obeys the shared two-variable polynomial-error
contract, with prefactor `3` and exponents `1 / 2` and `1`. -/
theorem directPassingErrorEnvelope_isPolyErr₂ : IsPolyErr₂ directPassingErrorEnvelope := by
  refine ⟨3, 1 / 2, 1, by norm_num, by norm_num, by norm_num, ?_⟩
  intro x y hx hy
  constructor
  · exact mul_nonneg (by norm_num) (add_nonneg (Real.sqrt_nonneg x) hy)
  · simp [directPassingErrorEnvelope, Real.sqrt_eq_rpow]

/-- A positive second input makes the direct passing-error envelope positive. -/
theorem directPassingErrorEnvelope_pos (x y : ℝ) (hy : 0 < y) :
    0 < directPassingErrorEnvelope x y := by
  dsimp [directPassingErrorEnvelope]
  nlinarith [Real.sqrt_nonneg x]

/-- The proposed seven-term scalar error is bounded by nine times the uncapped
linear-square-root expression. The variables are only nonnegative real numbers here;
no game-level branch estimate is asserted. -/
theorem seven_branch_scalar_error_le (Q L r : ℝ) (hQ : 0 ≤ Q) (hL : 0 ≤ L)
    (hr : 0 ≤ r) :
    Q + 16 * L + 4 * Real.sqrt (Q + 2 * L) + 5 * r ≤
      9 * (2 * (Q + L) + Real.sqrt (Q + L) + r) := by
  have hQL : 0 ≤ Q + L := by linarith
  have hQ2L : 0 ≤ Q + 2 * L := by linarith
  have hroot : Real.sqrt (Q + 2 * L) ≤ 2 * Real.sqrt (Q + L) := by
    nlinarith [Real.sq_sqrt hQL, Real.sq_sqrt hQ2L,
      Real.sqrt_nonneg (Q + L), Real.sqrt_nonneg (Q + 2 * L)]
  nlinarith [Real.sqrt_nonneg (Q + L)]

private theorem min_linear_sqrt_le_directPassingErrorEnvelope (x y : ℝ)
    (hx : 0 ≤ x) (hy : 0 ≤ y) :
    min 1 (2 * x + Real.sqrt x + y) ≤ directPassingErrorEnvelope x y := by
  by_cases hxOne : x ≤ 1
  · have hsqrtOne : Real.sqrt x ≤ 1 := by
      simpa using Real.sqrt_le_sqrt hxOne
    have hxSqrt : x ≤ Real.sqrt x := by
      nlinarith [Real.sq_sqrt hx, Real.sqrt_nonneg x]
    exact (min_le_right _ _).trans (by
      dsimp [directPassingErrorEnvelope]
      nlinarith)
  · have hsqrtOne : 1 ≤ Real.sqrt x := by
      have hxOne' : 1 ≤ x := le_of_not_ge hxOne
      simpa using Real.sqrt_le_sqrt hxOne'
    exact (min_le_left _ _).trans (by
      dsimp [directPassingErrorEnvelope]
      nlinarith [Real.sqrt_nonneg x])

/-- After averaging the seven scalar contributions by the nine equally weighted game
branches and applying the probability cap, the result is bounded by the concrete
polynomial envelope. This theorem assumes only the displayed nonnegative scalar inputs;
it does not establish the unfinished branch bounds that would supply them. -/
theorem seven_branch_capped_error_le_directPassingErrorEnvelope
    (Q L r : ℝ) (hQ : 0 ≤ Q) (hL : 0 ≤ L) (hr : 0 ≤ r) :
    min 1 ((Q + 16 * L + 4 * Real.sqrt (Q + 2 * L) + 5 * r) / 9) ≤
      directPassingErrorEnvelope (Q + L) r := by
  have hraw := seven_branch_scalar_error_le Q L r hQ hL hr
  have hdiv :
      (Q + 16 * L + 4 * Real.sqrt (Q + 2 * L) + 5 * r) / 9 ≤
        2 * (Q + L) + Real.sqrt (Q + L) + r := by
    nlinarith
  exact (min_le_min_left 1 hdiv).trans
    (min_linear_sqrt_le_directPassingErrorEnvelope (Q + L) r (by linarith) hr)

end MIPStarRE.QPBT
