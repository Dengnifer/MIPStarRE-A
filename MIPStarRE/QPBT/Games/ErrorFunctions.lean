import MIPStarRE.LDT.Basic.ParametersBase

/-! # Polynomial error predicates

Shared quantitative predicates for the polynomial-error bounds in QPBT
chapters 12, 14, and 15.

## References

These are formalization-only auxiliaries for polynomially small QPBT error
functions. The one-parameter form includes the explicit square-root witnesses
in paper chapter 14; the two-parameter form is used by `lem:pasting` in paper
chapter 6.
-/

namespace MIPStarRE.QPBT

/-- A nonnegative one-parameter error function bounded by a positive real power.

**Local fix:** The prefactor and exponent are quantified separately. Paper
chapter 14 explicitly obtains `sqrt ε` at
`14_analysis_of_the_pauli_basis_test.tex:508-520,649-676`, which the coupled
constant in the shorthand at `04_preliminaries.tex:26-29` cannot bound on all
positive inputs. The correction is documented in
`docs/paper-gaps/qpbt_polynomial-error-square-root.tex` and tracked by issue
#16. -/
def IsPolyErr (f : ℝ → ℝ) : Prop :=
  ∃ C r : ℝ, 1 ≤ C ∧ 0 < r ∧ ∀ x, 0 ≤ x →
    0 ≤ f x ∧ f x ≤ C * Real.rpow x r

/-- A nonnegative two-parameter error function bounded by a sum of positive
real powers.

This is the polynomial-error convention used by `lem:pasting` at
`06_nonlocal_games_and_mipstar.tex:518-524`: the bound may remain positive on
either coordinate axis and is forced to vanish when both errors vanish.  The
former product encoding incorrectly forced the pasting error to vanish whenever
either input was zero; see `docs/paper-gaps/qpbt_pasting-product-error.tex`. -/
def IsPolyErr₂ (f : ℝ → ℝ → ℝ) : Prop :=
  ∃ C r s : ℝ, 1 ≤ C ∧ 0 < r ∧ 0 < s ∧ ∀ x y, 0 ≤ x → 0 ≤ y →
    0 ≤ f x y ∧ f x y ≤ C * (Real.rpow x r + Real.rpow y s)

end MIPStarRE.QPBT
