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
The prefactor and exponent are quantified separately: paper chapter 14 explicitly
obtains `sqrt ε` at `14_analysis_of_the_pauli_basis_test.tex:503-505,657-679`,
which would be excluded if the two constants were identified as in the shorthand
at `04_preliminaries.tex:26-29`. -/
def IsPolyErr (f : ℝ → ℝ) : Prop :=
  ∃ C r : ℝ, 1 ≤ C ∧ 0 < r ∧ ∀ x, 0 ≤ x →
    0 ≤ f x ∧ f x ≤ C * Real.rpow x r

/-- The two-parameter polynomial bound used by `lem:pasting`: on positive
arguments, one universal positive constant is both the prefactor and exponent.
This is the convention of `04_preliminaries.tex:26-29`, applied at
`06_nonlocal_games_and_mipstar.tex:518-524`; blueprint
`ch12_qpbt_games.tex:442-469`. -/
def IsPolyErr₂ (f : ℝ → ℝ → ℝ) : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ x y, 0 < x → 0 < y →
    0 ≤ f x y ∧ f x y ≤ C * Real.rpow (x * y) C

end MIPStarRE.QPBT
