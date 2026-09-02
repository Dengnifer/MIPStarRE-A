import MIPStarRE.LDT.Basic.ParametersBase

/-! # Polynomial error predicates

Shared quantitative predicates for the polynomial-error bounds in QPBT
chapters 12, 14, and 15.

## References

These are formalization-only auxiliaries for the `poly` convention at
`references/qpbt-paper/04_preliminaries.tex:26-29`. The two-parameter form is
used by `lem:pasting` in blueprint chapter 12 and paper chapter 6.
-/

namespace MIPStarRE.QPBT

/-- The one-parameter polynomial-smallness convention used in QPBT chapters
14--15. One universal positive constant is both the prefactor and exponent, as
in `references/qpbt-paper/04_preliminaries.tex:26-29`. -/
def IsPolyErr (f : ℝ → ℝ) : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ x, 0 < x →
    0 ≤ f x ∧ f x ≤ C * Real.rpow x C

/-- The two-parameter polynomial bound used by `lem:pasting`: on positive
arguments, one universal positive constant is both the prefactor and exponent.
This is the convention of `04_preliminaries.tex:26-29`, applied at
`06_nonlocal_games_and_mipstar.tex:518-524`; blueprint
`ch12_qpbt_games.tex:442-469`. -/
def IsPolyErr₂ (f : ℝ → ℝ → ℝ) : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ x y, 0 < x → 0 < y →
    0 ≤ f x y ∧ f x y ≤ C * Real.rpow (x * y) C

end MIPStarRE.QPBT
