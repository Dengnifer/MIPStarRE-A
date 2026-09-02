import MIPStarRE.LDT.Basic.ParametersBase

/-! # Polynomial error predicates

Shared quantitative predicates for the polynomial-error bounds in QPBT
chapters 12, 14, and 15.

## References

These are formalization-only auxiliaries for the `poly` notation in
`blueprint/src/chapter/ch12_qpbt_games.tex:402-427`, with paper origin
`references/qpbt-paper/06_nonlocal_games_and_mipstar.tex:504-525`.
-/

namespace MIPStarRE.QPBT

/-- The one-parameter polynomial-smallness convention used by `lem:pasting`
and QPBT chapters 14--15; blueprint `ch12_qpbt_games.tex:402-427`, paper
`references/qpbt-paper/06_nonlocal_games_and_mipstar.tex:504-525`. -/
def IsPolyErr (f : ℝ → ℝ) : Prop :=
  ∃ C r : ℝ, 1 ≤ C ∧ 0 < r ∧ ∀ x, 0 ≤ x →
    0 ≤ f x ∧ f x ≤ C * Real.rpow x r

/-- The two-parameter polynomial-smallness convention used by `lem:pasting`
and QPBT chapter 15; blueprint `ch12_qpbt_games.tex:402-427`, paper
`references/qpbt-paper/06_nonlocal_games_and_mipstar.tex:504-525`. -/
def IsPolyErr2 (f : ℝ → ℝ → ℝ) : Prop :=
  ∃ C r s : ℝ, 1 ≤ C ∧ 0 < r ∧ 0 < s ∧ ∀ x y, 0 ≤ x → 0 ≤ y →
    0 ≤ f x y ∧
      f x y ≤ C * (Real.rpow x r + Real.rpow y s)

/-- Unicode compatibility alias for the two-parameter polynomial-smallness
predicate used by `lem:pasting`, blueprint `ch12_qpbt_games.tex:402-427`, paper
`references/qpbt-paper/06_nonlocal_games_and_mipstar.tex:504-525`. -/
abbrev IsPolyErr₂ := IsPolyErr2

end MIPStarRE.QPBT
