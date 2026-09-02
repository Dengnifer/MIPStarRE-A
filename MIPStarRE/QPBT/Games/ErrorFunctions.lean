import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Polynomial error functions

This file records the asymptotic error predicates shared by the observable and
combining chapters.  They make the universal constants and positive exponents
explicit while leaving their values unspecified.

## References

These are Lean-only auxiliaries for the `poly` notation used in
`blueprint/src/chapter/ch14_qpbt_observables.tex` and
`blueprint/src/chapter/ch15_qpbt_combining.tex`.
-/

namespace MIPStarRE.QPBT

/-- A one-variable error function bounded by a positive power with a universal
constant.  This is a formalization-only auxiliary for the paper's `poly(ε)`
notation. -/
def IsPolyErr (f : ℝ → ℝ) : Prop :=
  ∃ C b : ℝ, 1 ≤ C ∧ 0 < b ∧
    ∀ ε : ℝ, 0 ≤ ε → f ε ≤ C * Real.rpow ε b

/-- A two-variable error function bounded by positive powers of both inputs.
This is a formalization-only auxiliary for the paper's `poly(ε, η)` notation. -/
def IsPolyErr2 (f : ℝ → ℝ → ℝ) : Prop :=
  ∃ C b c : ℝ, 1 ≤ C ∧ 0 < b ∧ 0 < c ∧
    ∀ ε η : ℝ, 0 ≤ ε → 0 ≤ η →
      f ε η ≤ C * (Real.rpow ε b + Real.rpow η c)

end MIPStarRE.QPBT
