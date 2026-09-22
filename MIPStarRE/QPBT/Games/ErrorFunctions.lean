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

open scoped BigOperators

/-- The literal finite-arity polynomial bound of
`references/qpbt-paper/04_preliminaries.tex:26-29`, retained as an **unasserted**
predicate. One positive constant is both prefactor and exponent, uniformly over
all strictly positive inputs. The source shorthand imposes neither a value at
zero nor an additional lower bound on the function.

This is not `IsPolyErr` or `IsPolyErr₂` and no implication from those corrected
predicates is asserted. See `docs/paper-gaps/qpbt_polynomial-error-square-root.tex`
and `docs/paper-gaps/qpbt_pasting-product-error.tex`, issues #16, #196, and #674. -/
def PrintedPolynomialBound {k : ℕ} (f : (Fin k → ℝ) → ℝ) : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ x : Fin k → ℝ, (∀ i, 0 < x i) →
    f x ≤ C * Real.rpow (∏ i, x i) C

/-- The square-root choice under the literal polynomial convention, retained
**without being asserted**. Paper `lem:qld-comm-cons` and
`lem:qld-comm-line-cons` choose `sqrt ε` in
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:508-520,649-676`.
This proposition records only their scalar contract, not their operator
conclusions. It is refuted by the elementary calculation in
`docs/paper-gaps/qpbt_polynomial-error-square-root.tex`, issue #16: the input
one forces `C ≥ 1`, after which small positive inputs contradict the bound.
Defining this proposition is not a proof of it. -/
def PrintedSquareRootPolynomialClaim : Prop :=
  PrintedPolynomialBound (fun x : Fin 1 → ℝ => Real.sqrt (x 0))

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

**Local fix:** The prefactor and the two exponents are quantified separately,
and the bound is imposed on the closed nonnegative quadrant. The shorthand at
`04_preliminaries.tex:22-29` reads `poly` of several arguments as a single
power of their product, which forces the pasting error of `lem:pasting` at
`06_nonlocal_games_and_mipstar.tex:504-525` to tend to zero with the collision
error at every fixed positive consistency error; a two-dimensional strategy
refutes the resulting statement. A sum of separate positive powers vanishes
exactly when both errors vanish, and bounds the terms the imported proof of
Fact 4.35 produces. The correction is documented in
`docs/paper-gaps/qpbt_pasting-product-error.tex` and tracked by issue #196. -/
def IsPolyErr₂ (f : ℝ → ℝ → ℝ) : Prop :=
  ∃ C r s : ℝ, 1 ≤ C ∧ 0 < r ∧ 0 < s ∧ ∀ x y, 0 ≤ x → 0 ≤ y →
    0 ≤ f x y ∧ f x y ≤ C * (Real.rpow x r + Real.rpow y s)

end MIPStarRE.QPBT
