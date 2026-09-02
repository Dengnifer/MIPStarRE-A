import MIPStarRE.QPBT.Games.Distance

/-!
# State-dependent consistency and operator distance

This file gives the concrete finite-dimensional quantities denoted by
state-dependent consistency and approximate operator equality in the QPBT
analysis.

## References

The consistency functional is `def:consistency` in
`blueprint/src/chapter/ch12_qpbt_games.tex`, with paper origin
`references/qpbt-paper/06_nonlocal_games_and_mipstar.tex`.  The operator
distance is used in
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:680-881`.
-/

open scoped BigOperators ComplexConjugate

namespace MIPStarRE.QPBT

open MIPStarRE.LDT
open MIPStarRE.Quantum

/-- Average off-diagonal overlap of two outcome-indexed operator families
already placed on a common Hilbert space.  This is `def:consistency`; the
paper's hidden universal constant is carried by the comparison bound, not by
this functional. -/
noncomputable def consistencyDefect {X α ι : Type*}
    [Fintype α] [DecidableEq α] [Fintype ι] [DecidableEq ι]
    (μ : Distribution X) (A B : X → α → Op ι)
    (ψ : EuclideanSpace ℂ ι) : ℝ :=
  avgOver μ fun x =>
    ∑ a : α, ∑ b : α,
      if a = b then 0
      else (inner ℂ ψ (applyOperatorToState (A x a * B x b) ψ)).re

/-- The relation denoted `simeq_δ`: the state-dependent consistency defect is
at most `δ`. -/
def IsConsistentWithin {X α ι : Type*}
    [Fintype α] [DecidableEq α] [Fintype ι] [DecidableEq ι]
    (μ : Distribution X) (A B : X → α → Op ι)
    (ψ : EuclideanSpace ℂ ι) (δ : ℝ) : Prop :=
  consistencyDefect μ A B ψ ≤ δ

/-- Average squared state-dependent distance between two single-operator
families.  This is the operator relation used in Chapter 14. -/
noncomputable def opDistSq {X ι : Type*}
    [Fintype ι] [DecidableEq ι]
    (μ : Distribution X) (A B : X → Op ι)
    (ψ : EuclideanSpace ℂ ι) : ℝ :=
  avgOver μ fun x => ‖applyOperatorToState (A x - B x) ψ‖ ^ 2

/-- `opDistSq` is `opFamilyDistSq` for a singleton outcome family.  This is a
formalization-only adapter between the chapter interfaces. -/
theorem opDistSq_eq_opFamilyDistSq_unit {X ι : Type*}
    [Fintype ι] [DecidableEq ι]
    (μ : Distribution X) (A B : X → Op ι)
    (ψ : EuclideanSpace ℂ ι) :
    opDistSq μ A B ψ =
      opFamilyDistSq μ (fun x (_ : Unit) => A x) (fun x (_ : Unit) => B x) ψ := by
  simp [opDistSq, opFamilyDistSq]

end MIPStarRE.QPBT
