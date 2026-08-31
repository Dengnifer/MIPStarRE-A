import Mathlib
import MIPStarRE.QPBT.Games.Defs

/-!
# Quantitative state and operator distances

The blueprint uses asymptotic `approx` notation.  The skeleton records the
corresponding squared norm functionals explicitly, leaving universal-constant
estimates to later proof stages.

## References

These are `def:state-distance` and `def:povm-distance` in
`blueprint/src/chapter/ch12_qpbt_games.tex:171-220`; the paper origin is
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:95-103`.
-/

open scoped BigOperators

namespace MIPStarRE.QPBT

open MIPStarRE.LDT
open MIPStarRE.Quantum

/--
Squared Euclidean distance between pure states.  Blueprint `def:state-distance`
(`blueprint/src/chapter/ch12_qpbt_games.tex:171-179`), paper origin
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:95-103`.
-/
noncomputable def stateDistSq {ι : Type*} [Fintype ι]
    [DecidableEq ι]
    (ψ φ : EuclideanSpace ℂ ι) : ℝ :=
  ‖ψ - φ‖ ^ 2

private noncomputable def applyOperatorToState {ι : Type*} [Fintype ι]
    (M : Op ι) (ψ : EuclideanSpace ℂ ι) : EuclideanSpace ℂ ι :=
  (EuclideanSpace.equiv ι ℂ).symm (M.mulVec ((EuclideanSpace.equiv ι ℂ) ψ))

/--
Average squared state-dependent distance between two operator families.  This
is `def:povm-distance` in `blueprint/src/chapter/ch12_qpbt_games.tex:203-210`,
with paper origin `references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:95-103`.
-/
noncomputable def opFamilyDistSq {X α ι : Type*}
    [Fintype α] [Fintype ι] [DecidableEq ι]
    (μ : Distribution X) (M N : X → α → Op ι)
    (ψ : EuclideanSpace ℂ ι) : ℝ :=
  avgOver μ (fun x =>
    ∑ a : α, ‖applyOperatorToState (M x a - N x a) ψ‖ ^ 2)

end MIPStarRE.QPBT
