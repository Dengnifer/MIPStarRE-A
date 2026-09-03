import MIPStarRE.QPBT.Algebra.FieldBasis
import MIPStarRE.QPBT.Games.Defs

/-!
# The quantum linearity theorem

This file states the external quantum-linearity result used to combine the
binary observables produced in the point analysis.  The statement uses a raw
positive trace-one operator, and its conclusion adjoins a finite ancillary
space on which the exactly linear observables act.

## References

The declaration is `thm:linearity` in
`blueprint/src/chapter/ch15_qpbt_combining.tex:82-180`.  The quotation in the
QPBT paper is at
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:713-725`; the
provider is Theorem 10 of Natarajan--Vidick, arXiv:1610.03574.
-/

open scoped BigOperators Matrix MatrixOrder ComplexOrder

namespace MIPStarRE.QPBT

open MIPStarRE.LDT
open MIPStarRE.Quantum

noncomputable section

/-- A binary observable is a Hermitian operator whose square is the identity.
This is the finite-matrix realization of `Obs(H)` in `thm:linearity`, blueprint
`blueprint/src/chapter/ch15_qpbt_combining.tex:82-180`, quoted at paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:713-725`. -/
def IsBinaryObservable {ι : Type} [Fintype ι] [DecidableEq ι]
    (O : Op ι) : Prop :=
  O.IsHermitian ∧ O * O = 1

/-- The rank-one density operator associated with an ancillary vector. -/
noncomputable def ancProj {ι : Type} [Fintype ι]
    (v : EuclideanSpace ℂ ι) : Op ι :=
  let w := (EuclideanSpace.equiv ι ℂ) v
  Matrix.vecMulVec w (star w)

/-- Squared state-dependent distance between two operators.  This is the
quantity `d_rho(S,T)^2` in `thm:linearity`, blueprint
`blueprint/src/chapter/ch15_qpbt_combining.tex:82-180`. -/
noncomputable def stateDepDistSq {ι : Type} [Fintype ι]
    (S T ρ : Op ι) : ℝ :=
  (Matrix.trace ((S - T)ᴴ * (S - T) * ρ)).re

/-- The quantum linearity theorem imported from Natarajan--Vidick.

The statement is `thm:linearity` in
`blueprint/src/chapter/ch15_qpbt_combining.tex:82-145`; the QPBT paper quotes
it at
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:713-725`.

As recorded in `rem:linearity-import` (blueprint lines 147--180), this
provider-faithful form imposes no upper bound on `δ`, preserves the error,
asserts exact linearity for every pair, and averages closeness only over `u`.
The paper quotation instead adds `δ ≤ 1`, phrases closeness pointwise under a
pair quantifier, and appends `L 0 = 1`; those three deviations are not
reproduced.  The identity at zero follows later from exact linearity and the
binary-observable condition. -/
theorem exists_exactly_linear_observables {ι : Type}
    [Fintype ι] [DecidableEq ι]
    (t : ℕ) (ht : 0 < t) (δ : ℝ) (hδ : 0 ≤ δ)
    (ρ : Op ι) (hρ : ρ.PosSemidef) (htrace : ρ.trace = 1)
    (O : (Fin t → ZMod 2) → Op ι)
    (hO : ∀ u, IsBinaryObservable (O u))
    (hcorrelation :
      1 - δ ≤ avgOver
        (uniformDistribution
          ((Fin t → ZMod 2) × (Fin t → ZMod 2)))
        (fun pair =>
          (Matrix.trace
            (O pair.1 * O pair.2 * O (pair.1 + pair.2) * ρ)).re)) :
    ∃ (ι' : Type) (_ : Fintype ι') (_ : DecidableEq ι')
        (anc : EuclideanSpace ℂ ι'),
      ‖anc‖ = 1 ∧
        ∃ L : (Fin t → ZMod 2) → Op (ι × ι'),
          (∀ u, IsBinaryObservable (L u)) ∧
          (∀ u u', L u * L u' = L (u + u')) ∧
          avgOver (uniformDistribution (Fin t → ZMod 2))
              (fun u => stateDepDistSq (L u)
                (heteroKron (O u) (1 : Op ι'))
                (heteroKron ρ (ancProj anc))) ≤ δ := by
  sorry

end

end MIPStarRE.QPBT
