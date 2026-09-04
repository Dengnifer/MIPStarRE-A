import MIPStarRE.QPBT.Algebra.FieldBasis
import MIPStarRE.QPBT.Games.Defs

/-!
# Binary observables and the state-dependent distance

This file collects the notions in which the quantum linearity theorem of
Natarajan and Vidick is stated: binary observables, the rank-one density
operator of an ancillary vector, and the squared state-dependent distance
between two operators weighted by a positive semidefinite trace-one operator.
The theorem itself, `exists_exactly_linear_observables`, is stated and proved
in `MIPStarRE/QPBT/Combining/Linearity.lean` from the Boolean Fourier,
operator BLR, Naimark rounding, and representation stability modules under
`MIPStarRE/QPBT/Combining/Linearity/`, all of which build on this file.

## Main definitions

* `IsBinaryObservable`: a Hermitian operator whose square is the identity.
* `ancProj`: the rank-one density operator `|v⟩⟨v|` of a vector `v`.
* `stateDepDistSq`: the squared state-dependent distance
  `d_ρ(S, T)^2 = Re Tr((S - T)^† (S - T) ρ)`.

## References

The notions are those of blueprint
`thm:linearity`, quoted in the QPBT
paper at `references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:713-725`
from Theorem 10 of Natarajan--Vidick, arXiv:1610.03574,
`references/nv-paper/fullpaper.tex:1074-1088`; the state-dependent distance is
defined there at lines 866--875.
-/

open scoped BigOperators Matrix MatrixOrder ComplexOrder

namespace MIPStarRE.QPBT

open MIPStarRE.LDT
open MIPStarRE.Quantum

noncomputable section

/-- A binary observable is a Hermitian operator whose square is the identity.
This is the finite-matrix realization of `Obs(H)` in blueprint
`thm:linearity`, quoted at paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:713-725`. -/
def IsBinaryObservable {ι : Type} [Fintype ι] [DecidableEq ι]
    (O : Op ι) : Prop :=
  O.IsHermitian ∧ O * O = 1

/-- The rank-one density operator associated with an ancillary vector.  This
is the state `|anc⟩⟨anc|` of the extension `ρ' = ρ ⊗ |anc⟩⟨anc|` in
blueprint
`thm:linearity`. -/
noncomputable def ancProj {ι : Type} [Fintype ι]
    (v : EuclideanSpace ℂ ι) : Op ι :=
  let w := (EuclideanSpace.equiv ι ℂ) v
  Matrix.vecMulVec w (star w)

/-- Squared state-dependent distance between two operators.  This is the
quantity `d_ρ(S,T)^2` in blueprint
`thm:linearity`, the state-dependent
distance of `references/nv-paper/fullpaper.tex:873-875`. -/
noncomputable def stateDepDistSq {ι : Type} [Fintype ι]
    (S T ρ : Op ι) : ℝ :=
  (Matrix.trace ((S - T)ᴴ * (S - T) * ρ)).re

end

end MIPStarRE.QPBT
