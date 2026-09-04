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

* `IsBinaryObservable`: a Hermitian operator whose square is the identity,
  together with its algebra: the identity is a binary observable, so is the
  product of two commuting ones, every binary observable is an isometry, and it
  remains one after ampliation by the identity of another tensor factor.
* `ancProj`: the rank-one density operator `|v⟩⟨v|` of a vector `v`.
* `stateDepDistSq`: the squared state-dependent distance
  `d_ρ(S, T)^2 = Re Tr((S - T)^† (S - T) ρ)`.

## References

The notions are those of `thm:linearity` in
`blueprint/src/chapter/ch15_qpbt_combining.tex:104-150`, quoted in the QPBT
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
This is the finite-matrix realization of `Obs(H)` in `thm:linearity`, blueprint
`blueprint/src/chapter/ch15_qpbt_combining.tex:104-150`, quoted at paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:713-725`. -/
def IsBinaryObservable {ι : Type} [Fintype ι] [DecidableEq ι]
    (O : Op ι) : Prop :=
  O.IsHermitian ∧ O * O = 1

namespace IsBinaryObservable

variable {ι : Type} [Fintype ι] [DecidableEq ι] {X Y : Op ι}

/-- A binary observable is self-adjoint. -/
theorem conjTranspose_eq (hX : IsBinaryObservable X) : Xᴴ = X := hX.1

/-- A binary observable squares to the identity. -/
theorem mul_self_eq_one (hX : IsBinaryObservable X) : X * X = 1 := hX.2

/-- A binary observable is isometric: being self-adjoint and an involution, its
adjoint is its own inverse. -/
theorem isometry (hX : IsBinaryObservable X) : Xᴴ * X = 1 := by
  rw [hX.conjTranspose_eq, hX.mul_self_eq_one]

/-- The identity is a binary observable. -/
theorem one : IsBinaryObservable (1 : Op ι) :=
  ⟨Matrix.isHermitian_one, one_mul 1⟩

/-- The product of two commuting binary observables is a binary observable. -/
theorem mul (hX : IsBinaryObservable X) (hY : IsBinaryObservable Y)
    (hcomm : X * Y = Y * X) : IsBinaryObservable (X * Y) := by
  refine ⟨?_, ?_⟩
  · rw [Matrix.IsHermitian, Matrix.conjTranspose_mul, hX.conjTranspose_eq,
      hY.conjTranspose_eq, ← hcomm]
  · calc X * Y * (X * Y) = X * (Y * X) * Y := by noncomm_ring
      _ = X * (X * Y) * Y := by rw [hcomm]
      _ = X * X * (Y * Y) := by noncomm_ring
      _ = 1 := by rw [hX.mul_self_eq_one, hY.mul_self_eq_one, one_mul]

end IsBinaryObservable

/-- The ampliation `O ⊗ 1` of a binary observable by the identity of a second
tensor factor is a binary observable.  This is the sense in which the original
observables `A(a)` act on the extended space in display (8) of
`references/nv-paper/fullpaper.tex:1083-1086`; it is also the way a Magic Square
observable of one player acts on the joint space of `thm:ms-rigidity`. -/
theorem isBinaryObservable_heteroKron_one {ι ι' : Type} [Fintype ι] [DecidableEq ι]
    [Fintype ι'] [DecidableEq ι'] {O : Op ι} (hO : IsBinaryObservable O) :
    IsBinaryObservable (heteroKron O (1 : Op ι')) := by
  unfold heteroKron
  simp only [Matrix.kronecker]
  refine ⟨?_, ?_⟩
  · rw [Matrix.IsHermitian, Matrix.conjTranspose_kronecker, hO.conjTranspose_eq,
      Matrix.conjTranspose_one]
  · rw [← Matrix.mul_kronecker_mul, hO.mul_self_eq_one, Matrix.one_mul,
      Matrix.one_kronecker_one]

/-- The ampliation `1 ⊗ O` of a binary observable by the identity of the first
tensor factor is a binary observable; this is the mirror of
`isBinaryObservable_heteroKron_one` for the second player's factor in
`thm:ms-rigidity`, blueprint `blueprint/src/chapter/ch13_qpbt_test.tex:224-253`. -/
theorem isBinaryObservable_one_heteroKron {ι ι' : Type} [Fintype ι] [DecidableEq ι]
    [Fintype ι'] [DecidableEq ι'] {O : Op ι'} (hO : IsBinaryObservable O) :
    IsBinaryObservable (heteroKron (1 : Op ι) O) := by
  unfold heteroKron
  simp only [Matrix.kronecker]
  refine ⟨?_, ?_⟩
  · rw [Matrix.IsHermitian, Matrix.conjTranspose_kronecker, hO.conjTranspose_eq,
      Matrix.conjTranspose_one]
  · rw [← Matrix.mul_kronecker_mul, hO.mul_self_eq_one, Matrix.one_mul,
      Matrix.one_kronecker_one]

/-- The rank-one density operator associated with an ancillary vector.  This
is the state `|anc⟩⟨anc|` of the extension `ρ' = ρ ⊗ |anc⟩⟨anc|` in
`thm:linearity`, blueprint
`blueprint/src/chapter/ch15_qpbt_combining.tex:104-150`. -/
noncomputable def ancProj {ι : Type} [Fintype ι]
    (v : EuclideanSpace ℂ ι) : Op ι :=
  let w := (EuclideanSpace.equiv ι ℂ) v
  Matrix.vecMulVec w (star w)

/-- Squared state-dependent distance between two operators.  This is the
quantity `d_ρ(S,T)^2` in `thm:linearity`, blueprint
`blueprint/src/chapter/ch15_qpbt_combining.tex:104-150`, the state-dependent
distance of `references/nv-paper/fullpaper.tex:873-875`. -/
noncomputable def stateDepDistSq {ι : Type} [Fintype ι]
    (S T ρ : Op ι) : ℝ :=
  (Matrix.trace ((S - T)ᴴ * (S - T) * ρ)).re

end

end MIPStarRE.QPBT
