import Mathlib
import Challenge.MIPStarRE.QPBT.Algebra.FieldBasis
import Challenge.MIPStarRE.Quantum.FiniteMatrix.Basic

/-! Challenge mirror of `MIPStarRE/QPBT/Algebra/Pauli.lean`.

One challenge module per contributing library module, importing the
mirrors of the library modules this one imports.  The partition is
what makes Lean generate the same auxiliary declarations, under the
same names, as the library does. -/

open scoped BigOperators MatrixOrder Matrix ComplexOrder
namespace MIPStarRE.QPBT

-- elaboration context of MIPStarRE/QPBT/Algebra/Pauli.lean
section
open MIPStarRE.Quantum
variable {K : Type*} [Field K] [Fintype K] [DecidableEq K]
  [Algebra (ZMod 2) K]

-- source: MIPStarRE/QPBT/Algebra/Pauli.lean:30-37  (MIPStarRE.QPBT.PauliKind)
/-- The two generalized Pauli bases used by the test in blueprint
`def:generalized-pauli`, paper origin
`references/qpbt-paper/04_preliminaries.tex:1052-1096`.
-/
inductive PauliKind where
  | X
  | Z
  deriving DecidableEq, Repr, Inhabited, Fintype

-- source: MIPStarRE/QPBT/Algebra/Pauli.lean:39-45  (MIPStarRE.QPBT.phaseSign)
/-- The binary character used for generalized Pauli phases; see
`references/qpbt-paper/04_preliminaries.tex:1052-1081`.

It is public because the Fourier expansion declarations below expose this
character in their statement types. -/
noncomputable def phaseSign (t : ZMod 2) : ℂ :=
  if t = 0 then 1 else -1

-- source: MIPStarRE/QPBT/Algebra/Pauli.lean:353-359  (MIPStarRE.QPBT.singlePauliVec)
/-- The single-qudit eigenvector coordinate used in the tensor-product basis;
see `references/qpbt-paper/04_preliminaries.tex:1126-1161`. -/
noncomputable def singlePauliVec (W : PauliKind) (e x : K) : ℂ :=
  match W with
  | .Z => if x = e then 1 else 0
  | .X =>
      (Real.sqrt (Fintype.card K : ℝ) : ℂ)⁻¹ * phaseSign (binTrace K (e * x))

-- source: MIPStarRE/QPBT/Algebra/Pauli.lean:361-370  (MIPStarRE.QPBT.pauliVec)
/--
The normalized single/multi-qudit eigenvector for a Pauli basis label.  For an
index type `ι`, the input `e : ι → K` labels the tensor-product basis vector.
This is the vector form of blueprint
`def:generalized-pauli`, paper origin
`references/qpbt-paper/04_preliminaries.tex:1101-1122`.
-/
noncomputable def pauliVec {ι : Type*} [Fintype ι] [DecidableEq ι]
    (W : PauliKind) (e : ι → K) (x : ι → K) : ℂ :=
  ∏ i : ι, singlePauliVec W (e i) (x i)

-- source: MIPStarRE/QPBT/Algebra/Pauli.lean:372-379  (MIPStarRE.QPBT.pauliProj)
/--
The rank-one projector onto `pauliVec W e`.  This is the projective measurement
element `τ^W_e` in blueprint `def:generalized-pauli`; paper
`references/qpbt-paper/04_preliminaries.tex:1101-1122`.
-/
noncomputable def pauliProj {ι : Type*} [Fintype ι] [DecidableEq ι]
    (W : PauliKind) (e : ι → K) : Op (ι → K) :=
  Matrix.vecMulVec (pauliVec W e) (fun x => star (pauliVec W e x))

-- source: MIPStarRE/QPBT/Algebra/Pauli.lean:506-514  (MIPStarRE.QPBT.eprState)
/--
The EPR vector on a finite label space.  Blueprint `def:EPR`; paper origin
`references/qpbt-paper/04_preliminaries.tex:946-955`.
-/
noncomputable def eprState (V : Type*) [Fintype V] [DecidableEq V] [Nonempty V] :
    EuclideanSpace ℂ (V × V) :=
  (EuclideanSpace.equiv (V × V) ℂ).symm
    (fun p : V × V =>
      if p.1 = p.2 then (Real.sqrt (Fintype.card V : ℝ) : ℂ)⁻¹ else 0)
end  -- module scope
end MIPStarRE.QPBT
