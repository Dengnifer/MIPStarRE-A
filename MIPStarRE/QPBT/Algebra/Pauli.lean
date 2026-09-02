import MIPStarRE.QPBT.Algebra.FieldBasis
import MIPStarRE.Quantum.FiniteMatrix.Basic

/-!
# Generalized Pauli operators and EPR states

The definitions here use finite matrix entries and rank-one projectors, so they
are usable by the later game statements without introducing an abstract
operator algebra.  The Fourier/orthogonality identities are retained as named
proof obligations for subsequent stages.

## References

The source-facing nodes are `def:lin-reg`, `def:EPR`, `def:generalized-pauli`,
and `lem:pauli-observable-expansion` in
`blueprint/src/chapter/ch11_qpbt_algebra.tex:494-652`.  The paper origin is
`references/qpbt-paper/04_preliminaries.tex:908-1161`.
-/

open scoped BigOperators Matrix ComplexOrder

namespace MIPStarRE.QPBT

open MIPStarRE.Quantum

variable {K : Type*} [Field K] [Fintype K] [DecidableEq K]
  [Algebra (ZMod 2) K]

/-- The two generalized Pauli bases used by the test in `def:generalized-pauli`,
blueprint `ch11_qpbt_algebra.tex:529-571`, paper origin
`references/qpbt-paper/04_preliminaries.tex:1052-1096`.
-/
inductive PauliKind where
  | X
  | Z
  deriving DecidableEq, Repr, Inhabited, Fintype

/-- The binary character used for generalized Pauli phases; see
`references/qpbt-paper/04_preliminaries.tex:1052-1081`.

It is public because the Fourier expansion declarations below expose this
character in their statement types. -/
noncomputable def phaseSign (t : ZMod 2) : ℂ :=
  if t = 0 then 1 else -1

/--
The shift operator `τ^X(a)`.  Blueprint `def:generalized-pauli`,
`blueprint/src/chapter/ch11_qpbt_algebra.tex:529-571`; paper origin
`references/qpbt-paper/04_preliminaries.tex:1052-1096`.
-/
noncomputable def tauShift (a : K) : Op K :=
  fun i j => if i = j + a then 1 else 0

/--
The phase operator `τ^Z(b)`, with the fixed binary trace in the phase.  It is
the second operator of `def:generalized-pauli` (blueprint lines 529-571; paper
`references/qpbt-paper/04_preliminaries.tex:1052-1096`).
-/
noncomputable def tauPhase (b : K) : Op K :=
  fun i j => if i = j then phaseSign (binTrace K (b * j)) else 0

/-- The single-qudit eigenvector coordinate used in the tensor-product basis;
see `references/qpbt-paper/04_preliminaries.tex:1126-1161`. -/
private noncomputable def singlePauliVec (W : PauliKind) (e x : K) : ℂ :=
  match W with
  | .Z => if x = e then 1 else 0
  | .X =>
      (Real.sqrt (Fintype.card K : ℝ) : ℂ)⁻¹ * phaseSign (binTrace K (e * x))

/--
The normalized single/multi-qudit eigenvector for a Pauli basis label.  For an
index type `ι`, the input `e : ι → K` labels the tensor-product basis vector.
This is the vector form of `def:generalized-pauli`, blueprint
`blueprint/src/chapter/ch11_qpbt_algebra.tex:550-570`, paper origin
`references/qpbt-paper/04_preliminaries.tex:1101-1122`.
-/
noncomputable def pauliVec {ι : Type*} [Fintype ι] [DecidableEq ι]
    (W : PauliKind) (e : ι → K) (x : ι → K) : ℂ :=
  ∏ i : ι, singlePauliVec W (e i) (x i)

/--
The rank-one projector onto `pauliVec W e`.  This is the projective measurement
element `τ^W_e` in `def:generalized-pauli` (blueprint lines 562-570; paper
`references/qpbt-paper/04_preliminaries.tex:1101-1122`).
-/
noncomputable def pauliProj {ι : Type*} [Fintype ι] [DecidableEq ι]
    (W : PauliKind) (e : ι → K) : Op (ι → K) :=
  Matrix.vecMulVec (pauliVec W e) (fun x => star (pauliVec W e x))

/-- A compact operator-valued form of a generalized Pauli observable from
`def:generalized-pauli`, blueprint `ch11_qpbt_algebra.tex:529-571`, paper origin
`references/qpbt-paper/04_preliminaries.tex:1052-1096`.
-/
noncomputable def tauObservable {ι : Type*} [Fintype ι] [DecidableEq ι]
    (W : PauliKind) (a : ι → K) : Op (ι → K) :=
  fun x y =>
    ∏ i : ι,
      match W with
      | .X => tauShift (a i) (x i) (y i)
      | .Z => tauPhase (a i) (x i) (y i)

/--
The EPR vector on a finite label space.  Blueprint `def:EPR`,
`blueprint/src/chapter/ch11_qpbt_algebra.tex:513-523`; paper origin
`references/qpbt-paper/04_preliminaries.tex:946-955`.
-/
noncomputable def eprState (V : Type*) [Fintype V] [DecidableEq V] [Nonempty V] :
    EuclideanSpace ℂ (V × V) :=
  (EuclideanSpace.equiv (V × V) ℂ).symm
    (fun p : V × V =>
      if p.1 = p.2 then (Real.sqrt (Fintype.card V : ℝ) : ℂ)⁻¹ else 0)

/-- The EPR vector is normalized on a nonempty finite carrier; see
`def:EPR`, `references/qpbt-paper/04_preliminaries.tex:946-955`. -/
theorem eprState_norm (V : Type*) [Fintype V] [DecidableEq V] [Nonempty V] :
    ‖eprState V‖ = 1 := by
  sorry

/--
Fourier expansion of a generalized Pauli observable in the Pauli projectors.
This is `lem:pauli-observable-expansion`, equations `eq:pauli-obs-proj` and
`eq:pauli-inversion-0`, in `blueprint/src/chapter/ch11_qpbt_algebra.tex:638-652`;
paper origin `references/qpbt-paper/04_preliminaries.tex:1141-1161`.
Both directions are deliberately left as proof-level obligations in stage 4.1.
-/
theorem tauObservable_eq_sum_pauliProj {ι : Type*} [Fintype ι] [DecidableEq ι]
    (W : PauliKind) (a : ι → K) :
    tauObservable W a =
      ∑ e : ι → K, phaseSign (binTrace K (dotProduct a e)) • pauliProj W e := by
  sorry

/-- The inverse Fourier expansion of a Pauli projector
(`lem:pauli-observable-expansion`), blueprint
`ch11_qpbt_algebra.tex:638-652`, paper origin
`references/qpbt-paper/04_preliminaries.tex:1141-1161`.
-/
theorem pauliProj_eq_avg_tauObservable {ι : Type*} [Fintype ι] [DecidableEq ι]
    (W : PauliKind) (e : ι → K) :
    pauliProj W e =
      (Fintype.card (ι → K) : ℂ)⁻¹ •
        ∑ a : ι → K, phaseSign (binTrace K (dotProduct a e)) • tauObservable W a := by
  sorry

end MIPStarRE.QPBT
