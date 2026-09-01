import Mathlib
import MIPStarRE.LDT.Basic.ParametersBase

/-!
# Finite-field bases and the fixed binary representation

The Pauli basis test uses fields of size `2^k` for odd `k`, together with a
chosen self-dual normal basis over `ZMod 2`.  This file records that choice as
data, while exposing Mathlib's basis and algebra-trace APIs for later proofs.

## References

The declarations correspond to `def:admissible-size`, `def:subfields-kappa`,
`def:subfield-trace`, and `def:binary-representation` in
`blueprint/src/chapter/ch11_qpbt_algebra.tex:182-232` and `298-315`.
Their paper origin is `references/qpbt-paper/04_preliminaries.tex:433-502,653-728`.
-/

open scoped BigOperators

namespace MIPStarRE.QPBT

/-- `IsAdmissibleSize q` is the predicate `q = 2^k` for an odd exponent.
This is `def:admissible-size` in the blueprint
`blueprint/src/chapter/ch11_qpbt_algebra.tex:210-212`, with paper origin
`references/qpbt-paper/04_preliminaries.tex:662-667`.
-/
def IsAdmissibleSize (q : ℕ) : Prop := ∃ k : ℕ, Odd k ∧ q = 2 ^ k

/--
A fixed finite-field model records the carrier and the chosen coding of its
elements by `Fin q`.  The algebra structure and stored basis data make explicit
the paper's once-and-for-all self-dual normal-basis convention; they are
deliberately part of the model rather than quantified afresh by the soundness
theorem.  This is the Lean carrier for `def:binary-representation`, blueprint
`blueprint/src/chapter/ch11_qpbt_algebra.tex:298-315`, paper origin
`references/qpbt-paper/04_preliminaries.tex:653-728`.
-/
/- The finite-field carrier is specialized to `Type 0`, as are the finite
models used by the surrounding Euclidean-space API. -/
structure FixedFieldModel (q : ℕ) extends MIPStarRE.LDT.FieldModel.{0} q where
  /-- Scalar restriction from `ZMod 2` to the chosen field. -/
  algebra : Algebra (ZMod 2) K
  /-- Dimension of the chosen basis over the prime subfield. -/
  basisDim : ℕ
  /-- The chosen basis dimension is odd, as required for a self-dual normal basis
  over the binary field. -/
  basisDimOdd : Odd basisDim
  /-- The admissible field-size relation for the chosen basis dimension. -/
  basisCard : q = 2 ^ basisDim
  /-- The chosen basis of `K` over `ZMod 2`. -/
  basis : Module.Basis (Fin basisDim) (ZMod 2) K
  /--
  The inherited coding of `K` is the natural binary encoding of the stored
  basis coordinates.  This field records the source's `downsize` convention
  rather than allowing an unrelated permutation of `Fin q`.  It is the
  coordinate clause of `def:binary-representation` in
  `blueprint/src/chapter/ch11_qpbt_algebra.tex:298-315`, with paper origin
  `references/qpbt-paper/04_preliminaries.tex:669-680`.
  -/
  representation_natural :
    ∀ v : Fin basisDim → ZMod 2,
      (toFieldModel.equiv (basis.equivFun.symm v)).val =
        ∑ i : Fin basisDim, if v i = 1 then 2 ^ i.1 else 0
  /-- Self-duality of the chosen basis with respect to the field trace. -/
  selfDual : ∀ i j, Algebra.trace (ZMod 2) K (basis i * basis j) =
    if i = j then 1 else 0
  /-- Normality of the chosen basis, recorded by a Frobenius generator. -/
  normal : ∃ α : K, ∀ i, basis i = α ^ (2 ^ i.1)

/-!
The paper fixes the field representation and self-dual normal basis once for
each admissible field size.  We expose that choice through a single global
selector rather than carrying a potentially different model in every game
parameter record.  Existence is a named stage-4.3 proof obligation; the
selector itself is the resulting noncomputable choice.
-/

/-- An admissible binary field size admits the fixed self-dual normal model used
by the Pauli basis test.  This is the existence assertion implicit in
`def:dual-self-dual-normal-basis` and `def:binary-representation`, blueprint
`blueprint/src/chapter/ch11_qpbt_algebra.tex:234-246,298-315`, paper origin
`references/qpbt-paper/04_preliminaries.tex:653-680,702-725`.

The construction of the basis and its natural coding is deferred to the
algebra stage; keeping it as a named theorem makes the proof obligation visible
without adding a model hypothesis to the source-facing test statements.
-/
theorem exists_fixed_field_model (q : ℕ) (hq : IsAdmissibleSize q) :
    Nonempty (FixedFieldModel q) := by
  sorry

/-- The once-and-for-all field model selected for an admissible size.  Every
QPBT parameter record uses this same choice, matching the paper's fixed
self-dual normal-basis identification rather than quantifying over arbitrary
representations.  Blueprint `ch11_qpbt_algebra.tex:298-315`; paper origin
`references/qpbt-paper/04_preliminaries.tex:653-680`.
-/
noncomputable def fixedFieldModel (q : ℕ) (hq : IsAdmissibleSize q) :
    FixedFieldModel q :=
  Classical.choice (exists_fixed_field_model q hq)

instance {q : ℕ} (F : FixedFieldModel q) : Field F.K := F.toFieldModel.instField
instance {q : ℕ} (F : FixedFieldModel q) : Fintype F.K := F.toFieldModel.instFintype
instance {q : ℕ} (F : FixedFieldModel q) : DecidableEq F.K := F.toFieldModel.instDecidableEq
instance {q : ℕ} (F : FixedFieldModel q) : Algebra (ZMod 2) F.K := F.algebra

/-- The fixed binary representation of field elements (`def:binary-representation`).
Blueprint: `blueprint/src/chapter/ch11_qpbt_algebra.tex:298-315`; paper origin:
`references/qpbt-paper/04_preliminaries.tex:653-680`.
-/
noncomputable def binaryEquiv {q : ℕ} (F : FixedFieldModel q) : F.K ≃ Fin q :=
  F.toFieldModel.equiv

/-- The fixed binary representation obtained from the chosen basis coordinates. -/
noncomputable def binaryRepresentation {q : ℕ} (F : FixedFieldModel q) : F.K ≃ Fin q :=
  binaryEquiv F

/--
The coordinate map associated with a finite basis.  This is the `κ` of
`def:subfields-kappa` in `blueprint/src/chapter/ch11_qpbt_algebra.tex:182-208`,
whose paper origin is `references/qpbt-paper/04_preliminaries.tex:433-502`.
-/
noncomputable abbrev kappa {F K ι : Type*} [CommSemiring F] [Semiring K]
    [Algebra F K] [Finite ι]
    (b : Module.Basis ι F K) : K ≃ₗ[F] (ι → F) :=
  b.equivFun

/--
Multiplication by `a` in basis coordinates, using Mathlib's
`Algebra.leftMulMatrix`.  It is the multiplication table `K_a` in
`def:subfields-kappa` (blueprint lines 196-199; paper
`references/qpbt-paper/04_preliminaries.tex:481-502`).
-/
noncomputable abbrev multiplicationTable {F K ι : Type*} [CommSemiring F]
    [Semiring K] [Algebra F K] [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι F K) : K →ₐ[F] Matrix ι ι F :=
  Algebra.leftMulMatrix b

/--
The finite-field trace used by the Pauli phases.  This is a thin wrapper around
Mathlib's basis-independent `Algebra.trace`, matching `def:subfield-trace` and
Equation `eq:def-trace` in `blueprint/src/chapter/ch11_qpbt_algebra.tex:217-232`
(`references/qpbt-paper/04_preliminaries.tex:481-502`).
-/
noncomputable abbrev binTrace (K : Type*) [CommRing K] [Algebra (ZMod 2) K] :
    K →ₗ[ZMod 2] ZMod 2 :=
  Algebra.trace (ZMod 2) K

/-- The trace selected by a fixed model; this is the map denoted `tr` in the
paper's `def:binary-representation`, blueprint `ch11_qpbt_algebra.tex:298-315`,
paper origin `references/qpbt-paper/04_preliminaries.tex:653-680`. -/
noncomputable def fixedBinTrace {q : ℕ} (F : FixedFieldModel q) : F.K → ZMod 2 :=
  binTrace F.K

/--
The matrix-trace presentation of `fixedBinTrace`, a statement-level bridge to
Equation `eq:def-trace`.  It is the trace assertion in `def:subfield-trace`,
blueprint `blueprint/src/chapter/ch11_qpbt_algebra.tex:217-232`, paper origin
`references/qpbt-paper/04_preliminaries.tex:481-502`.  Mathlib's
`Algebra.trace_eq_matrix_trace` supplies the basis-independent equality.
-/
theorem fixedBinTrace_eq_matrixTrace {q ι : ℕ} (F : FixedFieldModel q)
    (b : Module.Basis (Fin ι) (ZMod 2) F.K) (a : F.K) :
    fixedBinTrace F a = (multiplicationTable b a).trace := by
  exact Algebra.trace_eq_matrix_trace b a

end MIPStarRE.QPBT
