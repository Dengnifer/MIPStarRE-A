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
Their paper origin is `references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:902-905`
and `references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:958-961`.
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
elements by `Fin q`.  The algebra structure and the `selfDualNormal` witness
make explicit the paper's once-and-for-all self-dual normal-basis convention;
they are deliberately part of the model rather than quantified afresh by the
soundness theorem.  This is the Lean carrier for `def:binary-representation`,
blueprint `blueprint/src/chapter/ch11_qpbt_algebra.tex:298-315`, paper origin
`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:902-905`.
-/
structure FixedFieldModel (q : ℕ) extends MIPStarRE.LDT.FieldModel q where
  /-- The fixed binary-coordinate equivalence supplied by the chosen basis. -/
  binaryEquiv : K ≃ Fin q
  /-- Scalar restriction from `ZMod 2` to the chosen field. -/
  algebra : Algebra (ZMod 2) K
  /-- The chosen basis is self-dual and normal (the existence proof is deferred). -/
  selfDualNormal : Prop

instance {q : ℕ} (F : FixedFieldModel q) : Field F.K := F.toFieldModel.instField
instance {q : ℕ} (F : FixedFieldModel q) : Fintype F.K := F.toFieldModel.instFintype
instance {q : ℕ} (F : FixedFieldModel q) : DecidableEq F.K := F.toFieldModel.instDecidableEq
instance {q : ℕ} (F : FixedFieldModel q) : Algebra (ZMod 2) F.K := F.algebra

/-- The fixed binary representation of field elements (`def:binary-representation`).
Blueprint: `blueprint/src/chapter/ch11_qpbt_algebra.tex:298-315`; paper origin:
`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:958-961`.
-/
def binaryRepresentation {q : ℕ} (F : FixedFieldModel q) : F.K ≃ Fin q :=
  F.binaryEquiv

/--
The coordinate map associated with a finite basis.  This is the `κ` of
`def:subfields-kappa` in `blueprint/src/chapter/ch11_qpbt_algebra.tex:182-208`,
whose paper origin is `references/qpbt-paper/04_preliminaries.tex:89-93`.
-/
noncomputable abbrev kappa {F K ι : Type*} [CommSemiring F] [Semiring K]
    [Algebra F K] [Finite ι]
    (b : Module.Basis ι F K) : K ≃ₗ[F] (ι → F) :=
  b.equivFun

/--
Multiplication by `a` in basis coordinates, using Mathlib's
`Algebra.leftMulMatrix`.  It is the multiplication table `K_a` in
`def:subfields-kappa` (blueprint lines 196-199; paper
`references/qpbt-paper/04_preliminaries.tex:89-93`).
-/
noncomputable abbrev multiplicationTable {F K ι : Type*} [CommSemiring F]
    [Semiring K] [Algebra F K] [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι F K) : K →ₐ[F] Matrix ι ι F :=
  Algebra.leftMulMatrix b

/--
The finite-field trace used by the Pauli phases.  This is a thin wrapper around
Mathlib's basis-independent `Algebra.trace`, matching `def:subfield-trace` and
Equation `eq:def-trace` in `blueprint/src/chapter/ch11_qpbt_algebra.tex:217-232`
(`references/qpbt-paper/04_preliminaries.tex:89-93`).
-/
noncomputable abbrev binTrace (K : Type*) [CommRing K] [Algebra (ZMod 2) K] :
    K →ₗ[ZMod 2] ZMod 2 :=
  Algebra.trace (ZMod 2) K

/-- The trace selected by a fixed model; this is the map denoted `tr` in the
paper's `def:binary-representation`, blueprint `ch11_qpbt_algebra.tex:298-315`,
paper origin `references/qpbt-paper/04_preliminaries.tex:732-750`. -/
noncomputable def fixedBinTrace {q : ℕ} (F : FixedFieldModel q) : F.K → ZMod 2 :=
  binTrace F.K

/--
The matrix-trace presentation of `fixedBinTrace`, a statement-level bridge to
Equation `eq:def-trace`.  It is the trace assertion in `def:subfield-trace`,
blueprint `blueprint/src/chapter/ch11_qpbt_algebra.tex:217-232`, paper origin
`references/qpbt-paper/04_preliminaries.tex:732-750`.  It remains a proof
obligation in stage 4.1.
-/
theorem fixedBinTrace_eq_matrixTrace {q ι : ℕ} (F : FixedFieldModel q)
    (b : Module.Basis (Fin ι) (ZMod 2) F.K) (a : F.K) :
    fixedBinTrace F a = (multiplicationTable b a).trace := by
  sorry

end MIPStarRE.QPBT
