import Mathlib

/-!
# Basic finite-dimensional matrix operators

This module contains the elementary trace and matrix-algebra facts used by the
finite-dimensional quantum layer.  It introduces the local operator abbreviation
`Op d = Matrix d d ℂ` and keeps the basic trace bookkeeping independent of the
positive-semidefinite order and normalized-trace material.

## References

The declarations in this file are matrix facts for the LDT
formalization of `references/ldt-paper/`.
-/

open scoped BigOperators MatrixOrder Matrix ComplexOrder Matrix.Norms.Elementwise
open WithLp

namespace Matrix

/-! ### Trace bookkeeping -/

/-- Reindexing rows and columns by the same equivalence preserves matrix trace.

This generic matrix lemma is used when moving between equivalent finite index
presentations of the same operator. -/
theorem trace_reindex {α β R : Type*} [Fintype α] [Fintype β]
    [AddCommMonoid R] (e : α ≃ β) (M : Matrix α α R) :
    Matrix.trace (Matrix.reindex e e M) = Matrix.trace M := by
  classical
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.reindex_apply]
  rw [← e.symm.sum_comp (fun i : α => M i i)]
  rfl

/-! ### Linear matrix maps -/

/-- Taking a submatrix is linear in the ambient matrix.

This packages the entrywise linearity of `Matrix.submatrix` in the same style
as Mathlib's block-diagonal additive and linear maps. -/
def submatrixLinearMap (R : Type*) {m n m' n' α : Type*}
    [Semiring R] [AddCommMonoid α] [Module R α]
    (row : m' → m) (col : n' → n) :
    Matrix m n α →ₗ[R] Matrix m' n' α where
  toFun := fun A => Matrix.submatrix A row col
  map_add' := by
    intro A B
    ext i j
    rfl
  map_smul' := by
    intro c A
    ext i j
    rfl

@[simp]
theorem submatrixLinearMap_apply (R : Type*) {m n m' n' α : Type*}
    [Semiring R] [AddCommMonoid α] [Module R α]
    (row : m' → m) (col : n' → n) (A : Matrix m n α) :
    Matrix.submatrixLinearMap R row col A = Matrix.submatrix A row col :=
  rfl

/-- The trace pairing of two block-diagonal matrices is the sum of the trace
pairings of the corresponding diagonal blocks. -/
theorem trace_blockDiagonal_mul {o m R : Type*}
    [Fintype o] [DecidableEq o] [Fintype m] [NonUnitalNonAssocSemiring R]
    (B D : o → Matrix m m R) :
    Matrix.trace (Matrix.blockDiagonal B * Matrix.blockDiagonal D) =
      ∑ b : o, Matrix.trace (B b * D b) := by
  rw [← Matrix.blockDiagonal_mul B D, Matrix.trace_blockDiagonal]

end Matrix

namespace MIPStarRE.Quantum

/-! ### Named instances shared by the comparator statement closure

Instance synthesis returns these two facts as *non-atomic* proof terms:
`RingHomInvPair.ids` applied to a synthesized `Semiring ℂ`, and
`Nat.instNeZeroSucc` applied to `1`.  Lean lifts a non-atomic nested proof out
of a definition's value into an auto-generated auxiliary constant and names it
after whichever declaration first needed it in that module.  The library
spreads the affected declarations over six modules and so produces several
copies of the same fact under different names, while the generated
Mathlib-only comparator challenge is a single module and produces exactly one.
The statement closure then fails to match even though both sides hold the same
proposition with the same proof.

Naming the two facts here — in the one module that every affected declaration
imports — makes synthesis return an atomic constant, so no auxiliary constant
is generated on either side.  No statement, definition body or proof script
changes.  See `docs/comparator.md`, "Environment alignment for QPBT".
-/

/-- The identity ring homomorphism on `ℂ` is its own inverse pair.  Named so
that it is an atomic term in the comparator statement closure. -/
instance instRingHomInvPairIdComplex :
    RingHomInvPair (RingHom.id ℂ) (RingHom.id ℂ) := RingHomInvPair.ids

/-- Two is nonzero.  Named so that the `Fintype (ZMod 2)` instance behind the
qubit alphabet is an atomic term in the comparator statement closure. -/
instance instNeZeroTwo : NeZero (2 : ℕ) := ⟨by decide⟩

/-! ### Basic operator type -/

/-- Square complex matrices as the finite-dimensional operator algebra. -/
abbrev Op (d : Type*) := Matrix d d ℂ

/-! ### Kronecker product bookkeeping -/

/-- Kronecker product is additive in the right factor, rewritten for subtraction. -/
theorem kronecker_sub_right
    {d₁ d₂ : Type*} {A : Op d₁} {B₁ B₂ : Op d₂} :
    Matrix.kronecker A B₁ - Matrix.kronecker A B₂ =
      Matrix.kronecker A (B₁ - B₂) := by
  have hneg : Matrix.kronecker A (-B₂) = -Matrix.kronecker A B₂ := by
    simpa using (Matrix.kronecker_smul (-1 : ℂ) A B₂)
  calc
    Matrix.kronecker A B₁ - Matrix.kronecker A B₂
        = Matrix.kronecker A B₁ + Matrix.kronecker A (-B₂) := by
            rw [hneg]
            simp [sub_eq_add_neg]
    _ = Matrix.kronecker A (B₁ - B₂) := by
          simpa [sub_eq_add_neg] using (Matrix.kronecker_add A B₁ (-B₂)).symm

/-- Kronecker product is additive in the left factor, rewritten for subtraction. -/
theorem kronecker_sub_left
    {d₁ d₂ : Type*} {A₁ A₂ : Op d₁} {B : Op d₂} :
    Matrix.kronecker A₁ B - Matrix.kronecker A₂ B =
      Matrix.kronecker (A₁ - A₂) B := by
  have hneg : Matrix.kronecker (-A₂) B = -Matrix.kronecker A₂ B := by
    simpa using (Matrix.smul_kronecker (-1 : ℂ) A₂ B)
  calc
    Matrix.kronecker A₁ B - Matrix.kronecker A₂ B
        = Matrix.kronecker A₁ B + Matrix.kronecker (-A₂) B := by
            rw [hneg]
            simp [sub_eq_add_neg]
    _ = Matrix.kronecker (A₁ - A₂) B := by
          simpa [sub_eq_add_neg] using (Matrix.add_kronecker A₁ (-A₂) B).symm

end MIPStarRE.Quantum
