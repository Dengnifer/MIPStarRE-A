import Mathlib
import Challenge.MIPStarRE.Quantum.FiniteMatrix.Basic

/-! Challenge mirror of `MIPStarRE/Quantum/Measurement.lean`.

One challenge module per contributing library module, importing the
mirrors of the library modules this one imports.  The partition is
what makes Lean generate the same auxiliary declarations, under the
same names, as the library does. -/

open scoped BigOperators MatrixOrder Matrix ComplexOrder
namespace MIPStarRE.Quantum

-- source: MIPStarRE/Quantum/Measurement.lean:30-40  (MIPStarRE.Quantum.Submeasurement)
/--
A submeasurement on a finite answer type `α` is a family of PSD matrices
`M : α → Op d` with `∑ a, M a ≤ 1`.
-/
structure Submeasurement (α : Type*) [Fintype α] (d : Type*) [Fintype d] [DecidableEq d] where
  /-- The effect operators. -/
  effect : α → Op d
  /-- Each effect is positive semidefinite. -/
  pos : ∀ a, 0 ≤ effect a
  /-- The effects sum to at most the identity. -/
  sum_le_one : ∑ a, effect a ≤ 1

-- source: MIPStarRE/Quantum/Measurement.lean:42-48  (MIPStarRE.Quantum.Measurement)
/--
A measurement is a submeasurement whose effects sum exactly to the identity.
-/
structure Measurement (α : Type*) [Fintype α] (d : Type*) [Fintype d] [DecidableEq d]
    extends Submeasurement α d where
  /-- The effects sum to the identity. -/
  sum_eq_one : ∑ a, effect a = 1
namespace Submeasurement

-- elaboration context of MIPStarRE/Quantum/Measurement.lean:52-94
section
variable {d : Type*} [Fintype d] [DecidableEq d]
variable {α β : Type*} [Fintype α] [Fintype β]

-- source: MIPStarRE/Quantum/Measurement.lean:63-75  (MIPStarRE.Quantum.Submeasurement.postprocess)
/--
Data processing: relabel the answer set by `f : α → β`, summing the effects over
fibers.
-/
noncomputable def postprocess [DecidableEq α] [DecidableEq β]
    (M : Submeasurement α d) (f : α → β) : Submeasurement β d where
  effect b := ∑ a ∈ Finset.univ.filter (fun a => f a = b), M.effect a
  pos b := Finset.sum_nonneg fun a _ => M.pos a
  sum_le_one := by
    calc
      ∑ b, ∑ a ∈ Finset.univ.filter (fun a => f a = b), M.effect a
          = ∑ a, M.effect a := Finset.sum_fiberwise Finset.univ f M.effect
      _ ≤ 1 := M.sum_le_one
end  -- module scope
end Submeasurement
namespace Measurement

-- elaboration context of MIPStarRE/Quantum/Measurement.lean:96-223
section
variable {d : Type*} [Fintype d] [DecidableEq d]
variable {α β : Type*} [Fintype α] [Fintype β]

-- source: MIPStarRE/Quantum/Measurement.lean:120-134  (MIPStarRE.Quantum.Measurement.postprocess)
/--
Postprocess a complete measurement by relabeling outcomes.

This formalizes `references/ldt-paper/preliminaries.tex:169--180`: regrouping
the effects along the fibers of `f` preserves the total operator, so a POVM
remains a POVM after postprocessing.
-/
noncomputable def postprocess [DecidableEq α] [DecidableEq β]
    (M : Measurement α d) (f : α → β) : Measurement β d where
  toSubmeasurement := M.toSubmeasurement.postprocess f
  sum_eq_one := by
    calc
      ∑ b, ∑ a ∈ Finset.univ.filter (fun a => f a = b), M.effect a
          = ∑ a, M.effect a := Finset.sum_fiberwise Finset.univ f M.effect
      _ = 1 := M.sum_eq_one
end  -- module scope
end Measurement
end MIPStarRE.Quantum
