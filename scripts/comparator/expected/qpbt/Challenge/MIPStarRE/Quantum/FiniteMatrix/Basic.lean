import Mathlib

/-! Challenge mirror of `MIPStarRE/Quantum/FiniteMatrix/Basic.lean`.

One challenge module per contributing library module, importing the
mirrors of the library modules this one imports.  The partition is
what makes Lean generate the same auxiliary declarations, under the
same names, as the library does. -/

open scoped BigOperators MatrixOrder Matrix ComplexOrder
namespace MIPStarRE.Quantum

-- source: MIPStarRE/Quantum/FiniteMatrix/Basic.lean:100-102  (MIPStarRE.Quantum.instNeZeroTwo)
/-- Two is nonzero.  Named so that the `Fintype (ZMod 2)` instance behind the
qubit alphabet is an atomic term in the comparator statement closure. -/
instance instNeZeroTwo : NeZero (2 : ℕ) := ⟨by decide⟩

-- source: MIPStarRE/Quantum/FiniteMatrix/Basic.lean:106-107  (MIPStarRE.Quantum.Op)
/-- Square complex matrices as the finite-dimensional operator algebra. -/
abbrev Op (d : Type*) := Matrix d d ℂ
end MIPStarRE.Quantum
