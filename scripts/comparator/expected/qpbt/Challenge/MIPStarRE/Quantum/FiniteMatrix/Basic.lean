import Mathlib

/-! Challenge mirror of `MIPStarRE/Quantum/FiniteMatrix/Basic.lean`.

One challenge module per contributing library module, importing the
mirrors of the library modules this one imports.  The partition is
what makes Lean generate the same auxiliary declarations, under the
same names, as the library does. -/

open scoped BigOperators MatrixOrder Matrix ComplexOrder
namespace MIPStarRE.Quantum

-- source: MIPStarRE/Quantum/FiniteMatrix/Basic.lean:78-79  (MIPStarRE.Quantum.Op)
/-- Square complex matrices as the finite-dimensional operator algebra. -/
abbrev Op (d : Type*) := Matrix d d ℂ
end MIPStarRE.Quantum
