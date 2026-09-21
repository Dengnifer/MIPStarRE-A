import Mathlib
import Challenge.MIPStarRE.Quantum.FiniteMatrix.Basic

/-! Challenge mirror of `MIPStarRE/Quantum/FiniteMatrix/NormalizedTrace.lean`.

One challenge module per contributing library module, importing the
mirrors of the library modules this one imports.  The partition is
what makes Lean generate the same auxiliary declarations, under the
same names, as the library does. -/

open scoped BigOperators MatrixOrder Matrix ComplexOrder
namespace MIPStarRE.Quantum

-- elaboration context of MIPStarRE/Quantum/FiniteMatrix/NormalizedTrace.lean
section
open scoped Matrix.Norms.Elementwise
open WithLp
variable {d : Type*} [Fintype d]

-- source: MIPStarRE/Quantum/FiniteMatrix/NormalizedTrace.lean:82-83  (MIPStarRE.Quantum.IsProj)
/-- Paper-facing name for Mathlib's predicate that a matrix is a self-adjoint idempotent. -/
abbrev IsProj (P : Op d) : Prop := IsStarProjection P
end  -- module scope
end MIPStarRE.Quantum
