import Mathlib
import Challenge.MIPStarRE.QPBT.Algebra.Subspaces

/-! Challenge mirror of `MIPStarRE/QPBT/Algebra/Lines.lean`.

One challenge module per contributing library module, importing the
mirrors of the library modules this one imports.  The partition is
what makes Lean generate the same auxiliary declarations, under the
same names, as the library does. -/

open scoped BigOperators MatrixOrder Matrix ComplexOrder
namespace MIPStarRE.QPBT

-- elaboration context of MIPStarRE/QPBT/Algebra/Lines.lean
section
variable {K : Type*} [Field K]

-- source: MIPStarRE/QPBT/Algebra/Lines.lean:39-45  (MIPStarRE.QPBT.coordinateDirection)
/-- The elementary coordinate direction used in the axis-parallel predicate of
blueprint `def:line`; paper origin
`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:106-124`.
-/
def coordinateDirection {m : ℕ}
    (i : Fin m) : Fin m → K :=
  Pi.single i 1

-- source: MIPStarRE/QPBT/Algebra/Lines.lean:79-88  (MIPStarRE.QPBT.lineRepMap)
/--
The canonical linear representative map of a line direction.  It projects onto
the coordinate complement of the span of `v`; for `v = 0` the span is bottom,
so the resulting map is the identity.  Blueprint `def:line-representative`;
paper origin
`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:143-174`.
-/
noncomputable def lineRepMap {m : ℕ}
    (v : Fin m → K) : (Fin m → K) →ₗ[K] (Fin m → K) :=
  canonicalProjOfKernel (Submodule.span K ({v} : Set (Fin m → K)))
end  -- module scope
end MIPStarRE.QPBT
