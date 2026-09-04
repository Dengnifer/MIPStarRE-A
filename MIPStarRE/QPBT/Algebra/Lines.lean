import MIPStarRE.QPBT.Algebra.Subspaces

/-!
# Lines and canonical representatives

The classical and Pauli question distributions use affine lines in a finite
coordinate space.  This module keeps the zero-direction case explicit and
provides the canonical projection used for line representatives.

## References

The source-facing nodes are blueprint `def:line`, `prop:line-equiv`, and
`def:line-representative`.
The paper origin is `references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:102-174`.
-/

namespace MIPStarRE.QPBT

open scoped BigOperators

variable {K : Type*} [Field K]

/--
The affine line through `u` in direction `v`, including the singleton case
`v = 0`.  Blueprint `def:line`;
paper origin
`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:106-124`.
-/
def linePoints {m : ℕ}
    (u v : Fin m → K) : Set (Fin m → K) :=
  {x | ∃ t : K, x = u + t • v}

/-- The elementary coordinate direction used in the axis-parallel predicate of
blueprint `def:line`, paper origin
`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:106-124`.
-/
def coordinateDirection {m : ℕ}
    (i : Fin m) : Fin m → K :=
  Pi.single i 1

/--
`IsAxisParallel v` means that `v` is a standard coordinate direction.  This is
the axis-parallel clause of blueprint `def:line`; paper
`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:106-124`.
-/
def IsAxisParallel {m : ℕ} (v : Fin m → K) : Prop :=
  ∃ i : Fin m, v = coordinateDirection i

/--
The diagonal-direction predicate from `def:line`; a prefix of coordinates may
vanish.  Blueprint `def:line`; paper origin
`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:106-124`.
-/
def IsDiagonal {m : ℕ} (v : Fin m → K) : Prop :=
  ∃ i : Fin m, ∀ j : Fin m, j.1 < i.1 → v j = 0

/--
Changing the base point to another point on a line leaves the line unchanged.
This is blueprint `prop:line-equiv`,
with paper origin `references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:128-132`.
-/
theorem linePoints_eq_of_mem {m : ℕ}
    (u v u' : Fin m → K) (h : u' ∈ linePoints u v) :
    linePoints u v = linePoints u' v := by
  sorry

/--
The canonical linear representative map of a line direction.  It projects onto
the coordinate complement of the span of `v`; for `v = 0` the span is bottom,
so the resulting map is the identity.  Blueprint `def:line-representative`; paper origin
`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:143-174`.
-/
noncomputable def lineRepMap {m : ℕ}
    (v : Fin m → K) : (Fin m → K) →ₗ[K] (Fin m → K) :=
  canonicalProjOfKernel (Submodule.span K ({v} : Set (Fin m → K)))

/- The point-valued companion to `lineRepMap`; Lean-only notation for the
canonical representative in `def:line-representative`. -/
/-- The canonical representative point `lineRepMap v u`.  Blueprint
`def:line-representative`, paper origin
`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:166-174`.
-/
noncomputable def lineRep {m : ℕ}
    (u v : Fin m → K) : Fin m → K :=
  lineRepMap v u

end MIPStarRE.QPBT
