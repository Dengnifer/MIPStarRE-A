import MIPStarRE.QPBT.Algebra.Subspaces

/-!
# Lines and canonical representatives

The classical and Pauli question distributions use affine lines in a finite
coordinate space.  This module keeps the zero-direction case explicit and
provides the canonical projection used for line representatives.

## References

The source-facing nodes are `def:line`, `prop:line-equiv`, and
`def:line-representative` in `blueprint/src/chapter/ch11_qpbt_algebra.tex:464-520`;
the formalization support nodes `lem:line-rep-kernel` and
`lem:line-rep-incidence` are at `ch11_qpbt_algebra.tex:522-550`.
The paper origin is `references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:102-174`.
-/

namespace MIPStarRE.QPBT

open scoped BigOperators

variable {K : Type*} [Field K]

/--
The affine line through `u` in direction `v`, including the singleton case
`v = 0`.  Blueprint `def:line`, `blueprint/src/chapter/ch11_qpbt_algebra.tex:464-478`;
paper origin
`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:106-124`.
-/
def linePoints {m : ℕ}
    (u v : Fin m → K) : Set (Fin m → K) :=
  {x | ∃ t : K, x = u + t • v}

/-- The elementary coordinate direction used in the axis-parallel predicate of
`def:line`; blueprint `ch11_qpbt_algebra.tex:464-478`, paper origin
`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:106-124`.
-/
def coordinateDirection {m : ℕ}
    (i : Fin m) : Fin m → K :=
  Pi.single i 1

/--
`IsAxisParallel v` means that `v` is a standard coordinate direction.  This is
the axis-parallel clause of `def:line` (blueprint lines 464-478; paper
`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:106-124`).
-/
def IsAxisParallel {m : ℕ} (v : Fin m → K) : Prop :=
  ∃ i : Fin m, v = coordinateDirection i

/--
The diagonal-direction predicate from `def:line`; a prefix of coordinates may
vanish.  Blueprint `blueprint/src/chapter/ch11_qpbt_algebra.tex:464-478`; paper origin
`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:106-124`.
-/
def IsDiagonal {m : ℕ} (v : Fin m → K) : Prop :=
  ∃ i : Fin m, ∀ j : Fin m, j.1 < i.1 → v j = 0

/--
Changing the base point to another point on a line leaves the line unchanged.
This is `prop:line-equiv` in `blueprint/src/chapter/ch11_qpbt_algebra.tex:480-486`,
with paper origin `references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:128-132`.
-/
theorem linePoints_eq_of_mem {m : ℕ}
    (u v u' : Fin m → K) (h : u' ∈ linePoints u v) :
    linePoints u v = linePoints u' v := by
  obtain ⟨t, rfl⟩ := h
  ext x
  constructor
  · rintro ⟨s, rfl⟩
    exact ⟨s - t, by module⟩
  · rintro ⟨s, rfl⟩
    exact ⟨t + s, by module⟩

/--
The canonical linear representative map of a line direction.  It projects onto
the coordinate complement of the span of `v`; for `v = 0` the span is bottom,
so the resulting map is the identity.  Blueprint `def:line-representative`,
`blueprint/src/chapter/ch11_qpbt_algebra.tex:500-520`; paper origin
`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:143-174`.
-/
noncomputable def lineRepMap {m : ℕ}
    (v : Fin m → K) : (Fin m → K) →ₗ[K] (Fin m → K) :=
  canonicalProjOfKernel (Submodule.span K ({v} : Set (Fin m → K)))

/- The point-valued companion to `lineRepMap`; Lean-only notation for the
canonical representative in `def:line-representative`. -/
/-- The canonical representative point `lineRepMap v u`.  Blueprint
`blueprint/src/chapter/ch11_qpbt_algebra.tex:500-520`, paper origin
`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:166-174`.
-/
noncomputable def lineRep {m : ℕ}
    (u v : Fin m → K) : Fin m → K :=
  lineRepMap v u

/--
Formalization support node `lem:line-rep-kernel` for
`def:line-representative` (blueprint
`blueprint/src/chapter/ch11_qpbt_algebra.tex:522-530`, paper origin
`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:143-174`).
The canonical representative map is a projection whose kernel is the line
`K v`, so a point and its canonical representative differ by a scalar multiple
of the direction.
-/
theorem sub_lineRepMap_mem_span {m : ℕ} (v u : Fin m → K) :
    u - lineRepMap v u ∈ Submodule.span K ({v} : Set (Fin m → K)) := by
  have hc :
      IsCompl
        (registerSubmodule K
          (canonicalComplement (Submodule.span K ({v} : Set (Fin m → K)))))
        (Submodule.span K ({v} : Set (Fin m → K))) :=
    (isCompl_registerSubmodule_canonicalComplement
      (Submodule.span K ({v} : Set (Fin m → K)))).symm
  have hrep : lineRepMap v u =
      (registerSubmodule K
        (canonicalComplement (Submodule.span K ({v} : Set (Fin m → K))))).projection
        (Submodule.span K ({v} : Set (Fin m → K))) hc u := rfl
  rw [hrep, ← Submodule.projection_eq_self_sub_projection hc u]
  exact Submodule.projection_apply_mem hc.symm u

/--
Formalization support node `lem:line-rep-incidence` for
`def:line-representative` (blueprint
`blueprint/src/chapter/ch11_qpbt_algebra.tex:537-545`, paper origin
`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:166-174`).
Every point lies on the line through its own canonical representative in the
same direction; this is the incidence property used by the line-versus-point
samplers.
-/
theorem mem_linePoints_lineRepMap {m : ℕ} (v u : Fin m → K) :
    u ∈ linePoints (lineRepMap v u) v := by
  obtain ⟨t, ht⟩ := Submodule.mem_span_singleton.mp (sub_lineRepMap_mem_span v u)
  exact ⟨t, by rw [ht]; abel⟩

end MIPStarRE.QPBT
