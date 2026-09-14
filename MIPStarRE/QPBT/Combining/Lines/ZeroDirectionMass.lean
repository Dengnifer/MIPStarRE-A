import MIPStarRE.QPBT.Observables.LineDefs

/-!
# Zero-direction mass for axis lines

This module records that the axis-line component of the line-point sampler has
no mass at zero direction.

## References

The sampler is `def:line-point-dist`, from
`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:274-287`.
-/

namespace MIPStarRE.QPBT

open MIPStarRE.LDT

noncomputable section

/-- Axis-line sampling gives zero mass to zero directions, since a coordinate
direction is nonzero. This is a formalization-only consequence of
`def:line-point-dist`, paper `08_classical_and_quantum_low_degree_tests.tex:274-287`. -/
theorem aLinePointDist_zero_direction_mass (L : LdParams) :
    avgOver (aLinePointDist L) (fun sample =>
      if sample.1.direction = 0 then 1 else 0) = 0 := by
  classical
  unfold aLinePointDist
  rw [Distribution.avgOver_map]
  have hdir (raw : LdSpace L) : (aLineDescOf L raw).direction ≠ 0 := by
    intro hzero
    have hcoord := congrFun hzero (chiIndex L raw.seed)
    simp [aLineDescOf, LineDesc.direction, coordinateDirection] at hcoord
  simp [avgOver, hdir]

end

end MIPStarRE.QPBT
