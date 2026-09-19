import MIPStarRE.QPBT.Combining.Lines.WeightedCollision

/-!
# Collision bounds on a fixed nondegenerate line fiber

This module specializes the weighted collision estimate for the mixed
line-point distribution to the indicator of one fixed line.

## References

The estimate is the Schwartz--Zippel step in `lem:qld-xz-lines`,
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:950-955`.
-/

namespace MIPStarRE.QPBT

open MIPStarRE.LDT

noncomputable section

/-- On each nonzero-direction line fiber the collision mass is at most the
degree-to-field-size ratio times the fiber mass. Thus division by any positive
fiber mass gives the conditional probability required by `lem:pasting`. This
proof-only estimate supports paper `14_analysis_of_the_pauli_basis_test.tex:955`;
transport to the product law and the pasting register presentation is separate. -/
theorem linePointDist_nondegenerate_fiber_collision_le {L : LdParams} {bound : ℕ}
    (line : LineDesc L) (hdir : line.direction ≠ 0)
    (first second : DegPoly L bound) (hne : first ≠ second) :
    avgOver (linePointDist L) (fun sample =>
      if sample.1 = line then
        (if evalOpt sample.1 sample.2 first = evalOpt sample.1 sample.2 second
          then 1 else 0) else 0) ≤
      (bound : ℝ) / Fintype.card (ScalarQ L) *
        avgOver (linePointDist L) (fun sample => if sample.1 = line then 1 else 0) := by
  classical
  have hweight (other : LineDesc L) : (0 : ℝ) ≤ if other = line then 1 else 0 := by
    split_ifs <;> norm_num
  have hbound := linePointDist_nondegenerate_weighted_collision_le
    (fun other => if other = line then 1 else 0)
    hweight first second hne
  have hleft (sample : LineDesc L × (Fin L.m → ScalarQ L)) :
      (if sample.1.direction ≠ 0 then (if sample.1 = line then (1 : ℝ) else 0) *
        (if evalOpt sample.1 sample.2 first = evalOpt sample.1 sample.2 second
          then 1 else 0) else 0) =
      (if sample.1 = line then
        (if evalOpt sample.1 sample.2 first = evalOpt sample.1 sample.2 second
          then 1 else 0) else 0) := by
    by_cases heq : sample.1 = line <;> simp [heq, hdir]
  have hright (sample : LineDesc L × (Fin L.m → ScalarQ L)) :
      (if sample.1.direction ≠ 0 then (if sample.1 = line then (1 : ℝ) else 0) else 0) =
        (if sample.1 = line then 1 else 0) := by
    by_cases heq : sample.1 = line <;> simp [heq, hdir]
  simpa only [hleft, hright] using hbound

end

end MIPStarRE.QPBT
