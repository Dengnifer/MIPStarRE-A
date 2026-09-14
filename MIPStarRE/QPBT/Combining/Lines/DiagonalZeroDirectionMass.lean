import MIPStarRE.QPBT.Observables.LineDefs

/-!
# Zero-direction mass for diagonal lines

This module bounds the zero-direction mass of the diagonal component of the
line-point sampler by the inverse scalar-field size.

## References

The sampler is `def:line-point-dist`, from
`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:274-287`.
-/

namespace MIPStarRE.QPBT

open MIPStarRE.LDT

noncomputable section

private theorem dLineDescOf_ldDLineCL_direction (L : LdParams) (z : LdSpace L) :
    (dLineDescOf L (ldDLineCL L z)).direction = (dLineDescOf L z).direction := by
  exact prefixProjection_idempotent _ _

/-- Under the unchanged diagonal line-point law, zero projected directions have
probability at most the inverse field size: the final raw direction coordinate
must vanish and is uniform. This is a formalization-only consequence of
`def:line-point-dist`, paper `08_classical_and_quantum_low_degree_tests.tex:274-287`. -/
theorem dLinePointDist_zero_direction_mass_le (L : LdParams) :
    avgOver (dLinePointDist L) (fun sample =>
      if sample.1.direction = 0 then 1 else 0) ≤
      1 / Fintype.card (ScalarQ L) := by
  classical
  let last : Fin L.m := ⟨L.m - 1, by have := L.hm; omega⟩
  let coord : LdIndex L := .inr last
  have hmap : (uniformDistribution (LdSpace L)).map (fun raw => raw coord) =
      uniformDistribution (ScalarQ L) := by
    change (uniformDistribution (LdSpace L)).map
      (fun raw => (Equiv.funSplitAt coord (ScalarQ L) raw).1) = _
    rw [← Distribution.map_map, uniformDistribution_map_equiv,
      uniformDistribution_map_fst]
  have hzero : avgOver (uniformDistribution (LdSpace L))
      (fun raw => if raw coord = 0 then (1 : ℝ) else 0) =
      1 / Fintype.card (ScalarQ L) := by
    rw [← Distribution.avgOver_map (uniformDistribution (LdSpace L))
      (fun raw => raw coord) (fun value => if value = 0 then (1 : ℝ) else 0), hmap]
    simp [avgOver, uniformDistribution_weight_apply, mul_ite]
  unfold dLinePointDist clDistribution
  rw [Distribution.avgOver_map, Distribution.avgOver_map]
  refine le_trans (avgOver_mono _ _ _ ?_) hzero.le
  intro raw
  dsimp only
  rw [dLineDescOf_ldDLineCL_direction]
  split_ifs with hdir hcoord hcoord
  · exact le_rfl
  · exfalso
    apply hcoord
    have hlast := congrFun hdir last
    change prefixProjection (chiIndex L (LdSpace.seed raw))
      (LdSpace.direction raw) last = 0 at hlast
    have hindex : ¬ last.val < (chiIndex L (LdSpace.seed raw)).val := by
      have := (chiIndex L (LdSpace.seed raw)).isLt
      dsimp [last]
      omega
    simpa [prefixProjection, hindex, LdSpace.direction, coord] using hlast
  · norm_num
  · exact le_rfl

end

end MIPStarRE.QPBT
