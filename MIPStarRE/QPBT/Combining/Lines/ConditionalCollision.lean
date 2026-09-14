import MIPStarRE.QPBT.Combining.Lines.FiberCollision
import MIPStarRE.QPBT.Combining.Lines.NondegeneratePastingDistribution
import MIPStarRE.QPBT.Combining.Lines.ProductWeightedCollision
import MIPStarRE.QPBT.Games.RestrictedAverage
import MIPStarRE.QPBT.Observables.WinImplications.Setup

/-!
# Conditional collision bound for nondegenerate line pasting

This module verifies the conditional collision hypothesis used when applying
the pasting lemma to the proof-only nondegenerate line-pasting distribution.

## References

The collision estimate supports `lem:qld-xz-lines` at
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:950-963` and
instantiates the hypothesis of `lem:pasting` at
`references/qpbt-paper/06_nonlocal_games_and_mipstar.tex:504-525`.
-/

namespace MIPStarRE.QPBT

open MIPStarRE.LDT

noncomputable section

/-- The concrete nondegenerate line-pasting distribution satisfies the
conditional collision bound required by `lem:pasting`. This is the
formalization-only Schwartz--Zippel conditioning auxiliary used in
`lem:qld-xz-lines`, paper lines 950--963. -/
theorem nondegenerateLinePastingDist_collision_bound
    (P : AdmissibleParams) (bound : ℕ) :
    HasConditionalCollisionBound (nondegenerateLinePastingDist P.toLdParams)
      (fun (poly : DegPoly P.toLdParams bound) sample => evalOpt sample.1 sample.2 poly)
      ((bound : ℝ) / Fintype.card (ScalarQ P.toLdParams)) := by
  classical
  let L := P.toLdParams
  apply collision_bound_of_fiber_averages
  intro fixed first second hne
  simp only [nondegenerateLinePastingDist, Distribution.avgOver_map]
  have hpos := prod_linePointDist_nondegenerate_mass_pos L
  apply (mul_le_mul_iff_right₀ hpos).mp
  rw [avgOver_restrict_mul_mass, mul_left_comm _ ((bound : ℝ) /
    Fintype.card (ScalarQ L)), avgOver_restrict_mul_mass]
  have h := prod_linePointDist_nondegenerate_weighted_collision_le
    (fun line sample => if ((line, sample.1), sample) = fixed then 1 else 0)
    (fun line sample => by split_ifs <;> norm_num) first second hne
  have hswap (condition other : Prop) [Decidable condition] [Decidable other] (value : ℝ) :
      (if condition then (if other then value else 0) else 0) =
        (if other then (if condition then value else 0) else 0) := by
    split_ifs <;> rfl
  simpa only [avgOver, Finset.sum_filter, mul_ite, mul_one, mul_zero,
    ite_mul, one_mul, zero_mul, hswap] using h

end

end MIPStarRE.QPBT
