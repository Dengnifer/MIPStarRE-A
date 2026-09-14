import MIPStarRE.QPBT.Games.Sandwich.Defs

/-!
# Conditional collision bounds from fiber averages

This module converts an unnormalized collision estimate on every first-question
fiber into the positive-mass conditional collision predicate used by the
pasting theorem.

## References

The conditional collision hypothesis is from `lem:pasting`,
`references/qpbt-paper/06_nonlocal_games_and_mipstar.tex:504-525`. Its use in
the QPBT combining argument occurs at
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:950-963`.
-/

open scoped BigOperators

namespace MIPStarRE.QPBT

open MIPStarRE.LDT

noncomputable section

/-- An unnormalized collision estimate on every first-question fiber implies
the positive-mass conditional collision predicate of `lem:pasting`. This is a
formalization-only normalization adapter for paper lines 504--525. -/
theorem collision_bound_of_fiber_averages {X Y₁ Y₂ R₂ Γ₂ : Type*}
    [Fintype X] [DecidableEq X] [Fintype Y₁] [DecidableEq Y₁]
    [Fintype Y₂] [DecidableEq Y₂] [Fintype R₂] [DecidableEq R₂]
    [Fintype Γ₂] (dist : Distribution ((X × Y₁) × Y₂))
    (eval₂ : Γ₂ → Y₂ → R₂) (eta : ℝ)
    (hbound : ∀ fixed : X × Y₁, ∀ first second : Γ₂, first ≠ second →
      avgOver dist (fun sample => if sample.1 = fixed then
        (if eval₂ first sample.2 = eval₂ second sample.2 then 1 else 0) else 0) ≤
      eta * avgOver dist (fun sample => if sample.1 = fixed then 1 else 0)) :
    HasConditionalCollisionBound dist eval₂ eta := by
  classical
  intro question point _ first second hne
  have havg (value : ((X × Y₁) × Y₂) → ℝ) :
      avgOver dist value = ∑ sample, dist.weight sample * value sample := by
    exact (dist.sum_univ_eq_sum_support _ (fun sample hout => by
      rw [dist.outsideSupport sample hout, zero_mul])).symm
  have hmass : (dist.map Prod.fst).weight (question, point) =
      avgOver dist (fun sample => if sample.1 = (question, point) then 1 else 0) := by
    rw [Distribution.map_weight]
    unfold avgOver
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro sample _
    by_cases hfixed : sample.1 = (question, point) <;> simp [hfixed]
  rw [hmass]
  have h := hbound (question, point) first second hne
  simpa [havg, Fintype.sum_prod_type, mul_ite] using h

end

end MIPStarRE.QPBT
