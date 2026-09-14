import MIPStarRE.QPBT.Combining.Points.Absorption

/-!
# Marginal contraction for combined point measurements

This module records a formalization-only auxiliary estimate for recovering a
marginal operator from a projective refinement. It combines the two contraction
steps in the combined-line argument into a pointwise factor-four bound.

## References

Paper `references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:902-927`.
-/

open scoped BigOperators Matrix MatrixOrder ComplexOrder

namespace MIPStarRE.QPBT

open MIPStarRE.LDT hiding Measurement
open MIPStarRE.Quantum

noncomputable section

/-- A formalization-only auxiliary lemma: summing a projective refinement close to
`B_b D` recovers `D` with four times the squared-distance error.

It combines the absorption and orthogonal-projector contraction yielding `eq:qqm`
with the subsequent contraction through the projective measurement `B` used to obtain
`eq:qld-qxz-close-to-point` (paper lines 902--927). The bound is pointwise for a fixed
marginal fiber `Q`, with factor four from the squared triangle inequality; the paper
sums over outcomes and averages over questions. Completeness is required of `B`,
not of `Q`. -/
theorem norm_marginal_sub_sq_le {β ι : Type*} [Fintype β]
    [Fintype ι] [DecidableEq ι] (Q : β → Op ι)
    (hQ : ∀ b, IsProj (Q b))
    (horth : ∀ {b c}, b ≠ c → Q b * Q c = 0)
    (B : Quantum.Measurement β ι) (hB : Measurement.IsProjective B)
    (hcomm : ∀ b, Q b * B.effect b = B.effect b * Q b)
    (D : Op ι) (ψ : EuclideanSpace ℂ ι) :
    ‖applyOperatorToState ((∑ b, Q b) - D) ψ‖ ^ 2 ≤
      4 * ∑ b, ‖applyOperatorToState (Q b - B.effect b * D) ψ‖ ^ 2 := by
  classical
  let U : Op ι := ∑ b, Q b * (Q b - B.effect b * Q b)
  let V : Op ι := ∑ b, B.effect b * (Q b - B.effect b * D)
  have hU : ‖applyOperatorToState U ψ‖ ^ 2 ≤
      ∑ b, ‖applyOperatorToState (Q b - B.effect b * D) ψ‖ ^ 2 := by
    refine le_trans (DistanceCalculus.norm_finset_sum_projector_mul_sq_le
      Q (fun b => Q b - B.effect b * Q b) hQ horth Finset.univ ψ) ?_
    exact Finset.sum_le_sum fun b _ => norm_sub_projective_mul_sq_le B hB b (Q b) D ψ
  have hV : ‖applyOperatorToState V ψ‖ ^ 2 ≤
      ∑ b, ‖applyOperatorToState (Q b - B.effect b * D) ψ‖ ^ 2 :=
    DistanceCalculus.norm_finset_sum_projector_mul_sq_le B.effect
      (fun b => Q b - B.effect b * D) hB
      (fun hbc => DistanceCalculus.projective_effect_mul_effect_eq_zero B hB hbc)
      Finset.univ ψ
  have hsum : (∑ b, Q b) - D = U + V := by
    have hfirst : U = ∑ b, (Q b - B.effect b * Q b) := by
      apply Finset.sum_congr rfl
      intro b _
      rw [mul_sub, ← mul_assoc, hcomm b, mul_assoc,
        (hQ b).isIdempotentElem.eq]
    have hsecond : V = (∑ b, B.effect b * Q b) - D := by
      dsimp [V]
      simp only [mul_sub, ← mul_assoc, (hB _).isIdempotentElem.eq,
        Finset.sum_sub_distrib, ← Finset.sum_mul, B.sum_eq_one, one_mul]
    rw [hfirst, hsecond, Finset.sum_sub_distrib]
    abel
  rw [hsum]
  have htriangle : ‖applyOperatorToState (U + V) ψ‖ ≤
      ‖applyOperatorToState U ψ‖ + ‖applyOperatorToState V ψ‖ := by
    simpa only [applyOperatorToState, map_add, LinearMap.add_apply] using
      norm_add_le (applyOperatorToState U ψ) (applyOperatorToState V ψ)
  have hsquare := pow_le_pow_left₀ (norm_nonneg _) htriangle 2
  nlinarith [sq_nonneg (‖applyOperatorToState U ψ‖ - ‖applyOperatorToState V ψ‖)]

end

end MIPStarRE.QPBT
