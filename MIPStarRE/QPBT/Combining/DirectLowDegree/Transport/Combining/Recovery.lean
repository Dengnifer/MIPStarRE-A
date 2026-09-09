import MIPStarRE.QPBT.Combining.DirectLowDegree.Transport.Combining.ExactLinearity

/-!
# The joint recovery estimate in the point and combining variables

`lem:ld-combining-recovery` compares the tuple of values at a point of the
components recovered from an outcome of the combined game with the tuple of
answers of the point measurement of the original game.  The comparison rests on
a joint estimate over the sampled point `u` and the sampled combining vector
`α`: for every outcome `p` of the combined game and every tuple `b` of scalars,
the event that the recovered tuple of values at `u` differs from `b` while the
value of `p` at the combined point agrees with the combination `∑_r α_r b_r`
has probability at most `(m + k) d / q`.

Two cases occur.  If `p` is the combined polynomial of a tuple `g`, its value at
the combined point is the combination `∑_r α_r g_r(u)`, and two combinations
with distinct coefficient tuples agree at a uniformly sampled `α` with
probability at most `1 / q`.  If `p` is not combined, then by
`lem:ld-combining-exact-linearity` its restriction `p(u, ·)` fails to be a
linear form except with probability `m d / q` over `u`, and off that event the
restriction and the linear form of `b` are distinct polynomials of total degree
at most `k d`, so they agree at a uniformly sampled `α` with probability at
most `k d / q`.

The estimate is recorded in two stages, because the consistency calculus
averages it against Born weights which depend on the sampled point but not on
the sampled combining vector: a bound at a fixed point which does not depend on
the tuple `b`, and the average of that bound over the point.

## Main statements

* `directCombinedRecoveryLocalBound` — the bound at a fixed point.
* `directCombinedRecoveryEvent_avg_le` — the estimate at a fixed point.
* `directCombinedRecoveryLocalBound_avg_le` — the average of the bound at a
  fixed point over a uniformly sampled point.
* `directCombinedRecoveryBadEvent_avg_le` — the joint estimate of
  `lem:ld-combining-recovery`.

## References

* `references/neexp-paper/05_quantum_preliminaries.tex:1440-1503`
* `references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:413-458`
* `blueprint/src/chapter/ch13_qpbt_test.tex:617-680`
-/

open scoped BigOperators

namespace MIPStarRE.QPBT

open MIPStarRE.LDT
open MIPStarRE.LDT.Preliminaries

noncomputable section

/-! ## Elementary facts about the parameters -/

/-- The field size of a directly indexed low-degree game is positive. -/
theorem directLdFieldSize_pos (D : DirectLdParams) : (0 : ℝ) < (D.q : ℝ) := by
  have h : 0 < Fintype.card (DirectScalarQ D) := Fintype.card_pos
  rw [card_directScalarQ] at h
  exact_mod_cast h

/-- Commuting the two factors of a combination of a tuple of scalars. -/
private theorem directCombiningSum_comm {K : Type*} [CommSemiring K] {k : ℕ}
    (c α : Fin k → K) : ∑ r : Fin k, α r * c r = ∑ r : Fin k, c r * α r :=
  Finset.sum_congr rfl fun _ _ => mul_comm _ _

/-- The rational bound produced by the Schwartz--Zippel estimates, read in the
field size of the directly indexed game. -/
private theorem directCombiningRatio_eq (D : DirectLdParams) (n : ℕ) :
    ((((n : ℕ) : ℚ≥0) / Fintype.card (DirectScalarQ D) : ℚ≥0) : Error) =
      ((n : ℕ) : Error) / D.q := by
  rw [card_directScalarQ]
  push_cast
  ring

/-! ## The collision estimates in the combining variables -/

open scoped Classical in
/-- Collision of two combinations with distinct coefficient tuples, written with
the combining vector as the left factor. -/
private theorem directCombiningCollision_avg_le_comm (D : DirectLdParams)
    (c b : Fin D.k → DirectScalarQ D) (hne : c ≠ b) :
    avgOver (uniformDistribution (Fin D.k → DirectScalarQ D))
        (fun α => if ∑ r : Fin D.k, α r * c r = ∑ r : Fin D.k, α r * b r then
          (1 : Error) else 0) ≤ (1 : Error) / D.q := by
  refine le_trans (le_of_eq (avgOver_congr _ _ _ fun α => ?_))
    (directCombiningCollision_avg_le D c b hne)
  rw [directCombiningSum_comm c α, directCombiningSum_comm b α]

set_option maxHeartbeats 1000000 in
open scoped Classical in
/-- Collision of a restriction which is not a linear form with the linear form
of a tuple of scalars, written with the combining vector as the left factor. -/
private theorem directCombinedRestrictCollision_avg_le (D : DirectLdParams)
    (p : PolyIndex D.combined.m (DirectScalarQ D) D.d)
    (u : Fin D.m → DirectScalarQ D) (b : Fin D.k → DirectScalarQ D)
    (hu : ∀ c : Fin D.k → DirectScalarQ D,
      combinedRestrict p.1 u ≠ combiningLinearForm c) :
    avgOver (uniformDistribution (Fin D.k → DirectScalarQ D))
        (fun α => if MvPolynomial.eval (combinedPoint u α) p.1 =
          ∑ r : Fin D.k, α r * b r then (1 : Error) else 0) ≤
      ((D.k * D.d : ℕ) : Error) / D.q := by
  have hkd : 1 ≤ D.k * D.d := by simpa using Nat.mul_le_mul D.hk D.hd
  have hbound := combinedRestrict_collision_avg_le (d := D.d) p.2 hkd u b hu
  refine le_trans (le_of_eq (avgOver_congr _ _ _ fun α => ?_))
    (le_trans hbound (le_of_eq (directCombiningRatio_eq D (D.k * D.d))))
  rw [directCombiningSum_comm b α]

/-! ## The estimate at a fixed point -/

open scoped Classical in
/-- The bound at a fixed point of the recovery step: the collision probability
`1 / q` of two combinations when the outcome is combined, and otherwise the
indicator that the restriction of the outcome at the point is a linear form
together with the collision probability `k d / q` of two polynomials of total
degree at most `k d` in the combining variables. -/
def directCombinedRecoveryLocalBound (D : DirectLdParams)
    (p : PolyIndex D.combined.m (DirectScalarQ D) D.d)
    (u : Fin D.m → DirectScalarQ D) : Error :=
  if IsDirectCombined D p then (1 : Error) / D.q
  else
    (if ∃ c : Fin D.k → DirectScalarQ D,
        combinedRestrict p.1 u = combiningLinearForm c then (1 : Error) else 0) +
      ((D.k * D.d : ℕ) : Error) / D.q

/-- The bound at a fixed point of the recovery step is nonnegative. -/
theorem directCombinedRecoveryLocalBound_nonneg (D : DirectLdParams)
    (p : PolyIndex D.combined.m (DirectScalarQ D) D.d)
    (u : Fin D.m → DirectScalarQ D) :
    0 ≤ directCombinedRecoveryLocalBound D p u := by
  classical
  have hq := directLdFieldSize_pos D
  have hkd : (0 : Error) ≤ ((D.k * D.d : ℕ) : Error) / D.q := by positivity
  rw [directCombinedRecoveryLocalBound]
  split_ifs
  · positivity
  · linarith
  · linarith

set_option maxHeartbeats 1600000 in
open scoped Classical in
/-- Estimate at a fixed point of `lem:ld-combining-recovery`.  For a fixed
outcome `p` of the combined game, a fixed point `u` and a fixed tuple `b` of
scalars, the probability, over a uniformly sampled combining vector `α`, that
the tuple of values at `u` of the components recovered from `p` differs from `b`
while the value of `p` at the combined point with parts `u` and `α` equals the
combination `∑_r α_r b_r`, is at most the bound at the point.  The bound does
not depend on the tuple `b`. -/
theorem directCombinedRecoveryEvent_avg_le (D : DirectLdParams)
    (p : PolyIndex D.combined.m (DirectScalarQ D) D.d)
    (u : Fin D.m → DirectScalarQ D) (b : Fin D.k → DirectScalarQ D) :
    avgOver (uniformDistribution (Fin D.k → DirectScalarQ D)) (fun α =>
        if evalDirectPolyTupleAt u (directTupleOfCombined D p) ≠ b ∧
            MvPolynomial.eval (combinedPoint u α) p.1 =
              ∑ r : Fin D.k, α r * b r then (1 : Error) else 0) ≤
      directCombinedRecoveryLocalBound D p u := by
  classical
  have hq := directLdFieldSize_pos D
  rw [directCombinedRecoveryLocalBound]
  by_cases hc : IsDirectCombined D p
  · rw [if_pos hc]
    obtain ⟨g, hg⟩ := hc
    subst hg
    rw [directTupleOfCombined_directCombinedPolynomial]
    by_cases hub : evalDirectPolyTupleAt u g = b
    · have hzero : ∀ α : Fin D.k → DirectScalarQ D,
          (if evalDirectPolyTupleAt u g ≠ b ∧
              MvPolynomial.eval (combinedPoint u α)
                  (directCombinedPolynomial D g).1 =
                ∑ r : Fin D.k, α r * b r then (1 : Error) else 0) = 0 := by
        intro α
        refine if_neg ?_
        rintro ⟨hne, -⟩
        exact hne hub
      rw [avgOver_congr _ _ _ hzero, avgOver_zero]
      positivity
    · refine le_trans (avgOver_mono _ _
        (fun α => if ∑ r : Fin D.k, α r * evalDirectPolyTupleAt u g r =
          ∑ r : Fin D.k, α r * b r then (1 : Error) else 0) fun α => ?_)
        (directCombiningCollision_avg_le_comm D _ b hub)
      by_cases hev : evalDirectPolyTupleAt u g ≠ b ∧
          MvPolynomial.eval (combinedPoint u α)
              (directCombinedPolynomial D g).1 =
            ∑ r : Fin D.k, α r * b r
      · have h2 := hev.2
        rw [directCombinedPolynomial_eval] at h2
        rw [if_pos hev, if_pos h2]
      · rw [if_neg hev]
        split_ifs
        · exact zero_le_one
        · exact le_rfl
  · rw [if_neg hc]
    by_cases hu : ∃ c : Fin D.k → DirectScalarQ D,
        combinedRestrict p.1 u = combiningLinearForm c
    · rw [if_pos hu]
      have hkd : (0 : Error) ≤ ((D.k * D.d : ℕ) : Error) / D.q := by positivity
      refine le_trans (avgOver_mono _ _ (fun _ => (1 : Error)) fun α => ?_) ?_
      · split_ifs
        · exact le_rfl
        · exact zero_le_one
      · rw [avgOver_uniform_const]
        linarith
    · rw [if_neg hu, zero_add]
      push Not at hu
      refine le_trans (avgOver_mono _ _
        (fun α => if MvPolynomial.eval (combinedPoint u α) p.1 =
          ∑ r : Fin D.k, α r * b r then (1 : Error) else 0) fun α => ?_)
        (directCombinedRestrictCollision_avg_le D p u b hu)
      split_ifs with h1 h2
      · exact le_rfl
      · exact absurd h1.2 h2
      · exact zero_le_one
      · exact le_rfl

/-! ## The averaged estimate -/

set_option maxHeartbeats 800000 in
open scoped Classical in
/-- The bound at a fixed point of the recovery step averages to at most
`(m + k) d / q` over a uniformly sampled point.  For a combined outcome the
bound is the constant `1 / q`; for a non-combined outcome the indicator that the
restriction is a linear form averages to at most `m d / q` by
`lem:ld-combining-exact-linearity`. -/
theorem directCombinedRecoveryLocalBound_avg_le (D : DirectLdParams)
    (p : PolyIndex D.combined.m (DirectScalarQ D) D.d) :
    avgOver (uniformDistribution (Fin D.m → DirectScalarQ D))
        (directCombinedRecoveryLocalBound D p) ≤
      ((D.combined.m * D.d : ℕ) : Error) / D.q := by
  classical
  have hq := directLdFieldSize_pos D
  have hsplit : ((D.combined.m * D.d : ℕ) : Error) / D.q =
      ((D.m * D.d : ℕ) : Error) / D.q + ((D.k * D.d : ℕ) : Error) / D.q := by
    have hn : (D.combined.m * D.d : ℕ) = D.m * D.d + D.k * D.d := by
      simp [DirectLdParams.combined_m, Nat.add_mul]
    rw [hn]
    push_cast
    ring
  by_cases hc : IsDirectCombined D p
  · have hconst : ∀ u : Fin D.m → DirectScalarQ D,
        directCombinedRecoveryLocalBound D p u = (1 : Error) / D.q := by
      intro u
      rw [directCombinedRecoveryLocalBound, if_pos hc]
    rw [avgOver_congr _ _ _ hconst, avgOver_uniform_const]
    have h1 : (1 : Error) ≤ ((D.combined.m * D.d : ℕ) : Error) := by
      have hle : 1 ≤ D.combined.m * D.d := by
        simpa using Nat.mul_le_mul D.combined.hm D.combined.hd
      exact_mod_cast hle
    exact div_le_div_of_nonneg_right h1 hq.le
  · have hlin := directCombinedExactLinearity_avg_le D p hc
    have heq : ∀ u : Fin D.m → DirectScalarQ D,
        directCombinedRecoveryLocalBound D p u =
          (if ∃ c : Fin D.k → DirectScalarQ D,
              combinedRestrict p.1 u = combiningLinearForm c then (1 : Error)
            else 0) + ((D.k * D.d : ℕ) : Error) / D.q := by
      intro u
      rw [directCombinedRecoveryLocalBound, if_neg hc]
    rw [avgOver_congr _ _ _ heq, avgOver_add, avgOver_uniform_const, hsplit]
    linarith [hlin]

set_option maxHeartbeats 800000 in
open scoped Classical in
/-- Joint estimate of `lem:ld-combining-recovery`.  For a fixed outcome `p` of
the combined game and a fixed tuple `b` of scalars, the probability, over a
uniformly sampled point `u` of the original space and a uniformly sampled
combining vector `α`, that the tuple of values at `u` of the components
recovered from `p` differs from `b` while the value of `p` at the combined point
with parts `u` and `α` equals the combination `∑_r α_r b_r`, is at most
`(m + k) d / q`. -/
theorem directCombinedRecoveryBadEvent_avg_le (D : DirectLdParams)
    (p : PolyIndex D.combined.m (DirectScalarQ D) D.d)
    (b : Fin D.k → DirectScalarQ D) :
    avgOver (uniformDistribution (Fin D.m → DirectScalarQ D)) (fun u =>
        avgOver (uniformDistribution (Fin D.k → DirectScalarQ D)) (fun α =>
          if evalDirectPolyTupleAt u (directTupleOfCombined D p) ≠ b ∧
              MvPolynomial.eval (combinedPoint u α) p.1 =
                ∑ r : Fin D.k, α r * b r then (1 : Error) else 0)) ≤
      ((D.combined.m * D.d : ℕ) : Error) / D.q :=
  le_trans
    (avgOver_mono _ _ (directCombinedRecoveryLocalBound D p)
      fun u => directCombinedRecoveryEvent_avg_le D p u b)
    (directCombinedRecoveryLocalBound_avg_le D p)

end

end MIPStarRE.QPBT
