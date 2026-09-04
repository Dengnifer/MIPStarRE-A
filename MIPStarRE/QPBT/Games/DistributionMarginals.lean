import MIPStarRE.LDT.Basic.PMFAverages
import MIPStarRE.QPBT.Games.DistributionAux

/-!
# Marginals of probability distributions

The finite-distribution push-forward calculus gives corresponding identities
for probability mass functions and for projections transported across finite
equivalences.  These forms are used by the directly indexed low-degree
line-point laws and by the correspondence between the seed-indexed and directly
indexed question distributions.

## References

- `references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:243-272`
- `docs/paper-gaps/qpbt_ld-dimension-divisibility.tex`
-/

open scoped BigOperators

namespace MIPStarRE.QPBT

open MIPStarRE.LDT

/-- Two probabilistic finite distributions with the same stored support and
the same associated probability mass function are equal.  This is the PMF form
of `Distribution.ext_of_support_of_weight`, retained for the low-degree
marginal arguments that are stated using `Distribution.toPMF`. -/
theorem distribution_eq_of_support_eq_of_toPMF_eq {alpha : Type*}
    (mu nu : Distribution alpha) (hmu : mu.IsProbability)
    (hnu : nu.IsProbability) (hsupport : mu.support = nu.support)
    (hpmf : mu.toPMF hmu = nu.toPMF hnu) : mu = nu := by
  have hweight : mu.weight = nu.weight := by
    funext a
    calc
      mu.weight a = (mu.toPMF hmu a).toReal :=
        (Distribution.toPMF_apply_toReal mu hmu a).symm
      _ = (nu.toPMF hnu a).toReal := by rw [hpmf]
      _ = nu.weight a := Distribution.toPMF_apply_toReal nu hnu a
  exact Distribution.ext_of_support_of_weight hsupport hweight

/-- Composition of two push-forwards of a probabilistic finite distribution
is the push-forward by the composite map.  This probability-specialized form
is retained for the directly indexed low-degree marginal theorems. -/
theorem distribution_map_map_of_isProbability
    {alpha beta gamma : Type*} [DecidableEq beta] [DecidableEq gamma]
    (mu : Distribution alpha) (hmu : mu.IsProbability)
    (f : alpha → beta) (g : beta → gamma) :
    (mu.map f).map g = mu.map (g ∘ f) := by
  change (mu.map f).map g = mu.map fun a => g (f a)
  exact (fun _ : mu.IsProbability => Distribution.map_map mu f g) hmu

/-- Projection onto the first factor of an explicit finite product
equivalence sends the uniform distribution to the uniform first marginal.
This form combines invariance under equivalence with the uniform first-marginal
identity; it is `lem:uniform-first-marginal-after-equivalence` in blueprint
chapter 13. -/
theorem uniformDistribution_map_fst_of_equiv
    {alpha beta gamma : Type*}
    [Fintype alpha] [DecidableEq alpha] [Nonempty alpha]
    [Fintype beta] [DecidableEq beta] [Nonempty beta]
    [Finite gamma] [Nonempty gamma]
    (e : alpha ≃ beta × gamma) (f : alpha → beta)
    (hf : ∀ a, f a = (e a).1) :
    (uniformDistribution alpha).map f = uniformDistribution beta := by
  classical
  letI : Fintype gamma := Fintype.ofFinite gamma
  calc
    (uniformDistribution alpha).map f =
        (uniformDistribution alpha).map (fun a => (e a).1) := by
      congr 1
      funext a
      exact hf a
    _ = ((uniformDistribution alpha).map e).map Prod.fst :=
      (Distribution.map_map _ _ _).symm
    _ = (uniformDistribution (beta × gamma)).map Prod.fst := by
      rw [uniformDistribution_map_equiv]
    _ = uniformDistribution beta := uniformDistribution_map_fst

end MIPStarRE.QPBT
