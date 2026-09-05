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

/-- Two finite probability distributions with the same support and the same
probability mass at every point are equal. -/
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

/-- Formalization-only lemma for the low-degree sampling laws: if an
equivalence identifies a nonempty finite set with the product of two nonempty
finite sets and a map agrees with the first projection, then the map sends the
uniform law to the uniform law on the first factor.  This is
`lem:uniform-first-marginal-after-equivalence` in blueprint chapter 13. -/
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
