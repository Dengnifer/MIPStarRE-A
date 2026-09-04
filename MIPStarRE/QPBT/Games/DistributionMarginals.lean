import MIPStarRE.LDT.Basic.PMFAverages

/-!
# Marginals of finite distributions

Shared push-forward lemmas for the project's finite `Distribution` type:
extensionality through the associated probability mass function, composition
of push-forwards, and the uniform first marginal of the uniform law on an
explicit finite product.  They serve the marginal statements `lem:alnf` and
`lem:dlnf` of the low-degree line-point laws and the question-law transport
between the seed-indexed and directly indexed low-degree games.

## References

- `references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:243-272`
- `docs/paper-gaps/qpbt_ld-dimension-divisibility.tex`
-/

open scoped BigOperators

namespace MIPStarRE.QPBT

open MIPStarRE.LDT

/-- Two probabilistic finite distributions with the same stored support and
the same associated probability mass function are equal. -/
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
  cases mu with
  | mk muSupport muWeight muNonnegative muOutsideSupport =>
      cases nu with
      | mk nuSupport nuWeight nuNonnegative nuOutsideSupport =>
          cases hsupport
          cases hweight
          rfl

/-- Composition of two push-forwards of a probabilistic finite distribution
is the push-forward by the composite map. -/
theorem distribution_map_map_of_isProbability
    {alpha beta gamma : Type*} [DecidableEq beta] [DecidableEq gamma]
    (mu : Distribution alpha) (hmu : mu.IsProbability)
    (f : alpha → beta) (g : beta → gamma) :
    (mu.map f).map g = mu.map (g ∘ f) := by
  apply distribution_eq_of_support_eq_of_toPMF_eq
    ((mu.map f).map g) (mu.map (g ∘ f))
    ((hmu.map f).map g) (hmu.map (g ∘ f))
  · simp [Distribution.map_support, Finset.image_image]
  · calc
      ((mu.map f).map g).toPMF ((hmu.map f).map g) =
          ((mu.map f).toPMF (hmu.map f)).map g :=
        Distribution.toPMF_map (mu.map f) (hmu.map f) g
      _ = ((mu.toPMF hmu).map f).map g := by
        rw [Distribution.toPMF_map mu hmu f]
      _ = (mu.toPMF hmu).map (g ∘ f) :=
        PMF.map_comp f (mu.toPMF hmu) g
      _ = (mu.map (g ∘ f)).toPMF (hmu.map (g ∘ f)) :=
        (Distribution.toPMF_map mu hmu (g ∘ f)).symm

/-- Projection onto the first factor of an explicit finite product
equivalence sends the uniform distribution to the uniform first marginal. -/
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
  have hsurjective : Function.Surjective f := by
    intro b
    let c : gamma := Classical.choice (inferInstance : Nonempty gamma)
    refine ⟨e.symm (b, c), ?_⟩
    simpa using hf (e.symm (b, c))
  apply distribution_eq_of_support_eq_of_toPMF_eq
    ((uniformDistribution alpha).map f) (uniformDistribution beta)
    ((uniformDistribution_isProbability alpha).map f)
    (uniformDistribution_isProbability beta)
  · rw [Distribution.map_support, uniformDistribution_support,
      uniformDistribution_support,
      Finset.image_univ_of_surjective hsurjective]
  · calc
      ((uniformDistribution alpha).map f).toPMF
          ((uniformDistribution_isProbability alpha).map f) =
          ((uniformDistribution alpha).toPMF
            (uniformDistribution_isProbability alpha)).map f :=
        Distribution.toPMF_map (uniformDistribution alpha)
          (uniformDistribution_isProbability alpha) f
      _ = (PMF.uniformOfFintype alpha).map f := by
        rw [uniformDistribution_toPMF]
      _ = (PMF.uniformOfFintype alpha).map
          (Prod.fst ∘ e) := by
            exact congrArg
              (fun map : alpha → beta => (PMF.uniformOfFintype alpha).map map)
              (funext fun a => by simpa [Function.comp_def] using hf a)
      _ = ((PMF.uniformOfFintype alpha).map e).map Prod.fst :=
        (PMF.map_comp e (PMF.uniformOfFintype alpha) Prod.fst).symm
      _ = (PMF.uniformOfFintype (beta × gamma)).map Prod.fst := by
        rw [PMF.uniformOfFintype_map_equiv e]
      _ = PMF.uniformOfFintype beta := by
        rw [PMF.uniformOfFintype_prod_eq_bind]
        calc
          ((PMF.uniformOfFintype beta).bind fun a =>
              (PMF.uniformOfFintype gamma).map fun b => (a, b)).map Prod.fst =
              (PMF.uniformOfFintype beta).bind (fun a =>
                ((PMF.uniformOfFintype gamma).map fun b => (a, b)).map
                  Prod.fst) :=
            PMF.map_bind (PMF.uniformOfFintype beta)
              (fun a => (PMF.uniformOfFintype gamma).map fun b => (a, b))
              Prod.fst
          _ = (PMF.uniformOfFintype beta).bind (fun a => PMF.pure a) := by
            apply congrArg (fun q : beta → PMF beta =>
              (PMF.uniformOfFintype beta).bind q)
            funext a
            calc
              ((PMF.uniformOfFintype gamma).map fun b => (a, b)).map
                  Prod.fst =
                  (PMF.uniformOfFintype gamma).map
                    (Prod.fst ∘ fun b => (a, b)) :=
                PMF.map_comp _ (PMF.uniformOfFintype gamma) Prod.fst
              _ = (PMF.uniformOfFintype gamma).map
                  (Function.const gamma a) := by rfl
              _ = PMF.pure a :=
                PMF.map_const (PMF.uniformOfFintype gamma) a
          _ = PMF.uniformOfFintype beta :=
            PMF.bind_pure (PMF.uniformOfFintype beta)
      _ = (uniformDistribution beta).toPMF
          (uniformDistribution_isProbability beta) :=
        (uniformDistribution_toPMF beta).symm

end MIPStarRE.QPBT
