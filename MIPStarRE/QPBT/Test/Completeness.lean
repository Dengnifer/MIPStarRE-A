import MIPStarRE.QPBT.Games.StrategyClasses
import MIPStarRE.QPBT.Games.TypedCondLinear
import MIPStarRE.QPBT.Test.Completeness.HonestStrategy
import MIPStarRE.QPBT.Test.LowDegreeGameTheorems
import MIPStarRE.QPBT.Test.MagicSquareTheorems
import MIPStarRE.QPBT.Test.PauliBasisTest

/-!
# Completeness of the Pauli basis test

This file presents the Pauli basis test as a symmetric game and states its
value-one SPCC completeness theorem.  The honest measurements entering that
theorem are constructed in `MIPStarRE.QPBT.Test.Completeness.HonestStrategy`.

## References

The source statement is `lem:pauli-completeness` in
`blueprint/src/chapter/ch13_qpbt_test.tex:390-395`, from
`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:1229-1421`.
-/

open scoped BigOperators

-- The Pauli question space is a nested sum of six coefficient blocks, so the
-- definitional unfoldings below exceed the default elaboration depth.
set_option maxRecDepth 8000

namespace MIPStarRE.QPBT

open MIPStarRE.LDT

noncomputable section

/-! ### Auxiliary facts about finite distributions

The lemmas of this section are formalization-only.  They record elementary
identities about finite weighted distributions which the source treats as
implicit.
-/

/-- Formalization-only auxiliary: two finite distributions coincide as soon as
their supports and their weight functions coincide. -/
private theorem distribution_ext {α : Type*} {μ ν : Distribution α}
    (hsupport : μ.support = ν.support) (hweight : μ.weight = ν.weight) : μ = ν := by
  cases μ with
  | mk s w hn ho =>
    cases ν with
    | mk s' w' hn' ho' =>
      have hs : s = s' := hsupport
      have hw : w = w' := hweight
      subst hs
      subst hw
      rfl

/-- Formalization-only auxiliary: successive push-forwards compose. -/
private theorem distribution_map_map {α β γ : Type*}
    [DecidableEq β] [DecidableEq γ]
    (μ : Distribution α) (e : α → β) (f : β → γ) :
    (μ.map e).map f = μ.map fun a => f (e a) := by
  refine distribution_ext ?_ ?_
  · change (μ.support.image e).image f = μ.support.image fun a => f (e a)
    rw [Finset.image_image]
    rfl
  · funext c
    have hmaps : ∀ a ∈ μ.support.filter fun a => f (e a) = c,
        e a ∈ (μ.support.image e).filter fun b => f b = c := by
      intro a ha
      obtain ⟨ha1, ha2⟩ := Finset.mem_filter.mp ha
      exact Finset.mem_filter.mpr ⟨Finset.mem_image_of_mem _ ha1, ha2⟩
    have hkey := Finset.sum_fiberwise_of_maps_to hmaps μ.weight
    change (∑ b ∈ (μ.support.image e).filter fun b => f b = c,
        ∑ a ∈ μ.support.filter fun a => e a = b, μ.weight a) =
      ∑ a ∈ μ.support.filter fun a => f (e a) = c, μ.weight a
    rw [← hkey]
    refine Finset.sum_congr rfl fun b hb => ?_
    obtain ⟨-, hb2⟩ := Finset.mem_filter.mp hb
    congr 1
    ext a
    simp only [Finset.mem_filter]
    constructor
    · rintro ⟨ha1, rfl⟩
      exact ⟨⟨ha1, hb2⟩, rfl⟩
    · rintro ⟨⟨ha1, -⟩, hae⟩
      exact ⟨ha1, hae⟩

/-- Formalization-only auxiliary: the push-forward of a uniform distribution
does not depend on the finiteness and decidability data used to form it. -/
private theorem map_uniformDistribution_congr {α γ : Type*}
    (i₁ i₂ : Fintype α) (j₁ j₂ : DecidableEq α) (k₁ k₂ : Nonempty α)
    (d₁ d₂ : DecidableEq γ) (e : α → γ) :
    @Distribution.map α γ d₁ (@uniformDistribution α i₁ j₁ k₁) e =
      @Distribution.map α γ d₂ (@uniformDistribution α i₂ j₂ k₂) e := by
  have hi : i₁ = i₂ := Subsingleton.elim _ _
  have hj : j₁ = j₂ := funext fun _ => funext fun _ => Subsingleton.elim _ _
  have hd : d₁ = d₂ := funext fun _ => funext fun _ => Subsingleton.elim _ _
  subst hi
  subst hj
  subst hd
  rfl

/-- Formalization-only auxiliary: a uniformly seeded typed bind does not depend
on the finiteness and decidability data used to form it. -/
private theorem bind_map_uniformDistribution_congr {α β γ : Type*}
    (i₁ i₂ : Fintype β) (j₁ j₂ : DecidableEq β) (k₁ k₂ : Nonempty β)
    (d₁ d₂ : DecidableEq γ) (μ : Distribution α) (g : α → β → γ) :
    @Distribution.bind α γ d₁ μ
        (fun a => @Distribution.map β γ d₁ (@uniformDistribution β i₁ j₁ k₁) (g a)) =
      @Distribution.bind α γ d₂ μ
        (fun a => @Distribution.map β γ d₂ (@uniformDistribution β i₂ j₂ k₂) (g a)) := by
  have hi : i₁ = i₂ := Subsingleton.elim _ _
  have hj : j₁ = j₂ := funext fun _ => funext fun _ => Subsingleton.elim _ _
  have hd : d₁ = d₂ := funext fun _ => funext fun _ => Subsingleton.elim _ _
  subst hi
  subst hj
  subst hd
  rfl

/-- Formalization-only auxiliary: every point of a finite type carries the same
uniform weight. -/
private theorem uniform_weight_apply (α : Type*)
    [Fintype α] [DecidableEq α] [Nonempty α] (a : α) :
    (uniformDistribution α).weight a = 1 / (Fintype.card α : Error) := by
  simp [uniformDistribution]

/-- Formalization-only auxiliary: a push-forward of a uniform distribution
weights a value by the size of its fibre. -/
private theorem uniform_map_weight {α γ : Type*}
    [Fintype α] [DecidableEq α] [Nonempty α] [DecidableEq γ]
    (e : α → γ) (c : γ) :
    ((uniformDistribution α).map e).weight c =
      (((Finset.univ : Finset α).filter fun x => e x = c).card : Error) *
        (1 / (Fintype.card α : Error)) := by
  change (∑ x ∈ (Finset.univ : Finset α).filter (fun x => e x = c),
      (uniformDistribution α).weight x) = _
  rw [Finset.sum_congr rfl fun x _ => uniform_weight_apply α x,
    Finset.sum_const, nsmul_eq_mul]

/-- Formalization-only auxiliary: binding a uniform distribution on a finite
edge set to uniformly seeded push-forwards is the push-forward of the uniform
distribution on the product of an indexing type for that edge set with the
seed space. -/
private theorem bind_uniformOnFinset_map {α β γ σ : Type*}
    [Fintype σ] [DecidableEq σ] [Nonempty σ]
    [Fintype β] [DecidableEq β] [Nonempty β] [DecidableEq γ]
    (s : Finset α) (f : σ → α) (hinj : Function.Injective f)
    (hmem : ∀ a, a ∈ s ↔ ∃ x : σ, f x = a) (g : α → β → γ) :
    Distribution.bind (Distribution.uniformOnFinset s)
        (fun a => (uniformDistribution β).map (g a)) =
      (uniformDistribution (σ × β)).map fun q => g (f q.1) q.2 := by
  classical
  have himage : (Finset.univ : Finset σ).image f = s := by
    ext a
    simp [hmem a]
  have hcard : s.card = Fintype.card σ := by
    rw [← himage, Finset.card_image_of_injective _ hinj, Finset.card_univ]
  have hsum : ∀ h : α → Error, ∑ a ∈ s, h a = ∑ x : σ, h (f x) := by
    intro h
    rw [← himage, Finset.sum_image fun x _ y _ hxy => hinj hxy]
  refine distribution_ext ?_ ?_
  · change s.biUnion (fun a => (Finset.univ : Finset β).image (g a)) =
      (Finset.univ : Finset (σ × β)).image fun q => g (f q.1) q.2
    ext c
    simp only [Finset.mem_biUnion, Finset.mem_image, Finset.mem_univ, true_and,
      Prod.exists]
    constructor
    · rintro ⟨a, ha, b, rfl⟩
      obtain ⟨xx, rfl⟩ := (hmem a).mp ha
      exact ⟨xx, b, rfl⟩
    · rintro ⟨xx, b, rfl⟩
      exact ⟨f xx, (hmem _).mpr ⟨xx, rfl⟩, b, rfl⟩
  · funext c
    have key : ∀ a ∈ s, (Distribution.uniformOnFinset s).weight a *
        ((uniformDistribution β).map (g a)).weight c =
        (((Finset.univ : Finset β).filter fun b => g a b = c).card : Error) *
          (1 / ((Fintype.card σ : Error) * (Fintype.card β : Error))) := by
      intro a ha
      rw [Distribution.uniformOnFinset_weight, if_pos ha, uniform_map_weight, hcard]
      ring
    have hcount :
        ((Finset.univ : Finset (σ × β)).filter fun q => g (f q.1) q.2 = c).card =
          ∑ x : σ, ((Finset.univ : Finset β).filter fun b => g (f x) b = c).card := by
      simp only [Finset.card_filter]
      rw [Fintype.sum_prod_type]
    change (∑ a ∈ s, (Distribution.uniformOnFinset s).weight a *
        ((uniformDistribution β).map (g a)).weight c) =
      ∑ q ∈ (Finset.univ : Finset (σ × β)).filter fun q => g (f q.1) q.2 = c,
        (uniformDistribution (σ × β)).weight q
    rw [Finset.sum_congr rfl key,
      hsum fun a => (((Finset.univ : Finset β).filter fun b => g a b = c).card : Error) *
        (1 / ((Fintype.card σ : Error) * (Fintype.card β : Error))),
      ← Finset.sum_mul,
      Finset.sum_congr rfl fun q _ => uniform_weight_apply (σ × β) q,
      Finset.sum_const, nsmul_eq_mul, hcount, Fintype.card_prod]
    push_cast
    ring

/-! ### The Pauli question sampler as a typed conditionally linear distribution -/

/-- The Pauli question sampler equals the typed conditionally linear distribution
on the Pauli type graph from `def:typed-cl-distributions`; blueprint
`ch12_qpbt_games.tex:624-629`,
paper `references/qpbt-paper/07_types.tex:84-94`. -/
theorem pauliQuestionDistribution_eq_typedCL (P : AdmissibleParams) :
    pauliQuestionDistribution P =
      typedCLDistribution pauliEdges (by
        refine ⟨Sym2.mk (.point .X) (.point .X), ?_⟩
        simp [pauliEdges]) (pauliCL P) (pauliCL P) := by
  classical
  letI : Nonempty PauliEdge := pauliEdge_nonempty
  have hmem : ∀ ab : PauliType × PauliType,
      ab ∈ (Finset.univ : Finset (PauliType × PauliType)).filter
          (fun ab => Sym2.mk ab.1 ab.2 ∈ pauliEdges) ↔
        ∃ e : PauliEdge, e.val = ab := by
    intro ab
    constructor
    · intro h
      exact ⟨⟨ab, (Finset.mem_filter.mp h).2⟩, rfl⟩
    · rintro ⟨e, rfl⟩
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, e.2⟩
  have hmine : Distribution.bind
      (Distribution.uniformOnFinset ((Finset.univ : Finset (PauliType × PauliType)).filter
        (fun ab => Sym2.mk ab.1 ab.2 ∈ pauliEdges)))
      (fun uv => (uniformDistribution (PauliSpace P)).map fun z =>
        ((uv.1, pauliCL P uv.1 z), (uv.2, pauliCL P uv.2 z))) =
      pauliQuestionDistribution P := by
    rw [bind_uniformOnFinset_map _ (Subtype.val : PauliEdge → PauliType × PauliType)
      Subtype.val_injective hmem
      (fun uv z => ((uv.1, pauliCL P uv.1 z), (uv.2, pauliCL P uv.2 z)))]
    unfold pauliQuestionDistribution
    exact map_uniformDistribution_congr _ _ _ _ _ _ _ _ _
  rw [← hmine]
  simp only [typedCLDistribution, graphDistribution, clDistribution,
    distribution_map_map]
  exact bind_map_uniformDistribution_congr _ _ _ _ _ _ _ _ _ _

/-! ### Symmetry of the Pauli basis test -/

/-- Formalization-only auxiliary: reversing an ordered edge of the Pauli type
graph again yields an ordered edge. -/
private def pauliEdgeSwap (e : PauliEdge) : PauliEdge :=
  ⟨(e.val.2, e.val.1), by
    have he := e.2
    rwa [Sym2.eq_swap] at he⟩

/-- Formalization-only auxiliary: reversal of ordered edges is an involutive
equivalence of the Pauli edge type. -/
private def pauliEdgeSwapEquiv : PauliEdge ≃ PauliEdge where
  toFun := pauliEdgeSwap
  invFun := pauliEdgeSwap
  left_inv := fun _ => rfl
  right_inv := fun _ => rfl

/-- Symmetry of the Pauli question distribution in the symmetric game appearing
in `lem:pauli-completeness`. -/
theorem pauliQuestionDistribution_symm (P : AdmissibleParams)
    (x y : PauliQuestion P) :
    (pauliQuestionDistribution P).weight (x, y) =
      (pauliQuestionDistribution P).weight (y, x) := by
  classical
  letI : Nonempty PauliEdge := pauliEdge_nonempty
  have hcard : ∀ c : PauliQuestion P × PauliQuestion P,
      ((Finset.univ : Finset (PauliEdge × PauliSpace P)).filter fun q =>
          ((q.1.val.1, pauliCL P q.1.val.1 q.2),
            (q.1.val.2, pauliCL P q.1.val.2 q.2)) = c).card =
        ((Finset.univ : Finset (PauliEdge × PauliSpace P)).filter fun q =>
          ((q.1.val.1, pauliCL P q.1.val.1 q.2),
            (q.1.val.2, pauliCL P q.1.val.2 q.2)) = c.swap).card := by
    intro c
    refine Finset.card_equiv
      (Equiv.prodCongr pauliEdgeSwapEquiv (Equiv.refl (PauliSpace P))) ?_
    intro q
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · intro hq
      change Prod.swap (((q.1.val.1, pauliCL P q.1.val.1 q.2),
        (q.1.val.2, pauliCL P q.1.val.2 q.2))) = c.swap
      rw [hq]
    · intro hq
      have hq' : Prod.swap (((q.1.val.1, pauliCL P q.1.val.1 q.2),
        (q.1.val.2, pauliCL P q.1.val.2 q.2))) = c.swap := hq
      simpa using congrArg Prod.swap hq'
  change ((uniformDistribution (PauliEdge × PauliSpace P)).map
      (fun q => ((q.1.val.1, pauliCL P q.1.val.1 q.2),
        (q.1.val.2, pauliCL P q.1.val.2 q.2)))).weight (x, y) =
    ((uniformDistribution (PauliEdge × PauliSpace P)).map
      (fun q => ((q.1.val.1, pauliCL P q.1.val.1 q.2),
        (q.1.val.2, pauliCL P q.1.val.2 q.2)))).weight (y, x)
  rw [uniform_map_weight, uniform_map_weight, hcard (x, y), Prod.swap_prod_mk]

/-- Symmetry of the Pauli decision predicate in the symmetric game appearing in
`lem:pauli-completeness`. -/
theorem pauliWinPredicate_symm (P : AdmissibleParams)
    (x y : PauliQuestion P) (a b : PauliAnswer P) :
    pauliWinPredicate P x y a b = pauliWinPredicate P y x b a := by
  obtain ⟨tA, xA⟩ := x
  obtain ⟨tB, xB⟩ := y
  by_cases hT : tA = tB
  · subst hT
    simp only [pauliWinPredicate]
    rw [Bool.and_comm (validPauliAnswer tA b) (validPauliAnswer tA a)]
    by_cases hab : a = b
    · simp [hab]
    · simp [hab, Ne.symm hab]
  · cases hvA : validPauliAnswer tA a
    · simp [pauliWinPredicate, hvA]
    · cases hvB : validPauliAnswer tB b
      · simp [pauliWinPredicate, hvB]
      · simp only [pauliWinPredicate, hvA, hvB, Bool.and_self,
          if_neg hT, if_neg (Ne.symm hT)]
        rcases tA with (_|_)|(_|_)|(_|_)|(_|_)|(_|_)|_|(iA|jA) <;>
          rcases a with uA|fA|gA|bitsA|bitA|trA|hhA <;>
          (try exact Bool.noConfusion hvA) <;>
          rcases tB with (_|_)|(_|_)|(_|_)|(_|_)|(_|_)|_|(iB|jB) <;>
          rcases b with uB|fB|gB|bitsB|bitB|trB|hhB <;>
          (try exact Bool.noConfusion hvB) <;>
          rfl

/-- The symmetric presentation of the Pauli basis test. The field and basis
are those fixed by `P.model`; no additional model is quantified. -/
noncomputable def pauliBasisTestSymm (P : AdmissibleParams) : SymmetricGame where
  Question := PauliQuestion P
  Answer := PauliAnswer P
  μ := pauliQuestionDistribution P
  μ_prob := (pauliBasisTest P).μ_prob
  μ_symm := pauliQuestionDistribution_symm P
  decide := pauliWinPredicate P
  decide_symm := pauliWinPredicate_symm P

/-- The symmetric presentation has the Pauli basis test as its
underlying game. -/
theorem pauliBasisTestSymm_toGame (P : AdmissibleParams) :
    (pauliBasisTestSymm P).toGame = pauliBasisTest P := by
  rfl

/-- `lem:pauli-completeness`: every admissible Pauli basis test has a
value-one SPCC strategy. Blueprint `ch13_qpbt_test.tex:390-395`, paper
`08_classical_and_quantum_low_degree_tests.tex:1229-1421`. -/
theorem exists_spcc_value_one (P : AdmissibleParams) :
    ∃ S : SymmetricStrategy (pauliBasisTestSymm P),
      S.IsSPCC ∧ S.toStrategy.value = 1 := by
  sorry

end

end MIPStarRE.QPBT
