import MIPStarRE.QPBT.Games.CondLinear

/-!
# Reindexing of conditionally linear functions

A conditionally linear function of one register space transports along an
injective map of index types.  The transported function restricts a coefficient
vector to the registers named by that map, applies the original function, and
extends the result by zero outside the image; it is conditionally linear at the
same level on the full register.  In the one-level case the predicate holds of
every linear map of the ambient coefficient space, which is the converse
direction of the remark following `def:cl-func`.

## References

The source definition is `def:cl-func` in
`blueprint/src/chapter/ch12_qpbt_games.tex`, with paper origin
`references/qpbt-paper/05_conditionally_linear_functions.tex:35-57`.
-/

namespace MIPStarRE.QPBT

/-- A linear map of the ambient coefficient space is conditionally linear with a
single level on the full register.  This is the one-level case of `def:cl-func`,
blueprint `blueprint/src/chapter/ch12_qpbt_games.tex`, paper origin
`references/qpbt-paper/05_conditionally_linear_functions.tex:35-57`. -/
theorem isCondLinearOn_one_of_linear {K ι : Type*} [Field K]
    [Fintype ι] [DecidableEq ι] (L : (ι → K) →ₗ[K] (ι → K)) :
    IsCondLinearOn K Finset.univ 1 (fun x => L x) := by
  refine ⟨.succ Finset.univ L (fun _ i hi => absurd (Finset.mem_univ i) hi)
      (fun _ => .zero), ⟨Finset.subset_univ _, fun _ => trivial⟩, ?_⟩
  funext x
  have hx : coordinateRestriction (Finset.univ : Finset ι) x = x := by
    funext i
    simp [coordinateRestriction]
  change L (coordinateRestriction Finset.univ x) + 0 = L x
  rw [hx, add_zero]

/-- Transport a linear map of coefficient vectors along a reindexing `f` of
registers: restrict a vector to the registers named by `f`, apply the map, and
extend the result by zero outside the image of `f`.  This is the composition of
restriction along `f` with `Function.ExtendByZero.linearMap`, named here for the
reindexing of `def:cl-func`. -/
noncomputable def reindexLinearMap {K κ ι : Type*} [Field K] (f : κ → ι)
    (L : (κ → K) →ₗ[K] (κ → K)) : (ι → K) →ₗ[K] (ι → K) :=
  (Function.ExtendByZero.linearMap K f).comp (L.comp (LinearMap.funLeft K K f))

@[simp]
theorem reindexLinearMap_apply {K κ ι : Type*} [Field K] (f : κ → ι)
    (L : (κ → K) →ₗ[K] (κ → K)) (x : ι → K) :
    reindexLinearMap f L x = Function.extend f (L fun k => x (f k)) 0 :=
  rfl

/-- The reindexing of a linear map supported on a register vanishes off the
image of that register, so it satisfies the support condition of the successor
constructor of a representation of a conditionally linear function. -/
theorem reindexLinearMap_apply_eq_zero {K κ ι : Type*} [Field K] [DecidableEq ι]
    {f : κ → ι} (hf : Function.Injective f) {S₁ : Finset κ}
    {L₁ : (κ → K) →ₗ[K] (κ → K)} (hL : ∀ x i, i ∉ S₁ → L₁ x i = 0)
    (x : ι → K) (i : ι) (hi : i ∉ S₁.image f) :
    reindexLinearMap f L₁ x i = 0 := by
  rw [reindexLinearMap_apply]
  by_cases hex : ∃ k, f k = i
  · obtain ⟨k, rfl⟩ := hex
    have hk : k ∉ S₁ := fun hk => hi (Finset.mem_image_of_mem f hk)
    rw [hf.extend_apply]
    exact hL _ k hk
  · rw [Function.extend_apply' _ _ _ hex]
    rfl

/-- Transport a representation of a conditionally linear function along an
injective reindexing of registers; the linear contribution of each level is
reindexed by `reindexLinearMap` and its register is carried along by the image
under `f`. -/
noncomputable def CondLinearTerm.reindex {K κ ι : Type*} [Field K]
    [Fintype κ] [DecidableEq κ]
    [Fintype ι] [DecidableEq ι] {f : κ → ι} (hf : Function.Injective f) :
    {ell : ℕ} → CondLinearTerm K (ι := κ) ell → CondLinearTerm K (ι := ι) ell
  | _, .zero => .zero
  | _, .succ S₁ L₁ hL rest =>
      .succ (S₁.image f) (reindexLinearMap f L₁)
        (fun x i hi => reindexLinearMap_apply_eq_zero hf hL x i hi)
        (fun y => CondLinearTerm.reindex hf (rest fun k => y (f k)))

/-- The reindexed representation is supported on any register containing the
image of the register supporting the original one. -/
theorem CondLinearTerm.reindex_supportedOn {K κ ι : Type*} [Field K]
    [Fintype κ] [DecidableEq κ] [Fintype ι] [DecidableEq ι] {f : κ → ι}
    (hf : Function.Injective f) :
    ∀ {ell : ℕ} (t : CondLinearTerm K (ι := κ) ell) (S : Finset κ)
      (T : Finset ι), t.supportedOn S → S.image f ⊆ T →
      (CondLinearTerm.reindex hf t).supportedOn T := by
  intro ell t
  induction t with
  | zero => intro S T _ _; trivial
  | succ S₁ L₁ hL rest ih =>
      intro S T hsupp hST
      obtain ⟨h1, h2⟩ := hsupp
      refine ⟨fun i hi => hST (Finset.image_subset_image h1 hi), fun y => ?_⟩
      refine ih (fun k => y (f k)) (S \ S₁) (T \ S₁.image f) (h2 _) ?_
      intro i hi
      obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hi
      obtain ⟨hkS, hkS₁⟩ := Finset.mem_sdiff.mp hk
      refine Finset.mem_sdiff.mpr ⟨hST (Finset.mem_image_of_mem f hkS), ?_⟩
      intro hmem
      obtain ⟨k', hk', hk'eq⟩ := Finset.mem_image.mp hmem
      exact hkS₁ (hf hk'eq ▸ hk')

/-- Evaluation commutes with the reindexing of a representation of a
conditionally linear function: evaluating the reindexed representation at a
vector is the extension by zero of the evaluation of the original one at the
restricted vector. -/
theorem CondLinearTerm.eval_reindex {K κ ι : Type*} [Field K]
    [Fintype κ] [DecidableEq κ] [Fintype ι] [DecidableEq ι] {f : κ → ι}
    (hf : Function.Injective f) :
    ∀ {ell : ℕ} (t : CondLinearTerm K (ι := κ) ell) (x : ι → K),
      CondLinearTerm.eval (CondLinearTerm.reindex hf t) x =
        Function.extend f (CondLinearTerm.eval t fun k => x (f k)) 0 := by
  have hadd : ∀ u v : κ → K, Function.extend f (u + v) (0 : ι → K) =
      Function.extend f u 0 + Function.extend f v 0 := by
    intro u v
    simpa using Function.extend_add f u v (0 : ι → K) 0
  intro ell t
  induction t with
  | zero => intro x; exact (Function.extend_zero f).symm
  | succ S₁ L₁ hL rest ih =>
      intro x
      have hres : (fun k => coordinateRestriction (S₁.image f) x (f k)) =
          coordinateRestriction S₁ (fun k => x (f k)) := by
        funext k
        by_cases hk : k ∈ S₁
        · have hmem : f k ∈ S₁.image f := Finset.mem_image_of_mem f hk
          simp [coordinateRestriction, hk, hmem]
        · have hni : f k ∉ S₁.image f := by
            intro hmem
            obtain ⟨k', hk', hk'eq⟩ := Finset.mem_image.mp hmem
            exact hk (hf hk'eq ▸ hk')
          simp [coordinateRestriction, hk, hni]
      have hhead : reindexLinearMap f L₁ (coordinateRestriction (S₁.image f) x) =
          Function.extend f (L₁ (coordinateRestriction S₁ fun k => x (f k))) 0 := by
        rw [reindexLinearMap_apply, hres]
      have hcomp : (fun k => reindexLinearMap f L₁
            (coordinateRestriction (S₁.image f) x) (f k)) =
          L₁ (coordinateRestriction S₁ fun k => x (f k)) := by
        funext k
        rw [hhead]
        exact hf.extend_apply _ _ k
      change reindexLinearMap f L₁ (coordinateRestriction (S₁.image f) x) +
          CondLinearTerm.eval (CondLinearTerm.reindex hf (rest
            (fun k => reindexLinearMap f L₁
              (coordinateRestriction (S₁.image f) x) (f k)))) x =
        Function.extend f (L₁ (coordinateRestriction S₁ fun k => x (f k)) +
          CondLinearTerm.eval
            (rest (L₁ (coordinateRestriction S₁ fun k => x (f k))))
            (fun k => x (f k))) 0
      rw [hcomp, ih _ x, hhead, ← hadd]

/-- Conditional linearity at a level is preserved by an injective reindexing of
registers, the coordinates outside the image of the reindexing being set to
zero.  This transports `def:cl-func` between register spaces. -/
theorem isCondLinearOn_reindex {K κ ι : Type*} [Field K]
    [Fintype κ] [DecidableEq κ] [Fintype ι] [DecidableEq ι] {f : κ → ι}
    (hf : Function.Injective f) {ell : ℕ} {L : (κ → K) → (κ → K)}
    (h : IsCondLinearOn K Finset.univ ell L) :
    IsCondLinearOn K Finset.univ ell
      (fun x => Function.extend f (L fun k => x (f k)) 0) := by
  obtain ⟨t, hsupp, hval⟩ := h
  refine ⟨CondLinearTerm.reindex hf t,
    CondLinearTerm.reindex_supportedOn hf t Finset.univ Finset.univ hsupp
      (Finset.subset_univ _), ?_⟩
  funext x
  rw [CondLinearTerm.eval_reindex hf t x, hval]

end MIPStarRE.QPBT
