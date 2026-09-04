import MIPStarRE.QPBT.Games.CondLinear

/-! # Structure and direct sums of conditionally linear functions

This module records the prefix decomposition of a conditionally linear map and
the behavior of such maps and their shared-seed distributions under finite
coordinate direct sums.

## References

The source results are `lem:cl-kth`, `lem:cl-func-prod`, and
`lem:cl-dist-prod` in `blueprint/src/chapter/ch12_qpbt_games.tex:520-587`, with
paper origin
`references/qpbt-paper/05_conditionally_linear_functions.tex:150-379`.
-/

open scoped BigOperators

namespace MIPStarRE.QPBT

open MIPStarRE.LDT

/-- Add one empty first stage to a representation of a conditionally linear
function. -/
private def CondLinearTerm.raiseLevel {K ι : Type*} [Field K]
    [Fintype ι] [DecidableEq ι] {ell : ℕ}
    (t : CondLinearTerm K (ι := ι) ell) : CondLinearTerm K (ι := ι) (ell + 1) :=
  .succ ∅ 0 (by simp) (fun _ => t)

@[simp]
private theorem CondLinearTerm.eval_raiseLevel {K ι : Type*} [Field K]
    [Fintype ι] [DecidableEq ι] {ell : ℕ}
    (t : CondLinearTerm K (ι := ι) ell) (x : ι → K) :
    CondLinearTerm.eval t.raiseLevel x = CondLinearTerm.eval t x := by
  simp [CondLinearTerm.raiseLevel, CondLinearTerm.eval]

private theorem CondLinearTerm.raiseLevel_supportedOn {K ι : Type*} [Field K]
    [Fintype ι] [DecidableEq ι] {ell : ℕ}
    {t : CondLinearTerm K (ι := ι) ell} {S : Finset ι}
    (ht : CondLinearTerm.supportedOn t S) :
    CondLinearTerm.supportedOn t.raiseLevel S := by
  exact ⟨Finset.empty_subset S, fun _ => by simpa using ht⟩

/-- Raise a representation of a conditionally linear function by a specified
number of empty stages. -/
private def CondLinearTerm.raiseBy {K ι : Type*} [Field K]
    [Fintype ι] [DecidableEq ι] :
    (d : ℕ) → {ell : ℕ} → CondLinearTerm K (ι := ι) ell →
      CondLinearTerm K (ι := ι) (ell + d)
  | 0, _, t => t
  | d + 1, _, t => (raiseBy d t).raiseLevel

@[simp]
private theorem CondLinearTerm.eval_raiseBy {K ι : Type*} [Field K]
    [Fintype ι] [DecidableEq ι] (d : ℕ) {ell : ℕ}
    (t : CondLinearTerm K (ι := ι) ell) (x : ι → K) :
    CondLinearTerm.eval (CondLinearTerm.raiseBy d t) x = CondLinearTerm.eval t x := by
  induction d with
  | zero => rfl
  | succ d ih => simp [CondLinearTerm.raiseBy, ih]

private theorem CondLinearTerm.raiseBy_supportedOn {K ι : Type*} [Field K]
    [Fintype ι] [DecidableEq ι] (d : ℕ) {ell : ℕ}
    {t : CondLinearTerm K (ι := ι) ell} {S : Finset ι}
    (ht : CondLinearTerm.supportedOn t S) :
    CondLinearTerm.supportedOn (CondLinearTerm.raiseBy d t) S := by
  induction d with
  | zero => exact ht
  | succ d ih => exact CondLinearTerm.raiseLevel_supportedOn ih

/-- Conditional linearity is monotone in the number of levels. -/
private theorem IsCondLinearOn.mono_level {K ι : Type*} [Field K]
    [Fintype ι] [DecidableEq ι] {S : Finset ι} {ell k : ℕ}
    {L : (ι → K) → (ι → K)} (hL : IsCondLinearOn K S ell L)
    (h : ell ≤ k) : IsCondLinearOn K S k L := by
  rcases hL with ⟨t, ht, ht_eval⟩
  have hk : ell + (k - ell) = k := Nat.add_sub_of_le h
  rw [← hk]
  exact ⟨CondLinearTerm.raiseBy (k - ell) t,
    CondLinearTerm.raiseBy_supportedOn _ ht,
    funext fun x => by rw [CondLinearTerm.eval_raiseBy, congrFun ht_eval x]⟩

/-- A conditionally-linear map supported on `S` has values supported on `S`. -/
private theorem IsCondLinearOn.apply_eq_zero_of_not_mem {K ι : Type*} [Field K]
    [Fintype ι] [DecidableEq ι] {S : Finset ι} {ell : ℕ}
    {L : (ι → K) → (ι → K)} (hL : IsCondLinearOn K S ell L)
    (x : ι → K) {a : ι} (ha : a ∉ S) : L x a = 0 := by
  rcases hL with ⟨t, ht, ht_eval⟩
  rw [← congrFun (congrFun ht_eval x) a]
  exact CondLinearTerm.eval_eq_zero_of_not_mem ht x ha

/-- A conditionally-linear map supported on `S` depends only on the input in
`S`. -/
private theorem IsCondLinearOn.apply_coordinateRestriction {K ι : Type*} [Field K]
    [Fintype ι] [DecidableEq ι] {S : Finset ι} {ell : ℕ}
    {L : (ι → K) → (ι → K)} (hL : IsCondLinearOn K S ell L)
    (x : ι → K) : L (coordinateRestriction S x) = L x := by
  rcases hL with ⟨t, ht, ht_eval⟩
  rw [← congrFun ht_eval, CondLinearTerm.eval_coordinateRestriction ht,
    congrFun ht_eval]

/-- Prepend one supported linear stage to a family of residual
conditionally-linear maps. -/
private theorem IsCondLinearOn.cons {K ι : Type*} [Field K]
    [Fintype ι] [DecidableEq ι] {S S₁ : Finset ι} {ell : ℕ}
    (L₁ : (ι → K) →ₗ[K] (ι → K))
    (hS₁ : S₁ ⊆ S) (hSupport : ∀ x a, a ∉ S₁ → L₁ x a = 0)
    (R : (ι → K) → (ι → K) → (ι → K))
    (hR : ∀ y, IsCondLinearOn K (S \ S₁) ell (R y)) :
    IsCondLinearOn K S (ell + 1) (fun x =>
      L₁ (coordinateRestriction S₁ x) +
        R (L₁ (coordinateRestriction S₁ x)) x) := by
  classical
  choose t ht ht_eval using hR
  refine ⟨.succ S₁ L₁ hSupport t, ⟨hS₁, ht⟩, ?_⟩
  funext x
  change L₁ (coordinateRestriction S₁ x) +
      CondLinearTerm.eval (t (L₁ (coordinateRestriction S₁ x))) x = _
  rw [congrFun (ht_eval _) x]

private theorem coordinateRestriction_eq_self {K ι : Type*} [Field K]
    [DecidableEq ι] {S : Finset ι} {x : ι → K}
    (hx : ∀ a, a ∉ S → x a = 0) : coordinateRestriction S x = x := by
  ext a
  by_cases ha : a ∈ S
  · simp [coordinateRestriction, ha]
  · simp [coordinateRestriction, ha, hx a ha]

private theorem coordinateRestriction_add {K ι : Type*} [Field K]
    [DecidableEq ι] (S : Finset ι) (x y : ι → K) :
    coordinateRestriction S (x + y) =
      coordinateRestriction S x + coordinateRestriction S y := by
  ext a
  by_cases ha : a ∈ S <;> simp [coordinateRestriction, ha]

private theorem coordinateRestriction_eq_zero_of_disjoint {K ι : Type*} [Field K]
    [DecidableEq ι] {S T : Finset ι} (hST : Disjoint S T)
    {x : ι → K} (hx : ∀ a, a ∉ T → x a = 0) :
    coordinateRestriction S x = 0 := by
  ext a
  by_cases ha : a ∈ S
  · have haT : a ∉ T := fun h => Finset.disjoint_left.mp hST ha h
    simp [coordinateRestriction, ha, hx a haT]
  · simp [coordinateRestriction, ha]

/-- Coordinate restriction as a linear endomorphism. -/
private def coordinateRestrictionLinear {K ι : Type*} [Field K]
    [Fintype ι] [DecidableEq ι] (S : Finset ι) :
    (ι → K) →ₗ[K] (ι → K) where
  toFun := coordinateRestriction S
  map_add' := coordinateRestriction_add S
  map_smul' c x := by
    ext a
    by_cases ha : a ∈ S <;> simp [coordinateRestriction, ha]

private theorem sum_coordinateRestriction_eq {K ι J : Type*} [Field K]
    [DecidableEq ι] [Fintype J]
    (V : J → Finset ι) (hDisjoint : ∀ i j, i ≠ j → Disjoint (V i) (V j))
    (hCover : ∀ a, ∃ j, a ∈ V j) (x : ι → K) :
    ∑ j, coordinateRestriction (V j) x = x := by
  classical
  ext a
  obtain ⟨j, haj⟩ := hCover a
  rw [Finset.sum_apply, Finset.sum_eq_single j]
  · simp [coordinateRestriction, haj]
  · intro i _ hij
    have hai : a ∉ V i := fun hai =>
      Finset.disjoint_left.mp (hDisjoint i j hij) hai haj
    simp [coordinateRestriction, hai]
  · exact fun hj => (hj (Finset.mem_univ j)).elim

private theorem sum_eq_iff_coordinateRestriction_eq {K ι J : Type*} [Field K]
    [DecidableEq ι] [Fintype J]
    (V : J → Finset ι) (hDisjoint : ∀ i j, i ≠ j → Disjoint (V i) (V j))
    (hCover : ∀ a, ∃ j, a ∈ V j) (f : J → ι → K)
    (hf : ∀ j a, a ∉ V j → f j a = 0) (x : ι → K) :
    (∑ j, f j) = x ↔ ∀ j, f j = coordinateRestriction (V j) x := by
  classical
  constructor
  · intro h j
    rw [← h]
    exact (coordinateRestriction_sum_eq V hDisjoint f hf j).symm
  · intro h
    calc
      (∑ j, f j) = ∑ j, coordinateRestriction (V j) x := by
        exact Finset.sum_congr rfl fun j _ => h j
      _ = x := sum_coordinateRestriction_eq V hDisjoint hCover x

/-- The value of the strict-prefix marginal preceding `k`. This is a
formalization-only auxiliary for `lem:cl-kth`, blueprint
`ch12_qpbt_games.tex:520-540`, paper
`references/qpbt-paper/05_conditionally_linear_functions.tex:150-178`. -/
def clPrefix {K ι : Type*} [Zero K] {ell : ℕ}
    (marginal : Fin ell → (ι → K) → (ι → K)) (k : Fin ell)
    (x : ι → K) : ι → K :=
  if _hk : k.val = 0 then 0
  else marginal ⟨k.val - 1, lt_of_le_of_lt (Nat.sub_le _ _) k.isLt⟩ x

/-- Prefix-indexed decomposition data from `lem:cl-kth`. Factor spaces are
represented by their coordinate sets, matching the register-subspace encoding
used by `IsCondLinearOn`. Blueprint `ch12_qpbt_games.tex:520-540`, paper
`references/qpbt-paper/05_conditionally_linear_functions.tex:150-178`. -/
structure CLData (K ι : Type*) [Field K] [Fintype ι] [DecidableEq ι]
    (ell : ℕ) (L : (ι → K) → (ι → K)) where
  /-- The marginal `L_{≤k}`. -/
  marginal : Fin ell → (ι → K) → (ι → K)
  /-- The factor register selected by a prefix value. -/
  factor : Fin ell → (ι → K) → Finset ι
  /-- The linear map selected by a prefix value. -/
  linear : Fin ell → (ι → K) → ((ι → K) →ₗ[K] (ι → K))
  /-- Each marginal has the corresponding conditionally linear level. -/
  marginal_cl : ∀ k, IsCondLinearOn K Finset.univ (k.val + 1) (marginal k)
  /-- The selected factor registers are pairwise disjoint. -/
  factor_disjoint : ∀ x i j, i ≠ j →
    Disjoint (factor i (clPrefix marginal i x)) (factor j (clPrefix marginal j x))
  /-- The selected factor registers cover all coordinates. -/
  factor_cover : ∀ x a, ∃ i, a ∈ factor i (clPrefix marginal i x)
  /-- Each selected linear map is supported on its factor register. -/
  linear_supported : ∀ k u x a, a ∉ factor k u → linear k u x a = 0
  /-- Each marginal is the sum of the preceding selected linear pieces. -/
  sum_formula : ∀ k x, marginal k x =
    ∑ i : Fin ell, if i.val ≤ k.val then
      linear i (clPrefix marginal i x)
        (coordinateRestriction (factor i (clPrefix marginal i x)) x) else 0
  /-- The final marginal is the original function. -/
  top : ∀ h : 0 < ell,
    marginal ⟨ell - 1, Nat.sub_lt h (by decide)⟩ = L

/-- Prefix decomposition data on a register `S`, refining the decomposition
in `lem:cl-kth`. -/
private structure CLDataOn (K ι : Type*) [Field K] [Fintype ι]
    [DecidableEq ι] (S : Finset ι) (ell : ℕ)
    (L : (ι → K) → (ι → K)) where
  marginal : Fin ell → (ι → K) → (ι → K)
  factor : Fin ell → (ι → K) → Finset ι
  linear : Fin ell → (ι → K) → ((ι → K) →ₗ[K] (ι → K))
  marginal_cl : ∀ k, IsCondLinearOn K S (k.val + 1) (marginal k)
  factor_subset : ∀ k u, factor k u ⊆ S
  factor_disjoint : ∀ x i j, i ≠ j →
    Disjoint (factor i (clPrefix marginal i x))
      (factor j (clPrefix marginal j x))
  factor_cover : ∀ x a, a ∈ S → ∃ i, a ∈ factor i (clPrefix marginal i x)
  linear_supported : ∀ k u x a, a ∉ factor k u → linear k u x a = 0
  sum_formula : ∀ k x, marginal k x =
    ∑ i : Fin ell, if i.val ≤ k.val then
      linear i (clPrefix marginal i x)
        (coordinateRestriction (factor i (clPrefix marginal i x)) x) else 0
  top : ∀ h : 0 < ell,
    marginal ⟨ell - 1, Nat.sub_lt h (by decide)⟩ = L

/-- Every marginal in support-relative decomposition data is supported on the
active register. -/
private theorem CLDataOn.marginal_eq_zero_of_not_mem {K ι : Type*} [Field K]
    [Fintype ι] [DecidableEq ι] {S : Finset ι} {ell : ℕ}
    {L : (ι → K) → (ι → K)} (d : CLDataOn K ι S ell L)
    (k : Fin ell) (x : ι → K) {a : ι} (ha : a ∉ S) :
    d.marginal k x a = 0 := by
  rw [d.sum_formula, Finset.sum_apply]
  apply Finset.sum_eq_zero
  intro i _
  split_ifs
  · exact d.linear_supported i _ _ a (fun hai => ha (d.factor_subset i _ hai))
  · rfl

/-- Every strict-prefix marginal in support-relative decomposition data is
supported on the active register. -/
private theorem CLDataOn.prefix_eq_zero_of_not_mem {K ι : Type*} [Field K]
    [Fintype ι] [DecidableEq ι] {S : Finset ι} {ell : ℕ}
    {L : (ι → K) → (ι → K)} (d : CLDataOn K ι S ell L)
    (k : Fin ell) (x : ι → K) {a : ι} (ha : a ∉ S) :
    clPrefix d.marginal k x a = 0 := by
  unfold clPrefix
  split_ifs
  · rfl
  · exact d.marginal_eq_zero_of_not_mem _ x ha

private theorem CondLinearTerm.eval_zero {K ι : Type*} [Field K]
    [Fintype ι] [DecidableEq ι]
    (t : CondLinearTerm K (ι := ι) 0) (x : ι → K) :
    CondLinearTerm.eval t x = 0 := by
  cases t
  rfl

/-- A one-level representation of a conditionally linear function has
support-relative prefix decomposition data. -/
private theorem CondLinearTerm.nonempty_clDataOn_one {K ι : Type*} [Field K]
    [Fintype ι] [DecidableEq ι] (t : CondLinearTerm K (ι := ι) 1)
    {S : Finset ι} (ht : CondLinearTerm.supportedOn t S) :
    Nonempty (CLDataOn K ι S 1 (CondLinearTerm.eval t)) := by
  cases t with
  | @succ ell S₁ L₁ hSupport rest =>
      refine ⟨{
        marginal := fun _ => CondLinearTerm.eval (.succ S₁ L₁ hSupport rest)
        factor := fun _ _ => S
        linear := fun _ _ => L₁.comp (coordinateRestrictionLinear S₁)
        marginal_cl := ?_
        factor_subset := ?_
        factor_disjoint := ?_
        factor_cover := ?_
        linear_supported := ?_
        sum_formula := ?_
        top := ?_
      }⟩
      · intro k
        have hk : k = 0 := Subsingleton.elim _ _
        subst k
        exact ⟨.succ S₁ L₁ hSupport rest, ht, rfl⟩
      · intro k u
        exact Finset.Subset.rfl
      · intro x i j hij
        exact (hij (Subsingleton.elim i j)).elim
      · intro x a ha
        exact ⟨0, ha⟩
      · intro k u x a ha
        change L₁ (coordinateRestriction S₁ x) a = 0
        exact hSupport _ _ (fun haS₁ => ha (ht.1 haS₁))
      · intro k x
        have hk : k = 0 := Subsingleton.elim _ _
        subst k
        simp only [Fin.sum_univ_one, Fin.isValue, le_refl, ↓reduceIte]
        change CondLinearTerm.eval (.succ S₁ L₁ hSupport rest) x =
          L₁ (coordinateRestriction S₁ (coordinateRestriction S x))
        rw [coordinateRestriction_coordinateRestriction ht.1]
        change L₁ (coordinateRestriction S₁ x) +
            CondLinearTerm.eval
              (rest (L₁ (coordinateRestriction S₁ x))) x = _
        rw [CondLinearTerm.eval_zero]
        exact add_zero _
      · intro h
        rfl

/-- The first linear contribution in the inductive prefix decomposition. -/
private def clDataFirst {K ι : Type*} [Field K] [Fintype ι] [DecidableEq ι]
    (S₁ : Finset ι) (L₁ : (ι → K) →ₗ[K] (ι → K))
    (x : ι → K) : ι → K :=
  L₁ (coordinateRestriction S₁ x)

/-- Add the first contribution to each marginal of residual decomposition
data. -/
private def clDataConsMarginal {K ι : Type*} [Field K]
    [Fintype ι] [DecidableEq ι] {T : Finset ι} {ell : ℕ}
    {R : (ι → K) → (ι → K) → (ι → K)}
    (S₁ : Finset ι) (L₁ : (ι → K) →ₗ[K] (ι → K))
    (d : ∀ y, CLDataOn K ι T ell (R y)) :
    Fin (ell + 1) → (ι → K) → (ι → K) :=
  Fin.cases (clDataFirst S₁ L₁) fun k x =>
    clDataFirst S₁ L₁ x + (d (clDataFirst S₁ L₁ x)).marginal k x

/-- Select the first or residual factor register from a combined prefix. -/
private def clDataConsFactor {K ι : Type*} [Field K]
    [Fintype ι] [DecidableEq ι] {T : Finset ι} {ell : ℕ}
    {R : (ι → K) → (ι → K) → (ι → K)}
    (S₁ : Finset ι) (d : ∀ y, CLDataOn K ι T ell (R y)) :
    Fin (ell + 1) → (ι → K) → Finset ι :=
  Fin.cases (fun _ => S₁) fun k u =>
    (d (coordinateRestriction S₁ u)).factor k (coordinateRestriction T u)

/-- Select the first or residual linear map from a combined prefix. -/
private def clDataConsLinear {K ι : Type*} [Field K]
    [Fintype ι] [DecidableEq ι] {T : Finset ι} {ell : ℕ}
    {R : (ι → K) → (ι → K) → (ι → K)}
    (S₁ : Finset ι) (L₁ : (ι → K) →ₗ[K] (ι → K))
    (d : ∀ y, CLDataOn K ι T ell (R y)) :
    Fin (ell + 1) → (ι → K) → ((ι → K) →ₗ[K] (ι → K)) :=
  Fin.cases (fun _ => L₁.comp (coordinateRestrictionLinear S₁)) fun k u =>
    (d (coordinateRestriction S₁ u)).linear k (coordinateRestriction T u)

@[simp]
private theorem clDataConsMarginal_zero {K ι : Type*} [Field K]
    [Fintype ι] [DecidableEq ι] {T : Finset ι} {ell : ℕ}
    {R : (ι → K) → (ι → K) → (ι → K)}
    (S₁ : Finset ι) (L₁ : (ι → K) →ₗ[K] (ι → K))
    (d : ∀ y, CLDataOn K ι T ell (R y)) (x : ι → K) :
    clDataConsMarginal S₁ L₁ d 0 x = clDataFirst S₁ L₁ x := rfl

@[simp]
private theorem clDataConsMarginal_succ {K ι : Type*} [Field K]
    [Fintype ι] [DecidableEq ι] {T : Finset ι} {ell : ℕ}
    {R : (ι → K) → (ι → K) → (ι → K)}
    (S₁ : Finset ι) (L₁ : (ι → K) →ₗ[K] (ι → K))
    (d : ∀ y, CLDataOn K ι T ell (R y)) (k : Fin ell) (x : ι → K) :
    clDataConsMarginal S₁ L₁ d k.succ x =
      clDataFirst S₁ L₁ x +
        (d (clDataFirst S₁ L₁ x)).marginal k x := rfl

private theorem clPrefix_cons_succ {K ι : Type*} [Field K]
    [Fintype ι] [DecidableEq ι] {T : Finset ι} {ell : ℕ}
    {R : (ι → K) → (ι → K) → (ι → K)}
    (S₁ : Finset ι) (L₁ : (ι → K) →ₗ[K] (ι → K))
    (d : ∀ y, CLDataOn K ι T (ell + 1) (R y)) (k : Fin (ell + 1))
    (x : ι → K) :
    clPrefix (clDataConsMarginal S₁ L₁ d) k.succ x =
      clDataFirst S₁ L₁ x +
        clPrefix (d (clDataFirst S₁ L₁ x)).marginal k x := by
  cases k using Fin.cases with
  | zero => simp [clPrefix]
  | succ k =>
      simp only [clPrefix]
      change clDataConsMarginal S₁ L₁ d (Fin.castSucc k).succ x =
        clDataFirst S₁ L₁ x +
          (d (clDataFirst S₁ L₁ x)).marginal (Fin.castSucc k) x
      rfl

@[simp]
private theorem clDataConsFactor_zero {K ι : Type*} [Field K]
    [Fintype ι] [DecidableEq ι] {T : Finset ι} {ell : ℕ}
    {R : (ι → K) → (ι → K) → (ι → K)}
    (S₁ : Finset ι) (d : ∀ y, CLDataOn K ι T ell (R y)) (u : ι → K) :
    clDataConsFactor S₁ d 0 u = S₁ := rfl

@[simp]
private theorem clDataConsFactor_succ {K ι : Type*} [Field K]
    [Fintype ι] [DecidableEq ι] {T : Finset ι} {ell : ℕ}
    {R : (ι → K) → (ι → K) → (ι → K)}
    (S₁ : Finset ι) (d : ∀ y, CLDataOn K ι T ell (R y))
    (k : Fin ell) (u : ι → K) :
    clDataConsFactor S₁ d k.succ u =
      (d (coordinateRestriction S₁ u)).factor k (coordinateRestriction T u) := rfl

@[simp]
private theorem clDataConsLinear_zero {K ι : Type*} [Field K]
    [Fintype ι] [DecidableEq ι] {T : Finset ι} {ell : ℕ}
    {R : (ι → K) → (ι → K) → (ι → K)}
    (S₁ : Finset ι) (L₁ : (ι → K) →ₗ[K] (ι → K))
    (d : ∀ y, CLDataOn K ι T ell (R y)) (u : ι → K) :
    clDataConsLinear S₁ L₁ d 0 u =
      L₁.comp (coordinateRestrictionLinear S₁) := rfl

@[simp]
private theorem clDataConsLinear_succ {K ι : Type*} [Field K]
    [Fintype ι] [DecidableEq ι] {T : Finset ι} {ell : ℕ}
    {R : (ι → K) → (ι → K) → (ι → K)}
    (S₁ : Finset ι) (L₁ : (ι → K) →ₗ[K] (ι → K))
    (d : ∀ y, CLDataOn K ι T ell (R y)) (k : Fin ell) (u : ι → K) :
    clDataConsLinear S₁ L₁ d k.succ u =
      (d (coordinateRestriction S₁ u)).linear k (coordinateRestriction T u) := rfl

private theorem coordinateRestriction_clPrefix_cons_succ_left
    {K ι : Type*} [Field K] [Fintype ι] [DecidableEq ι]
    {T : Finset ι} {ell : ℕ}
    {R : (ι → K) → (ι → K) → (ι → K)}
    (S₁ : Finset ι) (L₁ : (ι → K) →ₗ[K] (ι → K))
    (hSupport : ∀ x a, a ∉ S₁ → L₁ x a = 0)
    (d : ∀ y, CLDataOn K ι T (ell + 1) (R y))
    (hDisjoint : Disjoint S₁ T) (k : Fin (ell + 1)) (x : ι → K) :
    coordinateRestriction S₁
        (clPrefix (clDataConsMarginal S₁ L₁ d) k.succ x) =
      clDataFirst S₁ L₁ x := by
  rw [clPrefix_cons_succ, coordinateRestriction_add]
  have hfirst : coordinateRestriction S₁ (clDataFirst S₁ L₁ x) =
      clDataFirst S₁ L₁ x :=
    coordinateRestriction_eq_self (x := clDataFirst S₁ L₁ x) (hSupport _)
  have htail : coordinateRestriction S₁
      (clPrefix (d (clDataFirst S₁ L₁ x)).marginal k x) = 0 :=
    coordinateRestriction_eq_zero_of_disjoint hDisjoint
      (fun a ha =>
        (d (clDataFirst S₁ L₁ x)).prefix_eq_zero_of_not_mem k x ha)
  rw [hfirst, htail]
  exact add_zero _

private theorem coordinateRestriction_clPrefix_cons_succ_right
    {K ι : Type*} [Field K] [Fintype ι] [DecidableEq ι]
    {T : Finset ι} {ell : ℕ}
    {R : (ι → K) → (ι → K) → (ι → K)}
    (S₁ : Finset ι) (L₁ : (ι → K) →ₗ[K] (ι → K))
    (hSupport : ∀ x a, a ∉ S₁ → L₁ x a = 0)
    (d : ∀ y, CLDataOn K ι T (ell + 1) (R y))
    (hDisjoint : Disjoint S₁ T) (k : Fin (ell + 1)) (x : ι → K) :
    coordinateRestriction T
        (clPrefix (clDataConsMarginal S₁ L₁ d) k.succ x) =
      clPrefix (d (clDataFirst S₁ L₁ x)).marginal k x := by
  rw [clPrefix_cons_succ, coordinateRestriction_add]
  have hfirst : coordinateRestriction T (clDataFirst S₁ L₁ x) = 0 :=
    coordinateRestriction_eq_zero_of_disjoint hDisjoint.symm (hSupport _)
  have htail : coordinateRestriction T
      (clPrefix (d (clDataFirst S₁ L₁ x)).marginal k x) =
        clPrefix (d (clDataFirst S₁ L₁ x)).marginal k x :=
    coordinateRestriction_eq_self
      (fun a ha =>
        (d (clDataFirst S₁ L₁ x)).prefix_eq_zero_of_not_mem k x ha)
  rw [hfirst, htail]
  exact zero_add _

private theorem clDataConsFactor_prefix_succ
    {K ι : Type*} [Field K] [Fintype ι] [DecidableEq ι]
    {T : Finset ι} {ell : ℕ}
    {R : (ι → K) → (ι → K) → (ι → K)}
    (S₁ : Finset ι) (L₁ : (ι → K) →ₗ[K] (ι → K))
    (hSupport : ∀ x a, a ∉ S₁ → L₁ x a = 0)
    (d : ∀ y, CLDataOn K ι T (ell + 1) (R y))
    (hDisjoint : Disjoint S₁ T) (k : Fin (ell + 1)) (x : ι → K) :
    clDataConsFactor S₁ d k.succ
        (clPrefix (clDataConsMarginal S₁ L₁ d) k.succ x) =
      (d (clDataFirst S₁ L₁ x)).factor k
        (clPrefix (d (clDataFirst S₁ L₁ x)).marginal k x) := by
  rw [clDataConsFactor_succ]
  rw [coordinateRestriction_clPrefix_cons_succ_left S₁ L₁ hSupport d
    hDisjoint]
  rw [coordinateRestriction_clPrefix_cons_succ_right S₁ L₁ hSupport d
    hDisjoint]

private theorem clDataConsLinear_prefix_succ
    {K ι : Type*} [Field K] [Fintype ι] [DecidableEq ι]
    {T : Finset ι} {ell : ℕ}
    {R : (ι → K) → (ι → K) → (ι → K)}
    (S₁ : Finset ι) (L₁ : (ι → K) →ₗ[K] (ι → K))
    (hSupport : ∀ x a, a ∉ S₁ → L₁ x a = 0)
    (d : ∀ y, CLDataOn K ι T (ell + 1) (R y))
    (hDisjoint : Disjoint S₁ T) (k : Fin (ell + 1)) (x : ι → K) :
    clDataConsLinear S₁ L₁ d k.succ
        (clPrefix (clDataConsMarginal S₁ L₁ d) k.succ x) =
      (d (clDataFirst S₁ L₁ x)).linear k
        (clPrefix (d (clDataFirst S₁ L₁ x)).marginal k x) := by
  rw [clDataConsLinear_succ]
  rw [coordinateRestriction_clPrefix_cons_succ_left S₁ L₁ hSupport d
    hDisjoint]
  rw [coordinateRestriction_clPrefix_cons_succ_right S₁ L₁ hSupport d
    hDisjoint]

/-- Prepending a syntax stage to support-relative residual data produces
support-relative data at the next level. -/
private theorem CondLinearTerm.nonempty_clDataOn_succ
    {K ι : Type*} [Field K] [Fintype ι] [DecidableEq ι] {ell : ℕ}
    (S₁ : Finset ι) (L₁ : (ι → K) →ₗ[K] (ι → K))
    (hSupport : ∀ x a, a ∉ S₁ → L₁ x a = 0)
    (rest : (ι → K) → CondLinearTerm K (ι := ι) (ell + 1))
    {S : Finset ι}
    (ht : CondLinearTerm.supportedOn (.succ S₁ L₁ hSupport rest) S)
    (hd : ∀ y, Nonempty (CLDataOn K ι (S \ S₁) (ell + 1)
      (fun x => CondLinearTerm.eval (rest y) x))) :
    Nonempty (CLDataOn K ι S ((ell + 1) + 1)
      (CondLinearTerm.eval (.succ S₁ L₁ hSupport rest))) := by
  classical
  let d := fun y => Classical.choice (hd y)
  have hDisjoint : Disjoint S₁ (S \ S₁) := Finset.disjoint_sdiff
  refine ⟨{
    marginal := clDataConsMarginal S₁ L₁ d
    factor := clDataConsFactor S₁ d
    linear := clDataConsLinear S₁ L₁ d
    marginal_cl := ?_
    factor_subset := ?_
    factor_disjoint := ?_
    factor_cover := ?_
    linear_supported := ?_
    sum_formula := ?_
    top := ?_
  }⟩
  · intro k
    refine Fin.cases ?_ (fun i => ?_) k
    · refine ⟨.succ S₁ L₁ hSupport (fun _ => .zero), ⟨ht.1, fun _ => trivial⟩, ?_⟩
      funext x
      simp [CondLinearTerm.eval, clDataFirst]
    · rw [show clDataConsMarginal S₁ L₁ d i.succ =
          (fun x => clDataFirst S₁ L₁ x +
            (d (clDataFirst S₁ L₁ x)).marginal i x) by
          funext x
          rfl]
      simpa only [clDataFirst, Fin.val_succ, Nat.add_assoc] using
        (IsCondLinearOn.cons L₁ ht.1 hSupport
          (fun y x => (d y).marginal i x) (fun y => (d y).marginal_cl i))
  · intro k u
    refine Fin.cases ?_ (fun i => ?_) k
    · exact ht.1
    · exact ((d (coordinateRestriction S₁ u)).factor_subset i _).trans
          Finset.sdiff_subset
  · intro x i j hij
    cases i using Fin.cases with
    | zero =>
        cases j using Fin.cases with
        | zero => exact (hij rfl).elim
        | succ j =>
            rw [clDataConsFactor_zero]
            rw [clDataConsFactor_prefix_succ S₁ L₁ hSupport d hDisjoint]
            exact hDisjoint.mono_right
              ((d (clDataFirst S₁ L₁ x)).factor_subset j _)
    | succ i =>
        cases j using Fin.cases with
        | zero =>
            rw [clDataConsFactor_zero]
            rw [clDataConsFactor_prefix_succ S₁ L₁ hSupport d hDisjoint]
            exact (hDisjoint.mono_right
              ((d (clDataFirst S₁ L₁ x)).factor_subset i _)).symm
        | succ j =>
            have hij' : i ≠ j := by
              intro h
              subst j
              exact hij rfl
            rw [clDataConsFactor_prefix_succ S₁ L₁ hSupport d hDisjoint]
            rw [clDataConsFactor_prefix_succ S₁ L₁ hSupport d hDisjoint]
            exact (d (clDataFirst S₁ L₁ x)).factor_disjoint x i j hij'
  · intro x a ha
    by_cases haS₁ : a ∈ S₁
    · exact ⟨0, by simpa using haS₁⟩
    · have haTail : a ∈ S \ S₁ := Finset.mem_sdiff.mpr ⟨ha, haS₁⟩
      obtain ⟨i, hai⟩ :=
        (d (clDataFirst S₁ L₁ x)).factor_cover x a haTail
      refine ⟨i.succ, ?_⟩
      rw [clDataConsFactor_prefix_succ S₁ L₁ hSupport d hDisjoint]
      exact hai
  · intro k u x a ha
    revert ha
    refine Fin.cases ?_ (fun i => ?_) k
    · intro ha
      change L₁ (coordinateRestriction S₁ x) a = 0
      exact hSupport _ _ ha
    · intro ha
      exact (d (coordinateRestriction S₁ u)).linear_supported i
          (coordinateRestriction (S \ S₁) u) x a ha
  · intro k x
    have hhead :
        clDataConsLinear S₁ L₁ d 0
            (clPrefix (clDataConsMarginal S₁ L₁ d) 0 x)
            (coordinateRestriction
              (clDataConsFactor S₁ d 0
                (clPrefix (clDataConsMarginal S₁ L₁ d) 0 x)) x) =
          clDataFirst S₁ L₁ x := by
      change L₁ (coordinateRestriction S₁ (coordinateRestriction S₁ x)) =
        L₁ (coordinateRestriction S₁ x)
      rw [coordinateRestriction_coordinateRestriction Finset.Subset.rfl]
    refine Fin.cases ?_ (fun j => ?_) k
    · rw [Fin.sum_univ_succ]
      simp only [Fin.val_zero, le_refl, ↓reduceIte, hhead]
      simp
    · rw [Fin.sum_univ_succ]
      simp only [Fin.val_zero, Nat.zero_le, ↓reduceIte, hhead]
      rw [clDataConsMarginal_succ]
      congr 1
      rw [(d (clDataFirst S₁ L₁ x)).sum_formula j x]
      apply Finset.sum_congr rfl
      intro i _
      by_cases hij : i.val ≤ j.val
      · have hsucc : i.succ.val ≤ j.succ.val := by
          simpa only [Fin.val_succ, Nat.succ_le_succ_iff] using hij
        rw [if_pos hsucc, if_pos hij]
        rw [clDataConsLinear_prefix_succ S₁ L₁ hSupport d hDisjoint]
        rw [clDataConsFactor_prefix_succ S₁ L₁ hSupport d hDisjoint]
      · have hsucc : ¬ i.succ.val ≤ j.succ.val := by
          simpa only [Fin.val_succ, Nat.succ_le_succ_iff] using hij
        rw [if_neg hsucc, if_neg hij]
  · intro h
    have hTail : 0 < ell + 1 := by omega
    let last : Fin (ell + 1) :=
      ⟨(ell + 1) - 1, Nat.sub_lt hTail (by decide)⟩
    have hlast :
        (⟨((ell + 1) + 1) - 1, Nat.sub_lt h (by decide)⟩ : Fin ((ell + 1) + 1)) =
          last.succ := by
      apply Fin.ext
      simp [last]
    funext x
    rw [hlast, clDataConsMarginal_succ]
    rw [congrFun ((d (clDataFirst S₁ L₁ x)).top hTail) x]
    rfl

/-- Every positive-level supported representation of a conditionally linear
function admits support-relative prefix decomposition data. -/
private theorem CondLinearTerm.nonempty_clDataOn {K ι : Type*} [Field K]
    [Fintype ι] [DecidableEq ι] {ell : ℕ} (hEll : 1 ≤ ell)
    (t : CondLinearTerm K (ι := ι) ell) {S : Finset ι}
    (ht : CondLinearTerm.supportedOn t S) :
    Nonempty (CLDataOn K ι S ell (CondLinearTerm.eval t)) := by
  induction ell using Nat.strong_induction_on generalizing S with
  | h ell ih =>
      cases ell with
      | zero => omega
      | succ n =>
          cases n with
          | zero => exact CondLinearTerm.nonempty_clDataOn_one t ht
          | succ n =>
              cases t with
              | @succ ell S₁ L₁ hSupport rest =>
                  apply CondLinearTerm.nonempty_clDataOn_succ S₁ L₁ hSupport rest ht
                  intro y
                  exact ih (n + 1) (by omega) (by omega) (rest y) (ht.2 y)

/-- A map is `ell`-level conditionally linear exactly when it admits the
prefix decomposition of `lem:cl-kth`; blueprint `ch12_qpbt_games.tex:520-540`,
paper `references/qpbt-paper/05_conditionally_linear_functions.tex:150-262`. -/
theorem isCondLinear_iff_nonempty_clData {K ι : Type*} [Field K]
    [Fintype ι] [DecidableEq ι] {ell : ℕ} (hEll : 1 ≤ ell)
    (L : (ι → K) → (ι → K)) :
    IsCondLinear ell L ↔ Nonempty (CLData K ι ell L) := by
  constructor
  · rintro ⟨t, ht, ht_eval⟩
    rw [← ht_eval]
    obtain ⟨d⟩ := CondLinearTerm.nonempty_clDataOn hEll t ht
    exact ⟨{
      marginal := d.marginal
      factor := d.factor
      linear := d.linear
      marginal_cl := d.marginal_cl
      factor_disjoint := d.factor_disjoint
      factor_cover := fun x a => d.factor_cover x a (Finset.mem_univ a)
      linear_supported := d.linear_supported
      sum_formula := d.sum_formula
      top := d.top
    }⟩
  · rintro ⟨d⟩
    have hPos : 0 < ell := by omega
    let last : Fin ell := ⟨ell - 1, Nat.sub_lt hPos (by decide)⟩
    have hLast := d.marginal_cl last
    rw [d.top hPos] at hLast
    simpa only [IsCondLinear, last, Nat.sub_add_cancel hEll] using hLast

/-- Coordinate direct sum of maps supported on a finite register partition.
This is a formalization-only auxiliary for `lem:cl-func-prod`, blueprint
`ch12_qpbt_games.tex:565-576`, paper
`references/qpbt-paper/05_conditionally_linear_functions.tex:315-364`. -/
def condLinearDirectSum {K ι : Type*} [Field K] [DecidableEq ι] {m : ℕ}
    (V : Fin m → Finset ι) (L : Fin m → (ι → K) → (ι → K))
    (x : ι → K) : ι → K :=
  ∑ j : Fin m, L j (coordinateRestriction (V j) x)

/-- Maximum of the levels in a finite direct sum. This formalization-only
auxiliary uses `0` for the empty family; `lem:cl-func-prod` separately assumes
the source boundary `m ≥ 1`. -/
def directSumLevel {m : ℕ} (ell : Fin m → ℕ) : ℕ :=
  Finset.univ.sup ell

/-- Direct sums over a register partition preserve conditional linearity. The
level-zero case is included explicitly, as required by the local correction to
`lem:cl-func-prod`; blueprint `ch12_qpbt_games.tex:565-576`, paper
`references/qpbt-paper/05_conditionally_linear_functions.tex:315-364`. -/
theorem IsCondLinear.directSum {K ι : Type*} [Field K]
    [Fintype ι] [DecidableEq ι] {m : ℕ} (hm : 1 ≤ m)
    (V : Fin m → Finset ι) (ell : Fin m → ℕ)
    (L : Fin m → (ι → K) → (ι → K))
    (hDisjoint : ∀ i j, i ≠ j → Disjoint (V i) (V j))
    (hCover : ∀ a, ∃ i, a ∈ V i)
    (hL : ∀ j, IsCondLinearOn K (V j) (ell j) (L j)) :
    IsCondLinear (directSumLevel ell) (condLinearDirectSum V L) := by
  classical
  let _sourceIndex : Fin m := ⟨0, hm⟩
  have hLevel (j : Fin m) : ell j ≤ directSumLevel ell :=
    Finset.le_sup (f := ell) (Finset.mem_univ j)
  have hRaised (j : Fin m) :
      IsCondLinearOn K (V j) (directSumLevel ell) (L j) :=
    IsCondLinearOn.mono_level (hL j) (hLevel j)
  have hUnion : Finset.univ.biUnion V = (Finset.univ : Finset ι) := by
    apply Finset.eq_univ_of_forall
    intro a
    obtain ⟨j, haj⟩ := hCover a
    exact Finset.mem_biUnion.mpr ⟨j, Finset.mem_univ _, haj⟩
  have hSum := IsCondLinearOn.directSum_sameLevel V (directSumLevel ell) L
    hDisjoint hRaised
  rw [hUnion] at hSum
  exact hSum

/-- Extend a vector on a register by zero to the ambient coordinate space. -/
private def extendRegister {K ι : Type*} [Zero K] [DecidableEq ι]
    (S : Finset ι) (x : S → K) : ι → K := fun a =>
  if ha : a ∈ S then x ⟨a, ha⟩ else 0

/-- A partition of the ambient coordinates identifies ambient vectors with
tuples of vectors on the partition registers. -/
private noncomputable def coordinatePartitionEquiv {K ι J : Type*}
    [AddCommMonoid K] [Fintype ι] [DecidableEq ι] [Fintype J] [DecidableEq J]
    (V : J → Finset ι) (hDisjoint : ∀ i j, i ≠ j → Disjoint (V i) (V j))
    (hCover : ∀ a, ∃ j, a ∈ V j) : (ι → K) ≃ ∀ j, V j → K where
  toFun x := fun _ a => x a
  invFun x := ∑ j, extendRegister (V j) (x j)
  left_inv x := by
    funext a
    obtain ⟨j, haj⟩ := hCover a
    change (∑ i, extendRegister (V i) (fun b => x b)) a = x a
    rw [Finset.sum_apply, Finset.sum_eq_single j]
    · simp [extendRegister, haj]
    · intro i _ hij
      have hai : a ∉ V i := fun hai =>
        Finset.disjoint_left.mp (hDisjoint i j hij) hai haj
      simp [extendRegister, hai]
    · exact fun hj => (hj (Finset.mem_univ j)).elim
  right_inv x := by
    funext j a
    change (∑ i, extendRegister (V i) (x i)) a.1 = x j a
    rw [Finset.sum_apply, Finset.sum_eq_single j]
    · simp [extendRegister, a.2]
    · intro i _ hij
      have hai : a.1 ∉ V i := fun hai =>
        Finset.disjoint_left.mp (hDisjoint i j hij) hai a.2
      simp [extendRegister, hai]
    · exact fun hj => (hj (Finset.mem_univ j)).elim

private theorem coordinatePartitionEquiv_apply {K ι J : Type*}
    [AddCommMonoid K] [Fintype ι] [DecidableEq ι] [Fintype J] [DecidableEq J]
    (V : J → Finset ι) (hDisjoint : ∀ i j, i ≠ j → Disjoint (V i) (V j))
    (hCover : ∀ a, ∃ j, a ∈ V j) (x : ι → K) (j : J) (a : V j) :
    coordinatePartitionEquiv V hDisjoint hCover x j a = x a := rfl

private theorem extendRegister_partition_apply {K ι J : Type*} [Field K]
    [Fintype ι] [DecidableEq ι] [Fintype J] [DecidableEq J]
    (V : J → Finset ι) (hDisjoint : ∀ i j, i ≠ j → Disjoint (V i) (V j))
    (hCover : ∀ a, ∃ j, a ∈ V j) (x : ι → K) (j : J) :
    extendRegister (V j) (coordinatePartitionEquiv V hDisjoint hCover x j) =
      coordinateRestriction (V j) x := by
  ext a
  by_cases ha : a ∈ V j
  · simp [extendRegister, coordinateRestriction, ha, coordinatePartitionEquiv_apply]
  · simp [extendRegister, coordinateRestriction, ha]

/-- Reindex the cardinality of a filtered finite type along an equivalence. -/
private theorem card_filter_equiv {A B : Type*} [Fintype A]
    [Fintype B] (e : A ≃ B) (p : A → Prop) (q : B → Prop)
    [DecidablePred p] [DecidablePred q] (hpq : ∀ a, p a ↔ q (e a)) :
    (Finset.univ.filter p).card = (Finset.univ.filter q).card := by
  classical
  have hmap : (Finset.univ.filter p).map e.toEmbedding = Finset.univ.filter q := by
    ext b
    simp only [Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨a, ha, rfl⟩
      exact (hpq a).mp ha
    · intro hb
      exact ⟨e.symm b, (hpq (e.symm b)).mpr (by simpa using hb), by simp⟩
  rw [← hmap, Finset.card_map]

private theorem card_filter_pi_apply_mem {J : Type*} [Fintype J] [DecidableEq J]
    (B : J → Type*) [∀ j, Fintype (B j)] [∀ j, DecidableEq (B j)]
    (j : J) (s : Finset (B j)) :
    ((Finset.univ : Finset (∀ i, B i)).filter fun x => x j ∈ s).card =
      s.card * ∏ i : {i // i ≠ j}, Fintype.card (B i.1) := by
  let u : ∀ i, Finset (B i) := fun _ => Finset.univ
  have hs : s ⊆ u j := Finset.subset_univ s
  rw [← Fintype.piFinset_univ]
  rw [← Fintype.piFinset_update_eq_filter_piFinset_mem u j hs]
  rw [Fintype.card_piFinset]
  rw [Fintype.prod_eq_mul_prod_subtype_ne _ j]
  have hsame : Function.update u j s j = s := by simp
  rw [hsame]
  apply congrArg (fun n => s.card * n)
  apply Finset.prod_congr rfl
  intro i _
  have hne : Function.update u j s i.1 = u i.1 := by simp [i.2]
  rw [hne]
  simp [u]

/-- The weight of a shared-seed distribution is its fiber cardinality divided
by the cardinality of the seed space. -/
private theorem clDistribution_weight_eq_card_filter_div {K ι : Type*}
    [Field K] [Fintype K] [DecidableEq K] [Fintype ι] [DecidableEq ι]
    (L R : (ι → K) → (ι → K)) (z : (ι → K) × (ι → K)) :
    (clDistribution L R).weight z =
      ((Finset.univ.filter fun x => (L x, R x) = z).card : Error) /
        Fintype.card (ι → K) := by
  classical
  rw [clDistribution, Distribution.map_weight, uniformDistribution_support]
  simp [uniformDistribution, Distribution.uniformOnFinset_weight, div_eq_mul_inv,
    mul_comm]

/-- The CL distribution of coordinate direct sums factors into the component
CL distributions. The equality is stated pointwise on weights, which is the
finite-distribution meaning of the product in `lem:cl-dist-prod`; blueprint
`ch12_qpbt_games.tex:582-587`, paper
`references/qpbt-paper/05_conditionally_linear_functions.tex:366-379`. -/
theorem clDistribution_directSum_eq_prod {K ι : Type*} [Field K]
    [Fintype K] [DecidableEq K] [Fintype ι] [DecidableEq ι]
    {m : ℕ} (hm : 1 ≤ m) (V : Fin m → Finset ι)
    (ell : Fin m → ℕ)
    (L R : Fin m → (ι → K) → (ι → K))
    (hDisjoint : ∀ i j, i ≠ j → Disjoint (V i) (V j))
    (hCover : ∀ a, ∃ i, a ∈ V i)
    (hL : ∀ j, IsCondLinearOn K (V j) (ell j) (L j))
    (hR : ∀ j, IsCondLinearOn K (V j) (ell j) (R j))
    (z : (ι → K) × (ι → K)) :
    (clDistribution (condLinearDirectSum V L) (condLinearDirectSum V R)).weight z =
      ∏ j : Fin m, (clDistribution (L j) (R j)).weight
        (coordinateRestriction (V j) z.1, coordinateRestriction (V j) z.2) := by
  classical
  let _sourceIndex : Fin m := ⟨0, hm⟩
  let e : (ι → K) ≃ ∀ j, V j → K :=
    coordinatePartitionEquiv V hDisjoint hCover
  let fiber : (j : Fin m) → Finset (V j → K) := fun j =>
    Finset.univ.filter fun x =>
      (L j (extendRegister (V j) x), R j (extendRegister (V j) x)) =
        (coordinateRestriction (V j) z.1, coordinateRestriction (V j) z.2)
  have hL_support (j : Fin m) (x : ι → K) (a : ι) (ha : a ∉ V j) :
      L j x a = 0 :=
    IsCondLinearOn.apply_eq_zero_of_not_mem (hL j) x ha
  have hR_support (j : Fin m) (x : ι → K) (a : ι) (ha : a ∉ V j) :
      R j x a = 0 :=
    IsCondLinearOn.apply_eq_zero_of_not_mem (hR j) x ha
  have hdirect (x : ι → K) :
      (condLinearDirectSum V L x, condLinearDirectSum V R x) = z ↔
        ∀ j,
          (L j (coordinateRestriction (V j) x),
              R j (coordinateRestriction (V j) x)) =
            (coordinateRestriction (V j) z.1, coordinateRestriction (V j) z.2) := by
    constructor
    · intro h j
      have hleft : condLinearDirectSum V L x = z.1 := congrArg Prod.fst h
      have hright : condLinearDirectSum V R x = z.2 := congrArg Prod.snd h
      have hleft_parts : ∀ i,
          L i (coordinateRestriction (V i) x) = coordinateRestriction (V i) z.1 := by
        apply (sum_eq_iff_coordinateRestriction_eq V hDisjoint hCover
          (fun i => L i (coordinateRestriction (V i) x))
          (fun i a ha => hL_support i _ a ha) z.1).mp
        exact hleft
      have hright_parts : ∀ i,
          R i (coordinateRestriction (V i) x) = coordinateRestriction (V i) z.2 := by
        apply (sum_eq_iff_coordinateRestriction_eq V hDisjoint hCover
          (fun i => R i (coordinateRestriction (V i) x))
          (fun i a ha => hR_support i _ a ha) z.2).mp
        exact hright
      exact Prod.ext (hleft_parts j) (hright_parts j)
    · intro h
      apply Prod.ext
      · apply (sum_eq_iff_coordinateRestriction_eq V hDisjoint hCover
          (fun i => L i (coordinateRestriction (V i) x))
          (fun i a ha => hL_support i _ a ha) z.1).mpr
        exact fun j => congrArg Prod.fst (h j)
      · apply (sum_eq_iff_coordinateRestriction_eq V hDisjoint hCover
          (fun i => R i (coordinateRestriction (V i) x))
          (fun i a ha => hR_support i _ a ha) z.2).mpr
        exact fun j => congrArg Prod.snd (h j)
  have hglobal_card :
      (Finset.univ.filter fun x =>
          (condLinearDirectSum V L x, condLinearDirectSum V R x) = z).card =
        ∏ j, (fiber j).card := by
    calc
      (Finset.univ.filter fun x =>
          (condLinearDirectSum V L x, condLinearDirectSum V R x) = z).card =
          (Finset.univ.filter fun x : ∀ j, V j → K => ∀ j, x j ∈ fiber j).card := by
            apply card_filter_equiv e
            intro x
            rw [hdirect]
            simp only [fiber, Finset.mem_filter, Finset.mem_univ, true_and]
            constructor
            · intro hx j
              simpa only [e, extendRegister_partition_apply V hDisjoint hCover]
                using hx j
            · intro hx j
              simpa only [e, extendRegister_partition_apply V hDisjoint hCover]
                using hx j
      _ = (Fintype.piFinset fiber).card := by
            congr 1
            ext x
            simp
      _ = ∏ j, (fiber j).card := Fintype.card_piFinset fiber
  have hcomponent_card (j : Fin m) :
      (Finset.univ.filter fun x =>
          (L j x, R j x) =
            (coordinateRestriction (V j) z.1, coordinateRestriction (V j) z.2)).card =
        (fiber j).card *
          ∏ i : {i // i ≠ j}, Fintype.card (V i.1 → K) := by
    calc
      (Finset.univ.filter fun x =>
          (L j x, R j x) =
            (coordinateRestriction (V j) z.1, coordinateRestriction (V j) z.2)).card =
          (Finset.univ.filter fun x : ∀ i, V i → K => x j ∈ fiber j).card := by
            apply card_filter_equiv e
            intro x
            simp only [fiber, Finset.mem_filter, Finset.mem_univ, true_and]
            rw [extendRegister_partition_apply V hDisjoint hCover]
            rw [IsCondLinearOn.apply_coordinateRestriction (hL j) x]
            rw [IsCondLinearOn.apply_coordinateRestriction (hR j) x]
      _ = (fiber j).card *
          ∏ i : {i // i ≠ j}, Fintype.card (V i.1 → K) :=
        card_filter_pi_apply_mem (fun i => V i → K) j (fiber j)
  have hcard_seed : Fintype.card (ι → K) = ∏ j, Fintype.card (V j → K) := by
    rw [Fintype.card_congr e, Fintype.card_pi]
  have hcomponent_weight (j : Fin m) :
      (clDistribution (L j) (R j)).weight
          (coordinateRestriction (V j) z.1, coordinateRestriction (V j) z.2) =
        ((fiber j).card : Error) / Fintype.card (V j → K) := by
    rw [clDistribution_weight_eq_card_filter_div, hcomponent_card, hcard_seed]
    rw [Fintype.prod_eq_mul_prod_subtype_ne _ j]
    push_cast
    have hcardj : (Fintype.card (V j → K) : Error) ≠ 0 := by positivity
    have hcard_rest :
        (∏ i : {i // i ≠ j}, (Fintype.card (V i.1 → K) : Error)) ≠ 0 := by
      positivity
    field_simp
  rw [clDistribution_weight_eq_card_filter_div, hglobal_card, hcard_seed]
  simp_rw [hcomponent_weight]
  rw [Finset.prod_div_distrib]
  push_cast
  rfl

end MIPStarRE.QPBT
