import MIPStarRE.QPBT.Games.CondLinear

/-!
# Coordinate direct sums of conditionally linear representations

This module assembles the direct sum of equal-level representations of
conditionally linear functions over a family of pairwise disjoint registers,
together with the coordinate-restriction lemmas its support and evaluation
proofs rely on.  It is the supporting layer of
`MIPStarRE/QPBT/Games/CondLinearTheorems.lean`, the module that owns the
behaviour of conditionally linear maps and of their shared-seed distributions
under finite coordinate direct sums.

## References

The source result is `lem:cl-func-prod` in
`blueprint/src/chapter/ch12_qpbt_games.tex:1123-1134`, approached through the
formalization support nodes `lem:cl-supported-vanishing`,
`lem:cl-restriction-idem`, `lem:cl-restriction-sum`,
`lem:cl-supported-restriction`, and `lem:cl-func-prod-same-level` at
`ch12_qpbt_games.tex:1156-1212`.  The paper origin is
`references/qpbt-paper/05_conditionally_linear_functions.tex:150-379`.
-/

open scoped BigOperators

namespace MIPStarRE.QPBT

open MIPStarRE.LDT

/-- A representation of a conditionally linear function supported on a register
takes values that vanish off that register.  This is a formalization-only
auxiliary for `lem:cl-dist-prod`, blueprint `lem:cl-supported-vanishing`. -/
theorem CondLinearTerm.eval_eq_zero_of_not_mem {K ι : Type*} [Field K]
    [Fintype ι] [DecidableEq ι] {ell : ℕ}
    {t : CondLinearTerm K (ι := ι) ell} {S : Finset ι}
    (ht : CondLinearTerm.supportedOn t S) (x : ι → K) {a : ι} (ha : a ∉ S) :
    CondLinearTerm.eval t x a = 0 := by
  induction t generalizing S with
  | zero => rfl
  | @succ ell S₁ L₁ hSupport rest ih =>
      rcases ht with ⟨hS₁, hrest⟩
      change (L₁ (coordinateRestriction S₁ x) +
        CondLinearTerm.eval (rest (L₁ (coordinateRestriction S₁ x))) x) a = 0
      rw [Pi.add_apply, hSupport _ a (fun haS₁ => ha (hS₁ haS₁))]
      rw [ih _ (hrest _) (fun haDiff => ha (Finset.mem_sdiff.mp haDiff).1)]
      exact zero_add 0

/-- A supported representation of a conditionally linear function depends only
on the coordinates in its register. -/
private theorem CondLinearTerm.eval_congr_of_eq_on {K ι : Type*} [Field K]
    [Fintype ι] [DecidableEq ι] {ell : ℕ}
    {t : CondLinearTerm K (ι := ι) ell} {S : Finset ι}
    (ht : CondLinearTerm.supportedOn t S) {x y : ι → K}
    (hxy : ∀ a ∈ S, x a = y a) :
    CondLinearTerm.eval t x = CondLinearTerm.eval t y := by
  induction t generalizing S with
  | zero => rfl
  | @succ ell S₁ L₁ hSupport rest ih =>
      rcases ht with ⟨hS₁, hrest⟩
      have hrestrict : coordinateRestriction S₁ x = coordinateRestriction S₁ y := by
        ext a
        by_cases ha : a ∈ S₁
        · simp [coordinateRestriction, ha, hxy a (hS₁ ha)]
        · simp [coordinateRestriction, ha]
      simp only [CondLinearTerm.eval, hrestrict]
      rw [ih _ (hrest _) (fun a ha => hxy a (Finset.mem_sdiff.mp ha).1)]

/-- Restricting the input to the register supporting a conditionally linear
function does not change its value.  This is a formalization-only auxiliary
for `lem:cl-func-prod` and `lem:cl-dist-prod`, blueprint
`lem:cl-supported-restriction`. -/
theorem CondLinearTerm.eval_coordinateRestriction {K ι : Type*} [Field K]
    [Fintype ι] [DecidableEq ι] {ell : ℕ}
    {t : CondLinearTerm K (ι := ι) ell} {S : Finset ι}
    (ht : CondLinearTerm.supportedOn t S) (x : ι → K) :
    CondLinearTerm.eval t (coordinateRestriction S x) = CondLinearTerm.eval t x := by
  exact CondLinearTerm.eval_congr_of_eq_on ht fun a ha => by
    simp [coordinateRestriction, ha]

/-- Restricting first to a larger register does not affect a subsequent
restriction to a smaller register.  This is a formalization-only auxiliary
for `lem:cl-kth` and `lem:cl-func-prod`, blueprint
`lem:cl-restriction-idem`. -/
theorem coordinateRestriction_coordinateRestriction {K ι : Type*} [Field K]
    [DecidableEq ι] {S T : Finset ι} (hST : S ⊆ T) (x : ι → K) :
    coordinateRestriction S (coordinateRestriction T x) = coordinateRestriction S x := by
  ext a
  by_cases ha : a ∈ S
  · simp [coordinateRestriction, ha, hST ha]
  · simp [coordinateRestriction, ha]

/-- In a register partition, restricting a sum of supported vectors selects
the corresponding summand.  This is a formalization-only auxiliary for
`lem:cl-func-prod` and `lem:cl-dist-prod`, blueprint
`lem:cl-restriction-sum`. -/
theorem coordinateRestriction_sum_eq {K ι J : Type*} [Field K]
    [DecidableEq ι] [Fintype J]
    (V : J → Finset ι) (hDisjoint : ∀ i j, i ≠ j → Disjoint (V i) (V j))
    (f : J → ι → K) (hf : ∀ j a, a ∉ V j → f j a = 0) (j : J) :
    coordinateRestriction (V j) (∑ i, f i) = f j := by
  ext a
  by_cases ha : a ∈ V j
  · rw [coordinateRestriction]
    simp only [ha, ↓reduceIte, Finset.sum_apply]
    apply Finset.sum_eq_single j
    · intro i _ hij
      apply hf i a
      intro hai
      exact Finset.disjoint_left.mp (hDisjoint i j hij) hai ha
    · exact fun hj => (hj (Finset.mem_univ j)).elim
  · rw [coordinateRestriction]
    simp [ha, hf j a ha]

/-- The first register of a positive-level conditionally-linear term. -/
private def CondLinearTerm.headSupport {K ι : Type*} [Field K]
    [Fintype ι] [DecidableEq ι] {ell : ℕ} :
    CondLinearTerm K (ι := ι) (ell + 1) → Finset ι
  | .succ S₁ _ _ _ => S₁

/-- The first linear map of a positive-level conditionally-linear term. -/
private def CondLinearTerm.headLinear {K ι : Type*} [Field K]
    [Fintype ι] [DecidableEq ι] {ell : ℕ} :
    CondLinearTerm K (ι := ι) (ell + 1) → ((ι → K) →ₗ[K] (ι → K))
  | .succ _ L₁ _ _ => L₁

/-- The residual family of a positive-level conditionally-linear term. -/
private def CondLinearTerm.tail {K ι : Type*} [Field K]
    [Fintype ι] [DecidableEq ι] {ell : ℕ} :
    CondLinearTerm K (ι := ι) (ell + 1) →
      ((ι → K) → CondLinearTerm K (ι := ι) ell)
  | .succ _ _ _ rest => rest

private theorem CondLinearTerm.headLinear_eq_zero_of_not_mem
    {K ι : Type*} [Field K] [Fintype ι] [DecidableEq ι] {ell : ℕ}
    (t : CondLinearTerm K (ι := ι) (ell + 1)) (x : ι → K) {a : ι}
    (ha : a ∉ t.headSupport) : t.headLinear x a = 0 := by
  cases t with
  | succ S₁ L₁ hSupport rest => exact hSupport x a ha

private theorem CondLinearTerm.supportedOn_headSupport {K ι : Type*} [Field K]
    [Fintype ι] [DecidableEq ι] {ell : ℕ}
    {t : CondLinearTerm K (ι := ι) (ell + 1)} {S : Finset ι}
    (ht : CondLinearTerm.supportedOn t S) : t.headSupport ⊆ S := by
  cases t with
  | succ S₁ L₁ hSupport rest => exact ht.1

private theorem CondLinearTerm.supportedOn_tail {K ι : Type*} [Field K]
    [Fintype ι] [DecidableEq ι] {ell : ℕ}
    {t : CondLinearTerm K (ι := ι) (ell + 1)} {S : Finset ι}
    (ht : CondLinearTerm.supportedOn t S) (y : ι → K) :
    CondLinearTerm.supportedOn (t.tail y) (S \ t.headSupport) := by
  cases t with
  | succ S₁ L₁ hSupport rest => exact ht.2 y

private theorem CondLinearTerm.eval_succ_eq {K ι : Type*} [Field K]
    [Fintype ι] [DecidableEq ι] {ell : ℕ}
    (t : CondLinearTerm K (ι := ι) (ell + 1)) (x : ι → K) :
    CondLinearTerm.eval t x =
      t.headLinear (coordinateRestriction t.headSupport x) +
        CondLinearTerm.eval
          (t.tail (t.headLinear (coordinateRestriction t.headSupport x))) x := by
  cases t
  rfl

/-- The sum of the first linear pieces of a finite family of positive-level
conditionally-linear terms. -/
private def condLinearHeadSum {K ι J : Type*} [Field K]
    [Fintype ι] [DecidableEq ι] [Fintype J] [DecidableEq J] {ell : ℕ}
    (t : J → CondLinearTerm K (ι := ι) (ell + 1)) :
    (ι → K) →ₗ[K] (ι → K) where
  toFun x := ∑ j, (t j).headLinear (coordinateRestriction (t j).headSupport x)
  map_add' x y := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j _
    rw [← map_add]
    congr 1
    ext b
    by_cases hb : b ∈ (t j).headSupport <;> simp [coordinateRestriction, hb]
  map_smul' c x := by
    rw [Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro j _
    rw [← map_smul]
    congr 1
    ext b
    by_cases hb : b ∈ (t j).headSupport <;> simp [coordinateRestriction, hb]

/-- Combine equal-level representations of conditionally linear functions on
disjoint registers. -/
private def CondLinearTerm.directSum {K ι J : Type*} [Field K]
    [Fintype ι] [DecidableEq ι] [Fintype J] [DecidableEq J]
    (V : J → Finset ι) :
    (ell : ℕ) → (J → CondLinearTerm K (ι := ι) ell) →
      CondLinearTerm K (ι := ι) ell
  | 0, _ => .zero
  | ell + 1, t =>
      .succ (Finset.univ.biUnion fun j => (t j).headSupport) (condLinearHeadSum t)
        (by
          intro x a ha
          simp only [condLinearHeadSum, LinearMap.coe_mk, AddHom.coe_mk,
            Finset.sum_apply]
          apply Finset.sum_eq_zero
          intro j _
          exact CondLinearTerm.headLinear_eq_zero_of_not_mem (t j) _
            (fun haj => ha (Finset.mem_biUnion.mpr ⟨j, Finset.mem_univ _, haj⟩)))
        (fun y => directSum (fun j => V j \ (t j).headSupport) ell
          (fun j => (t j).tail (coordinateRestriction (V j) y)))

private theorem CondLinearTerm.directSum_supportedOn {K ι J : Type*} [Field K]
    [Fintype ι] [DecidableEq ι] [Fintype J] [DecidableEq J]
    (V : J → Finset ι) (hDisjoint : ∀ i j, i ≠ j → Disjoint (V i) (V j))
    (ell : ℕ) (t : J → CondLinearTerm K (ι := ι) ell)
    (ht : ∀ j, CondLinearTerm.supportedOn (t j) (V j)) :
    CondLinearTerm.supportedOn (CondLinearTerm.directSum V ell t)
      (Finset.univ.biUnion V) := by
  induction ell generalizing V with
  | zero => trivial
  | succ ell ih =>
      have hhead (j : J) : (t j).headSupport ⊆ V j :=
        CondLinearTerm.supportedOn_headSupport (ht j)
      refine ⟨?_, ?_⟩
      · exact Finset.biUnion_subset.mpr fun j _ =>
          (hhead j).trans (Finset.subset_biUnion_of_mem V (Finset.mem_univ j))
      · intro y
        have htail (j : J) :
            CondLinearTerm.supportedOn
              ((t j).tail (coordinateRestriction (V j) y))
              (V j \ (t j).headSupport) :=
          CondLinearTerm.supportedOn_tail (ht j) _
        have hDisjointTail : ∀ i j, i ≠ j →
            Disjoint (V i \ (t i).headSupport) (V j \ (t j).headSupport) := by
          intro i j hij
          exact (hDisjoint i j hij).mono Finset.sdiff_subset Finset.sdiff_subset
        have hrec := ih _ hDisjointTail _ htail
        have hunion :
            Finset.univ.biUnion (fun j => V j \ (t j).headSupport) =
              Finset.univ.biUnion V \
                Finset.univ.biUnion (fun j => (t j).headSupport) := by
          ext a
          constructor
          · intro ha
            obtain ⟨j, _, hj⟩ := Finset.mem_biUnion.mp ha
            obtain ⟨haV, haS⟩ := Finset.mem_sdiff.mp hj
            refine Finset.mem_sdiff.mpr
              ⟨Finset.mem_biUnion.mpr ⟨j, Finset.mem_univ _, haV⟩, ?_⟩
            intro haHeads
            obtain ⟨i, _, hai⟩ := Finset.mem_biUnion.mp haHeads
            by_cases hij : i = j
            · subst i
              exact haS hai
            · exact Finset.disjoint_left.mp (hDisjoint i j hij) (hhead i hai) haV
          · intro ha
            obtain ⟨j, _, haV⟩ := Finset.mem_biUnion.mp (Finset.mem_sdiff.mp ha).1
            refine Finset.mem_biUnion.mpr
              ⟨j, Finset.mem_univ _, Finset.mem_sdiff.mpr ⟨haV, ?_⟩⟩
            intro haj
            exact (Finset.mem_sdiff.mp ha).2
              (Finset.mem_biUnion.mpr ⟨j, Finset.mem_univ _, haj⟩)
        simpa only [hunion] using hrec

private theorem CondLinearTerm.eval_directSum {K ι J : Type*} [Field K]
    [Fintype ι] [DecidableEq ι] [Fintype J] [DecidableEq J]
    (V : J → Finset ι) (hDisjoint : ∀ i j, i ≠ j → Disjoint (V i) (V j))
    (ell : ℕ) (t : J → CondLinearTerm K (ι := ι) ell)
    (ht : ∀ j, CondLinearTerm.supportedOn (t j) (V j)) (x : ι → K) :
    CondLinearTerm.eval (CondLinearTerm.directSum V ell t) x =
      ∑ j, CondLinearTerm.eval (t j) (coordinateRestriction (V j) x) := by
  induction ell generalizing V x with
  | zero =>
      apply Eq.symm
      apply Finset.sum_eq_zero
      intro j _
      cases t j
      rfl
  | succ ell ih =>
      let S : J → Finset ι := fun j => (t j).headSupport
      let y : J → ι → K := fun j =>
        (t j).headLinear (coordinateRestriction (S j) x)
      have hS (j : J) : S j ⊆ V j :=
        CondLinearTerm.supportedOn_headSupport (ht j)
      have hy (j : J) (a : ι) (ha : a ∉ V j) : y j a = 0 := by
        exact CondLinearTerm.headLinear_eq_zero_of_not_mem (t j) _
          (fun haS => ha (hS j haS))
      have hhead :
          condLinearHeadSum t
              (coordinateRestriction (Finset.univ.biUnion S) x) = ∑ j, y j := by
        apply Finset.sum_congr rfl
        intro j _
        change (t j).headLinear
            (coordinateRestriction (S j)
              (coordinateRestriction (Finset.univ.biUnion S) x)) =
          (t j).headLinear (coordinateRestriction (S j) x)
        rw [coordinateRestriction_coordinateRestriction
          (Finset.subset_biUnion_of_mem S (Finset.mem_univ j))]
      have hselect (j : J) : coordinateRestriction (V j) (∑ i, y i) = y j :=
        coordinateRestriction_sum_eq V hDisjoint y hy j
      have htail (j : J) :
          CondLinearTerm.supportedOn ((t j).tail (y j)) (V j \ S j) := by
        exact CondLinearTerm.supportedOn_tail (ht j) (y j)
      have hDisjointTail : ∀ i j, i ≠ j →
          Disjoint (V i \ S i) (V j \ S j) := by
        intro i j hij
        exact (hDisjoint i j hij).mono Finset.sdiff_subset Finset.sdiff_subset
      have htail_eval (j : J) :
          CondLinearTerm.eval ((t j).tail (y j))
              (coordinateRestriction (V j \ S j) x) =
            CondLinearTerm.eval ((t j).tail (y j))
              (coordinateRestriction (V j) x) := by
        have hrestrict := CondLinearTerm.eval_coordinateRestriction
          (htail j) (coordinateRestriction (V j) x)
        rwa [coordinateRestriction_coordinateRestriction Finset.sdiff_subset] at hrestrict
      have hcomponent (j : J) :
          CondLinearTerm.eval (t j) (coordinateRestriction (V j) x) =
            y j + CondLinearTerm.eval ((t j).tail (y j))
              (coordinateRestriction (V j \ S j) x) := by
        rw [CondLinearTerm.eval_succ_eq]
        change (t j).headLinear
              (coordinateRestriction (S j) (coordinateRestriction (V j) x)) +
            CondLinearTerm.eval
              ((t j).tail
                ((t j).headLinear
                  (coordinateRestriction (S j) (coordinateRestriction (V j) x))))
              (coordinateRestriction (V j) x) = _
        rw [coordinateRestriction_coordinateRestriction (hS j)]
        change y j + CondLinearTerm.eval ((t j).tail (y j))
            (coordinateRestriction (V j) x) = _
        rw [htail_eval]
      have hrec := ih (fun j => V j \ S j) hDisjointTail
        (fun j => (t j).tail (y j)) htail x
      have htail_family :
          (fun j => (t j).tail (coordinateRestriction (V j) (∑ i, y i))) =
            (fun j => (t j).tail (y j)) := by
        funext j
        rw [hselect]
      calc
        CondLinearTerm.eval (CondLinearTerm.directSum V (ell + 1) t) x =
            (∑ j, y j) +
              CondLinearTerm.eval
                (CondLinearTerm.directSum (fun j => V j \ S j) ell
                  (fun j => (t j).tail (y j))) x := by
              change condLinearHeadSum t
                    (coordinateRestriction
                      (Finset.univ.biUnion fun j => (t j).headSupport) x) +
                  CondLinearTerm.eval
                    (CondLinearTerm.directSum
                      (fun j => V j \ (t j).headSupport) ell
                      (fun j => (t j).tail
                        (coordinateRestriction (V j)
                          (condLinearHeadSum t
                            (coordinateRestriction
                              (Finset.univ.biUnion fun i => (t i).headSupport) x))))) x = _
              rw [show (fun j => (t j).headSupport) = S from rfl, hhead]
              rw [htail_family]
        _ = (∑ j, y j) + ∑ j, CondLinearTerm.eval ((t j).tail (y j))
              (coordinateRestriction (V j \ S j) x) := by rw [hrec]
        _ = ∑ j, (y j + CondLinearTerm.eval ((t j).tail (y j))
              (coordinateRestriction (V j \ S j) x)) := Finset.sum_add_distrib.symm
        _ = ∑ j, CondLinearTerm.eval (t j) (coordinateRestriction (V j) x) := by
              apply Finset.sum_congr rfl
              intro j _
              exact (hcomponent j).symm

/-- Equal-level direct sums of maps on disjoint registers are conditionally
linear on the union of those registers.  This is a formalization-only
auxiliary for `lem:cl-func-prod`, blueprint
`lem:cl-func-prod-same-level`. -/
theorem IsCondLinearOn.directSum_sameLevel {K ι J : Type*} [Field K]
    [Fintype ι] [DecidableEq ι] [Fintype J]
    (V : J → Finset ι) (ell : ℕ) (L : J → (ι → K) → (ι → K))
    (hDisjoint : ∀ i j, i ≠ j → Disjoint (V i) (V j))
    (hL : ∀ j, IsCondLinearOn K (V j) ell (L j)) :
    IsCondLinearOn K (Finset.univ.biUnion V) ell
      (fun x => ∑ j, L j (coordinateRestriction (V j) x)) := by
  classical
  choose t ht ht_eval using hL
  refine ⟨CondLinearTerm.directSum V ell t,
    CondLinearTerm.directSum_supportedOn V hDisjoint ell t ht, ?_⟩
  funext x
  rw [CondLinearTerm.eval_directSum V hDisjoint ell t ht x]
  apply Finset.sum_congr rfl
  intro j _
  exact congrFun (ht_eval j) (coordinateRestriction (V j) x)

end MIPStarRE.QPBT
