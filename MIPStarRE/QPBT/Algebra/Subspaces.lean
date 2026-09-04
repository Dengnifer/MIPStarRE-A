import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# Subspaces for the Pauli basis test

This module supplies the register subspaces, dot-product orthogonals, and the
canonical coordinate complement used by the conditionally linear maps.  The
canonical complement is presented through the intrinsic pivot-rank test; the
equivalence with a particular row-reduced-echelon implementation is a later
construction theorem.

## References

The statement-level definitions are `def:register-subspace`,
`def:dot-product-orthogonal`, `def:canonical-complement`, and
`def:cl-canonical` in `blueprint/src/chapter/ch11_qpbt_algebra.tex`;
the paper origin is `references/qpbt-paper/04_preliminaries.tex:231-384`.
-/

open scoped BigOperators

namespace MIPStarRE.QPBT

variable {K ι : Type*} [Field K] [Fintype ι] [DecidableEq ι]

/--
`registerSubmodule K S` is the span of the standard coordinate vectors indexed
by `S`.  It is the Lean encoding of `def:register-subspace` from
`blueprint/src/chapter/ch11_qpbt_algebra.tex:24-29`, whose paper origin is
`references/qpbt-paper/04_preliminaries.tex:231-239`.
-/
def registerSubmodule (K : Type*) [Field K] (S : Finset ι) : Submodule K (ι → K) :=
  Submodule.span K {v | ∃ i, i ∈ S ∧ v = Pi.single i 1}

/--
`dotOrthogonal W` consists of vectors whose coordinate dot product with every
member of `W` vanishes.  This is `def:dot-product-orthogonal` in
`blueprint/src/chapter/ch11_qpbt_algebra.tex:31-42`, with paper origin
`references/qpbt-paper/04_preliminaries.tex:241-255`.
-/
def dotOrthogonal (W : Submodule K (ι → K)) : Submodule K (ι → K) where
  carrier := {u | ∀ v, v ∈ W → dotProduct u v = 0}
  zero_mem' := by
    intro v hv
    simp [dotProduct]
  add_mem' := by
    intro u v hu hv w hw
    calc
      dotProduct (u + v) w =
          (dotProduct u w) + (dotProduct v w) := by
            change (∑ i, (u i + v i) * w i) =
              (∑ i, u i * w i) + (∑ i, v i * w i)
            simp_rw [add_mul]
            rw [Finset.sum_add_distrib]
      _ = 0 := by rw [hu w hw, hv w hw, add_zero]
  smul_mem' := by
    intro c u hu v hv
    calc
      dotProduct (c • u) v = c * dotProduct u v := by
        simp [dotProduct, smul_eq_mul, mul_assoc, Finset.mul_sum]
      _ = 0 := by rw [hu v hv, mul_zero]

/-- Restrict a coordinate vector to the first `k` coordinates.  Lean-only rank
infrastructure for `def:canonical-complement`, blueprint
`ch11_qpbt_algebra.tex:84-110`, paper `references/qpbt-paper/04_preliminaries.tex:231-384`.
-/
private def prefixMap (k n : ℕ) (hk : k ≤ n) :
    (Fin n → K) →ₗ[K] (Fin k → K) :=
  { toFun := fun x i => x ⟨i.1, lt_of_lt_of_le i.2 hk⟩
    map_add' := by
      intro x y
      rfl
    map_smul' := by
      intro c x
      rfl }

/-- The rank of a prefix restriction used by the pivot characterization. -/
private noncomputable def prefixRank {n : ℕ} (W : Submodule K (Fin n → K))
    (k : ℕ) (hk : k ≤ n) : ℕ :=
  Module.finrank K (W.map (prefixMap k n hk))

/--
The non-pivot coordinate set of `W`, defined by the rank-increase
characterization of pivots.  This is the basis-free encoding approved for
`def:canonical-complement` in `blueprint/src/chapter/ch11_qpbt_algebra.tex:84-110`;
the paper's Gaussian-elimination presentation is
`references/qpbt-paper/04_preliminaries.tex:303-320`.
-/
noncomputable def canonicalComplement {n : ℕ}
    (W : Submodule K (Fin n → K)) : Finset (Fin n) :=
  Finset.univ.filter fun j =>
    prefixRank W (j.1 + 1) (Nat.succ_le_of_lt j.2) =
      prefixRank W j.1 j.2.le

/-- The register submodule is the standard coordinate span on its index set. -/
private lemma registerSubmodule_eq_spanSubset (S : Finset ι) :
    registerSubmodule K S = Pi.spanSubset K (S : Set ι) := by
  classical
  rw [registerSubmodule, Pi.spanSubset]
  congr 1
  ext v
  simp [Pi.basisFun_apply, eq_comm]

/-- Prefix restriction rank is nondecreasing when one coordinate is added. -/
private lemma prefixRank_mono_succ {n : ℕ} (W : Submodule K (Fin n → K))
    (k : ℕ) (hk : k + 1 ≤ n) :
    prefixRank W k (Nat.le_trans (Nat.le_succ k) hk) ≤
      prefixRank W (k + 1) hk := by
  let drop := prefixMap (K := K) k (k + 1) (Nat.le_succ k)
  let large := prefixMap (K := K) (k + 1) n hk
  have hcomp : drop.comp large =
      prefixMap (K := K) k n (Nat.le_trans (Nat.le_succ k) hk) := by
    ext x i
    rfl
  rw [prefixRank, prefixRank, ← hcomp, Submodule.map_comp]
  exact Submodule.finrank_map_le drop (W.map large)

/-- If a coordinate does not increase prefix rank, it vanishes after all earlier coordinates do. -/
private lemma coordinate_eq_zero_of_prefixRank_eq {n : ℕ}
    (W : Submodule K (Fin n → K)) (j : Fin n)
    (hrank : prefixRank W (j.1 + 1) (Nat.succ_le_of_lt j.2) =
      prefixRank W j.1 j.2.le) {w : Fin n → K} (hw : w ∈ W)
    (hprevious : ∀ i : Fin n, i.1 < j.1 → w i = 0) :
    w j = 0 := by
  let small : W →ₗ[K] (Fin j.1 → K) :=
    (prefixMap (K := K) j.1 n j.2.le).domRestrict W
  let large : W →ₗ[K] (Fin (j.1 + 1) → K) :=
    (prefixMap (K := K) (j.1 + 1) n
      (Nat.succ_le_of_lt j.2)).domRestrict W
  have hker_le : LinearMap.ker large ≤ LinearMap.ker small := by
    intro x hx
    rw [LinearMap.mem_ker] at hx ⊢
    funext i
    have hi := congrFun hx (Fin.castSucc i)
    simpa [small, large, prefixMap] using hi
  have hrange : Module.finrank K (LinearMap.range large) =
      Module.finrank K (LinearMap.range small) := by
    dsimp [small, large]
    rw [LinearMap.range_domRestrict, LinearMap.range_domRestrict]
    exact hrank
  have hlarge := large.finrank_range_add_finrank_ker
  have hsmall := small.finrank_range_add_finrank_ker
  have hker_rank : Module.finrank K (LinearMap.ker large) =
      Module.finrank K (LinearMap.ker small) := by
    omega
  have hker_eq : LinearMap.ker large = LinearMap.ker small :=
    Submodule.eq_of_le_of_finrank_eq hker_le hker_rank
  let x : W := ⟨w, hw⟩
  have hxsmall : x ∈ LinearMap.ker small := by
    rw [LinearMap.mem_ker]
    funext i
    exact hprevious ⟨i.1, lt_of_lt_of_le i.2 j.2.le⟩ i.2
  have hxlarge : x ∈ LinearMap.ker large := by
    rw [hker_eq]
    exact hxsmall
  have hj := congrFun (LinearMap.mem_ker.mp hxlarge) (Fin.last j.1)
  simpa [x, large, prefixMap] using hj

/-- The number of strict steps in a nondecreasing natural-number sequence is at
most its endpoint. -/
private lemma card_strict_steps_le {n : ℕ} (r : ℕ → ℕ)
    (hmono : ∀ k, k < n → r k ≤ r (k + 1)) :
    ((Finset.range n).filter fun k => r (k + 1) ≠ r k).card ≤ r n := by
  classical
  induction n with
  | zero => simp
  | succ n ih =>
      have hih := ih fun k hk => hmono k (lt_trans hk (Nat.lt_succ_self n))
      have hn := hmono n (Nat.lt_succ_self n)
      by_cases h : r n = r (n + 1)
      · simpa [Finset.range_add_one, Finset.filter_insert, h] using hih.trans hn
      · have hstep : r n < r (n + 1) := lt_of_le_of_ne hn h
        have h' : r (n + 1) ≠ r n := Ne.symm h
        have := Nat.succ_le_of_lt (hih.trans_lt hstep)
        simpa [Finset.range_add_one, Finset.filter_insert, h'] using this

/--
The canonical coordinate complement spans a complement of `W`.  This is the
proposition `lem:canonical-complement` in
`blueprint/src/chapter/ch11_qpbt_algebra.tex:112-120`, with paper origin
`references/qpbt-paper/04_preliminaries.tex:342-373`.
The proof uses the intrinsic prefix-rank characterization; equivalence with a
particular reduced-row-echelon algorithm is outside this statement.
-/
theorem isCompl_registerSubmodule_canonicalComplement {n : ℕ}
    (W : Submodule K (Fin n → K)) :
    IsCompl W (registerSubmodule K (canonicalComplement W)) := by
  classical
  let C := canonicalComplement W
  let T := registerSubmodule K C
  change IsCompl W T
  have hT : T = Pi.spanSubset K (C : Set (Fin n)) :=
    registerSubmodule_eq_spanSubset C
  have hdisjoint : Disjoint W T := by
    refine Submodule.disjoint_def.mpr ?_
    intro w hwW hwT
    rw [hT] at hwT
    have hzero : ∀ k (hk : k < n), w ⟨k, hk⟩ = 0 := by
      intro k
      induction k using Nat.strong_induction_on with
      | h k ih =>
          intro hk
          let j : Fin n := ⟨k, hk⟩
          by_cases hj : j ∈ C
          · apply coordinate_eq_zero_of_prefixRank_eq W j
            · simpa [C, canonicalComplement] using hj
            · exact hwW
            · intro i hi
              simpa using ih i.1 hi i.2
          · exact Pi.mem_spanSubset_iff.mp hwT j hj
    funext j
    exact hzero j.1 j.2
  let P := Cᶜ
  let r : ℕ → ℕ := fun k =>
    if hk : k ≤ n then prefixRank W k hk else 0
  have hr_mono : ∀ k, k < n → r k ≤ r (k + 1) := by
    intro k hk
    simp only [r, dif_pos (Nat.le_of_lt hk), dif_pos (Nat.succ_le_of_lt hk)]
    exact prefixRank_mono_succ W k (Nat.succ_le_of_lt hk)
  have hP_filter : P = Finset.univ.filter fun j =>
      prefixRank W (j.1 + 1) (Nat.succ_le_of_lt j.2) ≠
        prefixRank W j.1 j.2.le := by
    ext j
    simp [P, C, canonicalComplement]
  have hP_card : P.card =
      ((Finset.range n).filter fun k => r (k + 1) ≠ r k).card := by
    rw [← Finset.card_map Fin.valEmbedding]
    congr 1
    ext k
    simp only [Finset.mem_map, Finset.mem_filter, Finset.mem_range]
    constructor
    · rintro ⟨j, hj, rfl⟩
      rw [hP_filter] at hj
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj
      refine ⟨j.2, ?_⟩
      simpa [r, Nat.le_of_lt j.2, Nat.succ_le_of_lt j.2] using hj
    · rintro ⟨hk, hstrict⟩
      let j : Fin n := ⟨k, hk⟩
      refine ⟨j, ?_, rfl⟩
      rw [hP_filter]
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      simpa [j, r, Nat.le_of_lt hk, Nat.succ_le_of_lt hk] using hstrict
  have hP_le : P.card ≤ Module.finrank K W := by
    calc
      P.card ≤ r n := by
        rw [hP_card]
        exact card_strict_steps_le r hr_mono
      _ ≤ Module.finrank K W := by
        simp only [r, dif_pos le_rfl]
        exact Submodule.finrank_map_le (prefixMap (K := K) n n le_rfl) W
  have hfinrankT : Module.finrank K T = C.card := by
    rw [hT, Pi.dim_spanSubset]
    simp
  have hpartition : C.card + P.card = n := by
    simpa only [P, Fintype.card_fin] using Finset.card_add_card_compl C
  have hdim : Module.finrank K (Fin n → K) ≤
      Module.finrank K W + Module.finrank K T := by
    rw [hfinrankT]
    simp only [Module.finrank_fin_fun]
    omega
  exact (Submodule.isCompl_iff_disjoint W T hdim).mpr hdisjoint

/--
The projector onto the canonical coordinate complement along `W`.  This is
`def:cl-canonical` in `blueprint/src/chapter/ch11_qpbt_algebra.tex:133-145`,
originating at `references/qpbt-paper/04_preliminaries.tex:375-384`.
-/
noncomputable def canonicalProjOfKernel {n : ℕ}
    (W : Submodule K (Fin n → K)) : (Fin n → K) →ₗ[K] (Fin n → K) := by
  let T := registerSubmodule K (canonicalComplement W)
  let p : (Fin n → K) →ₗ[K] T :=
    Submodule.projectionOnto T W
      (isCompl_registerSubmodule_canonicalComplement W).symm
  exact T.subtype.comp p

end MIPStarRE.QPBT
