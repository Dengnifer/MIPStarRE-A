import MIPStarRE.QPBT.Games.CondLinear

/-! # Structure and direct sums of conditionally linear functions

This module records the prefix decomposition of a conditionally linear map and
the behavior of such maps and their shared-seed distributions under finite
coordinate direct sums.

## References

The source results are `lem:cl-kth`, `lem:cl-func-prod`, and
`lem:cl-dist-prod` in `blueprint/src/chapter/ch12_qpbt_games.tex:520-585`, with
paper origin
`references/qpbt-paper/05_conditionally_linear_functions.tex:150-379`.
-/

open scoped BigOperators

namespace MIPStarRE.QPBT

open MIPStarRE.LDT

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

/-- A map is `ell`-level conditionally linear exactly when it admits the
prefix decomposition of `lem:cl-kth`; blueprint `ch12_qpbt_games.tex:520-540`,
paper `references/qpbt-paper/05_conditionally_linear_functions.tex:150-262`. -/
theorem isCondLinear_iff_nonempty_clData {K ι : Type*} [Field K]
    [Fintype ι] [DecidableEq ι] {ell : ℕ} (hEll : 1 ≤ ell)
    (L : (ι → K) → (ι → K)) :
    IsCondLinear ell L ↔ Nonempty (CLData K ι ell L) := by
  sorry

/-- Coordinate direct sum of maps supported on a finite register partition.
This is a formalization-only auxiliary for `lem:cl-func-prod`, blueprint
`ch12_qpbt_games.tex:565-574`, paper
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
`lem:cl-func-prod`; blueprint `ch12_qpbt_games.tex:565-574`, paper
`references/qpbt-paper/05_conditionally_linear_functions.tex:315-364`. -/
theorem IsCondLinear.directSum {K ι : Type*} [Field K]
    [Fintype ι] [DecidableEq ι] {m : ℕ} (hm : 1 ≤ m)
    (V : Fin m → Finset ι) (ell : Fin m → ℕ)
    (L : Fin m → (ι → K) → (ι → K))
    (hDisjoint : ∀ i j, i ≠ j → Disjoint (V i) (V j))
    (hCover : ∀ a, ∃ i, a ∈ V i)
    (hL : ∀ j, IsCondLinearOn K (V j) (ell j) (L j)) :
    IsCondLinear (directSumLevel ell) (condLinearDirectSum V L) := by
  sorry

/-- The CL distribution of coordinate direct sums factors into the component
CL distributions. The equality is stated pointwise on weights, which is the
finite-distribution meaning of the product in `lem:cl-dist-prod`; blueprint
`ch12_qpbt_games.tex:580-585`, paper
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
  sorry

end MIPStarRE.QPBT
