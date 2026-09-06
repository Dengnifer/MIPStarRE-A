import MIPStarRE.LDT.Preliminaries.Polynomials

/-!
# The combining map on tuples of low individual degree polynomials

The extension of the quantum soundness of the low individual degree test from
simultaneity parameter `1` to a general simultaneity parameter `k` is obtained
in the source by a reduction, not coordinatewise: the `k` answer polynomials
`g_0, …, g_{k-1}` in `m` variables are combined into the single polynomial

`comb(g)(u, α) = ∑_{r < k} α_r g_r(u)`

in `m + k` variables, the case `k = 1` is applied once in dimension `m + k`,
and the `k` polynomials are recovered from the resulting outcome by exact
linearity in the combining variables `α` together with the Schwartz--Zippel
lemma.  This module develops the polynomial algebra of that combining map: the
coordinate split of `Fin (m + k)`, the map itself, its evaluation identity, its
individual-degree bound, and the substitution recovering the `r`-th component,
which exhibits the map as injective.

The combining map of `def:combine-map` (`MIPStarRE/QPBT/Combining/Defs.lean`)
is the special case of two components used by the Chapter 15 combining
argument, written there in the fixed coordinate layout of that chapter; the
present map is the general `k`-component form required by the reduction, in the
coordinate layout of the directly indexed low-degree game, where the `m` point
coordinates precede the `k` combining coordinates.

## Main definitions

* `combinedPointVar`, `combinedCoefficientVar` — the two coordinate blocks of
  the combined dimension `m + k`.
* `combinePolyTuple` — the combining map on tuples of polynomials.
* `splitCombinedPoly` — the substitution `α ↦ e_r` recovering the `r`-th
  component of a combined polynomial.

## References

* `references/neexp-paper/05_quantum_preliminaries.tex:1409-1503`
  (the derivation of Theorem 4.43 from Theorem 4.40)
* `references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:413-458`
* `blueprint/src/chapter/ch13_qpbt_test.tex:240-250`
* `docs/paper-gaps/qpbt_ld-simultaneous-sandwich.tex`
-/

open scoped BigOperators

namespace MIPStarRE.QPBT

open MIPStarRE.LDT.Preliminaries

noncomputable section

/-! ## The coordinates of the combined dimension -/

/-- The point coordinates of the combined dimension `m + k`.  The `m` point
coordinates come first, so that zeroing a prefix of a direction of the combined
space restricts to zeroing the corresponding prefix of its point part. -/
def combinedPointVar (m k : ℕ) (j : Fin m) : Fin (m + k) :=
  finSumFinEquiv (Sum.inl j)

/-- The combining coordinates of the combined dimension `m + k`.  Coordinate
`combinedCoefficientVar m k r` carries the scalar `α_r` multiplying the `r`-th
component of a polynomial tuple. -/
def combinedCoefficientVar (m k : ℕ) (r : Fin k) : Fin (m + k) :=
  finSumFinEquiv (Sum.inr r)

theorem combinedPointVar_injective (m k : ℕ) :
    Function.Injective (combinedPointVar m k) := by
  intro j j' h
  simpa using finSumFinEquiv.injective h

theorem combinedCoefficientVar_injective (m k : ℕ) :
    Function.Injective (combinedCoefficientVar m k) := by
  intro r r' h
  simpa using finSumFinEquiv.injective h

/-- The two coordinate blocks of the combined dimension are disjoint. -/
theorem combinedCoefficientVar_ne_combinedPointVar (m k : ℕ) (r : Fin k) (j : Fin m) :
    combinedCoefficientVar m k r ≠ combinedPointVar m k j := by
  intro h
  have := finSumFinEquiv.injective h
  simp at this

theorem combinedCoefficientVar_notMem_range (m k : ℕ) (r : Fin k) :
    combinedCoefficientVar m k r ∉ Set.range (combinedPointVar m k) := by
  rintro ⟨j, hj⟩
  exact combinedCoefficientVar_ne_combinedPointVar m k r j hj.symm

/-- The point part of a point of the combined space. -/
def combinedPointPart {K : Type*} {m k : ℕ} (z : Fin (m + k) → K) : Fin m → K :=
  fun j => z (combinedPointVar m k j)

/-- The combining part of a point of the combined space. -/
def combinedCoefficientPart {K : Type*} {m k : ℕ} (z : Fin (m + k) → K) : Fin k → K :=
  fun r => z (combinedCoefficientVar m k r)

/-- The point of the combined space with the given point and combining parts. -/
def combinedPoint {K : Type*} {m k : ℕ} (u : Fin m → K) (α : Fin k → K) :
    Fin (m + k) → K :=
  fun i => Sum.elim u α (finSumFinEquiv.symm i)

@[simp] theorem combinedPointPart_combinedPoint {K : Type*} {m k : ℕ}
    (u : Fin m → K) (α : Fin k → K) :
    combinedPointPart (combinedPoint u α) = u := by
  funext j
  simp [combinedPointPart, combinedPoint, combinedPointVar]

@[simp] theorem combinedCoefficientPart_combinedPoint {K : Type*} {m k : ℕ}
    (u : Fin m → K) (α : Fin k → K) :
    combinedCoefficientPart (combinedPoint u α) = α := by
  funext r
  simp [combinedCoefficientPart, combinedPoint, combinedCoefficientVar]

/-! ## The combining map -/

/-- The combining map of the reduction: the tuple `g` is sent to the polynomial
`(u, α) ↦ ∑_{r < k} α_r g_r(u)` in `m + k` variables.

Source `references/neexp-paper/05_quantum_preliminaries.tex:1425-1435`. -/
def combinePolyTuple {K : Type*} [CommSemiring K] {m k : ℕ}
    (g : Fin k → MvPolynomial (Fin m) K) : MvPolynomial (Fin (m + k)) K :=
  ∑ r : Fin k, MvPolynomial.X (combinedCoefficientVar m k r) *
    MvPolynomial.rename (combinedPointVar m k) (g r)

/-- Evaluation of a combined polynomial is the displayed combining formula. -/
theorem combinePolyTuple_eval {K : Type*} [CommSemiring K] {m k : ℕ}
    (g : Fin k → MvPolynomial (Fin m) K) (z : Fin (m + k) → K) :
    MvPolynomial.eval z (combinePolyTuple g) =
      ∑ r : Fin k, combinedCoefficientPart z r *
        MvPolynomial.eval (combinedPointPart z) (g r) := by
  simp only [combinePolyTuple, map_sum, map_mul, MvPolynomial.eval_X,
    MvPolynomial.eval_rename, combinedCoefficientPart]
  rfl

/-- Evaluation of a combined polynomial at a point given by its two blocks. -/
theorem combinePolyTuple_eval_combinedPoint {K : Type*} [CommSemiring K] {m k : ℕ}
    (g : Fin k → MvPolynomial (Fin m) K) (u : Fin m → K) (α : Fin k → K) :
    MvPolynomial.eval (combinedPoint u α) (combinePolyTuple g) =
      ∑ r : Fin k, α r * MvPolynomial.eval u (g r) := by
  rw [combinePolyTuple_eval, combinedPointPart_combinedPoint,
    combinedCoefficientPart_combinedPoint]

/-! ## Recovering the components -/

/-- The substitution sending each point coordinate to its own variable and the
combining coordinates to the `r`-th standard basis vector.  Applied to a
combined polynomial it returns the `r`-th component of the tuple. -/
def combinedSubstitution (K : Type*) [CommSemiring K] (m k : ℕ) (r : Fin k) :
    Fin (m + k) → MvPolynomial (Fin m) K :=
  fun i => Sum.elim (fun j : Fin m => MvPolynomial.X j)
    (fun s : Fin k => if s = r then 1 else 0) (finSumFinEquiv.symm i)

@[simp] theorem combinedSubstitution_point (K : Type*) [CommSemiring K] (m k : ℕ)
    (r : Fin k) (j : Fin m) :
    combinedSubstitution K m k r (combinedPointVar m k j) = MvPolynomial.X j := by
  simp [combinedSubstitution, combinedPointVar]

@[simp] theorem combinedSubstitution_coefficient (K : Type*) [CommSemiring K] (m k : ℕ)
    (r s : Fin k) :
    combinedSubstitution K m k r (combinedCoefficientVar m k s) =
      if s = r then 1 else 0 := by
  simp [combinedSubstitution, combinedCoefficientVar]

/-- The `r`-th component of a polynomial in the combined variables: substitute
the `r`-th standard basis vector for the combining variables. -/
def splitCombinedPoly {K : Type*} [CommSemiring K] {m k : ℕ}
    (p : MvPolynomial (Fin (m + k)) K) (r : Fin k) : MvPolynomial (Fin m) K :=
  MvPolynomial.aeval (combinedSubstitution K m k r) p

/-- The components of a combined polynomial are the polynomials it combines. -/
theorem splitCombinedPoly_combinePolyTuple {K : Type*} [CommSemiring K] {m k : ℕ}
    (g : Fin k → MvPolynomial (Fin m) K) (r : Fin k) :
    splitCombinedPoly (combinePolyTuple g) r = g r := by
  classical
  have hcomp : (combinedSubstitution K m k r) ∘ (combinedPointVar m k) =
      (MvPolynomial.X : Fin m → MvPolynomial (Fin m) K) := by
    funext j
    exact combinedSubstitution_point K m k r j
  have hterm : ∀ s : Fin k,
      MvPolynomial.aeval (combinedSubstitution K m k r)
          (MvPolynomial.X (combinedCoefficientVar m k s) *
            MvPolynomial.rename (combinedPointVar m k) (g s)) =
        (if s = r then 1 else 0) * g s := by
    intro s
    rw [map_mul, MvPolynomial.aeval_X, combinedSubstitution_coefficient,
      MvPolynomial.aeval_rename, hcomp, MvPolynomial.aeval_X_left_apply]
  rw [splitCombinedPoly, combinePolyTuple, map_sum]
  simp only [hterm, ite_mul, one_mul, zero_mul]
  simp

/-- The combining map is injective: the components of a combined polynomial are
determined by it. -/
theorem combinePolyTuple_injective {K : Type*} [CommSemiring K] {m k : ℕ} :
    Function.Injective (combinePolyTuple (K := K) (m := m) (k := k)) := by
  intro g g' h
  funext r
  rw [← splitCombinedPoly_combinePolyTuple g r, h,
    splitCombinedPoly_combinePolyTuple]

/-! ## The individual-degree bound -/

/-- Membership in the low individual degree class from a bound on every
individual degree.  This is the converse direction of
`degreeOf_le_of_mem_polyFunc`. -/
theorem mem_polyFunc_of_degreeOf_le {m d : ℕ} {K : Type*} [CommSemiring K]
    {p : MvPolynomial (Fin m) K} (h : ∀ i, p.degreeOf i ≤ d) :
    p ∈ polyFunc m K d := by
  rw [MvPolynomial.mem_restrictDegree]
  exact fun s hs i => MvPolynomial.degreeOf_le_iff.mp (h i) s hs

private theorem degreeOf_X_le_one {τ K : Type*} [CommSemiring K] (c i : τ) :
    (MvPolynomial.X c : MvPolynomial τ K).degreeOf i ≤ 1 := by
  rw [MvPolynomial.degreeOf_le_iff]
  intro s hs
  have hs' : s ∈ ({Finsupp.single c 1} : Finset (τ →₀ ℕ)) :=
    MvPolynomial.support_monomial_subset hs
  rw [Finset.mem_singleton] at hs'
  subst hs'
  by_cases h : c = i
  · simp [h]
  · simp [h]

private theorem degreeOf_rename_le {σ τ K : Type*} [CommSemiring K]
    {f : σ → τ} (hf : Function.Injective f) {p : MvPolynomial σ K} {d : ℕ}
    (hp : ∀ j : σ, p.degreeOf j ≤ d) (i : τ) :
    (MvPolynomial.rename f p).degreeOf i ≤ d := by
  classical
  rw [MvPolynomial.degreeOf_le_iff]
  intro s hs
  rw [MvPolynomial.support_rename_of_injective hf] at hs
  obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hs
  by_cases hi : ∃ j, f j = i
  · obtain ⟨j, rfl⟩ := hi
    rw [Finsupp.mapDomain_apply hf]
    exact le_trans (MvPolynomial.le_degreeOf_of_mem_support j ht) (hp j)
  · rw [Finsupp.mapDomain_notin_range t i (by simpa using hi)]
    exact Nat.zero_le d

private theorem degreeOf_rename_eq_zero_of_notMem_range {σ τ K : Type*} [CommSemiring K]
    {f : σ → τ} (hf : Function.Injective f) (p : MvPolynomial σ K)
    {i : τ} (hi : i ∉ Set.range f) :
    (MvPolynomial.rename f p).degreeOf i = 0 := by
  classical
  rw [← Nat.le_zero, MvPolynomial.degreeOf_le_iff]
  intro s hs
  rw [MvPolynomial.support_rename_of_injective hf] at hs
  obtain ⟨t, _, rfl⟩ := Finset.mem_image.mp hs
  exact le_of_eq (Finsupp.mapDomain_notin_range t i hi)

/-- The combining map preserves the individual-degree bound.  The two coordinate
blocks are disjoint: a component polynomial depends only on the point
coordinates, so multiplying it by a combining variable leaves its individual
degrees in the point block unchanged and produces individual degree one in the
fresh combining coordinate.  The hypothesis `1 ≤ d` supplies exactly the bound
needed on that fresh coordinate; no bound `d + 1` is introduced.  This is the
individual-degree counterpart of the degree-`d + 1` bound used for total degree
in `references/neexp-paper/05_quantum_preliminaries.tex:1435-1440`. -/
theorem combinePolyTuple_mem_polyFunc {K : Type*} [CommSemiring K] {m k d : ℕ}
    (hd : 1 ≤ d) (g : Fin k → MvPolynomial (Fin m) K)
    (hg : ∀ r, g r ∈ polyFunc m K d) :
    combinePolyTuple g ∈ polyFunc (m + k) K d := by
  classical
  refine Submodule.sum_mem _ fun r _ => mem_polyFunc_of_degreeOf_le fun i => ?_
  refine le_trans (MvPolynomial.degreeOf_mul_le i _ _) ?_
  by_cases hi : i ∈ Set.range (combinedPointVar m k)
  · have hne : i ≠ combinedCoefficientVar m k r := by
      rintro rfl
      exact combinedCoefficientVar_notMem_range m k r hi
    rw [MvPolynomial.degreeOf_X_of_ne hne, zero_add]
    exact degreeOf_rename_le (combinedPointVar_injective m k)
      (fun j => degreeOf_le_of_mem_polyFunc (hg r) j) i
  · rw [degreeOf_rename_eq_zero_of_notMem_range (combinedPointVar_injective m k) _ hi,
      add_zero]
    exact le_trans (degreeOf_X_le_one _ _) hd

end

end MIPStarRE.QPBT
