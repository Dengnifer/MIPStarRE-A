import MIPStarRE.QPBT.Combining.Defs
import MIPStarRE.QPBT.Combining.DirectLowDegree.Transport.Combining.Coefficients

/-!
# The separated image of the polynomial combining map

The two coefficients of a polynomial homogeneous linear in `alpha, beta` are
polynomials in the `2 * m` point coordinates. Separation means that the first
coefficient uses only the `x` block and the second only the `z` block. This
condition is expressed by coefficient vanishing and containment of variable
sets, without assuming a pair of component polynomials.

Specializing the combining variables to a standard basis vector and the other
point block to zero recovers the components. Reconstruction and the inherited
individual-degree bounds identify the separated image with actual pairs of
bounded-degree polynomials. These are formalization-only algebraic auxiliary
results, not the quantitative assertion about the mass of the separated image.

## References

* `references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:970-983`
  (the combining map), and `eq:qld-g-non-separable`, `eq:qld-sgg-completeness`
  (the separated image and its reindexing).
* Blueprint `def:combine-map` and the proof of `lem:qld-4-7`.
* Issue #284.
-/

open scoped BigOperators

namespace MIPStarRE.QPBT

open MIPStarRE.LDT.Preliminaries

noncomputable section

/-- Coordinate inclusion of the `x` block (`r = 0`) or the `z` block (`r = 1`)
into the point coordinates of a combined polynomial. -/
def combinedBlockVar (m : ℕ) (r : Fin 2) (j : Fin m) : Fin (2 * m) :=
  (finCongr (by omega) : Fin (m + m) ≃ Fin (2 * m))
    (finSumFinEquiv (if r = 0 then Sum.inl j else Sum.inr j))

/-- Each point block is embedded without identifying variables. -/
theorem combinedBlockVar_injective (m : ℕ) (r : Fin 2) :
    Function.Injective (combinedBlockVar m r) := by
  intro i j h
  have h' := (finCongr (show m + m = 2 * m by omega)).injective h
  have h'' := finSumFinEquiv.injective h'
  by_cases hr : r = 0 <;> simpa [hr] using h''

private theorem combinedPointVar_block_zero (m : ℕ) :
    combinedPointVar (2 * m) 2 ∘ combinedBlockVar m 0 = embX m := by
  funext j
  apply Fin.ext
  simp [combinedPointVar, combinedBlockVar, embX, finCombineEquiv]

private theorem combinedPointVar_block_one (m : ℕ) :
    combinedPointVar (2 * m) 2 ∘ combinedBlockVar m 1 = embZ m := by
  funext j
  apply Fin.ext
  simp [combinedPointVar, combinedBlockVar, embZ, finCombineEquiv]

private theorem combinedCoefficientVar_zero (m : ℕ) :
    combinedCoefficientVar (2 * m) 2 0 = alphaVar m := by
  apply Fin.ext
  simp [combinedCoefficientVar, alphaVar, finCombineEquiv]

private theorem combinedCoefficientVar_one (m : ℕ) :
    combinedCoefficientVar (2 * m) 2 1 = betaVar m := by
  apply Fin.ext
  simp [combinedCoefficientVar, betaVar, finCombineEquiv]

/-- The disjoint-block combining map is the existing tuple combining map
applied to the two coefficients after embedding their respective blocks. -/
theorem combinePoly_eq_combinePolyTuple {K : Type*} [CommSemiring K] {m : ℕ}
    (f g : MvPolynomial (Fin m) K) :
    combinePoly f g = combinePolyTuple (fun r : Fin 2 =>
      MvPolynomial.rename (combinedBlockVar m r) (if r = 0 then f else g)) := by
  simp [combinePoly, combinePolyTuple, Fin.sum_univ_two, MvPolynomial.rename_rename,
    combinedPointVar_block_zero, combinedPointVar_block_one,
    combinedCoefficientVar_zero, combinedCoefficientVar_one]

/-- A polynomial is separated when it is homogeneous linear in `alpha, beta`
and the coefficient of each of these variables uses only its corresponding
point block. This is the algebraic locus `G` in the source proof before
`eq:qld-g-non-separable`, expressed independently of image membership. -/
def IsSeparatedCombined {K : Type*} [CommSemiring K] {m : ℕ}
    (p : MvPolynomial (Fin (2 * m + 2)) K) : Prop :=
  (∀ μ : Fin 2 →₀ ℕ, (∀ r : Fin 2, μ ≠ Finsupp.single r 1) →
    combinedCoef p μ = 0) ∧
  ∀ r : Fin 2, (↑(combinedCoef p (Finsupp.single r 1)).vars : Set (Fin (2 * m))) ⊆
    Set.range (combinedBlockVar m r)

/-- Recover the `x` component (`r = 0`) or the `z` component (`r = 1`) by
specializing `(alpha, beta)` to the `r`-th standard basis vector, then setting
the other point block to zero. Both operations are polynomial algebra
homomorphisms; no inverse or image-membership witness is chosen. -/
def recoverCombinedPoly {K : Type*} [CommSemiring K] {m : ℕ}
    (p : MvPolynomial (Fin (2 * m + 2)) K) (r : Fin 2) : MvPolynomial (Fin m) K :=
  MvPolynomial.killCompl (combinedBlockVar_injective m r) (splitCombinedPoly p r)

/-- Specialization recovers either component of an actual combined polynomial. -/
@[simp] theorem recoverCombinedPoly_combinePoly {K : Type*} [CommSemiring K] {m : ℕ}
    (f g : MvPolynomial (Fin m) K) (r : Fin 2) :
    recoverCombinedPoly (combinePoly f g) r = if r = 0 then f else g := by
  rw [recoverCombinedPoly, combinePoly_eq_combinePolyTuple,
    splitCombinedPoly_combinePolyTuple, MvPolynomial.killCompl_rename_app]

/-- Combining polynomials is injective as a map on actual pairs, independently
of degree bounds or assumptions about the coefficient field. -/
theorem combinePoly_injective {K : Type*} [CommSemiring K] {m : ℕ} :
    Function.Injective (fun fg : MvPolynomial (Fin m) K × MvPolynomial (Fin m) K =>
      combinePoly fg.1 fg.2) := by
  intro fg fg' h
  apply Prod.ext
  · simpa using congrArg (fun p => recoverCombinedPoly p 0) h
  · simpa using congrArg (fun p => recoverCombinedPoly p 1) h

/-- Every combined polynomial satisfies the coefficient and variable support
conditions defining separation. -/
theorem isSeparatedCombined_combinePoly {K : Type*} [CommSemiring K] {m : ℕ}
    (f g : MvPolynomial (Fin m) K) : IsSeparatedCombined (combinePoly f g) := by
  rw [combinePoly_eq_combinePolyTuple]
  refine ⟨fun μ hμ => combinedCoef_combinePolyTuple_eq_zero _ hμ, ?_⟩
  intro r j hj
  rw [combinedCoef_combinePolyTuple] at hj
  obtain ⟨i, _, hi⟩ := MvPolynomial.mem_vars_rename _ _ hj
  exact ⟨i, hi⟩

/-- For a separated polynomial, the embedded recovered component is exactly
its coefficient at the corresponding combining variable. -/
theorem rename_recoverCombinedPoly {K : Type*} [CommSemiring K] {m : ℕ}
    {p : MvPolynomial (Fin (2 * m + 2)) K} (hp : IsSeparatedCombined p) (r : Fin 2) :
    MvPolynomial.rename (combinedBlockVar m r) (recoverCombinedPoly p r) =
      combinedCoef p (Finsupp.single r 1) := by
  obtain ⟨g, hg⟩ := (combinePolyTuple_combinedCoef_iff p).mpr hp.1
  have hsplit : splitCombinedPoly p r = combinedCoef p (Finsupp.single r 1) := by
    rw [hg, splitCombinedPoly_combinePolyTuple, combinedCoef_combinePolyTuple]
  obtain ⟨f, hf⟩ := MvPolynomial.exists_rename_eq_of_vars_subset_range
    (combinedCoef p (Finsupp.single r 1)) (combinedBlockVar m r)
    (combinedBlockVar_injective m r) (hp.2 r)
  rw [recoverCombinedPoly, hsplit, ← hf, MvPolynomial.killCompl_rename_app]

/-- Specializing and recombining a separated polynomial returns that polynomial.
The proof derives reconstruction from the coefficient support condition. -/
theorem combinePoly_recoverCombinedPoly {K : Type*} [CommSemiring K] {m : ℕ}
    {p : MvPolynomial (Fin (2 * m + 2)) K} (hp : IsSeparatedCombined p) :
    combinePoly (recoverCombinedPoly p 0) (recoverCombinedPoly p 1) = p := by
  obtain ⟨g, hg⟩ := (combinePolyTuple_combinedCoef_iff p).mpr hp.1
  rw [combinePoly_eq_combinePolyTuple]
  have hcomponent : ∀ r : Fin 2,
      MvPolynomial.rename (combinedBlockVar m r)
        (if r = 0 then recoverCombinedPoly p 0 else recoverCombinedPoly p 1) = g r := by
    intro r
    have hr := (rename_recoverCombinedPoly hp r).trans
      ((congrArg (fun q => combinedCoef q (Finsupp.single r 1)) hg).trans
        (combinedCoef_combinePolyTuple g r))
    rcases (show r = 0 ∨ r = 1 by omega) with rfl | rfl <;>
      simpa using hr
  rw [show (fun r : Fin 2 => MvPolynomial.rename (combinedBlockVar m r)
    (if r = 0 then recoverCombinedPoly p 0 else recoverCombinedPoly p 1)) = g from
      funext hcomponent]
  exact hg.symm

/-- The independently defined separation condition characterizes the image
of the actual disjoint-block combining map. -/
theorem isSeparatedCombined_iff_exists_combinePoly {K : Type*} [CommSemiring K] {m : ℕ}
    (p : MvPolynomial (Fin (2 * m + 2)) K) :
    IsSeparatedCombined p ↔ ∃ f g : MvPolynomial (Fin m) K, combinePoly f g = p := by
  constructor
  · intro hp
    exact ⟨_, _, combinePoly_recoverCombinedPoly hp⟩
  · rintro ⟨f, g, rfl⟩
    exact isSeparatedCombined_combinePoly f g

private theorem rename_mem_polyFunc_iff {K : Type*} [CommSemiring K] {m n d : ℕ}
    {e : Fin m → Fin n} (he : Function.Injective e) (p : MvPolynomial (Fin m) K) :
    MvPolynomial.rename e p ∈ polyFunc n K d ↔ p ∈ polyFunc m K d := by
  constructor
  · intro hp
    refine mem_polyFunc_of_degreeOf_le fun j => ?_
    rw [← MvPolynomial.degreeOf_rename_of_injective he j]
    exact degreeOf_le_of_mem_polyFunc hp (e j)
  · intro hp
    refine mem_polyFunc_of_degreeOf_le fun i => ?_
    by_cases hi : i ∈ Set.range e
    · obtain ⟨j, rfl⟩ := hi
      rw [MvPolynomial.degreeOf_rename_of_injective he]
      exact degreeOf_le_of_mem_polyFunc hp j
    · have hz : (MvPolynomial.rename e p).degreeOf i = 0 := by
        by_contra hne
        obtain ⟨j, _, hj⟩ := MvPolynomial.mem_vars_rename e p
          (MvPolynomial.mem_vars_iff_degreeOf_ne_zero.mpr hne)
        exact hi ⟨j, hj⟩
      rw [hz]
      exact Nat.zero_le d

/-- Recovered components inherit the individual-degree bound of the separated
polynomial. This uses the proved degree bound for its actual coefficients,
not a forward degree assertion about the combining map. No positivity
assumption on `d` is needed for this direction. -/
theorem recoverCombinedPoly_mem_polyFunc {K : Type*} [CommSemiring K] {m d : ℕ}
    {p : MvPolynomial (Fin (2 * m + 2)) K} (hp : p ∈ polyFunc (2 * m + 2) K d)
    (hs : IsSeparatedCombined p) (r : Fin 2) :
    recoverCombinedPoly p r ∈ polyFunc m K d := by
  apply (rename_mem_polyFunc_iff (combinedBlockVar_injective m r) _).mp
  rw [rename_recoverCombinedPoly hs]
  exact combinedCoef_mem_polyFunc hp (Finsupp.single r 1)

/-- For `1 ≤ d`, a combined polynomial has individual degree at most `d`
exactly when both components do. The forward construction uses the proved
tuple-combining degree theorem. The boundary condition bounds the two fresh
linear coordinates, as in the source definition at lines 977--983. -/
theorem combinePoly_mem_polyFunc_iff {K : Type*} [CommSemiring K] {m d : ℕ}
    (hd : 1 ≤ d) (f g : MvPolynomial (Fin m) K) :
    combinePoly f g ∈ polyFunc (2 * m + 2) K d ↔
      f ∈ polyFunc m K d ∧ g ∈ polyFunc m K d := by
  constructor
  · intro hp
    have hs := isSeparatedCombined_combinePoly f g
    exact ⟨by simpa using recoverCombinedPoly_mem_polyFunc hp hs 0,
      by simpa using recoverCombinedPoly_mem_polyFunc hp hs 1⟩
  · rintro ⟨hf, hg⟩
    rw [combinePoly_eq_combinePolyTuple]
    apply combinePolyTuple_mem_polyFunc hd
    intro r
    apply (rename_mem_polyFunc_iff (combinedBlockVar_injective m r) _).mpr
    split_ifs <;> assumption

/-- Every bounded separated polynomial has a unique pair of bounded components.
The pair is given by the two specialization maps, including when `d = 0`. -/
theorem existsUnique_bounded_combinePoly {K : Type*} [CommSemiring K] {m d : ℕ}
    {p : MvPolynomial (Fin (2 * m + 2)) K} (hp : p ∈ polyFunc (2 * m + 2) K d)
    (hs : IsSeparatedCombined p) :
    ∃! fg : ↥(polyFunc m K d) × ↥(polyFunc m K d), combinePoly fg.1.1 fg.2.1 = p := by
  refine ⟨(⟨recoverCombinedPoly p 0, recoverCombinedPoly_mem_polyFunc hp hs 0⟩,
    ⟨recoverCombinedPoly p 1, recoverCombinedPoly_mem_polyFunc hp hs 1⟩),
    combinePoly_recoverCombinedPoly hs, ?_⟩
  intro fg hfg
  apply Prod.ext
  · apply Subtype.ext
    simpa using congrArg (fun q => recoverCombinedPoly q 0) hfg
  · apply Subtype.ext
    simpa using congrArg (fun q => recoverCombinedPoly q 1) hfg

/-- The bounded separated locus, defined by individual degree, coefficient
vanishing, and variable support rather than by the existence of a pair. -/
abbrev SeparatedCombinedPoly (m : ℕ) (K : Type*) [CommSemiring K] (d : ℕ) :=
  {p : MvPolynomial (Fin (2 * m + 2)) K //
    p ∈ polyFunc (2 * m + 2) K d ∧ IsSeparatedCombined p}

/-- Reindex the bounded separated image by actual pairs of bounded polynomials.
This is the algebraic change of indices used in `eq:qld-sgg-completeness`;
it asserts no measurement or quantitative completeness bound. -/
def combinedPolynomialImageEquiv (m : ℕ) (K : Type*) [CommSemiring K] (d : ℕ)
    (hd : 1 ≤ d) :
    (↥(polyFunc m K d) × ↥(polyFunc m K d)) ≃ SeparatedCombinedPoly m K d where
  toFun fg := ⟨combinePoly fg.1.1 fg.2.1,
    (combinePoly_mem_polyFunc_iff hd _ _).mpr ⟨fg.1.2, fg.2.2⟩,
    isSeparatedCombined_combinePoly _ _⟩
  invFun p := (⟨recoverCombinedPoly p.1 0, recoverCombinedPoly_mem_polyFunc p.2.1 p.2.2 0⟩,
    ⟨recoverCombinedPoly p.1 1, recoverCombinedPoly_mem_polyFunc p.2.1 p.2.2 1⟩)
  left_inv fg := by
    apply Prod.ext
    · apply Subtype.ext
      simp
    · apply Subtype.ext
      simp
  right_inv p := Subtype.ext (combinePoly_recoverCombinedPoly p.2.2)

end

end MIPStarRE.QPBT
