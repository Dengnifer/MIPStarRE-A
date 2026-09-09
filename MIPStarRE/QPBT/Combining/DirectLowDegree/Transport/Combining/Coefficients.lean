import MIPStarRE.QPBT.Combining.DirectLowDegree.Transport.Combining.Restriction

/-!
# The coefficients of a polynomial in the combining variables

The recovery step of the combining reduction reads a polynomial `p` in the
`m + k` combined variables as a polynomial in the `k` combining variables whose
coefficients `c_μ` are polynomials in the `m` point variables, and characterises
the two properties it needs in terms of those coefficients: `p` is the combined
polynomial of a tuple exactly when `c_μ` vanishes for every exponent vector `μ`
outside the `k` standard basis vectors, and the restriction `p(u, ·)` is a
linear form exactly when `c_μ(u)` vanishes for every such `μ`.  The
individual degrees of the coefficients are bounded by those of `p`, so each
`c_μ` has total degree at most `m d` and the Schwartz--Zippel lemma applies to
it.

The rereading is the algebra homomorphism sending the point variables to
constants and keeping the combining variables; it is injective, its left
inverse being the substitution which renames the point variables back and sends
the combining variables to the combining coordinates.

## Main definitions

* `combinedPointExp`, `combinedCoefExp` — the two blocks of an exponent vector
  of the combined dimension.
* `combinedCoefAlgHom` — the rereading of a polynomial in the combined
  variables as a polynomial in the combining variables with polynomial
  coefficients.
* `combinedCoef` — the coefficient of the combining monomial `μ`.

## Main statements

* `combinedCoefAlgHom_monomial` — the rereading of a monomial.
* `combinedCoefAlgHom_injective` — the rereading is injective.
* `eval_combinedCoef` — the value at `u` of `c_μ` is the coefficient of `μ` in
  the restriction `p(u, ·)`.
* `combinePolyTuple_combinedCoef_iff` — `p` is combined exactly when `c_μ`
  vanishes off the standard basis vectors.
* `degreeOf_combinedCoef_le`, `totalDegree_combinedCoef_le` — the degree bounds.

## References

* `references/neexp-paper/05_quantum_preliminaries.tex:1440-1470`
* `references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:413-458`
* `blueprint/src/chapter/ch13_qpbt_test.tex:575-600`
-/

open scoped BigOperators

namespace MIPStarRE.QPBT

open MIPStarRE.LDT.Preliminaries

noncomputable section

/-! ## The two blocks of an exponent vector -/

/-- The point block of an exponent vector of the combined dimension. -/
def combinedPointExp {m k : ℕ} (s : Fin (m + k) →₀ ℕ) : Fin m →₀ ℕ :=
  Finsupp.comapDomain (combinedPointVar m k) s (combinedPointVar_injective m k).injOn

/-- The combining block of an exponent vector of the combined dimension. -/
def combinedCoefExp {m k : ℕ} (s : Fin (m + k) →₀ ℕ) : Fin k →₀ ℕ :=
  Finsupp.comapDomain (combinedCoefficientVar m k) s
    (combinedCoefficientVar_injective m k).injOn

@[simp] theorem combinedPointExp_apply {m k : ℕ} (s : Fin (m + k) →₀ ℕ) (j : Fin m) :
    combinedPointExp s j = s (combinedPointVar m k j) := rfl

@[simp] theorem combinedCoefExp_apply {m k : ℕ} (s : Fin (m + k) →₀ ℕ) (r : Fin k) :
    combinedCoefExp s r = s (combinedCoefficientVar m k r) := rfl

/-- A product over the combined dimension splits into the product over the point
coordinates and the product over the combining coordinates. -/
private theorem prod_combinedVar_split {M : Type*} [CommMonoid M] {m k : ℕ}
    (f : Fin (m + k) → M) :
    ∏ i : Fin (m + k), f i =
      (∏ j : Fin m, f (combinedPointVar m k j)) *
        ∏ r : Fin k, f (combinedCoefficientVar m k r) := by
  rw [← Fintype.prod_equiv finSumFinEquiv (fun x => f (finSumFinEquiv x)) f fun _ => rfl,
    Fintype.prod_sum_type]
  rfl

/-! ## Rereading a polynomial in the combining variables -/

/-- The substitution reading the point variables as constants of the polynomial
ring in the point variables and keeping the combining variables. -/
def combinedCoefSubstitution (K : Type*) [CommSemiring K] (m k : ℕ) :
    Fin (m + k) → MvPolynomial (Fin k) (MvPolynomial (Fin m) K) :=
  fun i => Sum.elim
    (fun j : Fin m => MvPolynomial.C (MvPolynomial.X j))
    (fun r : Fin k => MvPolynomial.X r) (finSumFinEquiv.symm i)

@[simp] theorem combinedCoefSubstitution_point (K : Type*) [CommSemiring K] (m k : ℕ)
    (j : Fin m) :
    combinedCoefSubstitution K m k (combinedPointVar m k j) =
      MvPolynomial.C (MvPolynomial.X j) := by
  simp [combinedCoefSubstitution, combinedPointVar]

@[simp] theorem combinedCoefSubstitution_coefficient (K : Type*) [CommSemiring K] (m k : ℕ)
    (r : Fin k) :
    combinedCoefSubstitution K m k (combinedCoefficientVar m k r) =
      (MvPolynomial.X r : MvPolynomial (Fin k) (MvPolynomial (Fin m) K)) := by
  simp [combinedCoefSubstitution, combinedCoefficientVar]

/-- The rereading of a polynomial in the `m + k` combined variables as a
polynomial in the `k` combining variables with coefficients in the polynomial
ring in the `m` point variables. -/
def combinedCoefAlgHom (K : Type*) [CommSemiring K] (m k : ℕ) :
    MvPolynomial (Fin (m + k)) K →ₐ[K]
      MvPolynomial (Fin k) (MvPolynomial (Fin m) K) :=
  MvPolynomial.aeval (combinedCoefSubstitution K m k)

@[simp] theorem combinedCoefAlgHom_X (K : Type*) [CommSemiring K] (m k : ℕ)
    (i : Fin (m + k)) :
    combinedCoefAlgHom K m k (MvPolynomial.X i) = combinedCoefSubstitution K m k i :=
  MvPolynomial.aeval_X _ _

theorem combinedCoefAlgHom_C (K : Type*) [CommSemiring K] (m k : ℕ) (a : K) :
    combinedCoefAlgHom K m k (MvPolynomial.C a) =
      MvPolynomial.C (MvPolynomial.C a) := by
  rw [combinedCoefAlgHom, MvPolynomial.aeval_C]
  simp [MvPolynomial.algebraMap_eq]

/-- The rereading of a monomial: its exponent vector splits into the combining
block, which becomes the exponent of the outer monomial, and the point block,
which becomes the exponent of the inner monomial. -/
theorem combinedCoefAlgHom_monomial {K : Type*} [CommSemiring K] {m k : ℕ}
    (s : Fin (m + k) →₀ ℕ) (a : K) :
    combinedCoefAlgHom K m k (MvPolynomial.monomial s a) =
      MvPolynomial.monomial (combinedCoefExp s)
        (MvPolynomial.monomial (combinedPointExp s) a) := by
  classical
  set A := MvPolynomial (Fin k) (MvPolynomial (Fin m) K)
  have hL : combinedCoefAlgHom K m k (MvPolynomial.monomial s a) =
      MvPolynomial.C (MvPolynomial.C a) *
        ((∏ j : Fin m, (MvPolynomial.C (MvPolynomial.X j) : A) ^ s (combinedPointVar m k j)) *
          ∏ r : Fin k, (MvPolynomial.X r : A) ^ s (combinedCoefficientVar m k r)) := by
    rw [MvPolynomial.monomial_eq,
      Finsupp.prod_fintype _ _ fun _ => pow_zero _, map_mul, map_prod,
      combinedCoefAlgHom_C]
    simp only [map_pow, combinedCoefAlgHom_X]
    rw [prod_combinedVar_split (fun i => (combinedCoefSubstitution K m k i) ^ s i)]
    simp
  have hR : MvPolynomial.monomial (combinedCoefExp s)
        (MvPolynomial.monomial (combinedPointExp s) a) =
      MvPolynomial.C (MvPolynomial.C a) *
        ((∏ j : Fin m, (MvPolynomial.C (MvPolynomial.X j) : A) ^ s (combinedPointVar m k j)) *
          ∏ r : Fin k, (MvPolynomial.X r : A) ^ s (combinedCoefficientVar m k r)) := by
    rw [MvPolynomial.monomial_eq (s := combinedCoefExp s),
      Finsupp.prod_fintype _ _ fun _ => pow_zero _,
      MvPolynomial.monomial_eq (s := combinedPointExp s),
      Finsupp.prod_fintype _ _ fun _ => pow_zero _, map_mul, map_prod]
    simp only [map_pow, combinedPointExp_apply, combinedCoefExp_apply]
    ring
  rw [hL, hR]

/-! ## Injectivity of the rereading -/

/-- The substitution inverting the rereading: rename the point variables back to
the point coordinates and send the combining variables to the combining
coordinates. -/
def combinedCoefInv (K : Type*) [CommSemiring K] (m k : ℕ) :
    MvPolynomial (Fin k) (MvPolynomial (Fin m) K) →+* MvPolynomial (Fin (m + k)) K :=
  MvPolynomial.eval₂Hom ((MvPolynomial.rename (combinedPointVar m k)).toRingHom)
    (fun r : Fin k => MvPolynomial.X (combinedCoefficientVar m k r))

theorem combinedCoefInv_combinedCoefAlgHom {K : Type*} [CommSemiring K] {m k : ℕ}
    (p : MvPolynomial (Fin (m + k)) K) :
    combinedCoefInv K m k (combinedCoefAlgHom K m k p) = p := by
  have h : (combinedCoefInv K m k).comp
      ((combinedCoefAlgHom K m k : MvPolynomial (Fin (m + k)) K →ₐ[K] _) :
        MvPolynomial (Fin (m + k)) K →+* _) = RingHom.id _ := by
    apply MvPolynomial.ringHom_ext
    · intro a
      simp [combinedCoefInv]
    · intro i
      rcases combinedVar_cases i with ⟨j, rfl⟩ | ⟨r, rfl⟩ <;>
        simp [combinedCoefInv]
  exact RingHom.congr_fun h p

/-- The rereading is injective: a polynomial in the combined variables is
determined by its coefficients in the combining variables. -/
theorem combinedCoefAlgHom_injective {K : Type*} [CommSemiring K] {m k : ℕ} :
    Function.Injective (combinedCoefAlgHom K m k) :=
  Function.LeftInverse.injective combinedCoefInv_combinedCoefAlgHom

/-! ## The coefficients -/

/-- The coefficient of the combining monomial `μ` in `p`: a polynomial in the
point variables. -/
def combinedCoef {K : Type*} [CommSemiring K] {m k : ℕ}
    (p : MvPolynomial (Fin (m + k)) K) (μ : Fin k →₀ ℕ) : MvPolynomial (Fin m) K :=
  MvPolynomial.coeff μ (combinedCoefAlgHom K m k p)

/-- The value at `u` of the coefficient of `μ` is the coefficient of `μ` in the
restriction of `p` at `u`. -/
theorem eval_combinedCoef {K : Type*} [CommSemiring K] {m k : ℕ}
    (p : MvPolynomial (Fin (m + k)) K) (u : Fin m → K) (μ : Fin k →₀ ℕ) :
    MvPolynomial.eval u (combinedCoef p μ) =
      MvPolynomial.coeff μ (combinedRestrict p u) := by
  have h : (MvPolynomial.mapAlgHom (MvPolynomial.aeval u)).comp (combinedCoefAlgHom K m k) =
      MvPolynomial.aeval (combinedRestrictSubstitution k u) := by
    apply MvPolynomial.algHom_ext
    intro i
    rcases combinedVar_cases i with ⟨j, rfl⟩ | ⟨r, rfl⟩ <;> simp
  have hp := AlgHom.congr_fun h p
  simp only [AlgHom.coe_comp, Function.comp_apply, MvPolynomial.mapAlgHom_apply] at hp
  rw [combinedRestrict, ← hp, combinedCoef, MvPolynomial.coeff_map]
  rfl

/-! ## Combined polynomials in terms of the coefficients -/

/-- A polynomial in the combining variables supported on the standard basis
vectors is the sum of its monomials at those vectors. -/
theorem eq_sum_monomial_single {B : Type*} [CommSemiring B] {k : ℕ}
    (q : MvPolynomial (Fin k) B)
    (h : ∀ μ : Fin k →₀ ℕ, (∀ r : Fin k, μ ≠ Finsupp.single r 1) →
      MvPolynomial.coeff μ q = 0) :
    q = ∑ r : Fin k, MvPolynomial.monomial (Finsupp.single r 1)
      (MvPolynomial.coeff (Finsupp.single r 1) q) := by
  classical
  have hsub : q.support ⊆ Finset.image (fun r : Fin k => Finsupp.single r 1) Finset.univ := by
    intro μ hμ
    by_contra hcon
    refine MvPolynomial.mem_support_iff.mp hμ (h μ fun r hr => hcon ?_)
    exact Finset.mem_image.mpr ⟨r, Finset.mem_univ r, hr.symm⟩
  conv_lhs => rw [q.as_sum]
  rw [Finset.sum_subset hsub, Finset.sum_image]
  · intro r _ r' _ hrr'
    exact Finsupp.single_left_injective one_ne_zero hrr'
  · intro μ _ hμ
    rw [MvPolynomial.notMem_support_iff.mp hμ, map_zero]

/-- The rereading of a combined polynomial: its coefficients are the components
of the tuple, at the standard basis vectors. -/
theorem combinedCoefAlgHom_combinePolyTuple {K : Type*} [CommSemiring K] {m k : ℕ}
    (g : Fin k → MvPolynomial (Fin m) K) :
    combinedCoefAlgHom K m k (combinePolyTuple g) =
      ∑ r : Fin k, MvPolynomial.monomial (Finsupp.single r 1) (g r) := by
  classical
  have hrename : ∀ h : MvPolynomial (Fin m) K,
      combinedCoefAlgHom K m k (MvPolynomial.rename (combinedPointVar m k) h) =
        MvPolynomial.C h := by
    intro h
    induction h using MvPolynomial.induction_on with
    | C a => simp
    | add p q hp hq => simp [hp, hq]
    | mul_X p j hp => simp [hp]
  rw [combinePolyTuple, map_sum]
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [map_mul, combinedCoefAlgHom_X, combinedCoefSubstitution_coefficient, hrename,
    mul_comm, MvPolynomial.C_mul_X_eq_monomial]

theorem combinedCoef_combinePolyTuple {K : Type*} [CommSemiring K] {m k : ℕ}
    (g : Fin k → MvPolynomial (Fin m) K) (r : Fin k) :
    combinedCoef (combinePolyTuple g) (Finsupp.single r 1) = g r := by
  classical
  rw [combinedCoef, combinedCoefAlgHom_combinePolyTuple, MvPolynomial.coeff_sum,
    Finset.sum_eq_single r]
  · simp
  · intro s _ hs
    rw [MvPolynomial.coeff_monomial, if_neg]
    exact fun hEq => hs (Finsupp.single_left_injective one_ne_zero hEq)
  · intro h
    exact absurd (Finset.mem_univ r) h

theorem combinedCoef_combinePolyTuple_eq_zero {K : Type*} [CommSemiring K] {m k : ℕ}
    (g : Fin k → MvPolynomial (Fin m) K) {μ : Fin k →₀ ℕ}
    (hμ : ∀ r : Fin k, μ ≠ Finsupp.single r 1) :
    combinedCoef (combinePolyTuple g) μ = 0 := by
  classical
  rw [combinedCoef, combinedCoefAlgHom_combinePolyTuple, MvPolynomial.coeff_sum]
  refine Finset.sum_eq_zero fun r _ => ?_
  rw [MvPolynomial.coeff_monomial, if_neg]
  exact fun hEq => hμ r hEq.symm

/-- A polynomial in the combined variables is combined exactly when its
coefficients vanish outside the `k` standard basis vectors.  This is the
first half of the characterisation used in `lem:ld-combining-exact-linearity`. -/
theorem combinePolyTuple_combinedCoef_iff {K : Type*} [CommSemiring K] {m k : ℕ}
    (p : MvPolynomial (Fin (m + k)) K) :
    (∃ g : Fin k → MvPolynomial (Fin m) K, p = combinePolyTuple g) ↔
      ∀ μ : Fin k →₀ ℕ, (∀ r : Fin k, μ ≠ Finsupp.single r 1) → combinedCoef p μ = 0 := by
  classical
  constructor
  · rintro ⟨g, rfl⟩ μ hμ
    exact combinedCoef_combinePolyTuple_eq_zero g hμ
  · intro h
    refine ⟨fun r => combinedCoef p (Finsupp.single r 1), combinedCoefAlgHom_injective ?_⟩
    rw [combinedCoefAlgHom_combinePolyTuple]
    exact eq_sum_monomial_single (combinedCoefAlgHom K m k p) h

/-! ## The degree bound on the coefficients -/

/-- The coefficient of `μ` as a sum over the support of `p`. -/
theorem combinedCoef_eq_sum {K : Type*} [CommSemiring K] {m k : ℕ}
    (p : MvPolynomial (Fin (m + k)) K) (μ : Fin k →₀ ℕ) :
    combinedCoef p μ = ∑ s ∈ p.support,
      (if combinedCoefExp s = μ then
        MvPolynomial.monomial (combinedPointExp s) (MvPolynomial.coeff s p) else 0) := by
  classical
  rw [combinedCoef]
  conv_lhs => rw [p.as_sum]
  rw [map_sum, MvPolynomial.coeff_sum]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [combinedCoefAlgHom_monomial, MvPolynomial.coeff_monomial]

/-- The coefficients inherit the individual-degree bound of `p`: the individual
degree of `c_μ` in the point variable `j` is at most the individual degree of
`p` in the corresponding point coordinate. -/
theorem degreeOf_combinedCoef_le {K : Type*} [CommSemiring K] {m k d : ℕ}
    {p : MvPolynomial (Fin (m + k)) K} (hp : ∀ i, p.degreeOf i ≤ d)
    (μ : Fin k →₀ ℕ) (j : Fin m) : (combinedCoef p μ).degreeOf j ≤ d := by
  classical
  rw [MvPolynomial.degreeOf_le_iff]
  intro ν hν
  rw [combinedCoef_eq_sum] at hν
  obtain ⟨s, hs, hνs⟩ := Finset.mem_biUnion.mp (MvPolynomial.support_sum hν)
  by_cases hc : combinedCoefExp s = μ
  · rw [if_pos hc] at hνs
    have hνeq : ν = combinedPointExp s := by
      have := MvPolynomial.support_monomial_subset hνs
      simpa using this
    subst hνeq
    exact MvPolynomial.degreeOf_le_iff.mp (hp (combinedPointVar m k j)) s hs
  · rw [if_neg hc] at hνs
    simp at hνs

/-- The coefficients of a polynomial of individual degree at most `d` lie in the
low individual degree class in the point variables. -/
theorem combinedCoef_mem_polyFunc {K : Type*} [CommSemiring K] {m k d : ℕ}
    {p : MvPolynomial (Fin (m + k)) K} (hp : p ∈ polyFunc (m + k) K d) (μ : Fin k →₀ ℕ) :
    combinedCoef p μ ∈ polyFunc m K d :=
  mem_polyFunc_of_degreeOf_le
    (degreeOf_combinedCoef_le (degreeOf_le_of_mem_polyFunc hp) μ)

/-- The components of a combined polynomial of individual degree at most `d`
have individual degree at most `d`: they are among its coefficients. -/
theorem mem_polyFunc_of_combinePolyTuple {K : Type*} [CommSemiring K] {m k d : ℕ}
    {p : MvPolynomial (Fin (m + k)) K} (hp : p ∈ polyFunc (m + k) K d)
    {g : Fin k → MvPolynomial (Fin m) K} (hg : p = combinePolyTuple g) (r : Fin k) :
    g r ∈ polyFunc m K d := by
  have h := combinedCoef_mem_polyFunc hp (Finsupp.single r 1)
  rwa [hg, combinedCoef_combinePolyTuple] at h

/-- The coefficients of a polynomial of individual degree at most `d` have total
degree at most `m d`, which is the bound the Schwartz--Zippel lemma is applied
to in `lem:ld-combining-exact-linearity`. -/
theorem totalDegree_combinedCoef_le {K : Type*} [CommSemiring K] {m k d : ℕ}
    {p : MvPolynomial (Fin (m + k)) K} (hp : p ∈ polyFunc (m + k) K d) (μ : Fin k →₀ ℕ) :
    (combinedCoef p μ).totalDegree ≤ m * d :=
  totalDegree_le_mul_of_degreeOf_le
    (degreeOf_combinedCoef_le (degreeOf_le_of_mem_polyFunc hp) μ)

end

end MIPStarRE.QPBT
