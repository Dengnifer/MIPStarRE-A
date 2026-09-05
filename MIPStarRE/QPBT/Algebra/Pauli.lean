import MIPStarRE.QPBT.Algebra.FieldBasis
import MIPStarRE.Quantum.FiniteMatrix.Basic
import MIPStarRE.LDT.Preliminaries.FiniteFields

/-!
# Generalized Pauli operators and EPR states

The definitions here use finite matrix entries and rank-one projectors, so they
are usable by the later game statements without introducing an abstract
operator algebra.  The observable/projector expansions are obtained from
finite-field Fourier orthogonality in characteristic two.

## References

The source-facing nodes are blueprint `def:lin-reg`, `def:EPR`,
`def:generalized-pauli`, and `lem:pauli-observable-expansion`.  The paper origin is
`references/qpbt-paper/04_preliminaries.tex:908-1161`.
-/

open scoped BigOperators Matrix ComplexOrder

namespace MIPStarRE.QPBT

open MIPStarRE.Quantum
open MIPStarRE.LDT.Preliminaries

variable {K : Type*} [Field K] [Fintype K] [DecidableEq K]
  [Algebra (ZMod 2) K]

/-- The two generalized Pauli bases used by the test in blueprint
`def:generalized-pauli`, paper origin
`references/qpbt-paper/04_preliminaries.tex:1052-1096`.
-/
inductive PauliKind where
  | X
  | Z
  deriving DecidableEq, Repr, Inhabited, Fintype

/-- The binary character used for generalized Pauli phases; see
`references/qpbt-paper/04_preliminaries.tex:1052-1081`.

It is public because the Fourier expansion declarations below expose this
character in their statement types. -/
noncomputable def phaseSign (t : ZMod 2) : ℂ :=
  if t = 0 then 1 else -1

/-- Formalization-only expansion of a sum over the binary field into its two
terms. -/
theorem sum_zmod_two {M : Type*} [AddCommMonoid M] (f : ZMod 2 → M) :
    ∑ b, f b = f 0 + f 1 := by
  calc
    ∑ b, f b = ∑ i : Fin 2, f (ZMod.finEquiv 2 i) := by
      exact Fintype.sum_equiv (ZMod.finEquiv 2).symm f
        (fun i : Fin 2 => f (ZMod.finEquiv 2 i)) (fun _ => rfl)
    _ = f (ZMod.finEquiv 2 0) + f (ZMod.finEquiv 2 1) := Fin.sum_univ_two _
    _ = f 0 + f 1 := by rfl

/-- Formalization-only case split for the binary field: every element is zero
or one. -/
theorem zmod_two_eq_zero_or_one (b : ZMod 2) : b = 0 ∨ b = 1 := by
  by_cases hb : b = 0
  · exact Or.inl hb
  · right
    have hval_ne : b.val ≠ 0 := (ZMod.val_ne_zero b).mpr hb
    have hval_lt : b.val < 2 := ZMod.val_lt b
    have hval : b.val = 1 := by omega
    exact (ZMod.val_eq_one (by omega) b).mp hval

/-- In characteristic two, the standard additive character is the sign
character used by the binary Pauli definitions. -/
theorem phaseSign_eq_ffChar (t : ZMod 2) :
    phaseSign t = ZMod.stdAddChar (N := 2) t := by
  by_cases ht : t = 0
  · subst t
    rw [phaseSign, if_pos rfl]
    exact (ZMod.stdAddChar (N := 2)).map_zero_eq_one.symm
  · have hval : t.val = 1 := by
      have hval_ne : t.val ≠ 0 := (ZMod.val_ne_zero t).mpr ht
      have hval_lt : t.val < 2 := ZMod.val_lt t
      omega
    have ht_one : t = 1 := (ZMod.val_eq_one (by omega) t).mp hval
    subst t
    rw [phaseSign, if_neg one_ne_zero]
    change (-1 : ℂ) = ZMod.stdAddChar (N := 2) ((1 : ℤ) : ZMod 2)
    rw [ZMod.stdAddChar_coe]
    convert Complex.exp_pi_mul_I.symm using 1
    all_goals ring_nf

/-- The binary sign character carries a sum to the product of the two signs.
This is the character property underlying blueprint
`def:generalized-pauli`, paper origin
`references/qpbt-paper/04_preliminaries.tex:1052-1096`. -/
theorem phaseSign_add (s t : ZMod 2) :
    phaseSign (s + t) = phaseSign s * phaseSign t := by
  rw [phaseSign_eq_ffChar, phaseSign_eq_ffChar, phaseSign_eq_ffChar]
  exact (ZMod.stdAddChar (N := 2)).map_add_eq_mul s t

/-- The binary sign character takes real values, so conjugation fixes it. It is
used by the observable expansions of blueprint
`def:generalized-pauli`, paper origin
`references/qpbt-paper/04_preliminaries.tex:1052-1096`. -/
theorem star_phaseSign (t : ZMod 2) : star (phaseSign t) = phaseSign t := by
  by_cases ht : t = 0 <;> simp [phaseSign, ht]

/-- The binary sign character squares to one, since the binary field has
characteristic two. This is the eigenvalue property used by the observables of
blueprint `def:generalized-pauli`, paper origin
`references/qpbt-paper/04_preliminaries.tex:1052-1096`. -/
theorem phaseSign_mul_self (t : ZMod 2) : phaseSign t * phaseSign t = 1 := by
  rw [← phaseSign_add]
  have hzero : t + t = 0 := by
    rcases zmod_two_eq_zero_or_one t with ht | ht <;> subst ht <;> decide
  rw [hzero, phaseSign, if_pos rfl]

/-- The binary sign character sends sums to products. -/
theorem phaseSign_sum {ι : Type*} [Fintype ι] (f : ι → ZMod 2) :
    phaseSign (∑ i, f i) = ∏ i, phaseSign (f i) := by
  classical
  induction (Finset.univ : Finset ι) using Finset.induction_on with
  | empty => simp [phaseSign]
  | @insert i s hi ih =>
      rw [Finset.sum_insert hi, Finset.prod_insert hi, phaseSign_add, ih]

omit [Fintype K] [DecidableEq K] in
/-- The product of the coordinate phases is the phase of the trace pairing. -/
theorem prod_phaseSign_binTrace_dotProduct {ι : Type*} [Fintype ι]
    (u v : ι → K) :
    ∏ i, phaseSign (binTrace K (u i * v i)) =
      phaseSign (binTrace K (dotProduct u v)) := by
  rw [← phaseSign_sum]
  congr 2
  simp [dotProduct]

/-- The complex amplitude `(√n)⁻¹` normalizing a uniform superposition over `n`
basis vectors squares to `n⁻¹`.

This formalization-only normalization identity supports the Pauli normalizer
of blueprint `def:EPR`, paper origin
`references/qpbt-paper/04_preliminaries.tex:908-950`, and the seed-fiber and
correlated-ancilla amplitudes of the direct low-degree transport. -/
theorem inv_sqrt_natCast_mul_self (n : ℕ) :
    (Real.sqrt (n : ℝ) : ℂ)⁻¹ * (Real.sqrt (n : ℝ) : ℂ)⁻¹ =
      (n : ℂ)⁻¹ := by
  calc
    (Real.sqrt (n : ℝ) : ℂ)⁻¹ * (Real.sqrt (n : ℝ) : ℂ)⁻¹ =
        ((Real.sqrt (n : ℝ) : ℂ) ^ 2)⁻¹ := by
      rw [pow_two, mul_inv_rev]
    _ = ((n : ℝ) : ℂ)⁻¹ := by
      rw [← Complex.ofReal_pow, Real.sq_sqrt (Nat.cast_nonneg n)]
    _ = (n : ℂ)⁻¹ := by norm_num

/-- Conjugated form of `inv_sqrt_natCast_mul_self`: the normalizing amplitude
`(√n)⁻¹` is real, so pairing it with its conjugate again gives `n⁻¹`.  This
formalization-only auxiliary is the form in which the identity occurs in Born
amplitudes, where the bra side carries the conjugate. -/
theorem inv_sqrt_natCast_mul_conj (n : ℕ) :
    (Real.sqrt (n : ℝ) : ℂ)⁻¹ *
        (starRingEnd ℂ) (Real.sqrt (n : ℝ) : ℂ)⁻¹ =
      (n : ℂ)⁻¹ := by
  rw [show (starRingEnd ℂ) (Real.sqrt (n : ℝ) : ℂ)⁻¹ =
      (Real.sqrt (n : ℝ) : ℂ)⁻¹ by simp]
  exact inv_sqrt_natCast_mul_self n

omit [Field K] [DecidableEq K] [Algebra (ZMod 2) K] in
private theorem pauliNormalizer_mul_self {ι : Type*} [Fintype ι]
    [DecidableEq ι] :
    (∏ _i : ι, (Real.sqrt (Fintype.card K : ℝ) : ℂ)⁻¹) *
        (∏ _i : ι, (Real.sqrt (Fintype.card K : ℝ) : ℂ)⁻¹) =
      (Fintype.card (ι → K) : ℂ)⁻¹ := by
  simp only [Finset.prod_const, Finset.card_univ]
  rw [← mul_pow, inv_sqrt_natCast_mul_self, inv_pow, Fintype.card_fun]
  norm_cast

omit [Fintype K] [DecidableEq K] in
private theorem phaseSign_binTrace_dotProduct_add {ι : Type*} [Fintype ι]
    (u v w : ι → K) :
    phaseSign (binTrace K (dotProduct u v)) *
        phaseSign (binTrace K (dotProduct u w)) =
      phaseSign (binTrace K (dotProduct u (v + w))) := by
  rw [← phaseSign_add]
  congr 2
  simp [dotProduct, mul_add, Finset.sum_add_distrib]

omit [Fintype K] [DecidableEq K] in
private theorem add_add_eq_zero_iff_eq_add {ι : Type*} (a x y : ι → K) :
    a + (x + y) = 0 ↔ x = y + a := by
  letI : CharP K 2 :=
    (Algebra.charP_iff (ZMod 2) K 2).mp (ZMod.charP 2)
  constructor
  · intro h
    funext i
    have hi : a i + (x i + y i) = 0 := by
      simpa only [Pi.add_apply, Pi.zero_apply] using congrFun h i
    have hax : a i + x i = y i := (CharTwo.add_eq_zero).mp (by
      simpa only [add_assoc] using hi)
    calc
      x i = a i + (a i + x i) := (CharTwo.add_cancel_left (a i) (x i)).symm
      _ = a i + y i := by rw [hax]
      _ = y i + a i := add_comm _ _
  · intro h
    funext i
    have hxi : x i = y i + a i := by
      simpa only [Pi.add_apply] using congrFun h i
    simp only [Pi.add_apply, Pi.zero_apply, hxi]
    calc
      a i + (y i + a i + y i) = (a i + a i) + (y i + y i) := by abel
      _ = 0 := by rw [CharTwo.add_self_eq_zero, CharTwo.add_self_eq_zero, zero_add]

private theorem expect_phaseSign_dotProduct {ι : Type*} [Fintype ι]
    [DecidableEq ι] (v : ι → K) :
    𝔼 u : (ι → K), phaseSign (binTrace K (dotProduct u v)) =
      if v = 0 then (1 : ℂ) else 0 := by
  let eι : ι ≃ Fin (Fintype.card ι) := Fintype.equivFin ι
  let reindex : (ι → K) ≃ (Fin (Fintype.card ι) → K) :=
    { toFun := fun u j => u (eι.symm j)
      invFun := fun u i => u (eι i)
      left_inv := fun u => by
        funext i
        simp
      right_inv := fun u => by
        funext j
        simp }
  let v' : Fin (Fintype.card ι) → K := reindex v
  calc
    𝔼 u : (ι → K), phaseSign (binTrace K (dotProduct u v)) =
        𝔼 u : (Fin (Fintype.card ι) → K),
          phaseSign (binTrace K (dotProduct u v')) := by
      refine Finset.expect_equiv reindex (by simp) ?_
      intro u _
      congr 3
      simpa [reindex, v', Function.comp_def] using
        (comp_equiv_dotProduct_comp_equiv u v eι.symm).symm
    _ = 𝔼 u : (Fin (Fintype.card ι) → K),
        ffVecChar (p := 2) (F := K) v' u := by
      apply Finset.expect_congr rfl
      intro u _
      simp only [ffVecChar_apply, ffChar_apply]
      rw [phaseSign_eq_ffChar]
      rfl
    _ = if v' = 0 then (1 : ℂ) else 0 := fourier_fact_vector v'
    _ = if v = 0 then (1 : ℂ) else 0 := by
      have reindex_zero : reindex (0 : ι → K) = 0 := by
        ext j
        rfl
      by_cases hv : v = 0
      · subst v
        rw [show v' = 0 by exact reindex_zero]
        simp
      · have hv' : v' ≠ 0 := by
          intro hv'
          apply hv
          apply reindex.injective
          rw [reindex_zero]
          exact hv'
        simp [hv, hv']

private theorem sum_phaseSign_dotProduct {ι : Type*} [Fintype ι]
    [DecidableEq ι] (v : ι → K) :
    ∑ u : ι → K, phaseSign (binTrace K (dotProduct u v)) =
      if v = 0 then (Fintype.card (ι → K) : ℂ) else 0 := by
  rw [← Fintype.card_smul_expect, expect_phaseSign_dotProduct]
  by_cases hv : v = 0 <;> simp [hv]

/--
The shift operator `τ^X(a)`.  Blueprint `def:generalized-pauli`; paper origin
`references/qpbt-paper/04_preliminaries.tex:1052-1096`.
-/
noncomputable def tauShift (a : K) : Op K :=
  fun i j => if i = j + a then 1 else 0

/--
The phase operator `τ^Z(b)`, with the fixed binary trace in the phase.  It is
the second operator of blueprint `def:generalized-pauli`; paper
`references/qpbt-paper/04_preliminaries.tex:1052-1096`.
-/
noncomputable def tauPhase (b : K) : Op K :=
  fun i j => if i = j then phaseSign (binTrace K (b * j)) else 0

/-- The binary shift Pauli operator is Hermitian.  This is a
formalization-only specialization of the generalized Pauli definition. -/
theorem binaryTauShift_conjTranspose :
    (tauShift (K := ZMod 2) 1)ᴴ = tauShift (K := ZMod 2) 1 := by
  ext i j
  have hiff : j = i + 1 ↔ i = j + 1 := by
    rw [CharTwo.eq_add_iff_add_eq, eq_comm]
  simp [tauShift, Matrix.conjTranspose_apply, hiff]

/-- The binary phase Pauli operator is Hermitian.  This is a
formalization-only specialization of the generalized Pauli definition. -/
theorem binaryTauPhase_conjTranspose :
    (tauPhase (K := ZMod 2) 1)ᴴ = tauPhase (K := ZMod 2) 1 := by
  ext i j
  rcases zmod_two_eq_zero_or_one i with rfl | rfl <;>
    rcases zmod_two_eq_zero_or_one j with rfl | rfl <;>
      norm_num [tauPhase, phaseSign, Matrix.conjTranspose_apply,
        Algebra.trace_self_apply]

/-- The binary shift Pauli operator is symmetric.  This formalization-only
identity supports transport across an EPR state. -/
theorem binaryTauShift_transpose :
    (tauShift (K := ZMod 2) 1)ᵀ = tauShift (K := ZMod 2) 1 := by
  ext i j
  have hiff : j = i + 1 ↔ i = j + 1 := by
    rw [CharTwo.eq_add_iff_add_eq, eq_comm]
  simp [tauShift, Matrix.transpose_apply, hiff]

/-- The binary phase Pauli operator is symmetric.  This formalization-only
identity supports transport across an EPR state. -/
theorem binaryTauPhase_transpose :
    (tauPhase (K := ZMod 2) 1)ᵀ = tauPhase (K := ZMod 2) 1 := by
  ext i j
  rcases zmod_two_eq_zero_or_one i with rfl | rfl <;>
    rcases zmod_two_eq_zero_or_one j with rfl | rfl <;>
      norm_num [tauPhase, phaseSign, Matrix.transpose_apply,
        Algebra.trace_self_apply]

/-- The binary shift Pauli operator squares to the identity.  This is a
formalization-only specialization of the generalized Pauli definition. -/
theorem binaryTauShift_sq :
    tauShift (K := ZMod 2) 1 * tauShift (K := ZMod 2) 1 = 1 := by
  ext i j
  simp only [Matrix.mul_apply]
  rw [sum_zmod_two]
  rcases zmod_two_eq_zero_or_one i with rfl | rfl <;>
    rcases zmod_two_eq_zero_or_one j with rfl | rfl <;>
      simp +decide [tauShift]

/-- The binary phase Pauli operator squares to the identity.  This is a
formalization-only specialization of the generalized Pauli definition. -/
theorem binaryTauPhase_sq :
    tauPhase (K := ZMod 2) 1 * tauPhase (K := ZMod 2) 1 = 1 := by
  ext i j
  simp only [Matrix.mul_apply]
  rw [sum_zmod_two]
  rcases zmod_two_eq_zero_or_one i with rfl | rfl <;>
    rcases zmod_two_eq_zero_or_one j with rfl | rfl <;>
      norm_num [tauPhase, phaseSign, Matrix.one_apply, Algebra.trace_self_apply]

/-- The binary shift and phase Pauli operators anticommute.  This is a
formalization-only specialization of their generalized definitions. -/
theorem binaryTauShift_mul_tauPhase :
    tauShift (K := ZMod 2) 1 * tauPhase (K := ZMod 2) 1 =
      -(tauPhase (K := ZMod 2) 1 * tauShift (K := ZMod 2) 1) := by
  ext i j
  change
    (∑ k, tauShift (K := ZMod 2) 1 i k * tauPhase (K := ZMod 2) 1 k j) =
      -(∑ k, tauPhase (K := ZMod 2) 1 i k * tauShift (K := ZMod 2) 1 k j)
  rw [sum_zmod_two, sum_zmod_two]
  rcases zmod_two_eq_zero_or_one i with rfl | rfl <;>
    rcases zmod_two_eq_zero_or_one j with rfl | rfl <;>
      simp +decide [tauShift, tauPhase, phaseSign]

/-- The single-qudit eigenvector coordinate used in the tensor-product basis;
see `references/qpbt-paper/04_preliminaries.tex:1126-1161`. -/
private noncomputable def singlePauliVec (W : PauliKind) (e x : K) : ℂ :=
  match W with
  | .Z => if x = e then 1 else 0
  | .X =>
      (Real.sqrt (Fintype.card K : ℝ) : ℂ)⁻¹ * phaseSign (binTrace K (e * x))

/--
The normalized single/multi-qudit eigenvector for a Pauli basis label.  For an
index type `ι`, the input `e : ι → K` labels the tensor-product basis vector.
This is the vector form of blueprint
`def:generalized-pauli`, paper origin
`references/qpbt-paper/04_preliminaries.tex:1101-1122`.
-/
noncomputable def pauliVec {ι : Type*} [Fintype ι] [DecidableEq ι]
    (W : PauliKind) (e : ι → K) (x : ι → K) : ℂ :=
  ∏ i : ι, singlePauliVec W (e i) (x i)

/--
The rank-one projector onto `pauliVec W e`.  This is the projective measurement
element `τ^W_e` in blueprint `def:generalized-pauli`; paper
`references/qpbt-paper/04_preliminaries.tex:1101-1122`.
-/
noncomputable def pauliProj {ι : Type*} [Fintype ι] [DecidableEq ι]
    (W : PauliKind) (e : ι → K) : Op (ι → K) :=
  Matrix.vecMulVec (pauliVec W e) (fun x => star (pauliVec W e x))

private theorem pauliProj_X_apply {ι : Type*} [Fintype ι] [DecidableEq ι]
    (e x y : ι → K) :
    pauliProj .X e x y =
      (Fintype.card (ι → K) : ℂ)⁻¹ *
        phaseSign (binTrace K (dotProduct e (x + y))) := by
  change
    (∏ i : ι, (Real.sqrt (Fintype.card K : ℝ) : ℂ)⁻¹ *
        phaseSign (binTrace K (e i * x i))) *
      star (∏ i : ι, (Real.sqrt (Fintype.card K : ℝ) : ℂ)⁻¹ *
        phaseSign (binTrace K (e i * y i))) = _
  rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib,
    prod_phaseSign_binTrace_dotProduct, prod_phaseSign_binTrace_dotProduct]
  simp only [star_mul, star_phaseSign]
  have hstar :
      star (∏ _i : ι, (Real.sqrt (Fintype.card K : ℝ) : ℂ)⁻¹) =
        ∏ _i : ι, (Real.sqrt (Fintype.card K : ℝ) : ℂ)⁻¹ := by
    simp
  rw [hstar]
  calc
    (∏ _i : ι, (Real.sqrt (Fintype.card K : ℝ) : ℂ)⁻¹) *
          phaseSign (binTrace K (dotProduct e x)) *
        (phaseSign (binTrace K (dotProduct e y)) *
          ∏ _i : ι, (Real.sqrt (Fintype.card K : ℝ) : ℂ)⁻¹) =
        ((∏ _i : ι, (Real.sqrt (Fintype.card K : ℝ) : ℂ)⁻¹) *
          ∏ _i : ι, (Real.sqrt (Fintype.card K : ℝ) : ℂ)⁻¹) *
            (phaseSign (binTrace K (dotProduct e x)) *
              phaseSign (binTrace K (dotProduct e y))) := by ring
    _ = _ := by
      rw [pauliNormalizer_mul_self, phaseSign_binTrace_dotProduct_add]

/-- A compact operator-valued form of a generalized Pauli observable from
blueprint `def:generalized-pauli`, paper origin
`references/qpbt-paper/04_preliminaries.tex:1052-1096`.
-/
noncomputable def tauObservable {ι : Type*} [Fintype ι] [DecidableEq ι]
    (W : PauliKind) (a : ι → K) : Op (ι → K) :=
  fun x y =>
    ∏ i : ι,
      match W with
      | .X => tauShift (a i) (x i) (y i)
      | .Z => tauPhase (a i) (x i) (y i)

/--
The EPR vector on a finite label space.  Blueprint `def:EPR`; paper origin
`references/qpbt-paper/04_preliminaries.tex:946-955`.
-/
noncomputable def eprState (V : Type*) [Fintype V] [DecidableEq V] [Nonempty V] :
    EuclideanSpace ℂ (V × V) :=
  (EuclideanSpace.equiv (V × V) ℂ).symm
    (fun p : V × V =>
      if p.1 = p.2 then (Real.sqrt (Fintype.card V : ℝ) : ℂ)⁻¹ else 0)

/-- The EPR vector is normalized on a nonempty finite carrier; see
`def:EPR`, `references/qpbt-paper/04_preliminaries.tex:946-955`. -/
theorem eprState_norm (V : Type*) [Fintype V] [DecidableEq V] [Nonempty V] :
    ‖eprState V‖ = 1 := by
  apply (sq_eq_sq₀ (norm_nonneg _) zero_le_one).mp
  rw [EuclideanSpace.norm_sq_eq]
  change
    (∑ p : V × V,
      ‖if p.1 = p.2 then (Real.sqrt (Fintype.card V : ℝ) : ℂ)⁻¹ else 0‖ ^ 2) =
      1 ^ 2
  rw [Fintype.sum_prod_type]
  have hcard : 0 < (Fintype.card V : ℝ) := by positivity
  calc
    ∑ x : V, ∑ y : V,
        ‖if x = y then (Real.sqrt (Fintype.card V : ℝ) : ℂ)⁻¹ else 0‖ ^ 2 =
        ∑ _x : V, ‖(Real.sqrt (Fintype.card V : ℝ) : ℂ)⁻¹‖ ^ 2 := by
      apply Finset.sum_congr rfl
      intro x _
      rw [Finset.sum_eq_single x]
      · simp
      · intro y _ hy
        simp [hy.symm]
      · simp
    _ = 1 := by
      rw [Finset.sum_const, nsmul_eq_mul]
      simp only [norm_inv, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (Real.sqrt_nonneg _)]
      rw [inv_pow, Real.sq_sqrt hcard.le]
      norm_num [hcard.ne']
    _ = 1 ^ 2 := by norm_num

/--
Fourier expansion of a generalized Pauli observable in the Pauli projectors.
This theorem is the characteristic-two (binary) specialization of the forward
identity `eq:pauli-obs-proj` in `lem:pauli-observable-expansion`,
with blueprint source `lem:pauli-observable-expansion`; paper origin
`references/qpbt-paper/04_preliminaries.tex:1151-1161`.

**Scope restriction:** This characteristic-two specialization is separated
from the general-prime identity as documented in
`docs/paper-gaps/qpbt_characteristic-two-pauli-scope.tex`.
-/
theorem tauObservable_eq_sum_pauliProj {ι : Type*} [Fintype ι] [DecidableEq ι]
    (W : PauliKind) (a : ι → K) :
    tauObservable W a =
      ∑ e : ι → K, phaseSign (binTrace K (dotProduct a e)) • pauliProj W e := by
  ext x y
  rw [show
    (∑ e : ι → K, phaseSign (binTrace K (dotProduct a e)) • pauliProj W e) x y =
      ∑ e : ι → K,
        phaseSign (binTrace K (dotProduct a e)) * pauliProj W e x y by
          rw [Matrix.sum_apply]
          rfl]
  cases W with
  | X =>
      change
        (∏ i : ι, if x i = y i + a i then 1 else 0) =
          ∑ e : ι → K,
            phaseSign (binTrace K (dotProduct a e)) * pauliProj .X e x y
      simp_rw [pauliProj_X_apply]
      rw [Fintype.prod_boole]
      have hsupport : (∀ i, x i = y i + a i) ↔ x = y + a := by
        simpa only [Pi.add_apply] using
          (funext_iff (f := x) (g := y + a)).symm
      simp only [hsupport]
      have hsum :
          (∑ e : ι → K,
            phaseSign (binTrace K (dotProduct a e)) *
              ((Fintype.card (ι → K) : ℂ)⁻¹ *
                phaseSign (binTrace K (dotProduct e (x + y))))) =
            (Fintype.card (ι → K) : ℂ)⁻¹ *
              ∑ e : ι → K,
                phaseSign (binTrace K (dotProduct e (a + (x + y)))) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro e _
        calc
          phaseSign (binTrace K (dotProduct a e)) *
                ((Fintype.card (ι → K) : ℂ)⁻¹ *
                  phaseSign (binTrace K (dotProduct e (x + y)))) =
              (Fintype.card (ι → K) : ℂ)⁻¹ *
                (phaseSign (binTrace K (dotProduct e a)) *
                  phaseSign (binTrace K (dotProduct e (x + y)))) := by
            rw [dotProduct_comm a e]
            ring
          _ = _ := by rw [phaseSign_binTrace_dotProduct_add]
      rw [hsum, sum_phaseSign_dotProduct]
      by_cases hsupport : x = y + a
      · have hzero : a + (x + y) = 0 :=
          (add_add_eq_zero_iff_eq_add a x y).mpr hsupport
        rw [if_pos hsupport, if_pos hzero]
        exact (inv_mul_cancel₀
          (show (Fintype.card (ι → K) : ℂ) ≠ 0 by positivity)).symm
      · have hzero : a + (x + y) ≠ 0 := fun h =>
          hsupport ((add_add_eq_zero_iff_eq_add a x y).mp h)
        simp [hsupport, hzero]
  | Z =>
      change
        (∏ i : ι, if x i = y i then phaseSign (binTrace K (a i * y i)) else 0) =
          ∑ e : ι → K, phaseSign (binTrace K (dotProduct a e)) *
            ((∏ i : ι, if x i = e i then 1 else 0) *
              star (∏ i : ι, if y i = e i then 1 else 0))
      simp only [Fintype.prod_ite_zero, Finset.prod_const_one]
      by_cases hxy : x = y
      · subst y
        rw [prod_phaseSign_binTrace_dotProduct]
        simp [← funext_iff]
      · simp [← funext_iff, hxy]

/-- The inverse Fourier expansion of a Pauli projector.  This theorem is the
characteristic-two (binary) specialization of the inverse identity
`eq:pauli-inversion-0` in `lem:pauli-observable-expansion`,
with blueprint source `lem:pauli-observable-expansion`; paper origin
`references/qpbt-paper/04_preliminaries.tex:1151-1161`.

**Scope restriction:** This characteristic-two specialization is separated
from the general-prime identity as documented in
`docs/paper-gaps/qpbt_characteristic-two-pauli-scope.tex`.
-/
theorem pauliProj_eq_avg_tauObservable {ι : Type*} [Fintype ι] [DecidableEq ι]
    (W : PauliKind) (e : ι → K) :
    pauliProj W e =
      (Fintype.card (ι → K) : ℂ)⁻¹ •
        ∑ a : ι → K, phaseSign (binTrace K (dotProduct a e)) • tauObservable W a := by
  have hcoeff (x : ι → K) :
      ∑ i : ι → K,
          (Fintype.card (ι → K) : ℂ)⁻¹ *
            (phaseSign (binTrace K (dotProduct i e)) *
              phaseSign (binTrace K (dotProduct i x))) =
        if x = e then 1 else 0 := by
    rw [← Finset.mul_sum]
    rw [show
      (∑ i : ι → K,
        phaseSign (binTrace K (dotProduct i e)) *
          phaseSign (binTrace K (dotProduct i x))) =
        ∑ i : ι → K, phaseSign (binTrace K (dotProduct i (e + x))) by
          apply Finset.sum_congr rfl
          intro i _
          exact phaseSign_binTrace_dotProduct_add i e x]
    rw [sum_phaseSign_dotProduct]
    have hzero : e + x = 0 ↔ x = e := by
      simpa using
        (add_add_eq_zero_iff_eq_add (K := K) e x (0 : ι → K))
    by_cases hx : x = e
    · rw [if_pos hx, if_pos (hzero.mpr hx)]
      exact inv_mul_cancel₀
        (show (Fintype.card (ι → K) : ℂ) ≠ 0 by positivity)
    · rw [if_neg hx, if_neg (fun h => hx (hzero.mp h))]
      simp
  simp_rw [tauObservable_eq_sum_pauliProj]
  simp_rw [Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  simp_rw [← Finset.sum_smul]
  simp_rw [hcoeff]
  simp

end MIPStarRE.QPBT
