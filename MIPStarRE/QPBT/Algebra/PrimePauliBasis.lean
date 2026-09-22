import MIPStarRE.QPBT.Algebra.PauliTheorems
import MIPStarRE.Quantum.FiniteMatrix.NormalizedTrace

/-!
# Prime-characteristic Pauli eigenbases

Generalized Pauli observables in arbitrary prime characteristic have the common
eigenvectors and rank-one projectors defined below. Their orthogonality,
projective-measurement properties, and Fourier expansions are established here.

## References

* Blueprint `def:generalized-pauli` and `lem:pauli-observable-expansion`.
* `references/qpbt-paper/04_preliminaries.tex:1096-1161`.
-/

open scoped BigOperators Matrix ComplexOrder

namespace MIPStarRE.QPBT

open MIPStarRE.LDT.Preliminaries MIPStarRE.Quantum

/-- The common eigenbasis vector of the prime-characteristic Pauli family.
For `W = true` this is the Fourier (`X`) vector with negative trace phase;
for `W = false` it is the computational (`Z`) basis vector.  This is the
many-qudit coordinate form of blueprint `def:generalized-pauli`, paper
`04_preliminaries.tex:1096-1155`. -/
noncomputable def primePauliVec {p : ℕ} {K ι : Type*} [Field K] [Fintype K]
    [DecidableEq K] [Fact p.Prime] [Algebra (ZMod p) K]
    [Fintype ι] [DecidableEq ι] (W : Bool) (e x : ι → K) : ℂ :=
  if W then
    (Real.sqrt (Fintype.card (ι → K) : ℝ) : ℂ)⁻¹ *
      ffChar (p := p) (F := K) (-dotProduct e x)
  else if x = e then 1 else 0

/-- The single-qudit Fourier transform from the computational basis to the
prime-characteristic `X` eigenbasis, as in `eq:fourier-f` of paper
`04_preliminaries.tex:1103-1111`. -/
noncomputable def primePauliFourier {p : ℕ} {K : Type*} [Field K] [Fintype K]
    [DecidableEq K] [Fact p.Prime] [Algebra (ZMod p) K] : Op K :=
  fun x e =>
    (Real.sqrt (Fintype.card K : ℝ) : ℂ)⁻¹ *
      ffChar (p := p) (F := K) (-(e * x))

/-- The rank-one projector onto `primePauliVec W e`, namely the effect
`τ^W_e` of the source projective measurement in blueprint
`def:generalized-pauli`, paper `04_preliminaries.tex:1112-1161`. -/
noncomputable def primePauliProj {p : ℕ} {K ι : Type*} [Field K] [Fintype K]
    [DecidableEq K] [Fact p.Prime] [Algebra (ZMod p) K]
    [Fintype ι] [DecidableEq ι] (W : Bool) (e : ι → K) : Op (ι → K) :=
  Matrix.vecMulVec (primePauliVec (p := p) W e)
    (fun x => star (primePauliVec (p := p) W e x))

/-- Sum form of Fourier orthogonality on an arbitrarily indexed finite power. -/
private theorem sum_ffChar_dotProduct {p : ℕ} {K ι : Type*} [Field K]
    [Fintype K] [DecidableEq K] [Fact p.Prime] [Algebra (ZMod p) K]
    [Fintype ι] [DecidableEq ι] (v : ι → K) :
    ∑ u : ι → K, ffChar (p := p) (F := K) (dotProduct u v) =
      if v = 0 then (Fintype.card (ι → K) : ℂ) else 0 := by
  simpa only [dotProduct] using
    (sum_ffChar_sum_mul (p := p) (F := K) (ι := ι) v)

/-- Entry formula for an `X`-basis rank-one projector. -/
private theorem primePauliProj_X_apply {p : ℕ} {K ι : Type*} [Field K]
    [Fintype K] [DecidableEq K] [Fact p.Prime] [Algebra (ZMod p) K]
    [Fintype ι] [DecidableEq ι] (e x y : ι → K) :
    primePauliProj (p := p) true e x y =
      (Fintype.card (ι → K) : ℂ)⁻¹ *
        ffChar (p := p) (F := K) (dotProduct e (y - x)) := by
  let ψ := ffChar (p := p) (F := K)
  let c : ℂ := (Real.sqrt (Fintype.card (ι → K) : ℝ) : ℂ)⁻¹
  have hstar (z : K) : star (ψ (-z)) = ψ z := by
    rw [Complex.star_def]
    simpa only [neg_neg] using (AddChar.map_neg_eq_conj ψ (-z)).symm
  have hc : star c = c := by simp [c]
  change (c * ψ (-dotProduct e x)) * star (c * ψ (-dotProduct e y)) = _
  rw [star_mul, hc, hstar]
  calc
    c * ψ (-dotProduct e x) * (ψ (dotProduct e y) * c) =
        (c * c) * (ψ (-dotProduct e x) * ψ (dotProduct e y)) := by ring
    _ = (Fintype.card (ι → K) : ℂ)⁻¹ *
        ψ (-dotProduct e x + dotProduct e y) := by
      rw [show c * c = (Fintype.card (ι → K) : ℂ)⁻¹ by
        exact inv_sqrt_natCast_mul_self _]
      rw [AddChar.map_add_eq_mul]
    _ = _ := by
      congr 2
      simp only [dotProduct, Pi.sub_apply, mul_sub, Finset.sum_sub_distrib]
      abel

/-- The prime-characteristic Pauli vectors form an orthonormal basis. -/
theorem primePauliVec_orthonormal {p : ℕ} {K ι : Type*} [Field K]
    [Fintype K] [DecidableEq K] [Fact p.Prime] [Algebra (ZMod p) K]
    [Fintype ι] [DecidableEq ι] (W : Bool) (e f : ι → K) :
    ∑ x : ι → K,
        star (primePauliVec (p := p) W e x) * primePauliVec (p := p) W f x =
      if e = f then 1 else 0 := by
  classical
  cases W with
  | false =>
      by_cases hef : e = f
      · subst f
        simp [primePauliVec]
      · simp [primePauliVec, hef, Ne.symm hef]
  | true =>
      let ψ := ffChar (p := p) (F := K)
      let c : ℂ := (Real.sqrt (Fintype.card (ι → K) : ℝ) : ℂ)⁻¹
      have hstar (z : K) : star (ψ (-z)) = ψ z := by
        rw [Complex.star_def]
        simpa only [neg_neg] using (AddChar.map_neg_eq_conj ψ (-z)).symm
      have hc : star c = c := by simp [c]
      have hsum :
          (∑ x : ι → K,
              star (c * ψ (-dotProduct e x)) *
                (c * ψ (-dotProduct f x))) =
            (c * c) * ∑ x : ι → K, ψ (dotProduct x (e - f)) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro x _
        rw [star_mul, hc, hstar]
        calc
          ψ (dotProduct e x) * c * (c * ψ (-dotProduct f x)) =
              (c * c) *
                (ψ (dotProduct e x) * ψ (-dotProduct f x)) := by ring
          _ = (c * c) * ψ (dotProduct e x + -dotProduct f x) := by
            rw [AddChar.map_add_eq_mul]
          _ = _ := by
            congr 2
            simp only [dotProduct, Pi.sub_apply, mul_sub, Finset.sum_sub_distrib]
            rw [show (∑ i, e i * x i) = ∑ i, x i * e i by
              apply Finset.sum_congr rfl
              intro i _
              exact mul_comm _ _]
            rw [show (∑ i, f i * x i) = ∑ i, x i * f i by
              apply Finset.sum_congr rfl
              intro i _
              exact mul_comm _ _]
            abel
      change (∑ x : ι → K,
        star (c * ψ (-dotProduct e x)) * (c * ψ (-dotProduct f x))) = _
      rw [hsum, show c * c = (Fintype.card (ι → K) : ℂ)⁻¹ by
        exact inv_sqrt_natCast_mul_self _, sum_ffChar_dotProduct]
      by_cases hef : e = f
      · subst f
        simp
      · have hsub : e - f ≠ 0 := sub_ne_zero.mpr hef
        simp [hef, hsub]

/-- Rank-one Pauli projectors are mutually orthogonal. -/
theorem primePauliProj_mul_primePauliProj {p : ℕ} {K ι : Type*} [Field K]
    [Fintype K] [DecidableEq K] [Fact p.Prime] [Algebra (ZMod p) K]
    [Fintype ι] [DecidableEq ι] (W : Bool) (e f : ι → K) :
    primePauliProj (p := p) W e * primePauliProj (p := p) W f =
      if e = f then primePauliProj (p := p) W e else 0 := by
  classical
  simp only [primePauliProj, Matrix.vecMulVec_mul_vecMulVec, dotProduct,
    primePauliVec_orthonormal]
  by_cases hef : e = f <;> simp [hef]

/-- Each prime-characteristic Pauli projector is self-adjoint. -/
theorem primePauliProj_conjTranspose {p : ℕ} {K ι : Type*} [Field K]
    [Fintype K] [DecidableEq K] [Fact p.Prime] [Algebra (ZMod p) K]
    [Fintype ι] [DecidableEq ι] (W : Bool) (e : ι → K) :
    (primePauliProj (p := p) W e)ᴴ = primePauliProj (p := p) W e := by
  ext x y
  simp [primePauliProj, Matrix.vecMulVec_apply, Matrix.conjTranspose_apply,
    mul_comm]

/-- Each prime-characteristic Pauli rank-one effect is a projection. -/
theorem primePauliProj_isProj {p : ℕ} {K ι : Type*} [Field K]
    [Fintype K] [DecidableEq K] [Fact p.Prime] [Algebra (ZMod p) K]
    [Fintype ι] [DecidableEq ι] (W : Bool) (e : ι → K) :
    IsProj (primePauliProj (p := p) W e) := by
  refine isStarProjection_iff'.2 ⟨?_, ?_⟩
  · simpa using primePauliProj_mul_primePauliProj (p := p) W e e
  · rw [Matrix.star_eq_conjTranspose, primePauliProj_conjTranspose]

/-- Entry formula for a multi-qudit shift observable. -/
private theorem primeTauObservable_X_apply {p : ℕ} {K ι : Type*} [Field K]
    [Fintype K] [DecidableEq K] [Fact p.Prime] [Algebra (ZMod p) K]
    [Fintype ι] [DecidableEq ι] (a x y : ι → K) :
    primeTauObservable (p := p) true a x y = if x = y + a then 1 else 0 := by
  change (∏ i : ι, if x i = y i + a i then (1 : ℂ) else 0) = _
  rw [Fintype.prod_boole]
  have hsupport : (∀ i, x i = y i + a i) ↔ x = y + a := by
    simpa only [Pi.add_apply] using (funext_iff (f := x) (g := y + a)).symm
  simp only [hsupport]

/-- Entry formula for a multi-qudit phase observable. -/
private theorem primeTauObservable_Z_apply {p : ℕ} {K ι : Type*} [Field K]
    [Fintype K] [DecidableEq K] [Fact p.Prime] [Algebra (ZMod p) K]
    [Fintype ι] [DecidableEq ι] (a x y : ι → K) :
    primeTauObservable (p := p) false a x y =
      if x = y then ffChar (p := p) (F := K) (dotProduct a y) else 0 := by
  change (∏ i : ι,
    if x i = y i then ffChar (p := p) (F := K) (a i * y i) else 0) = _
  have hchar := map_prod (ffChar (p := p) (F := K)).toMonoidHom
    (fun i => Multiplicative.ofAdd (a i * y i)) Finset.univ
  simp only [AddChar.toMonoidHom_apply, toAdd_prod, toAdd_ofAdd] at hchar
  rw [Fintype.prod_ite_zero, ← hchar]
  have hsupport : (∀ i, x i = y i) ↔ x = y :=
    (funext_iff (f := x) (g := y)).symm
  simp only [dotProduct, hsupport]

/-- Every `primePauliVec W e` is a simultaneous eigenvector of the observables
of kind `W`, with eigenvalue given by the positive trace phase from the source.
This is the eigenvalue calculation used in the proof of
`lem:pauli-observable-expansion`, paper `04_preliminaries.tex:1112-1159`. -/
theorem primeTauObservable_mulVec_primePauliVec {p : ℕ} {K ι : Type*}
    [Field K] [Fintype K] [DecidableEq K] [Fact p.Prime]
    [Algebra (ZMod p) K] [Fintype ι] [DecidableEq ι]
    (W : Bool) (a e : ι → K) :
    primeTauObservable (p := p) W a *ᵥ primePauliVec (p := p) W e =
      ffChar (p := p) (F := K) (dotProduct a e) •
        primePauliVec (p := p) W e := by
  classical
  ext x
  cases W with
  | false =>
      simp only [Matrix.mulVec_apply_eq_sum, primeTauObservable_Z_apply]
      rw [Finset.sum_eq_single x]
      · by_cases hxe : x = e
        · subst e
          simp [primePauliVec]
        · simp [primePauliVec, hxe]
      · intro y _ hy
        simp [Ne.symm hy]
      · simp
  | true =>
      simp only [Matrix.mulVec_apply_eq_sum, primeTauObservable_X_apply]
      let y : ι → K := x - a
      rw [Finset.sum_eq_single y]
      · have hshift : x = y + a := by
          funext i
          simp [y]
        rw [if_pos hshift, one_mul]
        simp only [primePauliVec, if_true, Pi.smul_apply,
          smul_eq_mul]
        calc
          (Real.sqrt (Fintype.card (ι → K) : ℝ) : ℂ)⁻¹ *
                ffChar (p := p) (F := K) (-dotProduct e y) =
              (Real.sqrt (Fintype.card (ι → K) : ℝ) : ℂ)⁻¹ *
                ffChar (p := p) (F := K)
                  (dotProduct a e + -dotProduct e x) := by
            congr 2
            simp only [y, dotProduct, Pi.sub_apply, mul_sub,
              Finset.sum_sub_distrib]
            rw [show (∑ i, a i * e i) = ∑ i, e i * a i by
              apply Finset.sum_congr rfl
              intro i _
              exact mul_comm _ _]
            abel
          _ = (Real.sqrt (Fintype.card (ι → K) : ℝ) : ℂ)⁻¹ *
                (ffChar (p := p) (F := K) (dotProduct a e) *
                  ffChar (p := p) (F := K) (-dotProduct e x)) := by
            rw [AddChar.map_add_eq_mul]
          _ = _ := by ring
      · intro z _ hz
        rw [if_neg]
        · simp
        · intro hshift
          apply hz
          funext i
          have hi := congrFun hshift i
          simp only [Pi.add_apply] at hi
          change z i = x i - a i
          calc
            z i = (z i + a i) - a i := by simp
            _ = x i - a i := by rw [← hi]
      · simp

/-- Fourier expansion of a generalized Pauli observable in its common
eigenbasis, in arbitrary prime characteristic.  This is
`eq:pauli-obs-proj` in blueprint `lem:pauli-observable-expansion`, paper
`04_preliminaries.tex:1112-1161`. -/
theorem primeTauObservable_eq_sum_primePauliProj {p : ℕ} {K ι : Type*}
    [Field K] [Fintype K] [DecidableEq K] [Fact p.Prime]
    [Algebra (ZMod p) K] [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (W : Bool) (a : ι → K) :
    primeTauObservable (p := p) W a =
      ∑ e : ι → K,
        ffChar (p := p) (F := K) (dotProduct a e) •
          primePauliProj (p := p) W e := by
  classical
  ext x y
  rw [show
    (∑ e : ι → K,
      ffChar (p := p) (F := K) (dotProduct a e) •
        primePauliProj (p := p) W e) x y =
      ∑ e : ι → K,
        ffChar (p := p) (F := K) (dotProduct a e) *
          primePauliProj (p := p) W e x y by
        rw [Matrix.sum_apply]
        rfl]
  cases W with
  | false =>
      rw [primeTauObservable_Z_apply]
      by_cases hxy : x = y
      · subst y
        simp [primePauliProj, primePauliVec, Matrix.vecMulVec_apply]
      · simp [primePauliProj, primePauliVec, Matrix.vecMulVec_apply, hxy]
  | true =>
      rw [primeTauObservable_X_apply]
      simp_rw [primePauliProj_X_apply]
      have hsum :
          (∑ e : ι → K,
            ffChar (p := p) (F := K) (dotProduct a e) *
              ((Fintype.card (ι → K) : ℂ)⁻¹ *
                ffChar (p := p) (F := K) (dotProduct e (y - x)))) =
            (Fintype.card (ι → K) : ℂ)⁻¹ *
              ∑ e : ι → K,
                ffChar (p := p) (F := K) (dotProduct e (a + y - x)) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro e _
        calc
          ffChar (p := p) (F := K) (dotProduct a e) *
                ((Fintype.card (ι → K) : ℂ)⁻¹ *
                  ffChar (p := p) (F := K) (dotProduct e (y - x))) =
              (Fintype.card (ι → K) : ℂ)⁻¹ *
                (ffChar (p := p) (F := K) (dotProduct e a) *
                  ffChar (p := p) (F := K) (dotProduct e (y - x))) := by
            rw [dotProduct_comm a e]
            ring
          _ = _ := by
            rw [← AddChar.map_add_eq_mul]
            congr 2
            simp only [dotProduct, Pi.add_apply, Pi.sub_apply, mul_add, mul_sub,
              Finset.sum_add_distrib, Finset.sum_sub_distrib]
            abel
      rw [hsum, sum_ffChar_dotProduct]
      have hsupport : a + y - x = 0 ↔ x = y + a := by
        constructor
        · intro h
          funext i
          have hi : a i + y i - x i = 0 := by
            simpa only [Pi.add_apply, Pi.sub_apply, Pi.zero_apply] using congrFun h i
          calc
            x i = a i + y i := (sub_eq_zero.mp hi).symm
            _ = y i + a i := add_comm _ _
        · intro h
          funext i
          have hi := congrFun h i
          simp only [Pi.add_apply] at hi
          change a i + y i - x i = 0
          apply sub_eq_zero.mpr
          rw [hi, add_comm]
      by_cases hxy : x = y + a
      · rw [if_pos hxy, if_pos (hsupport.mpr hxy)]
        exact (inv_mul_cancel₀
          (show (Fintype.card (ι → K) : ℂ) ≠ 0 by positivity)).symm
      · rw [if_neg hxy, if_neg (fun h => hxy (hsupport.mp h))]
        simp

/-- The prime-characteristic Pauli projectors sum to the identity and hence
form a complete projective measurement. -/
theorem sum_primePauliProj_eq_one {p : ℕ} {K ι : Type*} [Field K]
    [Fintype K] [DecidableEq K] [Fact p.Prime] [Algebra (ZMod p) K]
    [Fintype ι] [DecidableEq ι] [Nonempty ι] (W : Bool) :
    (∑ e : ι → K, primePauliProj (p := p) W e) = 1 := by
  have h := primeTauObservable_eq_sum_primePauliProj
    (p := p) (K := K) (ι := ι) W (0 : ι → K)
  have hzero : primeTauObservable (p := p) W (0 : ι → K) = 1 := by
    ext x y
    cases W <;>
      simp [primeTauObservable_X_apply, primeTauObservable_Z_apply,
        Matrix.one_apply]
  rw [hzero] at h
  rw [h]
  apply Finset.sum_congr rfl
  intro e _
  simp [dotProduct]

/-- Each prime-characteristic Pauli projector is positive semidefinite. -/
theorem posSemidef_primePauliProj {p : ℕ} {K ι : Type*} [Field K]
    [Fintype K] [DecidableEq K] [Fact p.Prime] [Algebra (ZMod p) K]
    [Fintype ι] [DecidableEq ι] (W : Bool) (e : ι → K) :
    (primePauliProj (p := p) W e).PosSemidef := by
  exact Matrix.posSemidef_vecMulVec_self_star (primePauliVec (p := p) W e)

/-- Inverse Fourier expansion of a prime-characteristic Pauli projector.
The coefficient uses the negative phase, exactly as in
`eq:pauli-inversion-0` of blueprint `lem:pauli-observable-expansion`, paper
`04_preliminaries.tex:1124-1161`. -/
theorem primePauliProj_eq_avg_primeTauObservable {p : ℕ} {K ι : Type*}
    [Field K] [Fintype K] [DecidableEq K] [Fact p.Prime]
    [Algebra (ZMod p) K] [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (W : Bool) (e : ι → K) :
    primePauliProj (p := p) W e =
      (Fintype.card (ι → K) : ℂ)⁻¹ •
        ∑ a : ι → K,
          ffChar (p := p) (F := K) (-dotProduct a e) •
            primeTauObservable (p := p) W a := by
  classical
  have hcoeff (b : ι → K) :
      ∑ a : ι → K,
          (Fintype.card (ι → K) : ℂ)⁻¹ *
            (ffChar (p := p) (F := K) (-dotProduct a e) *
              ffChar (p := p) (F := K) (dotProduct a b)) =
        if b = e then 1 else 0 := by
    rw [← Finset.mul_sum]
    rw [show
      (∑ a : ι → K,
        ffChar (p := p) (F := K) (-dotProduct a e) *
          ffChar (p := p) (F := K) (dotProduct a b)) =
        ∑ a : ι → K,
          ffChar (p := p) (F := K) (dotProduct a (b - e)) by
          apply Finset.sum_congr rfl
          intro a _
          rw [← AddChar.map_add_eq_mul]
          congr 2
          simp only [dotProduct, Pi.sub_apply, mul_sub, Finset.sum_sub_distrib]
          abel]
    rw [sum_ffChar_dotProduct]
    by_cases hbe : b = e
    · subst b
      simp
    · have hsub : e - b ≠ 0 := sub_ne_zero.mpr (Ne.symm hbe)
      have hsub' : b - e ≠ 0 := sub_ne_zero.mpr hbe
      simp [hbe, hsub']
  simp_rw [primeTauObservable_eq_sum_primePauliProj]
  simp_rw [Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  simp_rw [← Finset.sum_smul]
  simp_rw [hcoeff]
  simp

end MIPStarRE.QPBT
