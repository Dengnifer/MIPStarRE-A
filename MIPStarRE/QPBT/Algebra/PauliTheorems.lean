import MIPStarRE.QPBT.Algebra.Pauli
import MIPStarRE.QPBT.Algebra.SelfDualBasisTheorems
import MIPStarRE.QPBT.Algebra.Subspaces
import MIPStarRE.QPBT.State
import MIPStarRE.LDT.Preliminaries.FiniteFields

/-! # Pauli product, commutation, and cancellation identities

The principal results are `lem:twisted-commutation` and `lem:cancellation` in
`blueprint/src/chapter/ch11_qpbt_algebra.tex:553-660`, from
`references/qpbt-paper/04_preliminaries.tex:1056-1095,1124-1151`. The
general-prime statements use the canonical character `ffChar`; binary
declarations below are separately named QPBT specializations.
-/

open scoped BigOperators Matrix

namespace MIPStarRE.QPBT

open MIPStarRE.LDT MIPStarRE.LDT.Preliminaries MIPStarRE.Quantum

/-- The shift observable in `lem:twisted-commutation`, blueprint
`ch11_qpbt_algebra.tex:553-597`, paper `04_preliminaries.tex:1056-1089`. -/
noncomputable def primeTauShift {p : ℕ} {K : Type*} [Field K] [Fintype K]
    [DecidableEq K] [Fact p.Prime] [Algebra (ZMod p) K]
    (a : K) : Op K := fun i j => if i = j + a then 1 else 0

/-- The phase observable in `lem:twisted-commutation`, blueprint
`ch11_qpbt_algebra.tex:553-597`, paper `04_preliminaries.tex:1056-1089`. -/
noncomputable def primeTauPhase {p : ℕ} {K : Type*} [Field K] [Fintype K]
    [DecidableEq K] [Fact p.Prime] [Algebra (ZMod p) K]
    (b : K) : Op K := fun i j =>
  if i = j then ffChar (p := p) (F := K) (b * j) else 0

/-- The multi-qudit observable in `lem:twisted-commutation`, with `false`
denoting phase; blueprint `ch11_qpbt_algebra.tex:553-597`, paper
`04_preliminaries.tex:1073-1095,1141-1151`. -/
noncomputable def primeTauObservable {p : ℕ} {K ι : Type*} [Field K] [Fintype K]
    [DecidableEq K] [Fact p.Prime] [Algebra (ZMod p) K]
    [Fintype ι] [DecidableEq ι] (W : Bool) (a : ι → K) : Op (ι → K) :=
  fun x y => ∏ i : ι, if W then primeTauShift (p := p) (a i) (x i) (y i)
    else primeTauPhase (p := p) (a i) (x i) (y i)

/-- The coordinatewise tensor-entry presentation used by the Pauli observables. -/
private def productMatrix {ι κ : Type*} [Fintype ι]
    (A : ι → Matrix κ κ ℂ) : Matrix (ι → κ) (ι → κ) ℂ :=
  fun x y => ∏ i, A i (x i) (y i)

/-- Matrix multiplication distributes over `productMatrix`. -/
private theorem productMatrix_mul {ι κ : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype κ]
    (A B : ι → Matrix κ κ ℂ) :
    (productMatrix A * productMatrix B : Matrix (ι → κ) (ι → κ) ℂ) =
      productMatrix (fun i => A i * B i) := by
  classical
  ext x y
  simpa only [productMatrix, Matrix.mul_apply, Finset.prod_mul_distrib] using
    (Fintype.prod_sum (fun i z => A i (x i) z * B i z (y i))).symm

/-- Two single-coordinate shifts compose by adding their displacements. -/
private theorem primeTauShift_mul {p : ℕ} {K : Type*} [Field K] [Fintype K]
    [DecidableEq K] [Fact p.Prime] [Algebra (ZMod p) K] (a a' : K) :
    primeTauShift (p := p) a * primeTauShift (p := p) a' =
      primeTauShift (p := p) (a + a') := by
  ext x y
  simp [Matrix.mul_apply, primeTauShift, add_comm, add_left_comm]

/-- Two single-coordinate phases compose by adding their labels. -/
private theorem primeTauPhase_mul {p : ℕ} {K : Type*} [Field K] [Fintype K]
    [DecidableEq K] [Fact p.Prime] [Algebra (ZMod p) K] (b b' : K) :
    primeTauPhase (p := p) b * primeTauPhase (p := p) b' =
      primeTauPhase (p := p) (b + b') := by
  ext x y
  simp [Matrix.mul_apply, primeTauPhase, add_mul, AddChar.map_add_eq_mul]

/-- The generalized Pauli observable with zero label is the identity. -/
private theorem primeTauObservable_zero {p : ℕ} {K ι : Type*} [Field K]
    [Fintype K] [DecidableEq K] [Fact p.Prime] [Algebra (ZMod p) K]
    [Fintype ι] [DecidableEq ι] (W : Bool) :
    primeTauObservable (p := p) W (0 : ι → K) = 1 := by
  classical
  ext x y
  cases W <;>
    simp only [primeTauObservable, if_true, Pi.zero_apply, primeTauShift,
      primeTauPhase, zero_mul, AddChar.map_zero_eq_one, Matrix.one_apply]
  all_goals
    by_cases hxy : ∀ i, x i = y i
    · have h : x = y := funext hxy
      simp [h]
    · simp only [not_forall] at hxy
      obtain ⟨i, hi⟩ := hxy
      rw [Finset.prod_eq_zero (Finset.mem_univ i) (by simp [hi])]
      have h : x ≠ y := fun hxy => hi (congr_fun hxy i)
      simp [h]

/-- The product identity `eq:pauli-product-power`, blueprint
`ch11_qpbt_algebra.tex:599-633`, paper `04_preliminaries.tex:1082-1089`. -/
theorem primeTauObservable_mul {p : ℕ} {K ι : Type*} [Field K] [Fintype K]
    [DecidableEq K] [Fact p.Prime] [Algebra (ZMod p) K] [Fintype ι]
    [DecidableEq ι] (W : Bool) (a a' : ι → K) :
    primeTauObservable (p := p) W a * primeTauObservable (p := p) W a' =
      primeTauObservable (p := p) W (a + a') := by
  cases W with
  | false =>
      change productMatrix (fun i => primeTauPhase (p := p) (a i)) *
          productMatrix (fun i => primeTauPhase (p := p) (a' i)) =
        productMatrix (fun i => primeTauPhase (p := p) ((a + a') i))
      simpa [primeTauPhase_mul] using
        (productMatrix_mul
          (A := fun i => primeTauPhase (p := p) (a i))
          (B := fun i => primeTauPhase (p := p) (a' i)))
  | true =>
      change productMatrix (fun i => primeTauShift (p := p) (a i)) *
          productMatrix (fun i => primeTauShift (p := p) (a' i)) =
        productMatrix (fun i => primeTauShift (p := p) ((a + a') i))
      simpa [primeTauShift_mul] using
        (productMatrix_mul
          (A := fun i => primeTauShift (p := p) (a i))
          (B := fun i => primeTauShift (p := p) (a' i)))

/-- Natural powers of a generalized Pauli observable multiply its label by
repeated addition. -/
private theorem primeTauObservable_pow_nat {p : ℕ} {K ι : Type*} [Field K]
    [Fintype K] [DecidableEq K] [Fact p.Prime] [Algebra (ZMod p) K]
    [Fintype ι] [DecidableEq ι] (W : Bool) (a : ι → K) (n : ℕ) :
    (primeTauObservable (p := p) W a) ^ n =
      primeTauObservable (p := p) W (fun i => n • a i) := by
  induction n with
  | zero =>
      rw [pow_zero]
      have hzero : (fun i => (0 : ℕ) • a i) = (0 : ι → K) := by
        funext i
        simp
      rw [hzero]
      exact (primeTauObservable_zero (p := p) (K := K) (ι := ι) W).symm
  | succ n ih =>
      calc
        (primeTauObservable (p := p) W a) ^ (n + 1) =
            (primeTauObservable (p := p) W a) ^ n *
              primeTauObservable (p := p) W a := pow_succ _ _
        _ = primeTauObservable (p := p) W (fun i => n • a i) *
              primeTauObservable (p := p) W a := by rw [ih]
        _ = primeTauObservable (p := p) W ((fun i => n • a i) + a) :=
              primeTauObservable_mul W _ _
        _ = primeTauObservable (p := p) W (fun i => (n + 1) • a i) := by
              have hlabels : ((fun i => n • a i) + a) =
                  (fun i => (n + 1) • a i) := by
                funext i
                rw [Pi.add_apply, add_nsmul, one_nsmul]
              exact congrArg
                (fun c => primeTauObservable (p := p) W c) hlabels

/-- The prime-field exponent identity in `eq:pauli-product-power`, blueprint
`ch11_qpbt_algebra.tex:599-633`, paper `04_preliminaries.tex:1082-1089`. -/
theorem primeTauObservable_pow {p : ℕ} {K ι : Type*} [Field K] [Fintype K]
    [DecidableEq K] [Fact p.Prime] [Algebra (ZMod p) K] [Fintype ι]
    [DecidableEq ι] (W : Bool) (a : ι → K) (b : ZMod p) :
    (primeTauObservable (p := p) W a) ^ b.val =
      primeTauObservable (p := p) W (fun i => a i * algebraMap (ZMod p) K b) := by
  rw [primeTauObservable_pow_nat]
  congr 1
  funext i
  have hb : algebraMap (ZMod p) K b = (b.val : K) := by
    rw [← map_natCast (algebraMap (ZMod p) K), ZMod.natCast_zmod_val]
  rw [nsmul_eq_mul, hb, mul_comm]

/-- The characteristic-`p` consequence of `primeTauObservable_pow`, blueprint
`ch11_qpbt_algebra.tex:599-633`, paper `04_preliminaries.tex:1088-1089`. -/
theorem primeTauObservable_pow_char {p : ℕ} {K ι : Type*} [Field K] [Fintype K]
    [DecidableEq K] [Fact p.Prime] [Algebra (ZMod p) K] [Fintype ι]
    [DecidableEq ι] (W : Bool) (a : ι → K) :
    (primeTauObservable (p := p) W a) ^ p = 1 := by
  haveI : CharP K p := (Algebra.charP_iff (ZMod p) K p).mp (ZMod.charP p)
  rw [primeTauObservable_pow_nat]
  have hlabel : (fun i => p • a i) = (0 : ι → K) := by
    funext i
    simp [nsmul_eq_mul, CharP.cast_eq_zero]
  rw [hlabel, primeTauObservable_zero]

/-- Taking the adjoint of a single-coordinate shift negates its label. -/
private theorem star_primeTauShift {p : ℕ} {K : Type*} [Field K] [Fintype K]
    [DecidableEq K] [Fact p.Prime] [Algebra (ZMod p) K] (a : K) :
    star (primeTauShift (p := p) a) = primeTauShift (p := p) (-a) := by
  ext x y
  by_cases h : y = x + a
  · have h' : x = y + -a := by
      rw [h]
      abel
    rw [Matrix.star_apply]
    simp only [primeTauShift, if_pos h, if_pos h', star_one]
  · have h' : x ≠ y + -a := by
      intro h'
      apply h
      rw [h']
      abel
    rw [Matrix.star_apply]
    simp only [primeTauShift, if_neg h, if_neg h', star_zero]

/-- Taking the adjoint of a single-coordinate phase negates its label. -/
private theorem star_primeTauPhase {p : ℕ} {K : Type*} [Field K] [Fintype K]
    [DecidableEq K] [Fact p.Prime] [Algebra (ZMod p) K] (b : K) :
    star (primeTauPhase (p := p) b) = primeTauPhase (p := p) (-b) := by
  ext x y
  by_cases hxy : x = y
  · subst y
    simp only [Matrix.star_apply, primeTauPhase, if_pos]
    rw [Complex.star_def]
    simpa only [neg_mul] using
      (AddChar.map_neg_eq_conj (ffChar (p := p) (F := K)) (b * x)).symm
  · have hyx : y ≠ x := Ne.symm hxy
    simp [Matrix.star_apply, primeTauPhase, hxy, hyx]

/-- The adjoint of a coordinatewise tensor-entry matrix is the tensor-entry
matrix of the coordinatewise adjoints. -/
private theorem star_productMatrix {ι κ : Type*} [Fintype ι]
    (A : ι → Matrix κ κ ℂ) :
    star (productMatrix A) = productMatrix (fun i => star (A i)) := by
  classical
  ext x y
  simp [productMatrix, Matrix.star_apply]

/-- Taking the adjoint of a generalized Pauli observable negates its label. -/
private theorem star_primeTauObservable {p : ℕ} {K ι : Type*} [Field K]
    [Fintype K] [DecidableEq K] [Fact p.Prime] [Algebra (ZMod p) K]
    [Fintype ι] [DecidableEq ι] (W : Bool) (a : ι → K) :
    star (primeTauObservable (p := p) W a) =
      primeTauObservable (p := p) W (-a) := by
  cases W with
  | false =>
      change star (productMatrix (fun i => primeTauPhase (p := p) (a i))) =
        productMatrix (fun i => primeTauPhase (p := p) ((-a) i))
      rw [star_productMatrix]
      congr 1
      funext i
      simpa using star_primeTauPhase (p := p) (b := a i)
  | true =>
      change star (productMatrix (fun i => primeTauShift (p := p) (a i))) =
        productMatrix (fun i => primeTauShift (p := p) ((-a) i))
      rw [star_productMatrix]
      congr 1
      funext i
      simpa using star_primeTauShift (p := p) (a := a i)

/-- Generalized Pauli observables are unitary by their explicit shift and phase
matrices; blueprint `ch11_qpbt_algebra.tex:599-633`, paper
`04_preliminaries.tex:1056-1089`. -/
theorem primeTauObservable_isUnitary {p : ℕ} {K ι : Type*} [Field K] [Fintype K]
    [DecidableEq K] [Fact p.Prime] [Algebra (ZMod p) K] [Fintype ι]
    [DecidableEq ι] (W : Bool) (a : ι → K) :
    primeTauObservable (p := p) W a ∈ unitary (Op (ι → K)) := by
  rw [Unitary.mem_iff, star_primeTauObservable]
  constructor
  · rw [primeTauObservable_mul]
    simpa using primeTauObservable_zero (p := p) (K := K) (ι := ι) W
  · rw [primeTauObservable_mul]
    simpa using primeTauObservable_zero (p := p) (K := K) (ι := ι) W

/-- Every eigenvalue of a generalized Pauli observable is a `p`-th root of
unity. This is the spectral consequence of `eq:pauli-product-power`, blueprint
`ch11_qpbt_algebra.tex:599-633`, paper `04_preliminaries.tex:1082-1089`. -/
theorem primeTauObservable_eigenvalue_pow_char {p : ℕ} {K ι : Type*}
    [Field K] [Fintype K] [DecidableEq K] [Fact p.Prime]
    [Algebra (ZMod p) K] [Fintype ι] [DecidableEq ι]
    (W : Bool) (a : ι → K) (v : (ι → K) → ℂ) (eigenvalue : ℂ)
    (hv : v ≠ 0)
    (heigen : primeTauObservable (p := p) W a *ᵥ v = eigenvalue • v) :
    eigenvalue ^ p = 1 := by
  have hpow (n : ℕ) :
      (primeTauObservable (p := p) W a) ^ n *ᵥ v = eigenvalue ^ n • v := by
    induction n with
    | zero => simp
    | succ n ih =>
        rw [pow_succ, ← Matrix.mulVec_mulVec, heigen, Matrix.mulVec_smul, ih,
          pow_succ, smul_smul, mul_comm]
  have hp := hpow p
  rw [primeTauObservable_pow_char, Matrix.one_mulVec] at hp
  have hscalar : eigenvalue ^ p - 1 = 0 := by
    apply (smul_eq_zero_iff_left hv).mp
    rw [sub_smul, one_smul, ← hp, sub_self]
  exact sub_eq_zero.mp hscalar

/-- A single-coordinate shift and phase satisfy the generalized Pauli twisted
commutation relation. -/
private theorem primeTauShift_mul_primeTauPhase {p : ℕ} {K : Type*} [Field K]
    [Fintype K] [DecidableEq K] [Fact p.Prime] [Algebra (ZMod p) K]
    (a b : K) :
    primeTauShift (p := p) a * primeTauPhase (p := p) b =
      (ffChar (p := p) (F := K) (-a * b)) •
        (primeTauPhase (p := p) b * primeTauShift (p := p) a) := by
  ext x y
  by_cases hxy : x = y + a
  · subst x
    simp only [Matrix.mul_apply, primeTauShift, primeTauPhase, Matrix.smul_apply,
      smul_eq_mul]
    simp only [add_left_inj, mul_ite, ite_mul, one_mul, zero_mul, mul_zero,
      Finset.sum_ite_eq', Finset.mem_univ, mul_one]
    rw [← AddChar.map_add_eq_mul]
    congr 1
    ring_nf
  · simp [Matrix.mul_apply, primeTauShift, primeTauPhase, Matrix.smul_apply, hxy]

/-- An additive character sends a finite sum to the product of its values. -/
private theorem addChar_sum {A M ι : Type*} [AddCommMonoid A] [CommMonoid M]
    [Fintype ι] (ψ : AddChar A M) (f : ι → A) :
    ψ (∑ i, f i) = ∏ i, ψ (f i) := by
  classical
  induction (Finset.univ : Finset ι) using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
      rw [Finset.sum_insert hi, Finset.prod_insert hi, AddChar.map_add_eq_mul, ih]

/-- The source multi-qudit twisted relation `eq:twisted-fq`, blueprint
`ch11_qpbt_algebra.tex:599-633`, paper `04_preliminaries.tex:1090-1095,1141-1151`. -/
theorem primeTauObservable_X_mul_Z {p : ℕ} {K ι : Type*} [Field K] [Fintype K]
    [DecidableEq K] [Fact p.Prime] [Algebra (ZMod p) K] [Fintype ι]
    [DecidableEq ι] [Nonempty ι] (a b : ι → K) :
    primeTauObservable (p := p) true a * primeTauObservable (p := p) false b =
      (ffChar (p := p) (F := K) (-dotProduct a b)) •
        (primeTauObservable (p := p) false b * primeTauObservable (p := p) true a) := by
  let ψ := ffChar (p := p) (F := K)
  have hchar : ψ (-dotProduct a b) = ∏ i, ψ (-(a i) * b i) := by
    calc
      ψ (-dotProduct a b) = ψ (∑ i, -(a i) * b i) := by
        congr 1
        simp [dotProduct]
      _ = ∏ i, ψ (-(a i) * b i) := addChar_sum ψ _
  change productMatrix (fun i => primeTauShift (p := p) (a i)) *
      productMatrix (fun i => primeTauPhase (p := p) (b i)) =
    ψ (-dotProduct a b) •
      (productMatrix (fun i => primeTauPhase (p := p) (b i)) *
        productMatrix (fun i => primeTauShift (p := p) (a i)))
  rw [productMatrix_mul, productMatrix_mul]
  ext x y
  simp only [productMatrix, primeTauShift_mul_primeTauPhase, Matrix.smul_apply,
    smul_eq_mul, Finset.prod_mul_distrib]
  rw [← hchar]

/-- In characteristic two, the standard additive character is the sign
character used by the binary Pauli definitions. -/
private theorem phaseSign_eq_stdAddChar (t : ZMod 2) :
    phaseSign t = ZMod.stdAddChar t := by
  by_cases ht : t = 0
  · subst t
    simp [phaseSign]
  · rw [phaseSign, if_neg ht]
    have ht_ne_one : ZMod.stdAddChar t ≠ 1 := by
      intro h
      apply ht
      apply ZMod.injective_stdAddChar
      simpa using h
    have htwo : 2 • t = 0 := by
      simpa only [two_nsmul] using CharTwo.add_self_eq_zero t
    have hsq : (ZMod.stdAddChar t) ^ 2 = 1 := by
      rw [← AddChar.map_nsmul_eq_pow, htwo, AddChar.map_zero_eq_one]
    exact ((sq_eq_one_iff.mp hsq).resolve_left ht_ne_one).symm

/-- The canonical finite-field character at `p = 2` is `phaseSign` composed
with the binary trace. -/
private theorem ffChar_two_eq_phaseSign {K : Type*} [Field K]
    [Algebra (ZMod 2) K] (x : K) :
    ffChar (p := 2) (F := K) x = phaseSign (binTrace K x) := by
  rw [ffChar_apply]
  exact (phaseSign_eq_stdAddChar (binTrace K x)).symm

/-- The binary Pauli observable is the characteristic-two specialization of
the prime-characteristic observable. -/
private theorem tauObservable_eq_primeTauObservable {K ι : Type*} [Field K]
    [Fintype K] [DecidableEq K] [Algebra (ZMod 2) K] [Fintype ι]
    [DecidableEq ι] (W : PauliKind) (a : ι → K) :
    tauObservable W a = primeTauObservable (p := 2)
      (match W with | .X => true | .Z => false) a := by
  cases W with
  | X =>
      ext x y
      rfl
  | Z =>
      ext x y
      simp only [tauObservable, primeTauObservable, Bool.false_eq_true, if_false,
        tauPhase, primeTauPhase]
      apply Finset.prod_congr rfl
      intro i hi
      by_cases hxy : x i = y i
      · rw [if_pos hxy, if_pos hxy, ffChar_apply]
        exact phaseSign_eq_stdAddChar _
      · rw [if_neg hxy, if_neg hxy]

/-- With no coordinates, every binary Pauli observable is the identity. -/
private theorem tauObservable_eq_one_of_isEmpty {K ι : Type*} [Field K]
    [DecidableEq K] [Algebra (ZMod 2) K] [Fintype ι]
    [DecidableEq ι] [IsEmpty ι] (W : PauliKind) (a : ι → K) :
    tauObservable W a = 1 := by
  classical
  ext x y
  have hxy : x = y := Subsingleton.elim _ _
  subst y
  simp [tauObservable]

/-- Binary specialization of `eq:pauli-product-power`, blueprint
`ch11_qpbt_algebra.tex:599-633`, paper `04_preliminaries.tex:1082-1089`.

**Scope restriction:** This characteristic-two specialization is separated
from the general-prime identity as documented in
`docs/paper-gaps/qpbt_characteristic-two-pauli-scope.tex`. -/
theorem tauObservable_mul {K ι : Type*} [Field K] [Fintype K] [DecidableEq K]
    [Algebra (ZMod 2) K] [Fintype ι] [DecidableEq ι]
    (W : PauliKind) (a a' : ι → K) :
    tauObservable W a * tauObservable W a' = tauObservable W (a + a') := by
  cases W with
  | X =>
      simpa only [tauObservable_eq_primeTauObservable] using
        (primeTauObservable_mul (p := 2) true a a')
  | Z =>
      simpa only [tauObservable_eq_primeTauObservable] using
        (primeTauObservable_mul (p := 2) false a a')

/-- Binary characteristic-two specialization of `eq:pauli-product-power`,
blueprint `ch11_qpbt_algebra.tex:599-633`, paper `04_preliminaries.tex:1088-1089`.

**Scope restriction:** This characteristic-two specialization is separated
from the general-prime identity as documented in
`docs/paper-gaps/qpbt_characteristic-two-pauli-scope.tex`. -/
theorem tauObservable_sq {K ι : Type*} [Field K] [Fintype K] [DecidableEq K]
    [Algebra (ZMod 2) K] [Fintype ι] [DecidableEq ι] (W : PauliKind) (a : ι → K) :
    tauObservable W a * tauObservable W a = 1 := by
  cases W with
  | X =>
      simpa only [tauObservable_eq_primeTauObservable, pow_two] using
        (primeTauObservable_pow_char (p := 2) true a)
  | Z =>
      simpa only [tauObservable_eq_primeTauObservable, pow_two] using
        (primeTauObservable_pow_char (p := 2) false a)

/-- Binary specialization of `eq:twisted-fq`, blueprint
`ch11_qpbt_algebra.tex:599-633`, paper `04_preliminaries.tex:1090-1095`.

**Scope restriction:** This characteristic-two specialization is separated
from the general-prime identity as documented in
`docs/paper-gaps/qpbt_characteristic-two-pauli-scope.tex`. -/
theorem tauObservable_X_mul_Z {K ι : Type*} [Field K] [Fintype K] [DecidableEq K]
    [Algebra (ZMod 2) K] [Fintype ι] [DecidableEq ι] (a b : ι → K) :
    tauObservable .X a * tauObservable .Z b =
      (phaseSign (binTrace K (dotProduct a b))) •
        (tauObservable .Z b * tauObservable .X a) := by
  cases isEmpty_or_nonempty ι with
  | inl hι =>
      letI : IsEmpty ι := hι
      rw [tauObservable_eq_one_of_isEmpty]
      simp [dotProduct, phaseSign]
  | inr hι =>
      letI : Nonempty ι := hι
      have hphase : ffChar (p := 2) (F := K) (-dotProduct a b) =
          phaseSign (binTrace K (dotProduct a b)) := by
        rw [ffChar_two_eq_phaseSign]
        congr 1
        simp only [map_neg, ZMod.neg_eq_self_mod_two]
      simpa only [tauObservable_eq_primeTauObservable, hphase] using
        (primeTauObservable_X_mul_Z (p := 2) a b)

/-- Uniform complex expectation over a finite submodule, as used by
`lem:cancellation`; blueprint `ch11_qpbt_algebra.tex:649-660`, paper
`04_preliminaries.tex:1124-1132`. -/
noncomputable def submoduleExpect {K ι : Type*} [Field K] [Fintype K]
    [DecidableEq K] [Fintype ι] [DecidableEq ι]
    (V : Submodule K (ι → K)) (f : V → ℂ) : ℂ := by
  letI : Fintype V := Fintype.ofFinite V
  exact 𝔼 u : V, f u

/-- Fourier cancellation `lem:cancellation` over an arbitrary field submodule;
blueprint `ch11_qpbt_algebra.tex:649-660`, paper
`04_preliminaries.tex:1124-1132`. -/
theorem ffChar_dotProduct_submodule_expect_eq_zero {p : ℕ} {K ι : Type*}
    [Field K] [Fintype K] [DecidableEq K] [Fact p.Prime] [Algebra (ZMod p) K]
    [Fintype ι] [DecidableEq ι] (V : Submodule K (ι → K)) (v : ι → K)
    (hv : v ∉ dotOrthogonal V) :
    submoduleExpect V
      (fun u => ffChar (p := p) (F := K) (dotProduct (u : ι → K) v)) = 0 := by
  letI : Fintype V := Fintype.ofFinite V
  obtain ⟨u, hu, huv⟩ :
      ∃ u : ι → K, u ∈ V ∧ dotProduct u v ≠ 0 := by
    by_contra h
    push Not at h
    apply hv
    change ∀ u, u ∈ V → dotProduct v u = 0
    intro u hu
    rw [dotProduct_comm]
    exact h u hu
  have hfourier :
      (𝔼 r : K, ffChar (p := p) (F := K) (r * dotProduct u v)) = 0 := by
    simpa [huv] using
      (fourier_fact_scalar (p := p) (F := K) (dotProduct u v))
  obtain ⟨r, hr⟩ :
      ∃ r : K, ffChar (p := p) (F := K) (r * dotProduct u v) ≠ 1 := by
    by_contra h
    push Not at h
    have hmean :
        (𝔼 r : K, ffChar (p := p) (F := K) (r * dotProduct u v)) = 1 := by
      simp_rw [h]
      simp
    rw [hfourier] at hmean
    exact zero_ne_one hmean
  let φ : V →+ K :=
    { toFun := fun w => dotProduct (w : ι → K) v
      map_zero' := by simp
      map_add' := by
        intro w w'
        simp }
  let ψ : AddChar V ℂ :=
    (ffChar (p := p) (F := K)).compAddMonoidHom φ
  have hψ : ψ ≠ 0 := by
    rw [AddChar.ne_zero_iff]
    refine ⟨r • (⟨u, hu⟩ : V), ?_⟩
    simpa [ψ, φ, smul_eq_mul] using hr
  simpa [submoduleExpect, ψ, φ] using
    (AddChar.expect_eq_zero_iff_ne_zero.mpr hψ)

/-- Binary specialization of `lem:cancellation`, blueprint
`ch11_qpbt_algebra.tex:649-660`, paper `04_preliminaries.tex:1124-1132`.

**Scope restriction:** This characteristic-two specialization is separated
from the general-prime identity as documented in
`docs/paper-gaps/qpbt_characteristic-two-pauli-scope.tex`. -/
theorem avg_neg_one_pow_binTrace_eq_zero {K : Type*} [Field K] [Fintype K]
    {k : Type*}
    [DecidableEq K] [Algebra (ZMod 2) K] [Fintype k] [DecidableEq k]
    (V : Submodule K (k → K)) [Fintype V] (v : k → K)
    (hv : v ∉ dotOrthogonal V) :
    𝔼 u : V, phaseSign (binTrace K (dotProduct (u : k → K) v)) = 0 := by
  have hcancel :=
    ffChar_dotProduct_submodule_expect_eq_zero (p := 2) V v hv
  unfold submoduleExpect at hcancel
  have huniv :
      @Finset.univ V (Fintype.ofFinite V) = @Finset.univ V (inferInstance) := by
    ext u
    simp
  rw [huniv] at hcancel
  simpa only [ffChar_two_eq_phaseSign] using hcancel

/-- Relabeling a finite orthonormal basis transports its EPR state. -/
private theorem isometryTensor_piLpCongrLeft_epr
    {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    [Fintype κ] [DecidableEq κ] [Nonempty κ] (e : ι ≃ κ) :
    isometryTensor
        (LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ e).toLinearIsometry
        (LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ e).toLinearIsometry
        (eprState ι) = eprState κ := by
  apply (EuclideanSpace.equiv (κ × κ) ℂ).injective
  funext p
  simp only [isometryTensor, eprState, ContinuousLinearEquiv.apply_symm_apply]
  rw [Fintype.card_congr e]
  rw [Fintype.sum_eq_single (e.symm p.1)]
  · rw [Fintype.sum_eq_single (e.symm p.2)]
    · simp
    · intro j hj
      simp [Equiv.apply_eq_iff_eq_symm_apply, hj]
  · intro i hi
    simp [Equiv.apply_eq_iff_eq_symm_apply, hi]

/-- The matrix of a basis relabeling is the corresponding permutation matrix. -/
private theorem piLpCongrLeft_matrix_apply
    {ι κ : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype κ] [DecidableEq κ] (e : ι ≃ κ) (y : κ) (i : ι) :
    Matrix.toEuclideanLin.symm
        (LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ e).toLinearIsometry.toLinearMap y i =
      if y = e i then 1 else 0 := by
  change (LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ e
    (EuclideanSpace.single i 1)) y = _
  rw [EuclideanSpace.piLpCongrLeft_single]
  simp [PiLp.single_apply]

/-- Conjugation by an inverse basis relabeling is matrix reindexing. -/
private theorem conjIsometry_piLpCongrLeft_symm
    {ι κ : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype κ] [DecidableEq κ] (e : ι ≃ κ) (M : Op κ) :
    conjIsometry
        (LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ e).symm.toLinearIsometry M =
      Matrix.reindex e.symm e.symm M := by
  ext x y
  simp only [conjIsometry, Matrix.mul_apply, Matrix.conjTranspose_apply,
    Matrix.reindex_apply, Matrix.submatrix_apply]
  rw [Fintype.sum_eq_single (e y)]
  · rw [Fintype.sum_eq_single (e x)]
    · simp [piLpCongrLeft_matrix_apply]
    · intro j hj
      have hxj : x ≠ e.symm j := by
        intro h
        apply hj
        simp [h]
      simp [piLpCongrLeft_matrix_apply, hxj]
  · intro i hi
    have hyi : y ≠ e.symm i := by
      intro h
      apply hi
      simp [h]
    simp [piLpCongrLeft_matrix_apply, hyi]

/-- The label equivalence obtained by expanding each field element in the fixed
self-dual binary basis. -/
private noncomputable def quditQubitLabelEquiv {q : ℕ}
    (F : FixedFieldModel q) (L : ℕ) :
    (Fin L → F.K) ≃ (Fin L × Fin F.basisDim → ZMod 2) :=
  (Equiv.piCongrRight (fun _ : Fin L => F.binaryCoordinates.toEquiv)).trans
    (Equiv.curry (Fin L) (Fin F.basisDim) (ZMod 2)).symm

/-- The label equivalence is the uncurried form of `kappaVec`. -/
private theorem quditQubitLabelEquiv_eq_kappaVec {q : ℕ}
    (F : FixedFieldModel q) (L : ℕ) (u : Fin L → F.K) :
    quditQubitLabelEquiv F L u = kappaVec F u := by
  rfl

/-- Self-duality identifies the field trace pairing with the binary coordinate
pairing after relabeling. -/
private theorem binTrace_dotProduct_eq_quditQubitLabelEquiv
    {q : ℕ} (F : FixedFieldModel q) (L : ℕ) (a u : Fin L → F.K) :
    binTrace F.K (dotProduct a u) =
      binTrace (ZMod 2)
        (dotProduct (quditQubitLabelEquiv F L a) (kappaVec F u)) := by
  simp only [dotProduct, map_sum, binTrace_mul_eq_dotProduct F,
    Algebra.trace_self_apply, Fintype.sum_prod_type, quditQubitLabelEquiv,
    Equiv.trans_apply, Equiv.curry_symm_apply, kappaVec, basisCoordVec]
  rfl

/-- The binary sign character sends sums to products. -/
private theorem phaseSign_sum {ι : Type*} [Fintype ι] (f : ι → ZMod 2) :
    phaseSign (∑ i, f i) = ∏ i, phaseSign (f i) := by
  simpa only [phaseSign_eq_stdAddChar] using
    (addChar_sum (ZMod.stdAddChar (N := 2)) f)

/-- The product of the coordinate phases is the phase of the trace pairing. -/
private theorem prod_phaseSign_binTrace_dotProduct
    {K ι : Type*} [CommRing K] [Algebra (ZMod 2) K] [Fintype ι]
    (a u : ι → K) :
    (∏ i, phaseSign (binTrace K (a i * u i))) =
      phaseSign (binTrace K (dotProduct a u)) := by
  rw [← phaseSign_sum]
  simp [dotProduct]

/-- The coordinate label equivalence preserves addition. -/
private theorem quditQubitLabelEquiv_add {q : ℕ}
    (F : FixedFieldModel q) (L : ℕ) (a b : Fin L → F.K) :
    quditQubitLabelEquiv F L (a + b) =
      quditQubitLabelEquiv F L a + quditQubitLabelEquiv F L b := by
  ext p
  rcases p with ⟨i, j⟩
  change F.binaryCoordinates (a i + b i) j =
    F.binaryCoordinates (a i) j + F.binaryCoordinates (b i) j
  simp

/-- A shift observable is the permutation matrix for addition by its label. -/
private theorem tauObservable_X_apply
    {K ι : Type*} [Field K] [DecidableEq K]
    [Algebra (ZMod 2) K] [Fintype ι] [DecidableEq ι]
    (a x y : ι → K) :
    tauObservable .X a x y = if x = y + a then 1 else 0 := by
  change (∏ i : ι, if x i = y i + a i then 1 else 0) = _
  rw [Fintype.prod_boole]
  have hsupport : (∀ i, x i = y i + a i) ↔ x = y + a := by
    simpa only [Pi.add_apply] using
      (funext_iff (f := x) (g := y + a)).symm
  simp only [hsupport]

/-- A phase observable is diagonal, with its phase given by the trace pairing. -/
private theorem tauObservable_Z_apply
    {K ι : Type*} [Field K] [DecidableEq K]
    [Algebra (ZMod 2) K] [Fintype ι] [DecidableEq ι]
    (a x y : ι → K) :
    tauObservable .Z a x y =
      if x = y then phaseSign (binTrace K (dotProduct a y)) else 0 := by
  change
    (∏ i : ι,
      if x i = y i then phaseSign (binTrace K (a i * y i)) else 0) = _
  rw [Fintype.prod_ite_zero, prod_phaseSign_binTrace_dotProduct]
  have hsupport : (∀ i, x i = y i) ↔ x = y :=
    (funext_iff (f := x) (g := y)).symm
  simp only [hsupport]

/-- Binary-coordinate relabeling transports both generalized Pauli observables. -/
private theorem tauObservable_reindex_quditQubitLabelEquiv
    {q : ℕ} (F : FixedFieldModel q) (L : ℕ)
    (W : PauliKind) (a : Fin L → F.K) :
    tauObservable W a =
      Matrix.reindex (quditQubitLabelEquiv F L).symm
        (quditQubitLabelEquiv F L).symm
        (tauObservable W (quditQubitLabelEquiv F L a)) := by
  classical
  ext x y
  simp only [Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_symm]
  cases W with
  | X =>
      rw [tauObservable_X_apply, tauObservable_X_apply]
      have hadd := quditQubitLabelEquiv_add F L y a
      rw [← hadd]
      by_cases hshift : x = y + a
      · rw [if_pos hshift, if_pos]
        exact congrArg (quditQubitLabelEquiv F L) hshift
      · rw [if_neg hshift, if_neg]
        exact fun h => hshift ((quditQubitLabelEquiv F L).injective h)
  | Z =>
      rw [tauObservable_Z_apply, tauObservable_Z_apply]
      by_cases hxy : x = y
      · subst y
        rw [if_pos rfl, if_pos rfl,
          binTrace_dotProduct_eq_quditQubitLabelEquiv,
          quditQubitLabelEquiv_eq_kappaVec F L a,
          quditQubitLabelEquiv_eq_kappaVec F L x]
      · have hlabels : quditQubitLabelEquiv F L x ≠
            quditQubitLabelEquiv F L y := fun h =>
          hxy ((quditQubitLabelEquiv F L).injective h)
        rw [if_neg hxy, if_neg hlabels]

/-- Fourier inversion transports the Pauli projectors along the binary label
equivalence. -/
private theorem pauliProj_reindex_quditQubitLabelEquiv
    {q : ℕ} (F : FixedFieldModel q) (L : ℕ)
    (W : PauliKind) (u : Fin L → F.K) :
    pauliProj W u =
      Matrix.reindex (quditQubitLabelEquiv F L).symm
        (quditQubitLabelEquiv F L).symm
        (pauliProj W (kappaVec F u)) := by
  classical
  rw [pauliProj_eq_avg_tauObservable, pauliProj_eq_avg_tauObservable]
  ext x y
  simp only [Matrix.smul_apply, Matrix.sum_apply, smul_eq_mul,
    Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_symm]
  rw [Fintype.card_congr (quditQubitLabelEquiv F L)]
  congr 1
  apply Fintype.sum_equiv (quditQubitLabelEquiv F L)
  intro a
  have hphase := congrArg phaseSign
    (binTrace_dotProduct_eq_quditQubitLabelEquiv F L a u)
  have hentry := congrFun
    (congrFun (tauObservable_reindex_quditQubitLabelEquiv F L W a) x) y
  simp only [Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_symm] at hentry
  rw [hphase, hentry]

/-- The tensor product of binary Pauli projectors, obtained by specializing
`pauliProj` to `ZMod 2`. This is the binary target in `lem:pauli-binary`,
blueprint `ch11_qpbt_algebra.tex:710-741`, paper
`references/qpbt-paper/04_preliminaries.tex:1163-1208`. -/
noncomputable abbrev qubitPauliProj {ι : Type*} [Fintype ι] [DecidableEq ι]
    (W : PauliKind) (b : ι → ZMod 2) : Op (ι → ZMod 2) :=
  pauliProj W b

/-- `lem:pauli-binary`: the fixed binary coordinates induce an isometry that
maps EPR states and generalized Pauli projectors to their qubit forms.
Blueprint `ch11_qpbt_algebra.tex:710-741`, paper
`references/qpbt-paper/04_preliminaries.tex:1163-1208`.

**Local fix:** The source's final factor index is printed as
`j ∈ {1, ..., q}`; the basis expansion at paper lines 1191--1194 shows that
the intended range has `basisDim = log₂ q` entries. This correction is
documented in `rem:pauli-binary-source` and issue #16. -/
theorem exists_qubitIsometry (q : ℕ) (F : FixedFieldModel q) (L : ℕ) :
    ∃ φ : EuclideanSpace ℂ (Fin L → F.K) ≃ₗᵢ[ℂ]
        EuclideanSpace ℂ (Fin L × Fin F.basisDim → ZMod 2),
      isometryTensor φ.toLinearIsometry φ.toLinearIsometry
          (eprState (Fin L → F.K)) =
          eprState (Fin L × Fin F.basisDim → ZMod 2) ∧
        ∀ (W : PauliKind) (u : Fin L → F.K),
          pauliProj W u =
            conjIsometry φ.symm.toLinearIsometry
              (qubitPauliProj W (kappaVec F u)) := by
  let e := quditQubitLabelEquiv F L
  let φ := LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ e
  refine ⟨φ, isometryTensor_piLpCongrLeft_epr e, ?_⟩
  intro W u
  rw [conjIsometry_piLpCongrLeft_symm]
  exact pauliProj_reindex_quditQubitLabelEquiv F L W u

end MIPStarRE.QPBT
