import MIPStarRE.QPBT.Algebra.PauliTheorems
import MIPStarRE.QPBT.Test.MagicSquareTheorems
import MIPStarRE.QPBT.Test.PauliBasisTest

/-!
# The honest Pauli basis measurements of the completeness proof

This module builds the measurements used by the honest strategy of
`lem:pauli-completeness`: the generalized Pauli basis measurement in a fixed
basis `W`, and its coarse-graining by the binary trace
`h ↦ tr(g_h(u_W) r_W)` which the source calls `A` (for `W = X`) and `B`
(for `W = Z`).  The main results are the observable identity

  `A_0 - A_1 = τ^W(ind_m(u_W) r_W)`

of `eq:finally-got-an-observable`, and the resulting commutation law

  `𝒪_A 𝒪_B = (-1)^γ 𝒪_B 𝒪_A`

with `γ` the phase bit `eq:gamma-value`.  When `γ ≠ 0` the two observables
anticommute, so `thm:ms-from-ac` produces the Magic Square part of the honest
strategy.

## References

The construction is the strategy displayed in the proof of
`lem:pauli-completeness`,
`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:1290-1360`;
blueprint `blueprint/src/chapter/ch13_qpbt_test.tex:390-395`.
-/

open scoped BigOperators Matrix MatrixOrder ComplexOrder

namespace MIPStarRE.QPBT

open MIPStarRE.LDT MIPStarRE.Quantum

noncomputable section

variable {K ι : Type*} [Field K] [Fintype K] [DecidableEq K] [Algebra (ZMod 2) K]
  [Fintype ι] [DecidableEq ι]

/-! ### The generalized Pauli basis measurement -/

/-- The generalized Pauli observable at the zero label is the identity.  This is
the normalization implicit in `def:generalized-pauli`, blueprint
`blueprint/src/chapter/ch11_qpbt_algebra.tex:529-571`, paper origin
`references/qpbt-paper/04_preliminaries.tex:1052-1096`. -/
theorem tauObservable_zero (W : PauliKind) :
    tauObservable W (0 : ι → K) = 1 := by
  have hmul := tauObservable_mul W (0 : ι → K) 0
  rw [add_zero, tauObservable_sq] at hmul
  exact hmul.symm

/-- Every generalized Pauli projector is positive semidefinite: it is the
rank-one projector onto the corresponding basis vector of
`def:generalized-pauli`, blueprint `ch11_qpbt_algebra.tex:529-571`, paper origin
`references/qpbt-paper/04_preliminaries.tex:1101-1122`. -/
theorem pauliProj_posSemidef (W : PauliKind) (e : ι → K) :
    (pauliProj W e).PosSemidef :=
  Matrix.posSemidef_vecMulVec_self_star (pauliVec W e)

/-- Every generalized Pauli projector is a nonnegative operator. -/
theorem pauliProj_nonneg (W : PauliKind) (e : ι → K) : 0 ≤ pauliProj W e :=
  Matrix.nonneg_iff_posSemidef.mpr (pauliProj_posSemidef W e)

/-- Every generalized Pauli projector is Hermitian. -/
theorem pauliProj_conjTranspose (W : PauliKind) (e : ι → K) :
    (pauliProj W e)ᴴ = pauliProj W e :=
  (pauliProj_posSemidef W e).isHermitian.eq

/-- The generalized Pauli projectors in a fixed basis form a resolution of the
identity.  This is the completeness half of `def:generalized-pauli`, blueprint
`ch11_qpbt_algebra.tex:529-571`, paper origin
`references/qpbt-paper/04_preliminaries.tex:1101-1122`. -/
theorem sum_pauliProj (W : PauliKind) :
    ∑ e : ι → K, pauliProj W e = 1 := by
  have h := tauObservable_eq_sum_pauliProj (K := K) (ι := ι) W 0
  rw [tauObservable_zero] at h
  refine Eq.trans (Finset.sum_congr rfl fun e _ => ?_) h.symm
  have hzero : dotProduct (0 : ι → K) e = 0 := by simp
  simp [hzero, phaseSign]

/-- The generalized Pauli basis measurement in basis `W`: the projective
measurement whose outcomes are the labels of `def:generalized-pauli`, blueprint
`blueprint/src/chapter/ch11_qpbt_algebra.tex:529-571`, paper origin
`references/qpbt-paper/04_preliminaries.tex:1101-1122`. -/
noncomputable def pauliBasisMeasurement (W : PauliKind) :
    Measurement (ι → K) (ι → K) :=
  Measurement.ofSumEqOne (pauliProj W) (pauliProj_nonneg W) (sum_pauliProj W)

@[simp] theorem pauliBasisMeasurement_effect (W : PauliKind) (e : ι → K) :
    (pauliBasisMeasurement W).effect e = pauliProj W e := rfl

/-! ### Symmetry and Hermiticity of the generalized Pauli observables -/

/-- Formalization-only auxiliary: the binary sign character is real. -/
private theorem star_phaseSign' (t : ZMod 2) : star (phaseSign t) = phaseSign t := by
  by_cases ht : t = 0 <;> simp [phaseSign, ht]

omit [Fintype K] in
/-- Generalized Pauli observables are symmetric matrices in the computational
basis.  Symmetry is what makes the honest measurements consistent on the EPR
state used by `lem:pauli-completeness`, paper
`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:1290-1360`. -/
theorem tauObservable_transpose (W : PauliKind) (a : ι → K) :
    (tauObservable W a)ᵀ = tauObservable W a := by
  haveI : CharP K 2 := (Algebra.charP_iff (ZMod 2) K 2).mp (ZMod.charP 2)
  have hswap : ∀ x y c : K, (x = y + c) ↔ (y = x + c) := by
    intro x y c
    constructor
    · rintro rfl
      rw [add_assoc, CharTwo.add_self_eq_zero, add_zero]
    · rintro rfl
      rw [add_assoc, CharTwo.add_self_eq_zero, add_zero]
  ext x y
  rw [Matrix.transpose_apply]
  cases W with
  | X =>
      refine Finset.prod_congr rfl fun i _ => ?_
      change (if y i = x i + a i then (1 : ℂ) else 0) = if x i = y i + a i then 1 else 0
      by_cases h : x i = y i + a i
      · rw [if_pos h, if_pos ((hswap _ _ _).mp h)]
      · rw [if_neg h, if_neg (fun hc => h ((hswap _ _ _).mp hc))]
  | Z =>
      refine Finset.prod_congr rfl fun i _ => ?_
      change (if y i = x i then phaseSign (binTrace K (a i * x i)) else 0) =
        if x i = y i then phaseSign (binTrace K (a i * y i)) else 0
      by_cases h : x i = y i
      · rw [h]
      · rw [if_neg h, if_neg (fun hc => h hc.symm)]

/-- Generalized Pauli observables are Hermitian.  This is the self-adjointness
of the observables `𝒪_A` and `𝒪_B` used in the proof of
`lem:pauli-completeness`, paper
`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:1290-1360`. -/
theorem tauObservable_conjTranspose (W : PauliKind) (a : ι → K) :
    (tauObservable W a)ᴴ = tauObservable W a := by
  rw [tauObservable_eq_sum_pauliProj, Matrix.conjTranspose_sum]
  refine Finset.sum_congr rfl fun e _ => ?_
  rw [Matrix.conjTranspose_smul, star_phaseSign', pauliProj_conjTranspose]

/-- The generalized Pauli projectors are symmetric matrices, being real linear
combinations of the symmetric generalized Pauli observables. -/
theorem pauliProj_transpose (W : PauliKind) (e : ι → K) :
    (pauliProj W e)ᵀ = pauliProj W e := by
  rw [pauliProj_eq_avg_tauObservable, Matrix.transpose_smul, Matrix.transpose_sum]
  congr 1
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Matrix.transpose_smul, tauObservable_transpose]

/-! ### Orthogonality of the generalized Pauli projectors

The generalized Pauli projectors in a fixed basis are pairwise orthogonal, so
every coarse-graining of a Pauli basis measurement is again projective.  This is
the projectivity used throughout the honest strategy of `lem:pauli-completeness`,
paper `references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:1364-1370`.
-/

/-- Formalization-only auxiliary: the binary sign character is multiplicative.
It is derived here from the public `phaseSign_sum`. -/
private theorem phaseSign_add' (s t : ZMod 2) :
    phaseSign (s + t) = phaseSign s * phaseSign t := by
  have h := phaseSign_sum (ι := Fin 2) ![s, t]
  simpa [Fin.sum_univ_two, Fin.prod_univ_two] using h

omit [Fintype K] [DecidableEq K] in
/-- Formalization-only auxiliary: the binary sign character on `K` is the
canonical additive character of the finite field. -/
private theorem phaseSign_binTrace_eq_ffChar (y : K) :
    phaseSign (binTrace K y) =
      MIPStarRE.LDT.Preliminaries.ffChar (p := 2) (F := K) y := by
  rw [phaseSign_eq_ffChar, MIPStarRE.LDT.Preliminaries.ffChar_apply]

/-- Formalization-only auxiliary: the scalar character sum over a finite field.
This is Fourier orthogonality `prop:fourier-fact-scalar` written multiplicatively
for the binary sign character. -/
private theorem sum_phaseSign_binTrace_mul (c : K) :
    ∑ x : K, phaseSign (binTrace K (x * c)) =
      if c = 0 then (Fintype.card K : ℂ) else 0 := by
  have hexp := MIPStarRE.LDT.Preliminaries.fourier_fact_scalar (p := 2) (F := K) c
  have hsum : ∑ x : K, MIPStarRE.LDT.Preliminaries.ffChar (p := 2) (F := K) (x * c) =
      (Fintype.card K) • (if c = 0 then (1 : ℂ) else 0) := by
    rw [← hexp]
    exact (Fintype.card_smul_expect _).symm
  calc ∑ x : K, phaseSign (binTrace K (x * c))
      = ∑ x : K, MIPStarRE.LDT.Preliminaries.ffChar (p := 2) (F := K) (x * c) :=
        Finset.sum_congr rfl fun x _ => phaseSign_binTrace_eq_ffChar _
    _ = (Fintype.card K) • (if c = 0 then (1 : ℂ) else 0) := hsum
    _ = if c = 0 then (Fintype.card K : ℂ) else 0 := by
        by_cases hc : c = 0 <;> simp [hc]

/-- Formalization-only auxiliary: the vector character sum over a finite field,
obtained from the scalar case by factorizing the trace pairing. -/
private theorem sum_phaseSign_binTrace_dotProduct (v : ι → K) :
    ∑ a : ι → K, phaseSign (binTrace K (dotProduct a v)) =
      if v = 0 then (Fintype.card (ι → K) : ℂ) else 0 := by
  have hfactor : ∏ i : ι, ∑ x : K, phaseSign (binTrace K (x * v i)) =
      ∑ a : ι → K, phaseSign (binTrace K (dotProduct a v)) := by
    rw [Finset.prod_univ_sum, Fintype.piFinset_univ]
    exact Finset.sum_congr rfl fun a _ => prod_phaseSign_binTrace_dotProduct a v
  rw [← hfactor]
  by_cases hv : v = 0
  · subst hv
    rw [if_pos rfl, Fintype.card_fun]
    have hterm : ∀ i : ι, ∑ x : K, phaseSign (binTrace K (x * (0 : ι → K) i)) =
        (Fintype.card K : ℂ) := fun i => by simp [phaseSign]
    rw [Finset.prod_congr rfl fun i _ => hterm i, Finset.prod_const, Finset.card_univ]
    push_cast
    ring
  · obtain ⟨i₀, hi₀⟩ : ∃ i : ι, v i ≠ 0 := by
      by_contra hcon
      exact hv (funext fun i => not_not.mp (fun h => hcon ⟨i, h⟩))
    rw [if_neg hv]
    refine Finset.prod_eq_zero (Finset.mem_univ i₀) ?_
    rw [sum_phaseSign_binTrace_mul, if_neg hi₀]

/-- A generalized Pauli observable acts on a generalized Pauli projector of the
same basis by the character value of its label.  This is the eigenvalue relation
implicit in `lem:pauli-observable-expansion`, blueprint
`blueprint/src/chapter/ch11_qpbt_algebra.tex:674-688`, paper origin
`references/qpbt-paper/04_preliminaries.tex:1151-1161`. -/
theorem tauObservable_mul_pauliProj (W : PauliKind) (a f : ι → K) :
    tauObservable W a * pauliProj W f =
      phaseSign (binTrace K (dotProduct a f)) • pauliProj W f := by
  haveI : CharP K 2 := (Algebra.charP_iff (ZMod 2) K 2).mp (ZMod.charP 2)
  have hchar2 : ∀ x : ι → K, a + (a + x) = x := by
    intro x
    funext i
    simp [← add_assoc, CharTwo.add_self_eq_zero]
  calc tauObservable W a * pauliProj W f
      = (Fintype.card (ι → K) : ℂ)⁻¹ •
          ∑ b : ι → K,
            phaseSign (binTrace K (dotProduct b f)) • tauObservable W (a + b) := by
        rw [pauliProj_eq_avg_tauObservable, Matrix.mul_smul, Matrix.mul_sum]
        congr 1
        refine Finset.sum_congr rfl fun b _ => ?_
        rw [Matrix.mul_smul, tauObservable_mul]
    _ = (Fintype.card (ι → K) : ℂ)⁻¹ •
          ∑ c : ι → K,
            phaseSign (binTrace K (dotProduct (a + c) f)) • tauObservable W c := by
        congr 1
        refine Fintype.sum_equiv (Equiv.addLeft a) _ _ fun b => ?_
        change phaseSign (binTrace K (dotProduct b f)) • tauObservable W (a + b) =
          phaseSign (binTrace K (dotProduct (a + (a + b)) f)) • tauObservable W (a + b)
        rw [hchar2 b]
    _ = phaseSign (binTrace K (dotProduct a f)) • pauliProj W f := by
        rw [pauliProj_eq_avg_tauObservable (W := W) (e := f)]
        simp only [Finset.smul_sum, smul_smul]
        refine Finset.sum_congr rfl fun c _ => ?_
        congr 1
        rw [add_dotProduct, map_add, phaseSign_add']
        ring

/-- The generalized Pauli projectors of a fixed basis are pairwise orthogonal
idempotents.  This is the orthogonality half of `def:generalized-pauli`,
blueprint `blueprint/src/chapter/ch11_qpbt_algebra.tex:529-571`, paper origin
`references/qpbt-paper/04_preliminaries.tex:1101-1122`. -/
theorem pauliProj_mul_pauliProj (W : PauliKind) (e f : ι → K) :
    pauliProj W e * pauliProj W f = if e = f then pauliProj W e else 0 := by
  haveI : CharP K 2 := (Algebra.charP_iff (ZMod 2) K 2).mp (ZMod.charP 2)
  have hzero : ∀ x y : ι → K, x + y = 0 ↔ x = y := by
    intro x y
    constructor
    · intro h
      funext i
      have hi : x i + y i = 0 := congrFun h i
      exact CharTwo.add_eq_zero.mp hi
    · rintro rfl
      funext i
      simp [CharTwo.add_self_eq_zero]
  have hcard : (Fintype.card (ι → K) : ℂ) ≠ 0 := by positivity
  calc pauliProj W e * pauliProj W f
      = (Fintype.card (ι → K) : ℂ)⁻¹ •
          ∑ a : ι → K,
            (phaseSign (binTrace K (dotProduct a (e + f)))) • pauliProj W f := by
        rw [pauliProj_eq_avg_tauObservable (W := W) (e := e), Matrix.smul_mul,
          Finset.sum_mul]
        congr 1
        refine Finset.sum_congr rfl fun a _ => ?_
        rw [Matrix.smul_mul, tauObservable_mul_pauliProj, smul_smul, ← phaseSign_add',
          ← map_add, ← dotProduct_add]
    _ = ((Fintype.card (ι → K) : ℂ)⁻¹ *
          ∑ a : ι → K, phaseSign (binTrace K (dotProduct a (e + f)))) • pauliProj W f := by
        rw [← Finset.sum_smul, smul_smul]
    _ = if e = f then pauliProj W e else 0 := by
        rw [sum_phaseSign_binTrace_dotProduct]
        by_cases hef : e = f
        · rw [if_pos ((hzero e f).mpr hef), if_pos hef, inv_mul_cancel₀ hcard, one_smul, hef]
        · rw [if_neg (fun h => hef ((hzero e f).mp h)), if_neg hef, mul_zero, zero_smul]

/-- Every generalized Pauli projector is a projector. -/
theorem pauliProj_isProj (W : PauliKind) (e : ι → K) : IsProj (pauliProj W e) := by
  refine isStarProjection_iff'.2 ⟨?_, ?_⟩
  · simpa using pauliProj_mul_pauliProj W e e
  · rw [Matrix.star_eq_conjTranspose, pauliProj_conjTranspose]

/-- Every coarse-graining of a generalized Pauli basis measurement is
projective.  This is the projectivity of the honest Point, Line and Pauli
measurements in the proof of `lem:pauli-completeness`, paper
`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:1364-1370`. -/
theorem pauliBasisMeasurement_postprocess_projective {β : Type*} [Fintype β]
    [DecidableEq β] (W : PauliKind) (g : (ι → K) → β) :
    MIPStarRE.QPBT.Measurement.IsProjective ((pauliBasisMeasurement W).postprocess g) := by
  classical
  intro b
  rw [Measurement.postprocess_effect]
  refine isStarProjection_iff'.2 ⟨?_, ?_⟩
  · rw [Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun e he => ?_
    have hterm : ∀ f ∈ Finset.univ.filter (fun a : ι → K => g a = b),
        (pauliBasisMeasurement W).effect e * (pauliBasisMeasurement W).effect f =
          if e = f then pauliProj W e else 0 :=
      fun f _ => pauliProj_mul_pauliProj W e f
    rw [Finset.sum_congr rfl hterm,
      Finset.sum_ite_eq_of_mem _ e (fun _ => pauliProj W e) he]
    rfl
  · rw [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_sum]
    refine Finset.sum_congr rfl fun e _ => ?_
    exact pauliProj_conjTranspose W e

/-- Every coarse-graining of a generalized Pauli basis measurement has symmetric
effects, hence is consistent on the EPR state.  This is the consistency of the
honest Point, Line and Pauli measurements in the proof of
`lem:pauli-completeness`, paper
`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:1368-1372`. -/
theorem pauliBasisMeasurement_postprocess_isConsistentOn {β : Type*} [Fintype β]
    [DecidableEq β] [Nonempty ι] (W : PauliKind) (g : (ι → K) → β) :
    MIPStarRE.QPBT.Measurement.IsConsistentOn ((pauliBasisMeasurement W).postprocess g)
      (eprState (ι → K)) := by
  classical
  intro b
  refine epr_action_eq_of_transpose _ ?_
  rw [Measurement.postprocess_effect, Matrix.transpose_sum]
  refine Finset.sum_congr rfl fun e _ => ?_
  exact pauliProj_transpose W e

/-! ### The honest Pair/W measurements

For an ambient question `ω = (u_X, u_Z, r_X, r_Z)` the honest player measures
the Pauli register in basis `W` and reports the binary trace
`tr(g_h(u_W) r_W)` of the resulting label.  These are the measurements `A` and
`B` of the proof of `lem:pauli-completeness`,
`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:1290-1330`.
-/

/-- The binary trace bit `tr(g_h(u) r)` reported by the honest Pair/W
measurement on the Pauli label `h`.  Paper
`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:1290-1330`. -/
noncomputable def pauliTraceBit (P : AdmissibleParams)
    (u : Fin P.m → PauliScalar P) (r : PauliScalar P) (h : PauliRegister P) : ZMod 2 :=
  fixedBinTrace P.model (lowDegreeEnc h u * r)

/-- The honest Pair/W measurement `τ^W_{[tr(g_·(u) r) = β]}` of the proof of
`lem:pauli-completeness`: the generalized Pauli basis measurement coarse-grained
by the trace bit.  Paper
`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:1290-1330`,
blueprint `blueprint/src/chapter/ch13_qpbt_test.tex:390-395`. -/
noncomputable def pauliTraceMeasurement (P : AdmissibleParams) (W : PauliKind)
    (u : Fin P.m → PauliScalar P) (r : PauliScalar P) :
    Measurement (ZMod 2) (PauliRegister P) :=
  (pauliBasisMeasurement W).postprocess (pauliTraceBit P u r)

theorem pauliTraceMeasurement_effect (P : AdmissibleParams) (W : PauliKind)
    (u : Fin P.m → PauliScalar P) (r : PauliScalar P) (b : ZMod 2) :
    (pauliTraceMeasurement P W u r).effect b =
      ∑ h ∈ Finset.univ.filter (fun h : PauliRegister P => pauliTraceBit P u r h = b),
        pauliProj W h := rfl

/-- Equation `eq:finally-got-an-observable`: the observable of the honest
Pair/W measurement is the generalized Pauli observable at the label
`ind_m(u) r`.  Paper
`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:1300-1315`. -/
theorem obsOf_pauliTraceMeasurement (P : AdmissibleParams) (W : PauliKind)
    (u : Fin P.m → PauliScalar P) (r : PauliScalar P) :
    obsOf (pauliTraceMeasurement P W u r) =
      tauObservable W (r • indicatorVec u) := by
  classical
  have hdot : ∀ e : PauliRegister P,
      dotProduct (r • indicatorVec u) e = lowDegreeEnc e u * r := by
    intro e
    rw [lowDegreeEnc_eq_dotProduct]
    simp only [dotProduct, Finset.sum_mul, Pi.smul_apply, smul_eq_mul]
    exact Finset.sum_congr rfl fun y _ => by ring
  have hp : ∀ e : PauliRegister P,
      phaseSign (binTrace (PauliScalar P) (dotProduct (r • indicatorVec u) e)) =
        phaseSign (pauliTraceBit P u r e) := by
    intro e
    rw [hdot e]
    rfl
  rw [tauObservable_eq_sum_pauliProj,
    Finset.sum_congr rfl (fun e (_ : e ∈ Finset.univ) => by rw [hp e]),
    ← Finset.sum_filter_add_sum_filter_not (Finset.univ : Finset (PauliRegister P))
      (fun e => pauliTraceBit P u r e = 0)]
  have hfilter :
      (Finset.univ.filter fun e : PauliRegister P => ¬ pauliTraceBit P u r e = 0) =
        Finset.univ.filter fun e : PauliRegister P => pauliTraceBit P u r e = 1 := by
    ext e
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rcases zmod_two_eq_zero_or_one (pauliTraceBit P u r e) with h | h <;> simp [h]
  have h0 : ∑ e ∈ Finset.univ.filter (fun e : PauliRegister P => pauliTraceBit P u r e = 0),
      phaseSign (pauliTraceBit P u r e) • pauliProj W e =
      (pauliTraceMeasurement P W u r).effect 0 := by
    rw [pauliTraceMeasurement_effect]
    refine Finset.sum_congr rfl fun e he => ?_
    rw [(Finset.mem_filter.mp he).2]
    simp [phaseSign]
  have h1 : ∑ e ∈ Finset.univ.filter (fun e : PauliRegister P => ¬ pauliTraceBit P u r e = 0),
      phaseSign (pauliTraceBit P u r e) • pauliProj W e =
      -(pauliTraceMeasurement P W u r).effect 1 := by
    rw [hfilter, pauliTraceMeasurement_effect]
    calc ∑ e ∈ Finset.univ.filter (fun e : PauliRegister P => pauliTraceBit P u r e = 1),
          phaseSign (pauliTraceBit P u r e) • pauliProj W e
        = ∑ e ∈ Finset.univ.filter (fun e : PauliRegister P => pauliTraceBit P u r e = 1),
            (-1 : ℂ) • pauliProj W e :=
          Finset.sum_congr rfl fun e he => by
            rw [(Finset.mem_filter.mp he).2]
            norm_num [phaseSign]
      _ = (-1 : ℂ) • ∑ e ∈ Finset.univ.filter
            (fun e : PauliRegister P => pauliTraceBit P u r e = 1), pauliProj W e :=
          Finset.smul_sum.symm
      _ = _ := neg_one_smul ℂ _
  rw [h0, h1, ← sub_eq_add_neg]
  rfl

/-- Each effect of the honest Pair/W measurement is the spectral projector of
its observable, so the measurement is projective; part of the projectivity
assertion of the honest strategy in the proof of `lem:pauli-completeness`,
paper `references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:1364-1370`. -/
theorem pauliTraceMeasurement_effect_eq_reflectionEffect (P : AdmissibleParams)
    (W : PauliKind) (u : Fin P.m → PauliScalar P) (r : PauliScalar P) (b : ZMod 2) :
    (pauliTraceMeasurement P W u r).effect b =
      reflectionEffect (tauObservable W (r • indicatorVec u)) b := by
  rw [← obsOf_pauliTraceMeasurement, reflectionEffect_obsOf_measurement]

/-- The honest Pair/W measurement is projective, as asserted for the honest
strategy in the proof of `lem:pauli-completeness`, paper
`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:1364-1370`. -/
theorem pauliTraceMeasurement_projective (P : AdmissibleParams) (W : PauliKind)
    (u : Fin P.m → PauliScalar P) (r : PauliScalar P) :
    MIPStarRE.QPBT.Measurement.IsProjective (pauliTraceMeasurement P W u r) := by
  intro b
  rw [pauliTraceMeasurement_effect_eq_reflectionEffect]
  exact reflectionMeasurement_projective (tauObservable W (r • indicatorVec u))
    (tauObservable_conjTranspose W _) (tauObservable_sq W _) b

/-- The effects of the honest Pair/W measurement are symmetric matrices. -/
theorem pauliTraceMeasurement_effect_transpose (P : AdmissibleParams) (W : PauliKind)
    (u : Fin P.m → PauliScalar P) (r : PauliScalar P) (b : ZMod 2) :
    ((pauliTraceMeasurement P W u r).effect b)ᵀ =
      (pauliTraceMeasurement P W u r).effect b := by
  rw [pauliTraceMeasurement_effect_eq_reflectionEffect]
  rcases zmod_two_eq_zero_or_one b with rfl | rfl
  · simp only [reflectionEffect, if_pos]
    rw [Matrix.transpose_smul, Matrix.transpose_add, Matrix.transpose_one,
      tauObservable_transpose]
  · simp only [reflectionEffect, if_neg one_ne_zero]
    rw [Matrix.transpose_smul, Matrix.transpose_sub, Matrix.transpose_one,
      tauObservable_transpose]

/-- The honest Pair/W measurement is consistent on the EPR state, because its
effects are symmetric matrices.  This is the consistency assertion for the
Pauli basis measurements in the proof of `lem:pauli-completeness`, paper
`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:1364-1372`. -/
theorem pauliTraceMeasurement_isConsistentOn (P : AdmissibleParams) (W : PauliKind)
    (u : Fin P.m → PauliScalar P) (r : PauliScalar P) :
    MIPStarRE.QPBT.Measurement.IsConsistentOn (pauliTraceMeasurement P W u r)
      (eprState (PauliRegister P)) := fun b =>
  epr_action_eq_of_transpose _ (pauliTraceMeasurement_effect_transpose P W u r b)

/-! ### The honest Point/W measurements -/

/-- The honest Point/W measurement: the generalized Pauli basis measurement
coarse-grained by the value `g_h(u)` of the low-degree encoding at the point
`u`.  Paper
`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:1290-1300`. -/
noncomputable def pauliPointMeasurement (P : AdmissibleParams) (W : PauliKind)
    (u : Fin P.m → PauliScalar P) : Measurement (PauliScalar P) (PauliRegister P) :=
  (pauliBasisMeasurement W).postprocess (fun h => lowDegreeEnc h u)

/-- The honest Point/W measurement is projective. -/
theorem pauliPointMeasurement_projective (P : AdmissibleParams) (W : PauliKind)
    (u : Fin P.m → PauliScalar P) :
    MIPStarRE.QPBT.Measurement.IsProjective (pauliPointMeasurement P W u) :=
  pauliBasisMeasurement_postprocess_projective W _

/-- The honest Point/W measurement is consistent on the EPR state. -/
theorem pauliPointMeasurement_isConsistentOn (P : AdmissibleParams) (W : PauliKind)
    (u : Fin P.m → PauliScalar P) :
    MIPStarRE.QPBT.Measurement.IsConsistentOn (pauliPointMeasurement P W u)
      (eprState (PauliRegister P)) :=
  pauliBasisMeasurement_postprocess_isConsistentOn W _

/-- The Point/W measurement coarse-grained by the trace against `r` is the
Pair/W measurement.  This is the displayed identity
`E^{(Point,W),y}_{[tr(· r_W) = a]} = E^{(Pair,W),ω}_a` used twice in the
value-one argument of `lem:pauli-completeness`, paper
`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:1396-1420`. -/
theorem pauliPointMeasurement_postprocess_trace_effect (P : AdmissibleParams)
    (W : PauliKind) (u : Fin P.m → PauliScalar P) (r : PauliScalar P) (b : ZMod 2) :
    ((pauliPointMeasurement P W u).postprocess
        (fun a => fixedBinTrace P.model (a * r))).effect b =
      (pauliTraceMeasurement P W u r).effect b := by
  have hmaps : ∀ h ∈ Finset.univ.filter
      (fun h : PauliRegister P => pauliTraceBit P u r h = b),
      lowDegreeEnc h u ∈ Finset.univ.filter
        (fun a : PauliScalar P => fixedBinTrace P.model (a * r) = b) := fun h hh =>
    Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hh).2⟩
  have hinner : ∀ a ∈ Finset.univ.filter
      (fun a : PauliScalar P => fixedBinTrace P.model (a * r) = b),
      (Finset.univ.filter fun h : PauliRegister P => lowDegreeEnc h u = a) =
        (Finset.univ.filter fun h : PauliRegister P =>
          pauliTraceBit P u r h = b).filter fun h => lowDegreeEnc h u = a := by
    intro a ha
    ext h
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · intro hh
      refine ⟨?_, hh⟩
      change fixedBinTrace P.model (lowDegreeEnc h u * r) = b
      rw [hh]
      exact (Finset.mem_filter.mp ha).2
    · exact fun hh => hh.2
  calc ((pauliPointMeasurement P W u).postprocess
        (fun a => fixedBinTrace P.model (a * r))).effect b
      = ∑ a ∈ Finset.univ.filter
          (fun a : PauliScalar P => fixedBinTrace P.model (a * r) = b),
          ∑ h ∈ Finset.univ.filter (fun h : PauliRegister P => lowDegreeEnc h u = a),
            pauliProj W h := rfl
    _ = ∑ a ∈ Finset.univ.filter
          (fun a : PauliScalar P => fixedBinTrace P.model (a * r) = b),
          ∑ h ∈ (Finset.univ.filter fun h : PauliRegister P =>
              pauliTraceBit P u r h = b).filter (fun h => lowDegreeEnc h u = a),
            pauliProj W h :=
        Finset.sum_congr rfl fun a ha => by rw [hinner a ha]
    _ = ∑ h ∈ Finset.univ.filter (fun h : PauliRegister P => pauliTraceBit P u r h = b),
          pauliProj W h := Finset.sum_fiberwise_of_maps_to hmaps _
    _ = (pauliTraceMeasurement P W u r).effect b := rfl

/-! ### The commutation law of the honest pair -/

/-- The commutation law `𝒪_A 𝒪_B = (-1)^γ 𝒪_B 𝒪_A` of the proof of
`lem:pauli-completeness`, with `γ` the phase bit `eq:gamma-value`.  Paper
`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:1316-1330`. -/
theorem obsOf_pauliTraceMeasurement_mul_comm (P : AdmissibleParams) (z : PauliSpace P) :
    obsOf (pauliTraceMeasurement P .X (pauliXBlock z) (pauliRXBlock z)) *
        obsOf (pauliTraceMeasurement P .Z (pauliZBlock z) (pauliRZBlock z)) =
      phaseSign (pauliPairGamma P z) •
        (obsOf (pauliTraceMeasurement P .Z (pauliZBlock z) (pauliRZBlock z)) *
          obsOf (pauliTraceMeasurement P .X (pauliXBlock z) (pauliRXBlock z))) := by
  rw [obsOf_pauliTraceMeasurement, obsOf_pauliTraceMeasurement, tauObservable_X_mul_Z]
  rfl

/-- If the phase bit `γ` of `eq:gamma-value` is nonzero, the two honest Pair/W
observables anticommute.  Paper
`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:1316-1330`. -/
theorem obsOf_pauliTraceMeasurement_anticommute (P : AdmissibleParams)
    (z : PauliSpace P) (hgamma : pauliPairGamma P z ≠ 0) :
    obsOf (pauliTraceMeasurement P .X (pauliXBlock z) (pauliRXBlock z)) *
        obsOf (pauliTraceMeasurement P .Z (pauliZBlock z) (pauliRZBlock z)) =
      -(obsOf (pauliTraceMeasurement P .Z (pauliZBlock z) (pauliRZBlock z)) *
        obsOf (pauliTraceMeasurement P .X (pauliXBlock z) (pauliRXBlock z))) := by
  rw [obsOf_pauliTraceMeasurement_mul_comm]
  rcases zmod_two_eq_zero_or_one (pauliPairGamma P z) with h | h
  · exact absurd h hgamma
  · rw [h]
    simp [phaseSign]

/-- The Magic Square part of the honest strategy in the case `γ ≠ 0`: the two
honest Pair/W measurements anticommute, so `thm:ms-from-ac` supplies a
value-one SPCC Magic Square strategy whose first and fifth variable
measurements are the honest Pair/X and Pair/Z measurements.  Paper
`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:1345-1355`,
blueprint `blueprint/src/chapter/ch13_qpbt_test.tex:390-395`. -/
theorem exists_ms_perfect_strategy_of_pauliPairGamma_ne_zero (P : AdmissibleParams)
    (z : PauliSpace P) (hgamma : pauliPairGamma P z ≠ 0) :
    ∃ S : SymmetricStrategy msGameSymm, ∃ hι : S.ι = (PauliRegister P × ZMod 2),
      S.IsSPCC ∧ S.toStrategy.value = 1 ∧
      reindexState (Equiv.prodCongr (Equiv.cast hι) (Equiv.cast hι)) S.ψ =
        msPerfectState (PauliRegister P) ∧
      ∀ b : ZMod 2,
        reindexOp (Equiv.cast hι.symm) ((S.M (.var 0)).effect (.bit b)) =
            heteroKron
              ((pauliTraceMeasurement P .X (pauliXBlock z) (pauliRXBlock z)).effect b)
              (1 : Op (ZMod 2)) ∧
          reindexOp (Equiv.cast hι.symm) ((S.M (.var 4)).effect (.bit b)) =
            heteroKron
              ((pauliTraceMeasurement P .Z (pauliZBlock z) (pauliRZBlock z)).effect b)
              (1 : Op (ZMod 2)) := by
  haveI : Nonempty (PauliRegister P) := ⟨0⟩
  exact exists_ms_perfect_strategy_of_anticommuting
    (pauliTraceMeasurement P .X (pauliXBlock z) (pauliRXBlock z))
    (pauliTraceMeasurement P .Z (pauliZBlock z) (pauliRZBlock z))
    (pauliTraceMeasurement_projective P .X _ _)
    (pauliTraceMeasurement_projective P .Z _ _)
    (pauliTraceMeasurement_isConsistentOn P .X _ _)
    (pauliTraceMeasurement_isConsistentOn P .Z _ _)
    (obsOf_pauliTraceMeasurement_anticommute P z hgamma)

/-! ### The Pair measurement in the case `γ = 0`

If the phase bit vanishes, the two honest Pair/W measurements commute and their
product is the Pair measurement `E^{Pair,ω}_{β_X, β_Z} = A_{β_X} B_{β_Z}` of
Equation `eq:pair-definition` in the proof of `lem:pauli-completeness`, paper
`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:1331-1344`.
-/

/-- If the phase bit `γ` of `eq:gamma-value` vanishes, the two honest Pair/W
observables commute.  Paper
`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:1316-1330`. -/
theorem obsOf_pauliTraceMeasurement_commute (P : AdmissibleParams)
    (z : PauliSpace P) (hgamma : pauliPairGamma P z = 0) :
    Commute (obsOf (pauliTraceMeasurement P .X (pauliXBlock z) (pauliRXBlock z)))
      (obsOf (pauliTraceMeasurement P .Z (pauliZBlock z) (pauliRZBlock z))) := by
  rw [commute_iff_eq, obsOf_pauliTraceMeasurement_mul_comm, hgamma]
  simp [phaseSign]

/-- If the phase bit `γ` vanishes, the effects of the two honest Pair/W
measurements commute; this is the commutation assertion of the honest strategy
in the case `γ = 0`, paper
`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:1374-1382`. -/
theorem pauliTraceMeasurement_effect_commute (P : AdmissibleParams)
    (z : PauliSpace P) (hgamma : pauliPairGamma P z = 0) (a b : ZMod 2) :
    Commute ((pauliTraceMeasurement P .X (pauliXBlock z) (pauliRXBlock z)).effect a)
      ((pauliTraceMeasurement P .Z (pauliZBlock z) (pauliRZBlock z)).effect b) := by
  have hOO :
      Commute (tauObservable PauliKind.X (pauliRXBlock z • indicatorVec (pauliXBlock z)))
        (tauObservable PauliKind.Z (pauliRZBlock z • indicatorVec (pauliZBlock z))) := by
    rw [← obsOf_pauliTraceMeasurement P .X (pauliXBlock z) (pauliRXBlock z),
      ← obsOf_pauliTraceMeasurement P .Z (pauliZBlock z) (pauliRZBlock z)]
    exact obsOf_pauliTraceMeasurement_commute P z hgamma
  rw [pauliTraceMeasurement_effect_eq_reflectionEffect,
    pauliTraceMeasurement_effect_eq_reflectionEffect]
  exact reflectionEffect_commute hOO a b

/-- The Pair effect `E^{Pair,ω}_{β_X, β_Z} = A_{β_X} B_{β_Z}` of Equation
`eq:pair-definition`, paper
`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:1331-1339`. -/
noncomputable def pauliPairEffect (P : AdmissibleParams) (z : PauliSpace P)
    (β : ZMod 2 × ZMod 2) : Op (PauliRegister P) :=
  (pauliTraceMeasurement P .X (pauliXBlock z) (pauliRXBlock z)).effect β.1 *
    (pauliTraceMeasurement P .Z (pauliZBlock z) (pauliRZBlock z)).effect β.2

/-- For `γ = 0` the Pair effects are projectors, being products of commuting
projectors.  Paper
`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:1331-1344`. -/
theorem pauliPairEffect_isProj (P : AdmissibleParams) (z : PauliSpace P)
    (hgamma : pauliPairGamma P z = 0) (β : ZMod 2 × ZMod 2) :
    IsProj (pauliPairEffect P z β) :=
  IsStarProjection.mul (pauliTraceMeasurement_projective P .X _ _ β.1)
    (pauliTraceMeasurement_projective P .Z _ _ β.2)
    (pauliTraceMeasurement_effect_commute P z hgamma β.1 β.2)

/-- The Pair effects sum to the identity. -/
theorem sum_pauliPairEffect (P : AdmissibleParams) (z : PauliSpace P) :
    ∑ β : ZMod 2 × ZMod 2, pauliPairEffect P z β = 1 := by
  calc ∑ β : ZMod 2 × ZMod 2, pauliPairEffect P z β
      = ∑ a : ZMod 2, ∑ b : ZMod 2,
          (pauliTraceMeasurement P .X (pauliXBlock z) (pauliRXBlock z)).effect a *
            (pauliTraceMeasurement P .Z (pauliZBlock z) (pauliRZBlock z)).effect b :=
        Fintype.sum_prod_type _
    _ = ∑ a : ZMod 2,
          (pauliTraceMeasurement P .X (pauliXBlock z) (pauliRXBlock z)).effect a *
            ∑ b : ZMod 2,
              (pauliTraceMeasurement P .Z (pauliZBlock z) (pauliRZBlock z)).effect b :=
        Finset.sum_congr rfl fun a _ => by rw [Finset.mul_sum]
    _ = 1 := by
        rw [(pauliTraceMeasurement P .Z (pauliZBlock z) (pauliRZBlock z)).sum_eq_one]
        simp [(pauliTraceMeasurement P .X (pauliXBlock z) (pauliRXBlock z)).sum_eq_one]

/-- The Pair measurement of Equation `eq:pair-definition` in the case `γ = 0`,
paper `references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:1331-1344`,
blueprint `blueprint/src/chapter/ch13_qpbt_test.tex:390-395`. -/
noncomputable def pauliPairMeasurement (P : AdmissibleParams) (z : PauliSpace P)
    (hgamma : pauliPairGamma P z = 0) : Measurement (ZMod 2 × ZMod 2) (PauliRegister P) :=
  Measurement.ofSumEqOne (pauliPairEffect P z)
    (fun β => (pauliPairEffect_isProj P z hgamma β).nonneg) (sum_pauliPairEffect P z)

/-- The Pair measurement is projective. -/
theorem pauliPairMeasurement_projective (P : AdmissibleParams) (z : PauliSpace P)
    (hgamma : pauliPairGamma P z = 0) :
    MIPStarRE.QPBT.Measurement.IsProjective (pauliPairMeasurement P z hgamma) :=
  pauliPairEffect_isProj P z hgamma

/-- The Pair measurement is consistent on the EPR state.  This is the
consistency assertion for the Pair measurement in the case `γ = 0`, paper
`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:1368-1372`. -/
theorem pauliPairMeasurement_isConsistentOn (P : AdmissibleParams) (z : PauliSpace P)
    (hgamma : pauliPairGamma P z = 0) :
    MIPStarRE.QPBT.Measurement.IsConsistentOn (pauliPairMeasurement P z hgamma)
      (eprState (PauliRegister P)) := by
  intro β
  refine epr_action_eq_of_transpose _ ?_
  change (pauliPairEffect P z β)ᵀ = pauliPairEffect P z β
  rw [pauliPairEffect, Matrix.transpose_mul, pauliTraceMeasurement_effect_transpose,
    pauliTraceMeasurement_effect_transpose]
  exact (pauliTraceMeasurement_effect_commute P z hgamma β.1 β.2).eq.symm

end

end MIPStarRE.QPBT
