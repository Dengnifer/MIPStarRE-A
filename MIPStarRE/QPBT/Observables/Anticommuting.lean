import MIPStarRE.QPBT.Test.PauliBasisTest

/-!
# Commuting and anticommuting Pauli tuples

This module defines the tuple phase used in the Pauli basis test and the
conditional uniform distributions used by its observable analysis.

## References

The definitions and probability bounds formalize `def:anticommuting-tuple`
and `fact:omega-anticomm-prob` in
`blueprint/src/chapter/ch14_qpbt_observables.tex:128-267`, with paper origin
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:64-95`.
-/

namespace MIPStarRE.QPBT

open MIPStarRE.LDT

noncomputable section

/-- A tuple `(u_X,u_Z,r_X,r_Z)` over the fixed field model of an admissible
Pauli-test parameter tuple. This is the tuple space of
`def:anticommuting-tuple`, blueprint `ch14_qpbt_observables.tex:128-148`, paper
`14_analysis_of_the_pauli_basis_test.tex:64-68`. -/
abbrev PauliTuple (P : AdmissibleParams) :=
  (Fin P.m → PauliScalar P) ×
    (Fin P.m → PauliScalar P) × PauliScalar P × PauliScalar P

/-- A Pauli tuple is anticommuting when its phase bit is nonzero. This is
`def:anticommuting-tuple`, blueprint `ch14_qpbt_observables.tex:128-148`, paper
`14_analysis_of_the_pauli_basis_test.tex:64-68`. -/
def IsAnticommuting {P : AdmissibleParams} (ω : PauliTuple P) : Prop :=
  gammaValue P ω.1 ω.2.1 ω.2.2.1 ω.2.2.2 ≠ 0

/-- A Pauli tuple is commuting when its phase bit vanishes. This is the
complementary case in `def:anticommuting-tuple`, blueprint
`ch14_qpbt_observables.tex:128-148`, paper
`14_analysis_of_the_pauli_basis_test.tex:64-68`. -/
def IsCommuting {P : AdmissibleParams} (ω : PauliTuple P) : Prop :=
  gammaValue P ω.1 ω.2.1 ω.2.2.1 ω.2.2.2 = 0

noncomputable instance (P : AdmissibleParams) :
    DecidablePred (@IsAnticommuting P) := Classical.decPred _

noncomputable instance (P : AdmissibleParams) :
    DecidablePred (@IsCommuting P) := Classical.decPred _

/-- The uniform probability of the anticommuting event. This is the first
quantity in `fact:omega-anticomm-prob`, blueprint
`ch14_qpbt_observables.tex:151-178`, paper
`14_analysis_of_the_pauli_basis_test.tex:70-77`. -/
noncomputable def anticommProb (P : AdmissibleParams) : ℝ :=
  ((Finset.univ.filter (@IsAnticommuting P)).card : ℝ) /
    Fintype.card (PauliTuple P)

/-- The complementary uniform probability of the commuting event in
`fact:omega-anticomm-prob`, blueprint `ch14_qpbt_observables.tex:151-178`,
paper `14_analysis_of_the_pauli_basis_test.tex:70-77`. -/
noncomputable def commProb (P : AdmissibleParams) : ℝ :=
  ((Finset.univ.filter (@IsCommuting P)).card : ℝ) /
    Fintype.card (PauliTuple P)

/-! ### Auxiliary counting lemmas

The declarations of this section are formalization-only auxiliaries for the
proof of `fact:omega-anticomm-prob`, blueprint
`ch14_qpbt_observables.tex:151-267`. They record the cardinalities used by the
exact computation of the anticommuting probability. -/

/-- Formalization-only auxiliary: the scalar carrier of an admissible parameter
tuple has characteristic two, since it is an algebra over the two-element
field. Blueprint `ch14_qpbt_observables.tex:151-178`. -/
private theorem pauliScalar_charTwo (P : AdmissibleParams) :
    CharP (PauliScalar P) 2 :=
  (Algebra.charP_iff (ZMod 2) (PauliScalar P) 2).mp (ZMod.charP 2)

/-- Formalization-only auxiliary: the scalar carrier of an admissible parameter
tuple has exactly `q` elements. Blueprint
`ch14_qpbt_observables.tex:151-178`. -/
private theorem card_pauliScalar (P : AdmissibleParams) :
    Fintype.card (PauliScalar P) = P.q :=
  @FieldModel.card P.q P.model.toFieldModel

/-- Formalization-only auxiliary: an admissible field size is at least two.
Blueprint `ch14_qpbt_observables.tex:151-178`. -/
private theorem two_le_q (P : AdmissibleParams) : 2 ≤ P.q := by
  obtain ⟨k, hk, hq⟩ := P.hq
  obtain ⟨j, hj⟩ := hk
  rw [hq, hj]
  calc 2 = 2 ^ 1 := by norm_num
    _ ≤ 2 ^ (2 * j + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)

/-- Formalization-only auxiliary: an admissible field size is either two or a
multiple of eight, because its binary exponent is odd. Blueprint
`ch14_qpbt_observables.tex:151-178`. -/
private theorem q_eq_two_or_eight_dvd (P : AdmissibleParams) :
    P.q = 2 ∨ 8 ∣ P.q := by
  obtain ⟨k, hk, hq⟩ := P.hq
  obtain ⟨j, hj⟩ := hk
  rcases Nat.eq_zero_or_pos j with hj0 | hj0
  · left
    rw [hq, hj, hj0]
    norm_num
  · right
    refine ⟨2 ^ (2 * j + 1 - 3), ?_⟩
    rw [hq, hj, show (8 : ℕ) = 2 ^ 3 by norm_num, ← pow_add]
    congr 1
    omega

/-- Formalization-only auxiliary: over a commutative ring of characteristic
two, the inner product of two indicator vectors is the product of the
coordinate sums `1 + x_i + z_i`. This is the product expansion used in the
proof of `fact:omega-anticomm-prob`, blueprint
`ch14_qpbt_observables.tex:196-235`. -/
private theorem sum_indicatorVec_mul_indicatorVec {K : Type*} [CommRing K]
    [CharP K 2] {m : ℕ} (x z : Fin m → K) :
    ∑ y : Cube m, indicatorVec x y * indicatorVec z y
      = ∏ i : Fin m, (1 + x i + z i) := by
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  have hev : ∀ (u : Fin m → K) (y : Cube m),
      indicatorVec u y = ∏ i : Fin m, if y i then u i else 1 - u i := by
    intro u y
    simp [indicatorVec, indicatorPoly, apply_ite]
  have hfac : ∀ i : Fin m,
      ∑ b : Bool, ((if b then x i else 1 - x i) * (if b then z i else 1 - z i))
        = 1 + x i + z i := by
    intro i
    have h1 :
        ∑ b : Bool, ((if b then x i else 1 - x i) * (if b then z i else 1 - z i))
          = x i * z i + (1 - x i) * (1 - z i) := by
      rw [Fintype.sum_bool]
      simp
    rw [h1]
    linear_combination (x i * z i - x i - z i) * h2
  calc ∑ y : Cube m, indicatorVec x y * indicatorVec z y
      = ∑ y : Cube m, ∏ i : Fin m,
          ((if y i then x i else 1 - x i) * (if y i then z i else 1 - z i)) := by
        refine Finset.sum_congr rfl ?_
        intro y _
        rw [hev x y, hev z y, ← Finset.prod_mul_distrib]
    _ = ∏ i : Fin m, ∑ b : Bool,
          ((if b then x i else 1 - x i) * (if b then z i else 1 - z i)) := by
        rw [Finset.prod_univ_sum, Fintype.piFinset_univ]
    _ = ∏ i : Fin m, (1 + x i + z i) := Finset.prod_congr rfl fun i _ => hfac i

/-- The phase bit of a Pauli tuple is the trace of `r_Z r_X` times the product
of the coordinate sums `1 + u_{X,i} + u_{Z,i}`. This is the closed form of
`γ(ω)` derived in the proof of `fact:omega-anticomm-prob`, blueprint
`ch14_qpbt_observables.tex:196-235`. -/
private theorem gammaValue_eq_trace_prod (P : AdmissibleParams)
    (uX uZ : Fin P.m → PauliScalar P) (rX rZ : PauliScalar P) :
    gammaValue P uX uZ rX rZ =
      fixedBinTrace P.model (rZ * (rX * ∏ i : Fin P.m, (1 + uX i + uZ i))) := by
  haveI := pauliScalar_charTwo P
  have hprod : (∑ y : Cube P.m, indicatorVec uX y * indicatorVec uZ y)
      = ∏ i : Fin P.m, (1 + uX i + uZ i) :=
    sum_indicatorVec_mul_indicatorVec uX uZ
  unfold gammaValue
  congr 1
  rw [← hprod]
  simp only [dotProduct, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun y _ => by ring

/-- Formalization-only auxiliary: the field trace onto the two-element field
takes each of its two values on exactly half of the scalars. This is the final
step of the proof of `fact:omega-anticomm-prob`, blueprint
`ch14_qpbt_observables.tex:236-249`. -/
private theorem two_mul_card_trace_ne (P : AdmissibleParams) :
    2 * (Finset.univ.filter
        (fun a : PauliScalar P => fixedBinTrace P.model a ≠ 0)).card = P.q := by
  classical
  haveI := pauliScalar_charTwo P
  have hK := card_pauliScalar P
  have hadd : ∀ a c : PauliScalar P,
      fixedBinTrace P.model (a + c)
        = fixedBinTrace P.model a + fixedBinTrace P.model c := by
    intro a c
    simp [fixedBinTrace, binTrace]
  obtain ⟨b, hb⟩ : ∃ b : PauliScalar P, fixedBinTrace P.model b = 1 := by
    have hpos : 0 < P.model.basisDim := by
      obtain ⟨j, hj⟩ := P.model.basisDimOdd
      omega
    refine ⟨P.model.basis ⟨0, hpos⟩ * P.model.basis ⟨0, hpos⟩, ?_⟩
    simpa [fixedBinTrace, binTrace] using P.model.selfDual ⟨0, hpos⟩ ⟨0, hpos⟩
  have hbb : b + b = 0 := CharTwo.add_self_eq_zero b
  have himg :
      (Finset.univ.filter
          (fun a : PauliScalar P => fixedBinTrace P.model a = 0)).image (fun a => a + b)
        = Finset.univ.filter
            (fun a : PauliScalar P => ¬ (fixedBinTrace P.model a = 0)) := by
    ext a
    simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨c, hc, rfl⟩
      rw [hadd, hc, hb]
      simp
    · intro ha
      refine ⟨a + b, ?_, ?_⟩
      · rw [hadd, hb]
        have hone : fixedBinTrace P.model a = 1 := by
          revert ha
          generalize fixedBinTrace P.model a = t
          revert t
          decide
        rw [hone]
        decide
      · rw [add_assoc, hbb, add_zero]
  have hinj : Function.Injective (fun a : PauliScalar P => a + b) :=
    fun _ _ h => by simpa using h
  have hcard :
      (Finset.univ.filter (fun a : PauliScalar P => fixedBinTrace P.model a = 0)).card
        = (Finset.univ.filter
            (fun a : PauliScalar P => ¬ (fixedBinTrace P.model a = 0))).card := by
    rw [← himg, Finset.card_image_of_injective _ hinj]
  have hsplit :
      (Finset.univ.filter (fun a : PauliScalar P => fixedBinTrace P.model a = 0)).card
          + (Finset.univ.filter
              (fun a : PauliScalar P => ¬ (fixedBinTrace P.model a = 0))).card
        = Fintype.card (PauliScalar P) :=
    Finset.card_filter_add_card_filter_not _
  rw [hK] at hsplit
  simp only [ne_eq]
  omega

/-- Formalization-only auxiliary: the number of Pauli tuples. Blueprint
`ch14_qpbt_observables.tex:151-178`. -/
private theorem card_pauliTuple (P : AdmissibleParams) :
    Fintype.card (PauliTuple P) = P.q ^ P.m * (P.q ^ P.m * (P.q * P.q)) := by
  have hK := card_pauliScalar P
  simp [PauliTuple, Fintype.card_prod, hK]

/-- Twice the number of anticommuting tuples is `q^{m+1}(q-1)^{m+1}`. This is
the exact count established in the proof of `fact:omega-anticomm-prob`,
blueprint `ch14_qpbt_observables.tex:196-249`. -/
private theorem two_mul_card_anticommuting (P : AdmissibleParams) :
    2 * (Finset.univ.filter (@IsAnticommuting P)).card
      = P.q ^ (P.m + 1) * (P.q - 1) ^ (P.m + 1) := by
  classical
  haveI := pauliScalar_charTwo P
  have h2 : (2 : PauliScalar P) = 0 := CharTwo.two_eq_zero
  have hK := card_pauliScalar P
  have htr0 : fixedBinTrace P.model 0 = 0 := by
    simp [fixedBinTrace, binTrace]
  set N := (Finset.univ.filter
    (fun a : PauliScalar P => fixedBinTrace P.model a ≠ 0)).card with hNdef
  have hN : 2 * N = P.q := two_mul_card_trace_ne P
  -- the innermost sum, over the second scalar coordinate
  have hinner : ∀ c : PauliScalar P,
      (∑ r : PauliScalar P, if fixedBinTrace P.model (r * c) ≠ 0 then (1 : ℕ) else 0)
        = if c = 0 then 0 else N := by
    intro c
    by_cases hc : c = 0
    · subst hc
      simp [htr0]
    · rw [if_neg hc, hNdef, Finset.card_filter]
      exact Fintype.sum_equiv (Equiv.mulRight₀ c hc)
        (fun r => if fixedBinTrace P.model (r * c) ≠ 0 then (1 : ℕ) else 0)
        (fun a => if fixedBinTrace P.model a ≠ 0 then (1 : ℕ) else 0)
        (fun r => rfl)
  -- the sum over the first scalar coordinate
  have hnzcard :
      (Finset.univ.filter (fun x : PauliScalar P => ¬ (x = 0))).card = P.q - 1 := by
    have h1 : (Finset.univ.filter (fun x : PauliScalar P => x ≠ 0))
        = Finset.univ.erase 0 := Finset.filter_ne' _ _
    simp only [ne_eq] at h1
    rw [h1, Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, hK]
  have hmid : ∀ dd : PauliScalar P,
      (∑ rX : PauliScalar P, if rX * dd = 0 then (0 : ℕ) else N)
        = if dd = 0 then 0 else (P.q - 1) * N := by
    intro dd
    by_cases hd : dd = 0
    · subst hd
      simp
    · rw [if_neg hd]
      have hcong : ∀ rX : PauliScalar P,
          (if rX * dd = 0 then (0 : ℕ) else N) = if rX = 0 then 0 else N := by
        intro rX
        by_cases hr : rX = 0
        · simp [hr]
        · rw [if_neg (by simpa using mul_ne_zero hr hd), if_neg hr]
      rw [Finset.sum_congr rfl (fun x _ => hcong x), Finset.sum_ite]
      simp [hnzcard]
  -- the sum over the second point block
  have hDcard : ∀ uX : Fin P.m → PauliScalar P,
      (Finset.univ.filter (fun uZ : Fin P.m → PauliScalar P =>
        ¬ ((∏ i : Fin P.m, (1 + uX i + uZ i)) = 0))).card = (P.q - 1) ^ P.m := by
    intro uX
    have hset : (Finset.univ.filter (fun uZ : Fin P.m → PauliScalar P =>
        ¬ ((∏ i : Fin P.m, (1 + uX i + uZ i)) = 0)))
        = Fintype.piFinset (fun i : Fin P.m => Finset.univ.erase (1 + uX i)) := by
      ext uZ
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Fintype.mem_piFinset,
        Finset.mem_erase, and_true]
      constructor
      · intro h i hi
        refine h ?_
        refine Finset.prod_eq_zero (Finset.mem_univ i) ?_
        rw [hi]
        linear_combination (1 + uX i) * h2
      · intro h hz
        rw [Finset.prod_eq_zero_iff] at hz
        obtain ⟨i, -, hi⟩ := hz
        exact h i (by linear_combination hi - (1 + uX i) * h2)
    rw [hset, Fintype.card_piFinset]
    simp [Finset.card_erase_of_mem, Finset.card_univ, hK]
  have houter : ∀ uX : Fin P.m → PauliScalar P,
      (∑ uZ : Fin P.m → PauliScalar P,
          if (∏ i : Fin P.m, (1 + uX i + uZ i)) = 0 then (0 : ℕ) else (P.q - 1) * N)
        = (P.q - 1) ^ P.m * ((P.q - 1) * N) := by
    intro uX
    rw [Finset.sum_ite]
    simp [hDcard uX]
  have step1 : ∀ (uX uZ : Fin P.m → PauliScalar P) (rX : PauliScalar P),
      (∑ rZ : PauliScalar P,
          if IsAnticommuting ((uX, uZ, rX, rZ) : PauliTuple P) then (1 : ℕ) else 0)
        = if rX * ∏ i : Fin P.m, (1 + uX i + uZ i) = 0 then 0 else N := by
    intro uX uZ rX
    have hcongr : ∀ rZ : PauliScalar P,
        (if IsAnticommuting ((uX, uZ, rX, rZ) : PauliTuple P) then (1 : ℕ) else 0)
          = if fixedBinTrace P.model
              (rZ * (rX * ∏ i : Fin P.m, (1 + uX i + uZ i))) ≠ 0 then 1 else 0 := by
      intro rZ
      have hiff : IsAnticommuting ((uX, uZ, rX, rZ) : PauliTuple P)
          ↔ fixedBinTrace P.model
              (rZ * (rX * ∏ i : Fin P.m, (1 + uX i + uZ i))) ≠ 0 := by
        unfold IsAnticommuting
        rw [gammaValue_eq_trace_prod]
      by_cases h : fixedBinTrace P.model
          (rZ * (rX * ∏ i : Fin P.m, (1 + uX i + uZ i))) ≠ 0
      · rw [if_pos (hiff.mpr h), if_pos h]
      · rw [if_neg (fun hh => h (hiff.mp hh)), if_neg h]
    rw [Finset.sum_congr rfl (fun x _ => hcongr x), hinner]
  have hcount : (Finset.univ.filter (@IsAnticommuting P)).card
      = P.q ^ P.m * ((P.q - 1) ^ P.m * ((P.q - 1) * N)) := by
    rw [Finset.card_filter]
    simp only [Fintype.sum_prod_type]
    calc (∑ uX : Fin P.m → PauliScalar P, ∑ uZ : Fin P.m → PauliScalar P,
            ∑ rX : PauliScalar P, ∑ rZ : PauliScalar P,
              (if IsAnticommuting ((uX, uZ, rX, rZ) : PauliTuple P) then (1 : ℕ) else 0))
        = ∑ _uX : Fin P.m → PauliScalar P, (P.q - 1) ^ P.m * ((P.q - 1) * N) := by
          refine Finset.sum_congr rfl fun uX _ => ?_
          rw [← houter uX]
          refine Finset.sum_congr rfl fun uZ _ => ?_
          rw [← hmid (∏ i : Fin P.m, (1 + uX i + uZ i))]
          exact Finset.sum_congr rfl fun rX _ => step1 uX uZ rX
      _ = P.q ^ P.m * ((P.q - 1) ^ P.m * ((P.q - 1) * N)) := by
          rw [Finset.sum_const, Finset.card_univ, smul_eq_mul]
          congr 1
          simp [hK]
  rw [hcount]
  have hexpand : 2 * (P.q ^ P.m * ((P.q - 1) ^ P.m * ((P.q - 1) * N)))
      = P.q ^ P.m * ((P.q - 1) ^ P.m * ((P.q - 1) * (2 * N))) := by ring
  rw [hexpand, hN, pow_succ, pow_succ]
  ring

/-- The anticommuting and commuting events partition the tuple space.
Blueprint `ch14_qpbt_observables.tex:151-178`. -/
private theorem card_comm_add_card_anticomm (P : AdmissibleParams) :
    (Finset.univ.filter (@IsCommuting P)).card
      + (Finset.univ.filter (@IsAnticommuting P)).card
      = Fintype.card (PauliTuple P) := by
  classical
  have hfil : (Finset.univ.filter (@IsAnticommuting P))
      = Finset.univ.filter (fun ω : PauliTuple P => ¬ (@IsCommuting P ω)) := by
    refine Finset.filter_congr ?_
    intro ω _
    simp [IsAnticommuting, IsCommuting]
  rw [hfil, ← Finset.card_univ]
  exact Finset.card_filter_add_card_filter_not _

/-- Formalization-only auxiliary: the tuple space is nonempty and finite.
Blueprint `ch14_qpbt_observables.tex:151-178`. -/
private theorem card_pauliTuple_pos (P : AdmissibleParams) :
    0 < Fintype.card (PauliTuple P) := by
  have hq : 0 < P.q := lt_of_lt_of_le (by norm_num) (two_le_q P)
  rw [card_pauliTuple P]
  exact Nat.mul_pos (pow_pos hq _) (Nat.mul_pos (pow_pos hq _) (Nat.mul_pos hq hq))

/-! ### The exact anticommuting probability -/

/-- Exact anticommuting probability from `fact:omega-anticomm-prob`, blueprint
`ch14_qpbt_observables.tex:151-178`; its derivation replaces the erroneous
Schwartz--Zippel argument at paper
`14_analysis_of_the_pauli_basis_test.tex:79-93`. -/
theorem anticommProb_eq (P : AdmissibleParams) :
    anticommProb P = (1 - (P.q : ℝ)⁻¹) ^ (P.m + 1) / 2 := by
  have hq2 : 2 ≤ P.q := two_le_q P
  have hqR : (0 : ℝ) < (P.q : ℝ) := by
    have h : 0 < P.q := by omega
    exact_mod_cast h
  have hcast : ((2 * (Finset.univ.filter (@IsAnticommuting P)).card : ℕ) : ℝ)
      = ((P.q ^ (P.m + 1) * (P.q - 1) ^ (P.m + 1) : ℕ) : ℝ) := by
    exact_mod_cast congrArg (fun n : ℕ => (n : ℝ)) (two_mul_card_anticommuting P)
  rw [Nat.cast_mul, Nat.cast_mul, Nat.cast_pow, Nat.cast_pow,
    Nat.cast_sub (by omega : 1 ≤ P.q), Nat.cast_one, Nat.cast_ofNat] at hcast
  have hval : ((Finset.univ.filter (@IsAnticommuting P)).card : ℝ)
      = (P.q : ℝ) ^ (P.m + 1) * ((P.q : ℝ) - 1) ^ (P.m + 1) / 2 := by linarith
  have hbase : (1 : ℝ) - (P.q : ℝ)⁻¹ = ((P.q : ℝ) - 1) / (P.q : ℝ) := by
    field_simp
  rw [anticommProb, hval, card_pauliTuple P, hbase, div_pow]
  push_cast
  field_simp
  ring

/-- A tuple is commuting with the probability complementary to the
anticommuting one. This is the complementarity clause of
`fact:omega-anticomm-prob`, blueprint `ch14_qpbt_observables.tex:151-178`,
paper `14_analysis_of_the_pauli_basis_test.tex:70-77`. -/
theorem commProb_eq_one_sub_anticommProb (P : AdmissibleParams) :
    commProb P = 1 - anticommProb P := by
  have hpos : (0 : ℝ) < (Fintype.card (PauliTuple P) : ℝ) := by
    exact_mod_cast card_pauliTuple_pos P
  have hsum : ((Finset.univ.filter (@IsCommuting P)).card : ℝ)
      + ((Finset.univ.filter (@IsAnticommuting P)).card : ℝ)
      = (Fintype.card (PauliTuple P) : ℝ) := by
    exact_mod_cast card_comm_add_card_anticomm P
  rw [commProb, anticommProb, eq_sub_iff_add_eq, ← add_div, hsum,
    div_self hpos.ne']

/-- Formalization-only auxiliary: the base `1 - q^{-1}` of the exact
anticommuting probability lies in the unit interval. Blueprint
`ch14_qpbt_observables.tex:151-178`. -/
private theorem base_mem_unit_interval (P : AdmissibleParams) :
    (0 : ℝ) ≤ 1 - (P.q : ℝ)⁻¹ ∧ (1 : ℝ) - (P.q : ℝ)⁻¹ ≤ 1 := by
  have hq2 : 2 ≤ P.q := two_le_q P
  have hqR : (2 : ℝ) ≤ (P.q : ℝ) := by exact_mod_cast hq2
  have hinv : (P.q : ℝ)⁻¹ ≤ 1 / 2 := by
    rw [inv_le_comm₀ (by linarith) (by norm_num)]
    linarith
  have hinv0 : (0 : ℝ) ≤ (P.q : ℝ)⁻¹ := by positivity
  constructor <;> linarith

/-- The commuting event has probability at least one half. This is the
complementary bound in `fact:omega-anticomm-prob`, blueprint
`ch14_qpbt_observables.tex:151-178`, paper
`14_analysis_of_the_pauli_basis_test.tex:70-77`. -/
theorem commProb_ge_half (P : AdmissibleParams) : 1 / 2 ≤ commProb P := by
  obtain ⟨h0, h1⟩ := base_mem_unit_interval P
  have hle : (1 - (P.q : ℝ)⁻¹) ^ (P.m + 1) ≤ 1 := pow_le_one₀ h0 h1
  rw [commProb_eq_one_sub_anticommProb, anticommProb_eq]
  linarith

/-- When `m ≤ q`, the anticommuting event has the uniform constant lower
bound added in `fact:omega-anticomm-prob`, blueprint
`ch14_qpbt_observables.tex:151-178`. -/
theorem anticommProb_ge_of_m_le_q (P : AdmissibleParams) (hmq : P.m ≤ P.q) :
    (2 : ℝ) ^ (-4 : ℤ) ≤ anticommProb P := by
  obtain ⟨h0, h1⟩ := base_mem_unit_interval P
  have hq2 : 2 ≤ P.q := two_le_q P
  have hqR : (2 : ℝ) ≤ (P.q : ℝ) := by exact_mod_cast hq2
  have hmain : (1 : ℝ) / 8 ≤ (1 - (P.q : ℝ)⁻¹) ^ (P.m + 1) := by
    rcases q_eq_two_or_eight_dvd P with hq | hdvd
    · have hm : P.m ≤ 2 := hq ▸ hmq
      have hb : (1 : ℝ) - (P.q : ℝ)⁻¹ = 1 / 2 := by
        rw [hq]
        norm_num
      rw [hb]
      calc (1 : ℝ) / 8 = (1 / 2 : ℝ) ^ 3 := by norm_num
        _ ≤ (1 / 2 : ℝ) ^ (P.m + 1) :=
            pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
    · obtain ⟨j, hj⟩ := hdvd
      have hj1 : 1 ≤ j := by omega
      have hjR : (P.q : ℝ) = 8 * (j : ℝ) := by
        rw [hj]
        push_cast
        ring
      have hjR0 : (0 : ℝ) < (j : ℝ) := by exact_mod_cast hj1
      have hbern : (7 : ℝ) / 8 ≤ (1 - (P.q : ℝ)⁻¹) ^ j := by
        have hle : (-2 : ℝ) ≤ -(P.q : ℝ)⁻¹ := by
          have : (0 : ℝ) ≤ (P.q : ℝ)⁻¹ := by positivity
          have h2 : (P.q : ℝ)⁻¹ ≤ 1 := by
            rw [inv_le_one₀ (by linarith)]
            linarith
          linarith
        have hb := one_add_mul_le_pow hle j
        have hrw : (1 : ℝ) + (j : ℝ) * (-(P.q : ℝ)⁻¹) = 7 / 8 := by
          rw [hjR]
          field_simp
          ring
        have hbase : (1 : ℝ) + -(P.q : ℝ)⁻¹ = 1 - (P.q : ℝ)⁻¹ := by ring
        rw [hrw, hbase] at hb
        exact hb
      have hexp : P.m + 1 ≤ 9 * j := by omega
      have hstep : (1 - (P.q : ℝ)⁻¹) ^ (9 * j) ≤ (1 - (P.q : ℝ)⁻¹) ^ (P.m + 1) :=
        pow_le_pow_of_le_one h0 h1 hexp
      have hpow : ((7 : ℝ) / 8) ^ 9 ≤ ((1 - (P.q : ℝ)⁻¹) ^ j) ^ 9 := by
        gcongr
      rw [← pow_mul, mul_comm j 9] at hpow
      have hnum : (1 : ℝ) / 8 ≤ ((7 : ℝ) / 8) ^ 9 := by norm_num
      linarith
  rw [anticommProb_eq]
  have hconst : (2 : ℝ) ^ (-4 : ℤ) = 1 / 8 / 2 := by norm_num
  rw [hconst]
  linarith

/-- **Local fix:** For the positive parameters in `AdmissibleParams`, the
source lower bounds hold with the missing hypotheses restored. This is the
final display of `fact:omega-anticomm-prob`, blueprint
`ch14_qpbt_observables.tex:151-178`, correcting paper
`14_analysis_of_the_pauli_basis_test.tex:70-77`; see
`rem:omega-anticomm-prob-correction`. -/
theorem anticommProb_ge_of_one_le_md (P : AdmissibleParams) :
    (1 - (P.q : ℝ)⁻¹ ^ P.m) * (1 - (P.q : ℝ)⁻¹) *
        (1 - ((P.m * P.d : ℕ) : ℝ) / P.q) / 2 ≤ anticommProb P ∧
      (1 - 3 * ((P.m * P.d : ℕ) : ℝ) / P.q) / 2 ≤
        (1 - (P.q : ℝ)⁻¹ ^ P.m) * (1 - (P.q : ℝ)⁻¹) *
          (1 - ((P.m * P.d : ℕ) : ℝ) / P.q) / 2 ∧
      (1 - 3 * ((P.m * P.d : ℕ) : ℝ) / P.q) / 2 ≤ anticommProb P ∧
      (1 - 3 * ((P.m * P.d : ℕ) : ℝ) / P.q) / 2 ≤ commProb P := by
  obtain ⟨hb0, hb1⟩ := base_mem_unit_interval P
  have hq2 : 2 ≤ P.q := two_le_q P
  have hqR : (2 : ℝ) ≤ (P.q : ℝ) := by exact_mod_cast hq2
  have hm1 : 1 ≤ P.m := P.one_le_m
  have hd1 : 1 ≤ P.d := P.hd
  set B : ℝ := (P.q : ℝ)⁻¹ with hBdef
  set A : ℝ := B ^ P.m with hAdef
  set C : ℝ := ((P.m * P.d : ℕ) : ℝ) / (P.q : ℝ) with hCdef
  have hB0 : (0 : ℝ) < B := by
    rw [hBdef]
    positivity
  have hB1 : B ≤ 1 / 2 := by
    rw [hBdef, inv_le_comm₀ (by linarith) (by norm_num)]
    linarith
  have hq0 : (0 : ℝ) < (P.q : ℝ) := by linarith
  have hAB : A ≤ B := by
    calc A = B ^ P.m := hAdef
      _ ≤ B ^ 1 := pow_le_pow_of_le_one hB0.le (by linarith) hm1
      _ = B := pow_one B
  have hA0 : (0 : ℝ) < A := by
    rw [hAdef]
    positivity
  have hmdR : (1 : ℝ) ≤ ((P.m * P.d : ℕ) : ℝ) := by
    have h : 1 ≤ P.m * P.d := by
      calc 1 = 1 * 1 := by norm_num
        _ ≤ P.m * P.d := Nat.mul_le_mul hm1 hd1
    exact_mod_cast h
  have hBC : B ≤ C := by
    rw [hBdef, hCdef, div_eq_mul_inv]
    calc (P.q : ℝ)⁻¹ = 1 * (P.q : ℝ)⁻¹ := (one_mul _).symm
      _ ≤ ((P.m * P.d : ℕ) : ℝ) * (P.q : ℝ)⁻¹ :=
          mul_le_mul_of_nonneg_right hmdR (by positivity)
  have hC0 : (0 : ℝ) ≤ C := le_trans hB0.le hBC
  -- the first bound: comparison with the exact probability
  have hkey : (1 - A) * (1 - C) ≤ (1 - B) ^ P.m := by
    have hbern : (1 : ℝ) - (P.m : ℝ) * B ≤ (1 - B) ^ P.m := by
      have hle : (-2 : ℝ) ≤ -B := by linarith
      have hb := one_add_mul_le_pow hle P.m
      have h1 : (1 : ℝ) + (P.m : ℝ) * (-B) = 1 - (P.m : ℝ) * B := by ring
      have h2 : (1 : ℝ) + -B = 1 - B := by ring
      rw [h1, h2] at hb
      exact hb
    have hmC : (P.m : ℝ) * B ≤ C := by
      have hmd : (P.m : ℝ) ≤ ((P.m * P.d : ℕ) : ℝ) := by
        have h : P.m ≤ P.m * P.d := by
          calc P.m = P.m * 1 := by ring
            _ ≤ P.m * P.d := Nat.mul_le_mul le_rfl hd1
        exact_mod_cast h
      rw [hBdef, hCdef, div_eq_mul_inv]
      exact mul_le_mul_of_nonneg_right hmd (by positivity)
    by_cases hC1 : C ≤ 1
    · have hAC : (0 : ℝ) ≤ A * (1 - C) := mul_nonneg hA0.le (by linarith)
      nlinarith [hbern, hmC, hAC]
    · have hC1' : (1 : ℝ) < C := lt_of_not_ge hC1
      have hA1 : A ≤ 1 / 2 := le_trans hAB hB1
      have hpow : (0 : ℝ) ≤ (1 - B) ^ P.m := pow_nonneg (by linarith) _
      have hpr : (0 : ℝ) ≤ (1 - A) * (C - 1) :=
        mul_nonneg (by linarith) (by linarith)
      nlinarith [hpow, hpr]
  have hfirst : (1 - A) * (1 - B) * (1 - C) / 2 ≤ anticommProb P := by
    rw [anticommProb_eq, ← hBdef]
    have hstep : (1 - A) * (1 - B) * (1 - C) ≤ (1 - B) ^ (P.m + 1) := by
      rw [pow_succ]
      have h1B : (0 : ℝ) ≤ 1 - B := by linarith
      nlinarith [hkey, h1B]
    linarith
  -- the second bound: the linearized form
  have hsecond : (1 - 3 * ((P.m * P.d : ℕ) : ℝ) / (P.q : ℝ)) / 2
      ≤ (1 - A) * (1 - B) * (1 - C) / 2 := by
    have hC3 : 3 * ((P.m * P.d : ℕ) : ℝ) / (P.q : ℝ) = 3 * C := by
      rw [hCdef]
      ring
    rw [hC3]
    have hpos1 : (0 : ℝ) ≤ A * (1 - B) + B := by
      have h := mul_nonneg hA0.le (by linarith : (0 : ℝ) ≤ 1 - B)
      linarith
    have hpos2 : (0 : ℝ) ≤ C * (A * (1 - B) + B) := mul_nonneg hC0 hpos1
    have hpos3 : (0 : ℝ) ≤ A * B := by positivity
    have hpos4 : (0 : ℝ) ≤ 2 * C - A - B := by linarith
    nlinarith [hpos2, hpos3, hpos4]
  refine ⟨hfirst, hsecond, le_trans hsecond hfirst, ?_⟩
  have hhalf : 1 / 2 ≤ commProb P := commProb_ge_half P
  have hC3 : 3 * ((P.m * P.d : ℕ) : ℝ) / (P.q : ℝ) = 3 * C := by
    rw [hCdef]
    ring
  rw [hC3]
  linarith

/-! ### Conditional uniform distributions -/

/-- The conditional uniform distribution on anticommuting tuples. This is the
sampling convention for the anticommuting cases of
`lem:qld-win-implications`, blueprint `ch14_qpbt_observables.tex:505-660`,
paper `14_analysis_of_the_pauli_basis_test.tex:210-287`. -/
noncomputable def anticommTupleDist (P : AdmissibleParams) :
    Distribution (PauliTuple P) :=
  Distribution.uniformOnFinset (Finset.univ.filter (@IsAnticommuting P))

/-- The conditional uniform distribution on commuting tuples. This is the
sampling convention for the commuting cases of `lem:qld-win-implications`,
blueprint `ch14_qpbt_observables.tex:505-660`, paper
`14_analysis_of_the_pauli_basis_test.tex:210-287`. -/
noncomputable def commTupleDist (P : AdmissibleParams) :
    Distribution (PauliTuple P) :=
  Distribution.uniformOnFinset (Finset.univ.filter (@IsCommuting P))

/-- The anticommuting conditional distribution is probabilistic. This is the
well-formedness companion to the conditional sampling in
`lem:qld-win-implications`, blueprint `ch14_qpbt_observables.tex:505-660`. -/
theorem anticommTupleDist_isProbability (P : AdmissibleParams) :
    (anticommTupleDist P).IsProbability := by
  refine Distribution.uniformOnFinset_isProbability _ ?_
  rw [← Finset.card_pos]
  have hq2 : 2 ≤ P.q := two_le_q P
  have hcount := two_mul_card_anticommuting P
  have hpos : 0 < P.q ^ (P.m + 1) * (P.q - 1) ^ (P.m + 1) :=
    Nat.mul_pos (pow_pos (by omega) _) (pow_pos (by omega) _)
  omega

/-- The commuting conditional distribution is probabilistic. This is the
well-formedness companion to the conditional sampling in
`lem:qld-win-implications`, blueprint `ch14_qpbt_observables.tex:505-660`. -/
theorem commTupleDist_isProbability (P : AdmissibleParams) :
    (commTupleDist P).IsProbability := by
  refine Distribution.uniformOnFinset_isProbability _ ⟨0, ?_⟩
  refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
  change gammaValue P 0 0 0 0 = 0
  rw [gammaValue_eq_trace_prod]
  simp [fixedBinTrace, binTrace]

end

end MIPStarRE.QPBT
