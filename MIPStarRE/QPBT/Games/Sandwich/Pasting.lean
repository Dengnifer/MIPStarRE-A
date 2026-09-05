import MIPStarRE.QPBT.Games.Sandwich.Quantitative

/-! # Support lemmas for the pasting estimate

This module collects the quantitative steps of the proof of `lem:pasting`
recorded in `docs/paper-gaps/qpbt_pasting-product-error.tex`.

## References

Blueprint `blueprint/src/chapter/ch12_qpbt_games.tex:960-1050`; paper
`references/qpbt-paper/06_nonlocal_games_and_mipstar.tex:504-525`.
-/

open scoped BigOperators MatrixOrder Matrix ComplexOrder

namespace MIPStarRE.QPBT

open MIPStarRE.LDT hiding Measurement
open MIPStarRE.Quantum
open DistanceCalculus

/-- Cross consistency of the coarse-grained second codeword family. Under the
register exchange `eq:pasting-1-sym` of the second comparison in
`eq:pasting-1`, the self-consistency `eq:pasting-2` of the answer measurement
and that second comparison itself, the coarse second codeword family is
consistent with its own copy on the opposite factor, with the square-root loss
of the triangle estimate `fact:triangle-for-simeq`. This is the step of
`lem:pasting` that uses the symmetric convention; blueprint
`ch12_qpbt_games.tex:960-990`. -/
theorem consistencyDefect_codeword_cross_le
    {X Y₁ Y₂ R₁ R₂ Γ₂ ι : Type*}
    [Fintype X] [DecidableEq X] [Fintype Y₁] [DecidableEq Y₁]
    [Fintype Y₂] [DecidableEq Y₂] [Fintype R₁] [DecidableEq R₁]
    [Fintype R₂] [DecidableEq R₂] [Fintype Γ₂] [DecidableEq Γ₂]
    [Fintype ι] [DecidableEq ι]
    (D : Distribution ((X × Y₁) × Y₂)) (eval₂ : Γ₂ → Y₂ → R₂)
    (G₂ : X → Measurement Γ₂ ι) (A : ((X × Y₁) × Y₂) → Measurement (R₁ × R₂) ι)
    (ψ : EuclideanSpace ℂ (ι × ι)) (δ : ℝ)
    (hD : D.IsProbability) (hψ : ‖ψ‖ = 1)
    (hsym : consistencyDefect D
      (fun q a₂ => heteroKron (((G₂ q.1.1).postprocess
        (fun g => eval₂ g q.2)).effect a₂) 1)
      (fun q a₂ => heteroKron 1 (((A q).postprocess Prod.snd).effect a₂)) ψ ≤ δ)
    (hself : consistencyDefect D (fun q a => heteroKron ((A q).effect a) 1)
      (fun q a => heteroKron 1 ((A q).effect a)) ψ ≤ δ)
    (hfwd : consistencyDefect D
      (fun q a₂ => heteroKron (((A q).postprocess Prod.snd).effect a₂) 1)
      (fun q a₂ => heteroKron 1 (((G₂ q.1.1).postprocess
        (fun g => eval₂ g q.2)).effect a₂)) ψ ≤ δ) :
    consistencyDefect D
      (fun q a₂ => heteroKron (((G₂ q.1.1).postprocess
        (fun g => eval₂ g q.2)).effect a₂) 1)
      (fun q a₂ => heteroKron 1 (((G₂ q.1.1).postprocess
        (fun g => eval₂ g q.2)).effect a₂)) ψ ≤ δ + 2 * Real.sqrt (2 * δ) := by
  classical
  have hmarg : consistencyDefect D
      (fun q a₂ => heteroKron (((A q).postprocess Prod.snd).effect a₂) 1)
      (fun q a₂ => heteroKron 1 (((A q).postprocess Prod.snd).effect a₂)) ψ ≤ δ :=
    le_trans (consistencyDefect_postprocess_le D A A ψ Prod.snd) hself
  have hmain := consistencyDefect_trans_le D
    (fun q => Measurement.leftPlacement (ιB := ι)
      ((G₂ q.1.1).postprocess (fun g => eval₂ g q.2)))
    (fun q => Measurement.rightPlacement (ιA := ι) ((A q).postprocess Prod.snd))
    (fun q => Measurement.leftPlacement (ιB := ι) ((A q).postprocess Prod.snd))
    (fun q => Measurement.rightPlacement (ιA := ι)
      ((G₂ q.1.1).postprocess (fun g => eval₂ g q.2)))
    ψ δ δ δ hD hψ hsym hmarg hfwd
  have hδδ : δ + δ = 2 * δ := by ring
  rw [hδδ] at hmain
  exact hmain

/-- The coarse one-sided commutator estimate of `lem:pasting`. The two
comparisons `eq:pasting-1` move the coarse codeword families of the two
generators onto the joint projective answer measurement placed on the opposite
factor, so the two coarse families approximately commute on the state, with one
universal constant. This is step 3 of the proof of the adopted statement in
`docs/paper-gaps/qpbt_pasting-product-error.tex`; blueprint
`ch12_qpbt_games.tex:960-990`. -/
theorem exists_coarse_commutator_bound :
    ∃ C : ℝ, 1 ≤ C ∧
      ∀ {X Y₁ Y₂ R₁ R₂ Γ₁ Γ₂ ι : Type*}
        [Fintype X] [DecidableEq X] [Fintype Y₁] [DecidableEq Y₁]
        [Fintype Y₂] [DecidableEq Y₂] [Fintype R₁] [DecidableEq R₁]
        [Fintype R₂] [DecidableEq R₂] [Fintype Γ₁] [DecidableEq Γ₁]
        [Fintype Γ₂] [DecidableEq Γ₂] [Fintype ι] [DecidableEq ι]
        (D : Distribution ((X × Y₁) × Y₂))
        (eval₁ : Γ₁ → Y₁ → R₁) (eval₂ : Γ₂ → Y₂ → R₂)
        (G₁ : X → Measurement Γ₁ ι) (G₂ : X → Measurement Γ₂ ι)
        (A : ((X × Y₁) × Y₂) → Measurement (R₁ × R₂) ι)
        (ψ : EuclideanSpace ℂ (ι × ι)) (δ : ℝ),
        (∀ q, MIPStarRE.QPBT.Measurement.IsProjective (A q)) →
        consistencyDefect D
          (fun q a₁ => heteroKron (((A q).postprocess Prod.fst).effect a₁) 1)
          (fun q a₁ => heteroKron 1 (((G₁ q.1.1).postprocess
            (fun g => eval₁ g q.1.2)).effect a₁)) ψ ≤ δ →
        consistencyDefect D
          (fun q a₂ => heteroKron (((A q).postprocess Prod.snd).effect a₂) 1)
          (fun q a₂ => heteroKron 1 (((G₂ q.1.1).postprocess
            (fun g => eval₂ g q.2)).effect a₂)) ψ ≤ δ →
        opFamilyDistSq D
          (fun q (a : R₁ × R₂) => heteroKron 1
            (((G₁ q.1.1).postprocess (fun g => eval₁ g q.1.2)).effect a.1 *
                ((G₂ q.1.1).postprocess (fun g => eval₂ g q.2)).effect a.2 -
              ((G₂ q.1.1).postprocess (fun g => eval₂ g q.2)).effect a.2 *
                ((G₁ q.1.1).postprocess (fun g => eval₁ g q.1.2)).effect a.1))
          (fun _ _ => 0) ψ ≤ C * δ := by
  classical
  obtain ⟨C₀, hC₀, hcomm⟩ := opDistSq_commutator_right_le
  refine ⟨2 * C₀, by linarith, ?_⟩
  intro X Y₁ Y₂ R₁ R₂ Γ₁ Γ₂ ι _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    D eval₁ eval₂ G₁ G₂ A ψ δ hA h₁ h₂
  set P : ((X × Y₁) × Y₂) → Measurement R₁ ι :=
    fun q => (G₁ q.1.1).postprocess (fun g => eval₁ g q.1.2) with hPdef
  set Q : ((X × Y₁) × Y₂) → Measurement R₂ ι :=
    fun q => (G₂ q.1.1).postprocess (fun g => eval₂ g q.2) with hQdef
  let f₁ : R₁ ≃ (Unit × R₁) :=
    ⟨fun a => ((), a), fun p => p.2, fun _ => rfl, by rintro ⟨⟨⟩, a⟩; rfl⟩
  let f₂ : R₂ ≃ (Unit × R₂) :=
    ⟨fun a => ((), a), fun p => p.2, fun _ => rfl, by rintro ⟨⟨⟩, a⟩; rfl⟩
  let eB : ((Unit × R₁) × R₂) ≃ (R₁ × R₂) :=
    ⟨fun p => (p.1.2, p.2), fun a => (((), a.1), a.2),
      by rintro ⟨⟨⟨⟩, a⟩, b⟩; rfl, fun _ => rfl⟩
  let AR : ((X × Y₁) × Y₂) → Measurement (Unit × R₁) ι :=
    fun q => Measurement.congrAlphabet f₁.symm (P q)
  let DR : ((X × Y₁) × Y₂) → Measurement (Unit × R₂) ι :=
    fun q => Measurement.congrAlphabet f₂.symm (Q q)
  let BJ : ((X × Y₁) × Y₂) → Measurement ((Unit × R₁) × R₂) ι :=
    fun q => Measurement.congrAlphabet eB (A q)
  have hBJ : ∀ q, MIPStarRE.QPBT.Measurement.IsProjective (BJ q) :=
    fun q => Measurement.isProjective_congrAlphabet eB (A q) (hA q)
  have hd₁ : opFamilyDistSq D
      (fun q a₁ => heteroKron (((A q).postprocess Prod.fst).effect a₁) 1)
      (fun q a₁ => heteroKron 1 ((P q).effect a₁)) ψ ≤ 2 * δ := by
    refine le_trans (opFamilyDistSq_le_two_mul_consistencyDefect D
      (fun q => Measurement.leftPlacement ((A q).postprocess Prod.fst))
      (fun q => Measurement.rightPlacement (P q)) ψ) ?_
    simp only [Measurement.leftPlacement_effect,
      Measurement.rightPlacement_effect]
    linarith [h₁]
  have hd₂ : opFamilyDistSq D
      (fun q a₂ => heteroKron (((A q).postprocess Prod.snd).effect a₂) 1)
      (fun q a₂ => heteroKron 1 ((Q q).effect a₂)) ψ ≤ 2 * δ := by
    refine le_trans (opFamilyDistSq_le_two_mul_consistencyDefect D
      (fun q => Measurement.leftPlacement ((A q).postprocess Prod.snd))
      (fun q => Measurement.rightPlacement (Q q)) ψ) ?_
    simp only [Measurement.leftPlacement_effect,
      Measurement.rightPlacement_effect]
    linarith [h₂]
  have hBA : opFamilyDistSq D
      (fun q ab => heteroKron
        (((BJ q).postprocess (fun abc => abc.1)).effect ab) 1)
      (fun q ab => heteroKron 1 ((AR q).effect ab)) ψ ≤ 2 * δ := by
    refine le_trans (le_of_eq ?_) hd₁
    rw [opFamilyDistSq_reindex D f₁
      (fun q a₁ => heteroKron (((A q).postprocess Prod.fst).effect a₁) 1)
      (fun q a₁ => heteroKron 1 ((P q).effect a₁)) ψ]
    refine opFamilyDistSq_congr D _ _ _ _ ψ (fun q ab => ?_) (fun q ab => rfl)
    congr 1
    rw [Measurement.postprocess_congrAlphabet]
    simp only [Measurement.postprocess_effect]
    refine Finset.sum_congr (Finset.filter_congr fun a _ => ?_) fun _ _ => rfl
    simp [eB, f₁, Prod.ext_iff]
  have hBD : opFamilyDistSq D
      (fun q ac => heteroKron
        (((BJ q).postprocess (fun abc => (abc.1.1, abc.2))).effect ac) 1)
      (fun q ac => heteroKron 1 ((DR q).effect ac)) ψ ≤ 2 * δ := by
    refine le_trans (le_of_eq ?_) hd₂
    rw [opFamilyDistSq_reindex D f₂
      (fun q a₂ => heteroKron (((A q).postprocess Prod.snd).effect a₂) 1)
      (fun q a₂ => heteroKron 1 ((Q q).effect a₂)) ψ]
    refine opFamilyDistSq_congr D _ _ _ _ ψ (fun q ac => ?_) (fun q ac => rfl)
    congr 1
    rw [Measurement.postprocess_congrAlphabet]
    simp only [Measurement.postprocess_effect]
    refine Finset.sum_congr (Finset.filter_congr fun a _ => ?_) fun _ _ => rfl
    simp [eB, f₂, Prod.ext_iff]
  have hconc := hcomm D AR BJ DR ψ (2 * δ) hBJ hBA hBD
  rw [opFamilyDistSq_reindex D eB _ _ ψ] at hconc
  refine le_trans (le_of_eq ?_) (le_trans hconc (le_of_eq (by ring)))
  exact opFamilyDistSq_congr D _ _ _ _ ψ (fun q a => rfl) (fun q a => rfl)

/-- Averaging a collision term against the conditional collision bound. A
family of nonnegative weights indexed by pairs of distinct second codewords,
of total mass at most one for every question of the first marginal, has
average at most `η` once each pair is restricted to the second questions at
which the two codewords agree. This is the averaging step used twice in the
proof of the adopted statement in
`docs/paper-gaps/qpbt_pasting-product-error.tex`, the hypothesis being the
conditional collision assumption of `lem:pasting` written out; in step 4 to pass from the
coarse to the fine second codeword family and in step 5 to discard the
colliding part of the coarse cross term; blueprint
`ch12_qpbt_games.tex:960-990`. -/
theorem avgOver_collision_le {X Y₁ Y₂ R₂ Γ₂ : Type*}
    [Fintype X] [DecidableEq X] [Fintype Y₁] [DecidableEq Y₁]
    [Fintype Y₂] [DecidableEq Y₂] [Fintype R₂] [DecidableEq R₂]
    [Fintype Γ₂] [DecidableEq Γ₂]
    (D : Distribution ((X × Y₁) × Y₂)) (eval₂ : Γ₂ → Y₂ → R₂)
    (c : (X × Y₁) → Γ₂ → Γ₂ → ℝ) (η : ℝ)
    (hD : D.IsProbability) (hη : 0 ≤ η)
    (hc : ∀ p g g', 0 ≤ c p g g')
    (hmass : ∀ p, (∑ g : Γ₂, ∑ g' : Γ₂, if g = g' then 0 else c p g g') ≤ 1)
    (hcoll : ∀ x y₁, 0 < (D.map Prod.fst).weight (x, y₁) →
      ∀ g g' : Γ₂, g ≠ g' →
        (∑ y₂ : Y₂, D.weight ((x, y₁), y₂) *
          if eval₂ g y₂ = eval₂ g' y₂ then 1 else 0) ≤
          η * (D.map Prod.fst).weight (x, y₁)) :
    avgOver D (fun q => ∑ g : Γ₂, ∑ g' : Γ₂,
      if g = g' then 0 else
        if eval₂ g q.2 = eval₂ g' q.2 then c q.1 g g' else 0) ≤ η := by
  classical
  set FF : ((X × Y₁) × Y₂) → ℝ := fun q => ∑ g : Γ₂, ∑ g' : Γ₂,
    if g = g' then 0 else
      if eval₂ g q.2 = eval₂ g' q.2 then c q.1 g g' else 0 with hFF
  have hmarg : ∀ p : X × Y₁,
      (∑ y₂ : Y₂, D.weight (p, y₂)) = (D.map Prod.fst).weight p := by
    intro p
    have h1 : (D.map Prod.fst).weight p
        = ∑ a ∈ Finset.univ.filter (fun a : (X × Y₁) × Y₂ => a.1 = p),
            D.weight a := by
      rw [Distribution.map_weight]
      refine Finset.sum_subset
        (Finset.filter_subset_filter _ (Finset.subset_univ _)) ?_
      intro a ha hna
      refine D.outsideSupport a fun hsupp => hna ?_
      exact Finset.mem_filter.mpr ⟨hsupp, (Finset.mem_filter.mp ha).2⟩
    rw [h1, Finset.sum_filter, Fintype.sum_prod_type, Finset.sum_comm]
    exact Finset.sum_congr rfl fun y₂ _ => by simp
  have hWnn : ∀ p : X × Y₁, 0 ≤ (D.map Prod.fst).weight p :=
    fun p => (D.map Prod.fst).nonnegative p
  have hWsum : (∑ p : X × Y₁, (D.map Prod.fst).weight p) = 1 := by
    refine Distribution.IsProbability.weight_sum_univ_eq_one ?_
    unfold Distribution.IsProbability
    rw [Distribution.map_totalWeight]
    exact hD
  have hkey : ∀ (p : X × Y₁) (g g' : Γ₂),
      (∑ y₂ : Y₂, D.weight (p, y₂) *
        (if g = g' then 0 else
          if eval₂ g y₂ = eval₂ g' y₂ then c p g g' else 0)) ≤
        (if g = g' then 0 else c p g g') * (η * (D.map Prod.fst).weight p) := by
    rintro ⟨x, y₁⟩ g g'
    by_cases hgg : g = g'
    · simp [hgg]
    have hrw : ∀ y₂ : Y₂, D.weight ((x, y₁), y₂) *
        (if g = g' then 0 else
          if eval₂ g y₂ = eval₂ g' y₂ then c (x, y₁) g g' else 0) =
        c (x, y₁) g g' * (D.weight ((x, y₁), y₂) *
          (if eval₂ g y₂ = eval₂ g' y₂ then 1 else 0)) := by
      intro y₂
      rw [if_neg hgg]
      by_cases hcol : eval₂ g y₂ = eval₂ g' y₂
      · simp [hcol]
        ring
      · simp [hcol]
    rw [Finset.sum_congr rfl (fun y₂ _ => hrw y₂), ← Finset.mul_sum, if_neg hgg]
    rcases lt_or_eq_of_le (hWnn (x, y₁)) with hpos | hzero
    · exact mul_le_mul_of_nonneg_left (hcoll x y₁ hpos g g' hgg) (hc (x, y₁) g g')
    · have hz : ∀ y₂ : Y₂, D.weight ((x, y₁), y₂) = 0 := by
        intro y₂
        have hsum : (∑ z : Y₂, D.weight ((x, y₁), z)) = 0 := by
          rw [hmarg (x, y₁), ← hzero]
        exact le_antisymm
          ((Finset.single_le_sum (fun z _ => D.nonnegative ((x, y₁), z))
            (Finset.mem_univ y₂)).trans_eq hsum) (D.nonnegative _)
      rw [← hzero]
      simp [hz]
  calc avgOver D FF
      = ∑ q : (X × Y₁) × Y₂, D.weight q * FF q :=
        (Distribution.sum_univ_eq_sum_support D (fun q => D.weight q * FF q)
          (fun q hq => by rw [D.outsideSupport q hq, zero_mul])).symm
    _ = ∑ p : X × Y₁, ∑ y₂ : Y₂, D.weight (p, y₂) * FF (p, y₂) :=
        Fintype.sum_prod_type _
    _ = ∑ p : X × Y₁, ∑ g : Γ₂, ∑ g' : Γ₂, ∑ y₂ : Y₂,
          D.weight (p, y₂) *
            (if g = g' then 0 else
              if eval₂ g y₂ = eval₂ g' y₂ then c p g g' else 0) := by
        refine Finset.sum_congr rfl fun p _ => ?_
        simp only [hFF, Finset.mul_sum]
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun g _ => Finset.sum_comm
    _ ≤ ∑ p : X × Y₁, ∑ g : Γ₂, ∑ g' : Γ₂,
          (if g = g' then 0 else c p g g') *
            (η * (D.map Prod.fst).weight p) :=
        Finset.sum_le_sum fun p _ => Finset.sum_le_sum fun g _ =>
          Finset.sum_le_sum fun g' _ => hkey p g g'
    _ = ∑ p : X × Y₁,
          (∑ g : Γ₂, ∑ g' : Γ₂, if g = g' then 0 else c p g g') *
            (η * (D.map Prod.fst).weight p) := by
        simp only [← Finset.sum_mul]
    _ ≤ ∑ p : X × Y₁, 1 * (η * (D.map Prod.fst).weight p) :=
        Finset.sum_le_sum fun p _ => mul_le_mul_of_nonneg_right (hmass p)
          (mul_nonneg hη (hWnn p))
    _ = η * ∑ p : X × Y₁, (D.map Prod.fst).weight p := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun p _ => by ring
    _ = η := by rw [hWsum, mul_one]


/-- Fine-to-coarse comparison of the cross consistency of the second codeword
family. Two distinct fine codewords contribute to the coarse cross term exactly
when they disagree at the sampled second question, so the fine cross term
exceeds the coarse one by the colliding pairs, whose average is at most the
conditional collision bound of `lem:pasting`. This is the operator identity of
step 4 of the proof of the adopted statement in
`docs/paper-gaps/qpbt_pasting-product-error.tex`; blueprint
`ch12_qpbt_games.tex:960-990`. -/
theorem consistencyDefect_codeword_fine_le_coarse_add
    {X Y₁ Y₂ R₂ Γ₂ ι : Type*}
    [Fintype X] [DecidableEq X] [Fintype Y₁] [DecidableEq Y₁]
    [Fintype Y₂] [DecidableEq Y₂] [Fintype R₂] [DecidableEq R₂]
    [Fintype Γ₂] [DecidableEq Γ₂] [Fintype ι] [DecidableEq ι]
    (D : Distribution ((X × Y₁) × Y₂)) (eval₂ : Γ₂ → Y₂ → R₂)
    (G₂ : X → Measurement Γ₂ ι) (ψ : EuclideanSpace ℂ (ι × ι)) (η : ℝ)
    (hD : D.IsProbability) (hψ : ‖ψ‖ = 1) (hη : 0 ≤ η)
    (hcoll : ∀ x y₁, 0 < (D.map Prod.fst).weight (x, y₁) →
      ∀ g g' : Γ₂, g ≠ g' →
        (∑ y₂ : Y₂, D.weight ((x, y₁), y₂) *
          if eval₂ g y₂ = eval₂ g' y₂ then 1 else 0) ≤
          η * (D.map Prod.fst).weight (x, y₁)) :
    consistencyDefect D
        (fun q g => heteroKron ((G₂ q.1.1).effect g) 1)
        (fun q g => heteroKron 1 ((G₂ q.1.1).effect g)) ψ ≤
      consistencyDefect D
        (fun q a₂ => heteroKron (((G₂ q.1.1).postprocess
          (fun g => eval₂ g q.2)).effect a₂) 1)
        (fun q a₂ => heteroKron 1 (((G₂ q.1.1).postprocess
          (fun g => eval₂ g q.2)).effect a₂)) ψ + η := by
  classical
  have hcnn : ∀ (x : X) (g g' : Γ₂), 0 ≤ stateQForm ψ
      (heteroKron ((G₂ x).effect g) ((G₂ x).effect g')) := by
    intro x g g'
    exact stateQForm_nonneg ψ (kronecker_nonneg ((G₂ x).pos g) ((G₂ x).pos g'))
  have hfine : ∀ x : X,
      (∑ g : Γ₂, ∑ g' : Γ₂, if g = g' then 0 else stateQForm ψ
        (heteroKron ((G₂ x).effect g) ((G₂ x).effect g'))) =
      ‖ψ‖ ^ 2 - ∑ g : Γ₂, stateQForm ψ
        (heteroKron ((G₂ x).effect g) ((G₂ x).effect g)) := by
    intro x
    have h := point_defect_eq (leftPlacedMeasurement (ιB := ι) (G₂ x))
      (rightPlacedMeasurement (ιA := ι) (G₂ x)) ψ
    simp only [leftPlacedMeasurement, rightPlacedMeasurement,
      MIPStarRE.Quantum.Measurement.ofSumEqOne] at h
    simp_rw [placed_product_stateQForm_eq] at h
    exact h
  have hcoarse : ∀ (x : X) (y₂ : Y₂),
      (∑ r : R₂, ∑ r' : R₂, if r = r' then 0 else stateQForm ψ
        (heteroKron (((G₂ x).postprocess (fun g => eval₂ g y₂)).effect r)
          (((G₂ x).postprocess (fun g => eval₂ g y₂)).effect r'))) =
      ‖ψ‖ ^ 2 - ∑ r : R₂, stateQForm ψ
        (heteroKron (((G₂ x).postprocess (fun g => eval₂ g y₂)).effect r)
          (((G₂ x).postprocess (fun g => eval₂ g y₂)).effect r)) := by
    intro x y₂
    have h := point_defect_eq
      (leftPlacedMeasurement (ιB := ι)
        ((G₂ x).postprocess (fun g => eval₂ g y₂)))
      (rightPlacedMeasurement (ιA := ι)
        ((G₂ x).postprocess (fun g => eval₂ g y₂))) ψ
    simp only [leftPlacedMeasurement, rightPlacedMeasurement,
      MIPStarRE.Quantum.Measurement.ofSumEqOne] at h
    simp_rw [placed_product_stateQForm_eq] at h
    exact h
  have hsplit : ∀ (x : X) (y₂ : Y₂),
      (∑ g : Γ₂, ∑ g' : Γ₂, if eval₂ g y₂ = eval₂ g' y₂ then stateQForm ψ
        (heteroKron ((G₂ x).effect g) ((G₂ x).effect g')) else 0) =
      (∑ g : Γ₂, stateQForm ψ
        (heteroKron ((G₂ x).effect g) ((G₂ x).effect g))) +
      (∑ g : Γ₂, ∑ g' : Γ₂, if g = g' then 0 else
        if eval₂ g y₂ = eval₂ g' y₂ then stateQForm ψ
          (heteroKron ((G₂ x).effect g) ((G₂ x).effect g')) else 0) := by
    intro x y₂
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun g _ => ?_
    have hterm : ∀ g' : Γ₂,
        (if g = g' then (0 : ℝ) else
          if eval₂ g y₂ = eval₂ g' y₂ then stateQForm ψ
            (heteroKron ((G₂ x).effect g) ((G₂ x).effect g')) else 0) =
        (if eval₂ g y₂ = eval₂ g' y₂ then stateQForm ψ
            (heteroKron ((G₂ x).effect g) ((G₂ x).effect g')) else 0) -
        (if g = g' then stateQForm ψ
            (heteroKron ((G₂ x).effect g) ((G₂ x).effect g')) else 0) := by
      intro g'
      by_cases hg : g = g'
      · subst hg; simp
      · simp [hg]
    rw [Finset.sum_congr rfl (fun g' (_ : g' ∈ Finset.univ) => hterm g'),
      Finset.sum_sub_distrib]
    have hdel : (∑ g' : Γ₂, if g = g' then stateQForm ψ
        (heteroKron ((G₂ x).effect g) ((G₂ x).effect g')) else 0) =
        stateQForm ψ (heteroKron ((G₂ x).effect g) ((G₂ x).effect g)) := by
      simp
    rw [hdel]
    ring
  have hkey : ∀ q : (X × Y₁) × Y₂,
      (∑ g : Γ₂, ∑ g' : Γ₂, if g = g' then 0 else stateQForm ψ
        (heteroKron ((G₂ q.1.1).effect g) ((G₂ q.1.1).effect g'))) =
      (∑ r : R₂, ∑ r' : R₂, if r = r' then 0 else stateQForm ψ
        (heteroKron (((G₂ q.1.1).postprocess (fun g => eval₂ g q.2)).effect r)
          (((G₂ q.1.1).postprocess
            (fun g => eval₂ g q.2)).effect r'))) +
      (∑ g : Γ₂, ∑ g' : Γ₂, if g = g' then 0 else
        if eval₂ g q.2 = eval₂ g' q.2 then stateQForm ψ
          (heteroKron ((G₂ q.1.1).effect g) ((G₂ q.1.1).effect g')) else 0) := by
    intro q
    rw [hfine q.1.1, hcoarse q.1.1 q.2,
      SandwichProduct.diagonal_postprocess_stateQForm_eq_pair_sum (G₂ q.1.1) (G₂ q.1.1) ψ
        (fun g => eval₂ g q.2), hsplit q.1.1 q.2]
    ring
  have hmass : ∀ p : X × Y₁,
      (∑ g : Γ₂, ∑ g' : Γ₂, if g = g' then 0 else stateQForm ψ
        (heteroKron ((G₂ p.1).effect g) ((G₂ p.1).effect g'))) ≤ 1 := by
    intro p
    rw [hfine p.1, hψ, one_pow]
    have hnn : 0 ≤ ∑ g : Γ₂, stateQForm ψ
        (heteroKron ((G₂ p.1).effect g) ((G₂ p.1).effect g)) :=
      Finset.sum_nonneg fun g _ => hcnn p.1 g g
    linarith
  have havg := avgOver_collision_le D eval₂
    (fun p g g' => stateQForm ψ
      (heteroKron ((G₂ p.1).effect g) ((G₂ p.1).effect g'))) η hD hη
    (fun p g g' => hcnn p.1 g g') hmass hcoll
  rw [SandwichProduct.consistencyDefect_placed_eq_avg_point D (fun q => G₂ q.1.1)
      (fun q => G₂ q.1.1) ψ,
    SandwichProduct.consistencyDefect_placed_eq_avg_point D
      (fun q => (G₂ q.1.1).postprocess (fun g => eval₂ g q.2))
      (fun q => (G₂ q.1.1).postprocess (fun g => eval₂ g q.2)) ψ]
  rw [avgOver_congr D _ _ hkey, avgOver_add]
  linarith
end MIPStarRE.QPBT
