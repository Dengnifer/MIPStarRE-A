import MIPStarRE.QPBT.Games.Sandwich.Pasting3

/-! # Masses of the ordered products of the pasting estimate

This module records the mass estimates of step 3 of the proof of the adopted
statement of `lem:pasting` in `docs/paper-gaps/qpbt_pasting-product-error.tex`.

## References

Blueprint `ch12_qpbt_games.tex:960-990`, paper origin
`references/qpbt-paper/06_nonlocal_games_and_mipstar.tex:504-525`.
-/

open scoped BigOperators MatrixOrder Matrix ComplexOrder

namespace MIPStarRE.QPBT

open MIPStarRE.LDT hiding Measurement
open MIPStarRE.Quantum
open DistanceCalculus

/-- The squared norm of the image of a state is the quadratic form of the
operator against its adjoint. The identity of the distance calculus is inlined
here; see issue #204. -/
private theorem norm_sq_eq_stateQForm' {ι : Type*} [Fintype ι] [DecidableEq ι]
    (X : Op ι) (ψ : EuclideanSpace ℂ ι) :
    ‖applyOperatorToState X ψ‖ ^ 2 = stateQForm ψ (Xᴴ * X) := by
  have hqf : ∀ M N : Op ι, stateQForm ψ (M * N) =
      (inner ℂ (applyOperatorToState Mᴴ ψ) (applyOperatorToState N ψ)).re := by
    intro M N
    have happ : applyOperatorToState (M * N) ψ =
        applyOperatorToState M (applyOperatorToState N ψ) := by
      unfold applyOperatorToState
      simp [Matrix.toEuclideanLin, Matrix.toLpLin_mul_same]
    have hadj : (Matrix.toEuclideanLin M).adjoint = Matrix.toEuclideanLin Mᴴ := by
      rw [← Matrix.toEuclideanLin_conjTranspose_eq_adjoint]
    have h1 : (inner ℂ ((Matrix.toEuclideanLin M).adjoint ψ)
        (applyOperatorToState N ψ) : ℂ) =
        inner ℂ ψ (Matrix.toEuclideanLin M (applyOperatorToState N ψ)) :=
      LinearMap.adjoint_inner_left _ _ _
    rw [stateQForm, happ]
    rw [show applyOperatorToState Mᴴ ψ = (Matrix.toEuclideanLin M).adjoint ψ by
      rw [hadj]; rfl]
    rw [h1]
    rfl
  have hkey := hqf Xᴴ X
  rw [Matrix.conjTranspose_conjTranspose] at hkey
  rw [hkey]
  simpa using (inner_self_eq_norm_sq (𝕜 := ℂ) (applyOperatorToState X ψ)).symm

/-- A family whose adjoint products sum to the identity preserves the total
mass of a state. -/
private theorem sum_norm_sq_eq_of_sum_adjoint_mul_eq_one {γ ι : Type*}
    [Fintype γ] [Fintype ι] [DecidableEq ι]
    (C : γ → Op ι) (ψ : EuclideanSpace ℂ ι)
    (hC : (∑ c : γ, (C c)ᴴ * C c) = 1) :
    (∑ c : γ, ‖applyOperatorToState (C c) ψ‖ ^ 2) = ‖ψ‖ ^ 2 := by
  have hone : stateQForm ψ (1 : Op ι) = ‖ψ‖ ^ 2 := by
    have hid : applyOperatorToState (1 : Op ι) ψ = ψ := by
      simp [applyOperatorToState]
    rw [stateQForm, hid]
    simpa using (inner_self_eq_norm_sq (𝕜 := ℂ) ψ)
  calc (∑ c : γ, ‖applyOperatorToState (C c) ψ‖ ^ 2)
      = ∑ c : γ, stateQForm ψ ((C c)ᴴ * C c) :=
        Finset.sum_congr rfl fun c _ => norm_sq_eq_stateQForm' (C c) ψ
    _ = stateQForm ψ (∑ c : γ, (C c)ᴴ * C c) := (stateQForm_finset_sum ψ _ _).symm
    _ = ‖ψ‖ ^ 2 := by rw [hC, hone]

/-- A perturbation estimate for the total mass of a finite family of vectors:
the mass of a family of mass at most one increases by at most twice the square
root of the summed squared distance, plus that distance. -/
private theorem sum_norm_sq_le_of_mass_le_one {α ι : Type*} [Fintype α]
    [Fintype ι] [DecidableEq ι]
    (u v : α → EuclideanSpace ℂ ι) (hu : (∑ a : α, ‖u a‖ ^ 2) ≤ 1) :
    (∑ a : α, ‖v a‖ ^ 2) ≤ (∑ a : α, ‖u a‖ ^ 2) +
      2 * Real.sqrt (∑ a : α, ‖u a - v a‖ ^ 2) + ∑ a : α, ‖u a - v a‖ ^ 2 := by
  have hpt : ∀ a : α, ‖v a‖ ^ 2 ≤
      ‖u a‖ ^ 2 + 2 * (‖u a‖ * ‖u a - v a‖) + ‖u a - v a‖ ^ 2 := by
    intro a
    have hle : ‖v a‖ ≤ ‖u a‖ + ‖u a - v a‖ := by
      have := norm_sub_le (u a) (u a - v a)
      simpa using this
    nlinarith [norm_nonneg (v a), norm_nonneg (u a), norm_nonneg (u a - v a)]
  have hsum : (∑ a : α, ‖v a‖ ^ 2) ≤
      (∑ a : α, ‖u a‖ ^ 2) + 2 * (∑ a : α, ‖u a‖ * ‖u a - v a‖) +
        ∑ a : α, ‖u a - v a‖ ^ 2 := by
    have := Finset.sum_le_sum (fun a (_ : a ∈ Finset.univ) => hpt a)
    simpa [Finset.sum_add_distrib, Finset.mul_sum] using this
  have hcs : (∑ a : α, ‖u a‖ * ‖u a - v a‖) ≤
      Real.sqrt (∑ a : α, ‖u a‖ ^ 2) * Real.sqrt (∑ a : α, ‖u a - v a‖ ^ 2) := by
    simpa using Real.sum_mul_le_sqrt_mul_sqrt (s := (Finset.univ : Finset α))
      (f := fun a => ‖u a‖) (g := fun a => ‖u a - v a‖)
  have hsq : Real.sqrt (∑ a : α, ‖u a‖ ^ 2) ≤ 1 := by
    rw [show (1 : ℝ) = Real.sqrt 1 by rw [Real.sqrt_one]]
    exact Real.sqrt_le_sqrt hu
  have hnn : 0 ≤ Real.sqrt (∑ a : α, ‖u a - v a‖ ^ 2) := Real.sqrt_nonneg _
  nlinarith [hsum, hcs, hsq, hnn]

/-- The mass of the ordered products of the two coarse codeword families of
`lem:pasting` is almost one: the first family is close to a projective
measurement on the opposite factor, and reversing the order of the two
placements costs the commutator mass. This is the mass estimate of step 3 of the
proof of the adopted statement in
`docs/paper-gaps/qpbt_pasting-product-error.tex`; blueprint
`ch12_qpbt_games.tex:960-990`. -/
theorem mass_ordered_product_ge {X R₁ R₂ ι : Type*}
    [Fintype X] [DecidableEq X] [Fintype R₁] [DecidableEq R₁]
    [Fintype R₂] [DecidableEq R₂] [Fintype ι] [DecidableEq ι]
    (D : Distribution X) (Ac P : X → Measurement R₁ ι) (Q : X → Measurement R₂ ι)
    (ψ : EuclideanSpace ℂ (ι × ι)) (d K : ℝ)
    (hD : D.IsProbability) (hψ : ‖ψ‖ = 1)
    (hAc : ∀ q, MIPStarRE.QPBT.Measurement.IsProjective (Ac q))
    (hQ : ∀ q, MIPStarRE.QPBT.Measurement.IsProjective (Q q))
    (hd : opFamilyDistSq D (fun q a => heteroKron ((Ac q).effect a) 1)
      (fun q a => heteroKron 1 ((P q).effect a)) ψ ≤ d)
    (hK : opFamilyDistSq D (fun q (ab : R₁ × R₂) => heteroKron 1
      ((P q).effect ab.1 * (Q q).effect ab.2 -
        (Q q).effect ab.2 * (P q).effect ab.1)) (fun _ _ => 0) ψ ≤ K) :
    1 - 2 * Real.sqrt d - d - 2 * Real.sqrt K - K ≤
      avgOver D (fun q => ∑ ab : R₁ × R₂, ‖applyOperatorToState
        (heteroKron 1 ((P q).effect ab.1 * (Q q).effect ab.2)) ψ‖ ^ 2) := by
  classical
  -- the inlined identities of the distance calculus; see issue #204
  have hct : ∀ M N : Op ι, (heteroKron M N)ᴴ = heteroKron Mᴴ Nᴴ := by
    intro M N
    unfold heteroKron
    exact Matrix.conjTranspose_kronecker M N
  have hmulapp : ∀ (M N : Op (ι × ι)), applyOperatorToState (M * N) ψ =
      applyOperatorToState M (applyOperatorToState N ψ) := by
    intro M N
    unfold applyOperatorToState
    simp [Matrix.toEuclideanLin, Matrix.toLpLin_mul_same]
  have hlin : ∀ M N : Op (ι × ι), applyOperatorToState (M - N) ψ =
      applyOperatorToState M ψ - applyOperatorToState N ψ := by
    intro M N
    simp [applyOperatorToState]
  have hsubr : ∀ M N : Op ι,
      heteroKron (1 : Op ι) (M - N) = heteroKron 1 M - heteroKron 1 N := by
    intro M N
    ext p r
    simp [heteroKron, Matrix.kronecker, mul_sub]
  set S : X → ℝ := fun q => ∑ a : R₁,
    ‖applyOperatorToState (heteroKron 1 ((P q).effect a)) ψ‖ ^ 2 with hS
  set C1 : X → ℝ := fun q => ∑ ab : R₁ × R₂, ‖applyOperatorToState
    (heteroKron 1 ((P q).effect ab.1 * (Q q).effect ab.2)) ψ‖ ^ 2 with hC1
  set dq : X → ℝ := fun q => ∑ a : R₁, ‖applyOperatorToState
    (heteroKron ((Ac q).effect a) 1 - heteroKron 1 ((P q).effect a)) ψ‖ ^ 2 with hdq
  set kq : X → ℝ := fun q => ∑ ab : R₁ × R₂, ‖applyOperatorToState
    (heteroKron 1 ((P q).effect ab.1 * (Q q).effect ab.2 -
      (Q q).effect ab.2 * (P q).effect ab.1)) ψ‖ ^ 2 with hkq
  -- the projective family placed on the first factor carries the whole mass
  have hAcmass : ∀ q : X, (∑ a : R₁,
      ‖applyOperatorToState (heteroKron ((Ac q).effect a) 1) ψ‖ ^ 2) = 1 := by
    intro q
    have hterm : ∀ a : R₁, (heteroKron ((Ac q).effect a) (1 : Op ι))ᴴ *
        heteroKron ((Ac q).effect a) 1 = heteroKron ((Ac q).effect a) 1 := by
      intro a
      rw [hct, Matrix.conjTranspose_one, heteroKron_mul, mul_one,
        measurement_effect_hermitian (Ac q) a, (hAc q a).isIdempotentElem.eq]
    have hsum : (∑ a : R₁, (heteroKron ((Ac q).effect a) (1 : Op ι))ᴴ *
        heteroKron ((Ac q).effect a) 1) = 1 := by
      rw [Finset.sum_congr rfl fun a _ => hterm a,
        ← heteroKron_finset_sum_left, (Ac q).sum_eq_one, heteroKron_one_one]
    rw [sum_norm_sq_eq_of_sum_adjoint_mul_eq_one _ ψ hsum, hψ, one_pow]
  -- the mass of a placed measurement is at most one
  have hone : applyOperatorToState (1 : Op (ι × ι)) ψ = ψ := by
    simp [applyOperatorToState]
  have hSle : ∀ q : X, S q ≤ 1 := by
    intro q
    have hCP : ∑ a : R₁, (heteroKron (1 : Op ι) ((P q).effect a))ᴴ *
        heteroKron 1 ((P q).effect a) ≤ 1 := by
      simpa using MIPStarRE.QPBT.measurement_sum_adjoint_mul_le_one
        (Measurement.rightPlacement (ιA := ι) (P q))
    have h := sum_norm_mul_apply_le
      (fun a : R₁ => heteroKron (1 : Op ι) ((P q).effect a))
      (1 : Op (ι × ι)) ψ hCP
    rw [hone, hψ, one_pow] at h
    simpa [hS] using h
  have hC1le : ∀ q : X, C1 q ≤ 1 := by
    intro q
    simp only [hC1]
    rw [Fintype.sum_prod_type]
    exact sum_norm_ordered_product_le_one (P q) (Q q) ψ hψ
  -- reversing the order of the placements preserves the mass
  have hRv : ∀ q : X, (∑ ab : R₁ × R₂, ‖applyOperatorToState
      (heteroKron 1 ((Q q).effect ab.2 * (P q).effect ab.1)) ψ‖ ^ 2) = S q := by
    intro q
    have hQsum : (∑ b : R₂, (heteroKron (1 : Op ι) ((Q q).effect b))ᴴ *
        heteroKron 1 ((Q q).effect b)) = 1 := by
      have hterm : ∀ b : R₂, (heteroKron (1 : Op ι) ((Q q).effect b))ᴴ *
          heteroKron 1 ((Q q).effect b) = heteroKron 1 ((Q q).effect b) := by
        intro b
        rw [hct, Matrix.conjTranspose_one, heteroKron_mul, mul_one,
          measurement_effect_hermitian (Q q) b, (hQ q b).isIdempotentElem.eq]
      rw [Finset.sum_congr rfl fun b _ => hterm b,
        ← heteroKron_finset_sum_right, (Q q).sum_eq_one, heteroKron_one_one]
    rw [Fintype.sum_prod_type, hS]
    refine Finset.sum_congr rfl fun a _ => ?_
    have hsplit : ∀ b : R₂, applyOperatorToState
        (heteroKron 1 ((Q q).effect b * (P q).effect a)) ψ =
        applyOperatorToState (heteroKron (1 : Op ι) ((Q q).effect b))
          (applyOperatorToState (heteroKron 1 ((P q).effect a)) ψ) := by
      intro b
      rw [← hmulapp, heteroKron_mul, one_mul]
    rw [Finset.sum_congr rfl fun b _ => by rw [hsplit b]]
    exact sum_norm_sq_eq_of_sum_adjoint_mul_eq_one _ _ hQsum
  -- the two perturbation estimates at a fixed question
  have hP1 : ∀ q : X, 1 ≤ S q + 2 * Real.sqrt (dq q) + dq q := by
    intro q
    have h := sum_norm_sq_le_of_mass_le_one
      (fun a : R₁ => applyOperatorToState (heteroKron 1 ((P q).effect a)) ψ)
      (fun a : R₁ => applyOperatorToState (heteroKron ((Ac q).effect a) 1) ψ)
      (by simpa [hS] using hSle q)
    have hdist : (∑ a : R₁, ‖applyOperatorToState (heteroKron 1 ((P q).effect a)) ψ -
        applyOperatorToState (heteroKron ((Ac q).effect a) 1) ψ‖ ^ 2) = dq q := by
      rw [hdq]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [hlin, norm_sub_rev]
    rw [hAcmass q, hdist] at h
    simpa [hS] using h
  have hP2 : ∀ q : X, S q ≤ C1 q + 2 * Real.sqrt (kq q) + kq q := by
    intro q
    have h := sum_norm_sq_le_of_mass_le_one
      (fun ab : R₁ × R₂ => applyOperatorToState
        (heteroKron 1 ((P q).effect ab.1 * (Q q).effect ab.2)) ψ)
      (fun ab : R₁ × R₂ => applyOperatorToState
        (heteroKron 1 ((Q q).effect ab.2 * (P q).effect ab.1)) ψ)
      (by simpa [hC1] using hC1le q)
    have hdist : (∑ ab : R₁ × R₂, ‖applyOperatorToState
        (heteroKron 1 ((P q).effect ab.1 * (Q q).effect ab.2)) ψ -
        applyOperatorToState
          (heteroKron 1 ((Q q).effect ab.2 * (P q).effect ab.1)) ψ‖ ^ 2) = kq q := by
      rw [hkq]
      refine Finset.sum_congr rfl fun ab _ => ?_
      rw [hsubr, hlin]
    rw [hRv q, hdist] at h
    simpa [hC1] using h
  -- averaging the two estimates over the question
  have hdnn : ∀ q : X, 0 ≤ dq q := fun q => Finset.sum_nonneg fun a _ => sq_nonneg _
  have hknn : ∀ q : X, 0 ≤ kq q := fun q => Finset.sum_nonneg fun ab _ => sq_nonneg _
  have hdavg : avgOver D dq ≤ d := hd
  have hkavg : avgOver D kq ≤ K := by
    refine le_trans (le_of_eq ?_) hK
    refine (avgOver_congr D _ _ fun q => ?_).symm
    exact Finset.sum_congr rfl fun ab _ => by rw [sub_zero]
  have hJd : avgOver D (fun q => Real.sqrt (dq q)) ≤ Real.sqrt (avgOver D dq) :=
    le_trans (le_abs_self _)
      (MIPStarRE.LDT.Preliminaries.avgOver_abs_le_sqrt_of_pointwise D _ dq
        (fun q => by rw [abs_of_nonneg (Real.sqrt_nonneg _)]) hdnn
        (by rw [hD.weight_sum_eq_one]))
  have hJk : avgOver D (fun q => Real.sqrt (kq q)) ≤ Real.sqrt (avgOver D kq) :=
    le_trans (le_abs_self _)
      (MIPStarRE.LDT.Preliminaries.avgOver_abs_le_sqrt_of_pointwise D _ kq
        (fun q => by rw [abs_of_nonneg (Real.sqrt_nonneg _)]) hknn
        (by rw [hD.weight_sum_eq_one]))
  have hA1 : (1 : ℝ) ≤ avgOver D S + 2 * avgOver D (fun q => Real.sqrt (dq q)) +
      avgOver D dq := by
    have hmono := avgOver_mono D (fun _ : X => (1 : ℝ))
      (fun q => S q + 2 * Real.sqrt (dq q) + dq q) hP1
    rw [avgOver_const_of_isProbability D hD, avgOver_add, avgOver_add,
      avgOver_const_mul] at hmono
    exact hmono
  have hA2 : avgOver D S ≤ avgOver D C1 + 2 * avgOver D (fun q => Real.sqrt (kq q)) +
      avgOver D kq := by
    have hmono := avgOver_mono D S
      (fun q => C1 q + 2 * Real.sqrt (kq q) + kq q) hP2
    rw [avgOver_add, avgOver_add, avgOver_const_mul] at hmono
    exact hmono
  have hsd : Real.sqrt (avgOver D dq) ≤ Real.sqrt d := Real.sqrt_le_sqrt hdavg
  have hsk : Real.sqrt (avgOver D kq) ≤ Real.sqrt K := Real.sqrt_le_sqrt hkavg
  linarith

/-- The coarse pinched cross term exceeds the fine one by the colliding pairs of
second codewords. Grouping the fine effects into the fibers of the evaluation
map splits the coarse expectation into its diagonal, which is the fine
expectation, and the pairs of distinct codewords agreeing at the sampled second
question. This is the term comparison of step 5 of the proof of the adopted
statement in `docs/paper-gaps/qpbt_pasting-product-error.tex`; blueprint
`ch12_qpbt_games.tex:960-990`. -/
theorem pinched_coarse_sub_fine_eq {R₁ R₂ Γ₂ ι : Type*}
    [Fintype R₁] [DecidableEq R₁] [Fintype R₂] [DecidableEq R₂]
    [Fintype Γ₂] [DecidableEq Γ₂] [Fintype ι] [DecidableEq ι]
    (P : Measurement R₁ ι) (G : Measurement Γ₂ ι) (eval : Γ₂ → R₂)
    (ψ : EuclideanSpace ℂ (ι × ι)) :
    (∑ b : R₂, stateQForm ψ (heteroKron ((G.postprocess eval).effect b)
        (∑ a : R₁, P.effect a * (G.postprocess eval).effect b * P.effect a))) -
      (∑ g : Γ₂, stateQForm ψ (heteroKron (G.effect g)
        (∑ a : R₁, P.effect a * G.effect g * P.effect a))) =
    ∑ g : Γ₂, ∑ g' : Γ₂, if g = g' then 0 else
      if eval g = eval g' then
        ∑ a : R₁, stateQForm ψ (heteroKron (G.effect g')
          (P.effect a * G.effect g * P.effect a)) else 0 := by
  classical
  set F : Γ₂ → Γ₂ → ℝ := fun g g' => ∑ a : R₁, stateQForm ψ
    (heteroKron (G.effect g') (P.effect a * G.effect g * P.effect a)) with hF
  -- the coarse term is the sum of the fine terms over the fibers
  have hcoarse : ∀ b : R₂, stateQForm ψ
      (heteroKron ((G.postprocess eval).effect b)
        (∑ a : R₁, P.effect a * (G.postprocess eval).effect b * P.effect a)) =
      ∑ g' ∈ Finset.univ.filter (fun g' : Γ₂ => eval g' = b),
        ∑ g ∈ Finset.univ.filter (fun g : Γ₂ => eval g = b), F g g' := by
    intro b
    have hmid : (∑ a : R₁, P.effect a * (G.postprocess eval).effect b * P.effect a) =
        ∑ g ∈ Finset.univ.filter (fun g : Γ₂ => eval g = b),
          ∑ a : R₁, P.effect a * G.effect g * P.effect a := by
      simp only [MIPStarRE.Quantum.Measurement.postprocess_effect, Finset.mul_sum,
        Finset.sum_mul]
      rw [Finset.sum_comm]
    rw [hmid, MIPStarRE.Quantum.Measurement.postprocess_effect,
      heteroKron_finset_sum_left, stateQForm_finset_sum]
    refine Finset.sum_congr rfl fun g' _ => ?_
    rw [heteroKron_finset_sum_right, stateQForm_finset_sum]
    refine Finset.sum_congr rfl fun g _ => ?_
    simp only [hF]
    rw [heteroKron_finset_sum_right, stateQForm_finset_sum]
  -- the fibers of the evaluation map assemble into the colliding pairs
  have hfib : (∑ b : R₂, ∑ g' ∈ Finset.univ.filter (fun g' : Γ₂ => eval g' = b),
      ∑ g ∈ Finset.univ.filter (fun g : Γ₂ => eval g = b), F g g') =
      ∑ g' : Γ₂, ∑ g : Γ₂, if eval g = eval g' then F g g' else 0 := by
    have hstep : ∀ b : R₂, (∑ g' ∈ Finset.univ.filter (fun g' : Γ₂ => eval g' = b),
        ∑ g ∈ Finset.univ.filter (fun g : Γ₂ => eval g = b), F g g') =
        ∑ g' : Γ₂, ∑ g : Γ₂,
          if eval g' = b then (if eval g = b then F g g' else 0) else 0 := by
      intro b
      rw [Finset.sum_filter]
      refine Finset.sum_congr rfl fun g' _ => ?_
      by_cases h : eval g' = b
      · simp [h, Finset.sum_filter]
      · simp [h]
    rw [Finset.sum_congr rfl fun b _ => hstep b]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun g' _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun g _ => ?_
    rw [Finset.sum_ite_eq Finset.univ (eval g')
      (fun b => if eval g = b then F g g' else 0)]
    simp
  -- splitting off the diagonal
  have hsplit : ∀ g g' : Γ₂, (if eval g = eval g' then F g g' else 0) =
      (if g = g' then F g' g' else 0) +
        (if g = g' then 0 else if eval g = eval g' then F g g' else 0) := by
    intro g g'
    by_cases h : g = g'
    · subst h
      simp
    · simp [h]
  have hdiag : (∑ g' : Γ₂, ∑ g : Γ₂, if g = g' then F g' g' else 0) =
      ∑ g : Γ₂, F g g := by
    refine Finset.sum_congr rfl fun g' _ => ?_
    rw [Finset.sum_ite_eq' Finset.univ g' (fun _ => F g' g')]
    simp
  have hfine : (∑ g : Γ₂, stateQForm ψ (heteroKron (G.effect g)
      (∑ a : R₁, P.effect a * G.effect g * P.effect a))) = ∑ g : Γ₂, F g g := by
    refine Finset.sum_congr rfl fun g _ => ?_
    simp only [hF]
    rw [heteroKron_finset_sum_right, stateQForm_finset_sum]
  rw [Finset.sum_congr rfl fun b _ => hcoarse b, hfib, hfine]
  rw [Finset.sum_congr rfl fun g' _ =>
    Finset.sum_congr rfl fun g _ => hsplit g g']
  simp only [Finset.sum_add_distrib]
  rw [hdiag]
  have hcomm : (∑ g' : Γ₂, ∑ g : Γ₂, if g = g' then 0 else
      if eval g = eval g' then F g g' else 0) =
      ∑ g : Γ₂, ∑ g' : Γ₂, if g = g' then 0 else
        if eval g = eval g' then F g g' else 0 := Finset.sum_comm
  rw [hcomm]
  simp only [hF]
  ring

/-- The averaged commutator mass of the first codeword family against the fine
second codeword family of `lem:pasting`, in terms of the coarse commutator mass.
The two masses are expanded term by term: the reversed products contribute the
same expectation, the ordered products differ by at most the deficiency of the
coarse mass, and the two cross terms are compared after moving the rightmost
effect to the opposite tensor factor, the coarse one exceeding the fine one by
the colliding pairs of second codewords. This is step 5 of the proof of the
adopted statement in `docs/paper-gaps/qpbt_pasting-product-error.tex`; blueprint
`ch12_qpbt_games.tex:960-990`. -/
theorem commutator_mass_fine_le {X Y₁ Y₂ R₁ R₂ Γ₂ ι : Type*}
    [Fintype X] [DecidableEq X] [Fintype Y₁] [DecidableEq Y₁]
    [Fintype Y₂] [DecidableEq Y₂] [Fintype R₁] [DecidableEq R₁]
    [Fintype R₂] [DecidableEq R₂] [Fintype Γ₂] [DecidableEq Γ₂]
    [Fintype ι] [DecidableEq ι]
    (D : Distribution ((X × Y₁) × Y₂)) (eval₂ : Γ₂ → Y₂ → R₂)
    (G₂ : X → Measurement Γ₂ ι) (P : (X × Y₁) → Measurement R₁ ι)
    (ψ : EuclideanSpace ℂ (ι × ι)) (η K₀ m εc εf : ℝ)
    (hD : D.IsProbability) (hψ : ‖ψ‖ = 1) (hη : 0 ≤ η)
    (hG₂ : ∀ x, MIPStarRE.QPBT.Measurement.IsProjective (G₂ x))
    (hcoll : ∀ x y₁, 0 < (D.map Prod.fst).weight (x, y₁) →
      ∀ g g' : Γ₂, g ≠ g' →
        (∑ y₂ : Y₂, D.weight ((x, y₁), y₂) *
          if eval₂ g y₂ = eval₂ g' y₂ then 1 else 0) ≤
          η * (D.map Prod.fst).weight (x, y₁))
    (hK₀ : opFamilyDistSq D (fun q (ab : R₁ × R₂) => heteroKron 1
      ((P q.1).effect ab.1 * ((G₂ q.1.1).postprocess
          (fun g => eval₂ g q.2)).effect ab.2 -
        ((G₂ q.1.1).postprocess (fun g => eval₂ g q.2)).effect ab.2 *
          (P q.1).effect ab.1)) (fun _ _ => 0) ψ ≤ K₀)
    (hmass : 1 - m ≤ avgOver D (fun q => ∑ ab : R₁ × R₂,
      ‖applyOperatorToState (heteroKron 1 ((P q.1).effect ab.1 *
        ((G₂ q.1.1).postprocess (fun g => eval₂ g q.2)).effect ab.2)) ψ‖ ^ 2))
    (hglc : opFamilyDistSq D
      (fun q b => heteroKron 1 (((G₂ q.1.1).postprocess
        (fun g => eval₂ g q.2)).effect b))
      (fun q b => heteroKron (((G₂ q.1.1).postprocess
        (fun g => eval₂ g q.2)).effect b) 1) ψ ≤ εc)
    (hglf : opFamilyDistSq D (fun q g => heteroKron 1 ((G₂ q.1.1).effect g))
      (fun q g => heteroKron ((G₂ q.1.1).effect g) 1) ψ ≤ εf) :
    avgOver D (fun q => ∑ a : R₁, ∑ g : Γ₂, ‖applyOperatorToState
        (heteroKron 1 ((P q.1).effect a * (G₂ q.1.1).effect g -
          (G₂ q.1.1).effect g * (P q.1).effect a)) ψ‖ ^ 2) ≤
      K₀ + m + 2 * η + 2 * Real.sqrt εf + 2 * Real.sqrt εc := by
  classical
  set Qm : ((X × Y₁) × Y₂) → Measurement R₂ ι :=
    fun q => (G₂ q.1.1).postprocess (fun g => eval₂ g q.2) with hQm
  have hQproj : ∀ q, MIPStarRE.QPBT.Measurement.IsProjective (Qm q) := by
    intro q
    exact SandwichProduct.postprocess_isProjective (G₂ q.1.1) (hG₂ q.1.1) _
  set F1 : ((X × Y₁) × Y₂) → ℝ := fun q => ∑ a : R₁, ∑ g : Γ₂,
    ‖applyOperatorToState (heteroKron 1 ((P q.1).effect a *
      (G₂ q.1.1).effect g)) ψ‖ ^ 2 with hF1d
  set C1 : ((X × Y₁) × Y₂) → ℝ := fun q => ∑ a : R₁, ∑ b : R₂,
    ‖applyOperatorToState (heteroKron 1 ((P q.1).effect a *
      (Qm q).effect b)) ψ‖ ^ 2 with hC1d
  set Sq : ((X × Y₁) × Y₂) → ℝ := fun q => ∑ a : R₁,
    stateQForm ψ (heteroKron 1 ((P q.1).effect a * (P q.1).effect a)) with hSd
  set F3 : ((X × Y₁) × Y₂) → ℝ := fun q => ∑ a : R₁, ∑ g : Γ₂,
    stateQForm ψ (heteroKron 1 ((G₂ q.1.1).effect g * (P q.1).effect a *
      (G₂ q.1.1).effect g * (P q.1).effect a)) with hF3d
  set C3 : ((X × Y₁) × Y₂) → ℝ := fun q => ∑ a : R₁, ∑ b : R₂,
    stateQForm ψ (heteroKron 1 ((Qm q).effect b * (P q.1).effect a *
      (Qm q).effect b * (P q.1).effect a)) with hC3d
  set MF : ((X × Y₁) × Y₂) → ℝ := fun q => ∑ g : Γ₂,
    stateQForm ψ (heteroKron ((G₂ q.1.1).effect g)
      (∑ a : R₁, (P q.1).effect a * (G₂ q.1.1).effect g * (P q.1).effect a))
    with hMFd
  set MC : ((X × Y₁) × Y₂) → ℝ := fun q => ∑ b : R₂,
    stateQForm ψ (heteroKron ((Qm q).effect b)
      (∑ a : R₁, (P q.1).effect a * (Qm q).effect b * (P q.1).effect a))
    with hMCd
  set glf : ((X × Y₁) × Y₂) → ℝ := fun q => ∑ g : Γ₂, ‖applyOperatorToState
    (heteroKron 1 ((G₂ q.1.1).effect g) -
      heteroKron ((G₂ q.1.1).effect g) 1) ψ‖ ^ 2 with hglfd
  set glc : ((X × Y₁) × Y₂) → ℝ := fun q => ∑ b : R₂, ‖applyOperatorToState
    (heteroKron 1 ((Qm q).effect b) - heteroKron ((Qm q).effect b) 1) ψ‖ ^ 2
    with hglcd
  set col : ((X × Y₁) × Y₂) → ℝ := fun q => ∑ g : Γ₂, ∑ g' : Γ₂,
    if g = g' then 0 else if eval₂ g q.2 = eval₂ g' q.2 then
      ∑ a : R₁, stateQForm ψ (heteroKron ((G₂ q.1.1).effect g')
        ((P q.1).effect a * (G₂ q.1.1).effect g * (P q.1).effect a))
    else 0 with hcold
  -- the two expansions of the commutator masses
  have hfine : ∀ q, (∑ a : R₁, ∑ g : Γ₂, ‖applyOperatorToState
      (heteroKron 1 ((P q.1).effect a * (G₂ q.1.1).effect g -
        (G₂ q.1.1).effect g * (P q.1).effect a)) ψ‖ ^ 2) =
      F1 q + Sq q - 2 * F3 q := fun q =>
    commutator_mass_eq_expansion (P q.1) (G₂ q.1.1) ψ (hG₂ q.1.1)
  have hcoarse : ∀ q, (∑ a : R₁, ∑ b : R₂, ‖applyOperatorToState
      (heteroKron 1 ((P q.1).effect a * (Qm q).effect b -
        (Qm q).effect b * (P q.1).effect a)) ψ‖ ^ 2) =
      C1 q + Sq q - 2 * C3 q := fun q =>
    commutator_mass_eq_expansion (P q.1) (Qm q) ψ (hQproj q)
  -- the two moves and the collision split
  have hmoveF : ∀ q, |F3 q - MF q| ≤ Real.sqrt (glf q) := fun q =>
    abs_cross_move_gap_le_sqrt (P q.1) (G₂ q.1.1) ψ hψ
  have hmoveC : ∀ q, |C3 q - MC q| ≤ Real.sqrt (glc q) := fun q =>
    abs_cross_move_gap_le_sqrt (P q.1) (Qm q) ψ hψ
  have hsplit : ∀ q, MC q - MF q = col q := fun q =>
    pinched_coarse_sub_fine_eq (P q.1) (G₂ q.1.1) (fun g => eval₂ g q.2) ψ
  have hF1le : ∀ q, F1 q ≤ 1 := fun q =>
    sum_norm_ordered_product_le_one (P q.1) (G₂ q.1.1) ψ hψ
  -- averaging
  have hglfnn : ∀ q, 0 ≤ glf q := fun q => Finset.sum_nonneg fun g _ => sq_nonneg _
  have hglcnn : ∀ q, 0 ≤ glc q := fun q => Finset.sum_nonneg fun b _ => sq_nonneg _
  have hJf : |avgOver D F3 - avgOver D MF| ≤ Real.sqrt (avgOver D glf) := by
    rw [← avgOver_sub]
    exact MIPStarRE.LDT.Preliminaries.avgOver_abs_le_sqrt_of_pointwise D _ glf
      hmoveF hglfnn (by rw [hD.weight_sum_eq_one])
  have hJc : |avgOver D C3 - avgOver D MC| ≤ Real.sqrt (avgOver D glc) := by
    rw [← avgOver_sub]
    exact MIPStarRE.LDT.Preliminaries.avgOver_abs_le_sqrt_of_pointwise D _ glc
      hmoveC hglcnn (by rw [hD.weight_sum_eq_one])
  have hcolavg : avgOver D MC - avgOver D MF ≤ η := by
    rw [← avgOver_sub, avgOver_congr D _ col hsplit]
    exact avgOver_pinched_collision_le D eval₂ G₂ P ψ η hD hψ hη hcoll
  have hF1avg : avgOver D F1 ≤ 1 := by
    have := avgOver_mono D F1 (fun _ => (1 : ℝ)) hF1le
    rwa [avgOver_const_of_isProbability D hD] at this
  have hC1avg : 1 - m ≤ avgOver D C1 := by
    refine le_trans hmass (le_of_eq (avgOver_congr D _ C1 fun q => ?_))
    rw [hC1d, Fintype.sum_prod_type]
  have hK₀avg : avgOver D C1 + avgOver D Sq - 2 * avgOver D C3 ≤ K₀ := by
    have hEq : avgOver D (fun q => C1 q + Sq q - 2 * C3 q) =
        avgOver D C1 + avgOver D Sq - 2 * avgOver D C3 := by
      rw [avgOver_sub, avgOver_add, avgOver_const_mul]
    rw [← hEq]
    refine le_trans (le_of_eq ?_) hK₀
    refine avgOver_congr D _ _ fun q => ?_
    rw [← hcoarse q, Fintype.sum_prod_type]
    exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by
      rw [sub_zero]
  have hglfavg : avgOver D glf ≤ εf := hglf
  have hglcavg : avgOver D glc ≤ εc := hglc
  have hsf : Real.sqrt (avgOver D glf) ≤ Real.sqrt εf := Real.sqrt_le_sqrt hglfavg
  have hsc : Real.sqrt (avgOver D glc) ≤ Real.sqrt εc := Real.sqrt_le_sqrt hglcavg
  have hgoal : avgOver D (fun q => ∑ a : R₁, ∑ g : Γ₂, ‖applyOperatorToState
      (heteroKron 1 ((P q.1).effect a * (G₂ q.1.1).effect g -
        (G₂ q.1.1).effect g * (P q.1).effect a)) ψ‖ ^ 2) =
      avgOver D F1 + avgOver D Sq - 2 * avgOver D F3 := by
    rw [avgOver_congr D _ (fun q => F1 q + Sq q - 2 * F3 q) hfine,
      avgOver_sub, avgOver_add, avgOver_const_mul]
  rw [hgoal]
  have h1 := abs_le.mp hJf
  have h2 := abs_le.mp hJc
  linarith [h1.1, h1.2, h2.1, h2.2, hcolavg, hF1avg, hC1avg, hK₀avg, hsf, hsc]

/-- The quantitative form of `lem:pasting` with the error written out. Combining
the pinched reduction, the Cauchy--Schwarz estimate for the pinched defect and
the bound on the fine commutator mass, the defect of the pasted family is at
most twice the consistency error plus the square root of an explicit sum of
positive powers of the two errors. This is the assembly of the proof of the
adopted statement in `docs/paper-gaps/qpbt_pasting-product-error.tex`; blueprint
`ch12_qpbt_games.tex:960-990`. -/
theorem consistencyDefect_pasted_le_sqrt {X Y₁ Y₂ R₁ R₂ Γ₁ Γ₂ ι : Type*}
    [Fintype X] [DecidableEq X] [Fintype Y₁] [DecidableEq Y₁]
    [Fintype Y₂] [DecidableEq Y₂] [Fintype R₁] [DecidableEq R₁]
    [Fintype R₂] [DecidableEq R₂] [Fintype Γ₁] [DecidableEq Γ₁]
    [Fintype Γ₂] [DecidableEq Γ₂] [Fintype ι] [DecidableEq ι]
    (D : Distribution ((X × Y₁) × Y₂))
    (eval₁ : Γ₁ → Y₁ → R₁) (eval₂ : Γ₂ → Y₂ → R₂)
    (G₁ : X → Measurement Γ₁ ι) (G₂ : X → Measurement Γ₂ ι)
    (A : ((X × Y₁) × Y₂) → Measurement (R₁ × R₂) ι)
    (ψ : EuclideanSpace ℂ (ι × ι)) (η δ C : ℝ)
    (hD : D.IsProbability) (hψ : ‖ψ‖ = 1) (hη : 0 ≤ η)
    (hG₂ : ∀ x, MIPStarRE.QPBT.Measurement.IsProjective (G₂ x))
    (hA : ∀ q, MIPStarRE.QPBT.Measurement.IsProjective (A q))
    (hcoll : ∀ x y₁, 0 < (D.map Prod.fst).weight (x, y₁) →
      ∀ g g' : Γ₂, g ≠ g' →
        (∑ y₂ : Y₂, D.weight ((x, y₁), y₂) *
          if eval₂ g y₂ = eval₂ g' y₂ then 1 else 0) ≤
          η * (D.map Prod.fst).weight (x, y₁))
    (h₁ : consistencyDefect D
      (fun q a₁ => heteroKron (((A q).postprocess Prod.fst).effect a₁) 1)
      (fun q a₁ => heteroKron 1 (((G₁ q.1.1).postprocess
        (fun g => eval₁ g q.1.2)).effect a₁)) ψ ≤ δ)
    (h₂ : consistencyDefect D
      (fun q a₂ => heteroKron (((A q).postprocess Prod.snd).effect a₂) 1)
      (fun q a₂ => heteroKron 1 (((G₂ q.1.1).postprocess
        (fun g => eval₂ g q.2)).effect a₂)) ψ ≤ δ)
    (h₃ : consistencyDefect D (fun q a => heteroKron ((A q).effect a) 1)
      (fun q a => heteroKron 1 ((A q).effect a)) ψ ≤ δ)
    (h₄ : consistencyDefect D
      (fun q a₂ => heteroKron (((G₂ q.1.1).postprocess
        (fun g => eval₂ g q.2)).effect a₂) 1)
      (fun q a₂ => heteroKron 1 (((A q).postprocess Prod.snd).effect a₂)) ψ ≤ δ)
    (hK₀ : opFamilyDistSq D (fun q (ab : R₁ × R₂) => heteroKron 1
      (((G₁ q.1.1).postprocess (fun g => eval₁ g q.1.2)).effect ab.1 *
          ((G₂ q.1.1).postprocess (fun g => eval₂ g q.2)).effect ab.2 -
        ((G₂ q.1.1).postprocess (fun g => eval₂ g q.2)).effect ab.2 *
          ((G₁ q.1.1).postprocess (fun g => eval₁ g q.1.2)).effect ab.1))
      (fun _ _ => 0) ψ ≤ C * δ) :
    consistencyDefect D (fun q a => heteroKron ((A q).effect a) 1)
        (fun q a => heteroKron 1 (∑ g₁ : Γ₁, ∑ g₂ : Γ₂,
          if (eval₁ g₁ q.1.2, eval₂ g₂ q.2) = a then
            pastedMeasurement (fun g => (G₁ q.1.1).effect g)
              (fun g => (G₂ q.1.1).effect g) g₁ g₂ else 0)) ψ ≤
      2 * δ + Real.sqrt (C * δ +
        (2 * Real.sqrt (2 * δ) + 2 * δ + 2 * Real.sqrt (C * δ) + C * δ) + 2 * η +
        2 * Real.sqrt (2 * ((δ + 2 * Real.sqrt (2 * δ)) + η)) +
        2 * Real.sqrt (2 * (δ + 2 * Real.sqrt (2 * δ)))) := by
  classical
  set P : (X × Y₁) → Measurement R₁ ι :=
    fun p => (G₁ p.1).postprocess (fun g => eval₁ g p.2) with hPd
  set Ac : ((X × Y₁) × Y₂) → Measurement R₁ ι :=
    fun q => (A q).postprocess Prod.fst with hAcd
  have hAcproj : ∀ q, MIPStarRE.QPBT.Measurement.IsProjective (Ac q) := fun q =>
    SandwichProduct.postprocess_isProjective (A q) (hA q) Prod.fst
  have hQproj : ∀ q : (X × Y₁) × Y₂, MIPStarRE.QPBT.Measurement.IsProjective
      ((G₂ q.1.1).postprocess (fun g => eval₂ g q.2)) := fun q =>
    SandwichProduct.postprocess_isProjective (G₂ q.1.1) (hG₂ q.1.1) _
  -- cross consistency of the coarse and of the fine second codeword family
  have hεc : consistencyDefect D
      (fun q a₂ => heteroKron (((G₂ q.1.1).postprocess
        (fun g => eval₂ g q.2)).effect a₂) 1)
      (fun q a₂ => heteroKron 1 (((G₂ q.1.1).postprocess
        (fun g => eval₂ g q.2)).effect a₂)) ψ ≤ δ + 2 * Real.sqrt (2 * δ) :=
    consistencyDefect_codeword_cross_le D eval₂ G₂ A ψ δ hD hψ h₄ h₃ h₂
  have hεf : consistencyDefect D
      (fun q g => heteroKron ((G₂ q.1.1).effect g) 1)
      (fun q g => heteroKron 1 ((G₂ q.1.1).effect g)) ψ ≤
      (δ + 2 * Real.sqrt (2 * δ)) + η := by
    refine le_trans (consistencyDefect_codeword_fine_le_coarse_add D eval₂ G₂ ψ η
      hD hψ hη hcoll) ?_
    linarith [hεc]
  -- the two placements of the second codeword families are close
  have hglf : opFamilyDistSq D (fun q g => heteroKron 1 ((G₂ q.1.1).effect g))
      (fun q g => heteroKron ((G₂ q.1.1).effect g) 1) ψ ≤
      2 * ((δ + 2 * Real.sqrt (2 * δ)) + η) := by
    rw [← opFamilyDistSq_symm]
    refine le_trans (opFamilyDistSq_le_two_mul_consistencyDefect D
      (fun q => Measurement.leftPlacement (ιB := ι) (G₂ q.1.1))
      (fun q => Measurement.rightPlacement (ιA := ι) (G₂ q.1.1)) ψ) ?_
    simp only [Measurement.leftPlacement_effect, Measurement.rightPlacement_effect]
    linarith [hεf]
  have hglc : opFamilyDistSq D
      (fun q b => heteroKron 1 (((G₂ q.1.1).postprocess
        (fun g => eval₂ g q.2)).effect b))
      (fun q b => heteroKron (((G₂ q.1.1).postprocess
        (fun g => eval₂ g q.2)).effect b) 1) ψ ≤
      2 * (δ + 2 * Real.sqrt (2 * δ)) := by
    rw [← opFamilyDistSq_symm]
    refine le_trans (opFamilyDistSq_le_two_mul_consistencyDefect D
      (fun q => Measurement.leftPlacement (ιB := ι)
        ((G₂ q.1.1).postprocess (fun g => eval₂ g q.2)))
      (fun q => Measurement.rightPlacement (ιA := ι)
        ((G₂ q.1.1).postprocess (fun g => eval₂ g q.2))) ψ) ?_
    simp only [Measurement.leftPlacement_effect, Measurement.rightPlacement_effect]
    linarith [hεc]
  -- the first codeword family is close to the first marginal of the answers
  have hd : opFamilyDistSq D (fun q a => heteroKron ((Ac q).effect a) 1)
      (fun q a => heteroKron 1 ((P q.1).effect a)) ψ ≤ 2 * δ := by
    refine le_trans (opFamilyDistSq_le_two_mul_consistencyDefect D
      (fun q => Measurement.leftPlacement (ιB := ι) (Ac q))
      (fun q => Measurement.rightPlacement (ιA := ι) (P q.1)) ψ) ?_
    simp only [Measurement.leftPlacement_effect, Measurement.rightPlacement_effect]
    linarith [h₁]
  -- the mass of the coarse ordered products and the fine commutator mass
  have hmass := mass_ordered_product_ge D Ac (fun q => P q.1)
    (fun q => (G₂ q.1.1).postprocess (fun g => eval₂ g q.2)) ψ (2 * δ) (C * δ)
    hD hψ hAcproj hQproj hd hK₀
  have hKfine := commutator_mass_fine_le D eval₂ G₂ P ψ η (C * δ)
    (2 * Real.sqrt (2 * δ) + 2 * δ + 2 * Real.sqrt (C * δ) + C * δ)
    (2 * (δ + 2 * Real.sqrt (2 * δ)))
    (2 * ((δ + 2 * Real.sqrt (2 * δ)) + η))
    hD hψ hη hG₂ hcoll hK₀ (by linarith [hmass]) hglc hglf
  -- the pinched reduction and the Cauchy--Schwarz estimate
  have hpinch := consistencyDefect_pinched_le_marginal_add_sqrt D G₂
    (fun q => P q.1) Ac ψ (C * δ +
      (2 * Real.sqrt (2 * δ) + 2 * δ + 2 * Real.sqrt (C * δ) + C * δ) + 2 * η +
      2 * Real.sqrt (2 * ((δ + 2 * Real.sqrt (2 * δ)) + η)) +
      2 * Real.sqrt (2 * (δ + 2 * Real.sqrt (2 * δ))))
    hD hψ hAcproj hG₂ hKfine
  have hpaste := consistencyDefect_pasted_le_marginal_add_pinched D eval₁ eval₂
    G₁ G₂ A ψ hψ hG₂
  linarith [hpaste, hpinch, h₁, h₂]

/-- The defect of two placed measurement families never exceeds one. The
diagonal overlaps of the two placements are nonnegative and the total overlap
equals the squared norm of the state, so the off-diagonal sum of
`def:consistency` is at most one. Formalization-only auxiliary of the trivial
regime of `lem:pasting`, blueprint `ch12_qpbt_games.tex:195-208,960-990`. -/
theorem consistencyDefect_placed_le_one {X α ιA ιB : Type*}
    [Fintype X] [DecidableEq X] [Fintype α] [DecidableEq α]
    [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB]
    (μ : Distribution X) (A : X → Measurement α ιA) (B : X → Measurement α ιB)
    (ψ : EuclideanSpace ℂ (ιA × ιB)) (hμ : μ.IsProbability) (hψ : ‖ψ‖ = 1) :
    consistencyDefect μ (fun x a => heteroKron ((A x).effect a) 1)
      (fun x a => heteroKron 1 ((B x).effect a)) ψ ≤ 1 := by
  classical
  rw [SandwichProduct.consistencyDefect_placed_eq_avg_point]
  refine avgOver_le_of_weight_sum_le_one μ _ 1 (le_of_eq hμ.weight_sum_eq_one)
    zero_le_one ?_
  intro x
  have hpoint := point_defect_eq (leftPlacedMeasurement (ιB := ιB) (A x))
    (rightPlacedMeasurement (ιA := ιA) (B x)) ψ
  simp only [leftPlacedMeasurement, rightPlacedMeasurement,
    MIPStarRE.Quantum.Measurement.ofSumEqOne] at hpoint
  simp_rw [placed_product_stateQForm_eq] at hpoint
  have hdiag : 0 ≤ ∑ a : α, stateQForm ψ
      (heteroKron ((A x).effect a) ((B x).effect a)) :=
    Finset.sum_nonneg fun a _ => stateQForm_nonneg _
      (MIPStarRE.Quantum.kronecker_nonneg ((A x).pos a) ((B x).pos a))
  rw [hpoint, hψ]
  norm_num
  exact hdiag

/-- A square root is bounded by any nonnegative number whose square dominates
the radicand. Formalization-only arithmetic auxiliary. -/
private theorem sqrt_le_of_sq_le (X B : ℝ) (hB : 0 ≤ B) (h : X ≤ B ^ 2) :
    Real.sqrt X ≤ B := by
  calc Real.sqrt X ≤ Real.sqrt (B ^ 2) := Real.sqrt_le_sqrt h
    _ = B := Real.sqrt_sq hB

/-- The assembled error of the pasting estimate, written in the variables
`u = δ ^ (1/8)` and `v = η ^ (1/4)`, is at most `(3 * C + 19) * (v + u)` on the
unit square. Every summand of the radicand is dominated by `u ^ 2` or by
`v ^ 2`, and the square root of `(3 * C + 18) * u ^ 2 + 6 * v ^ 2` is at most
`(3 * C + 19) / 2 * u + 3 * v`. Formalization-only arithmetic auxiliary of
`lem:pasting`, blueprint `ch12_qpbt_games.tex:960-990`. -/
private theorem pasting_error_numeric_aux (C u v : ℝ) (hC : 1 ≤ C)
    (hu0 : 0 ≤ u) (hu1 : u ≤ 1) (hv0 : 0 ≤ v) (hv1 : v ≤ 1) :
    2 * u ^ 8 + Real.sqrt (C * u ^ 8 +
      (2 * Real.sqrt (2 * u ^ 8) + 2 * u ^ 8 + 2 * Real.sqrt (C * u ^ 8) +
        C * u ^ 8) + 2 * v ^ 4 +
      2 * Real.sqrt (2 * ((u ^ 8 + 2 * Real.sqrt (2 * u ^ 8)) + v ^ 4)) +
      2 * Real.sqrt (2 * (u ^ 8 + 2 * Real.sqrt (2 * u ^ 8)))) ≤
      (3 * C + 19) * (v + u) := by
  have hC0 : (0:ℝ) ≤ C := le_trans zero_le_one hC
  have hu82 : u ^ 8 ≤ u ^ 2 := pow_le_pow_of_le_one hu0 hu1 (by norm_num)
  have hu84 : u ^ 8 ≤ u ^ 4 := pow_le_pow_of_le_one hu0 hu1 (by norm_num)
  have hu42 : u ^ 4 ≤ u ^ 2 := pow_le_pow_of_le_one hu0 hu1 (by norm_num)
  have hu81 : u ^ 8 ≤ u := by
    simpa using pow_le_pow_of_le_one hu0 hu1 (show 1 ≤ 8 by norm_num)
  have hv42 : v ^ 4 ≤ v ^ 2 := pow_le_pow_of_le_one hv0 hv1 (by norm_num)
  have h1 : Real.sqrt (2 * u ^ 8) ≤ 3 / 2 * u ^ 4 := by
    refine sqrt_le_of_sq_le _ _ (by positivity) ?_
    nlinarith [pow_nonneg hu0 8]
  have h2 : Real.sqrt (C * u ^ 8) ≤ (C + 1) / 2 * u ^ 4 := by
    refine sqrt_le_of_sq_le _ _ (by positivity) ?_
    nlinarith [sq_nonneg (C - 1), pow_nonneg hu0 8]
  have h3 : Real.sqrt (2 * (u ^ 8 + 2 * Real.sqrt (2 * u ^ 8))) ≤ 3 * u ^ 2 := by
    refine sqrt_le_of_sq_le _ _ (by positivity) ?_
    nlinarith [h1, hu84, pow_nonneg hu0 4]
  have h4 : Real.sqrt (2 * ((u ^ 8 + 2 * Real.sqrt (2 * u ^ 8)) + v ^ 4)) ≤
      3 * u ^ 2 + 2 * v ^ 2 := by
    refine sqrt_le_of_sq_le _ _ (by positivity) ?_
    nlinarith [h1, hu84, pow_nonneg hu0 4, pow_nonneg hv0 4,
      mul_nonneg (sq_nonneg u) (sq_nonneg v)]
  have hCu8 : C * u ^ 8 ≤ C * u ^ 2 := mul_le_mul_of_nonneg_left hu82 hC0
  have hC1u : (C + 1) * u ^ 4 ≤ (C + 1) * u ^ 2 :=
    mul_le_mul_of_nonneg_left hu42 (by linarith)
  have hK : C * u ^ 8 +
      (2 * Real.sqrt (2 * u ^ 8) + 2 * u ^ 8 + 2 * Real.sqrt (C * u ^ 8) +
        C * u ^ 8) + 2 * v ^ 4 +
      2 * Real.sqrt (2 * ((u ^ 8 + 2 * Real.sqrt (2 * u ^ 8)) + v ^ 4)) +
      2 * Real.sqrt (2 * (u ^ 8 + 2 * Real.sqrt (2 * u ^ 8))) ≤
      (3 * C + 18) * u ^ 2 + 6 * v ^ 2 := by
    nlinarith [h1, h2, h3, h4, hu82, hu42, hv42, hCu8, hC1u]
  have hsK : Real.sqrt (C * u ^ 8 +
      (2 * Real.sqrt (2 * u ^ 8) + 2 * u ^ 8 + 2 * Real.sqrt (C * u ^ 8) +
        C * u ^ 8) + 2 * v ^ 4 +
      2 * Real.sqrt (2 * ((u ^ 8 + 2 * Real.sqrt (2 * u ^ 8)) + v ^ 4)) +
      2 * Real.sqrt (2 * (u ^ 8 + 2 * Real.sqrt (2 * u ^ 8)))) ≤
      (3 * C + 19) / 2 * u + 3 * v := by
    refine sqrt_le_of_sq_le _ _ (by positivity) ?_
    nlinarith [hK, mul_nonneg hu0 hv0, sq_nonneg u, sq_nonneg v,
      sq_nonneg (C * u), mul_nonneg (mul_nonneg hC0 hu0) hv0,
      mul_nonneg hC0 (sq_nonneg u)]
  nlinarith [hsK, hu81, mul_nonneg (sub_nonneg.mpr hC) hu0,
    mul_nonneg (sub_nonneg.mpr hC) hv0]

/-- On the unit square the assembled error of the pasting estimate is at most
`(3 * C + 19) * (η ^ (1/4) + δ ^ (1/8))`. Substituting `δ = u ^ 8` and
`η = v ^ 4` turns every summand of the radicand into a polynomial in the two
roots. Formalization-only arithmetic auxiliary of `lem:pasting`, blueprint
`ch12_qpbt_games.tex:960-990`. -/
theorem pasting_error_sqrt_le_rpow (C δ η : ℝ) (hC : 1 ≤ C) (hδ0 : 0 ≤ δ)
    (hδ1 : δ ≤ 1) (hη0 : 0 ≤ η) (hη1 : η ≤ 1) :
    2 * δ + Real.sqrt (C * δ +
      (2 * Real.sqrt (2 * δ) + 2 * δ + 2 * Real.sqrt (C * δ) + C * δ) + 2 * η +
      2 * Real.sqrt (2 * ((δ + 2 * Real.sqrt (2 * δ)) + η)) +
      2 * Real.sqrt (2 * (δ + 2 * Real.sqrt (2 * δ)))) ≤
      (3 * C + 19) * (η ^ (1/4 : ℝ) + δ ^ (1/8 : ℝ)) := by
  have hu0' : 0 ≤ δ ^ (1/8 : ℝ) := Real.rpow_nonneg hδ0 _
  have hv0' : 0 ≤ η ^ (1/4 : ℝ) := Real.rpow_nonneg hη0 _
  have hu1' : δ ^ (1/8 : ℝ) ≤ 1 := Real.rpow_le_one hδ0 hδ1 (by norm_num)
  have hv1' : η ^ (1/4 : ℝ) ≤ 1 := Real.rpow_le_one hη0 hη1 (by norm_num)
  have hδu' : δ = (δ ^ (1/8 : ℝ)) ^ 8 := by
    rw [← Real.rpow_natCast (δ ^ (1/8 : ℝ)) 8, ← Real.rpow_mul hδ0]
    norm_num
  have hηv' : η = (η ^ (1/4 : ℝ)) ^ 4 := by
    rw [← Real.rpow_natCast (η ^ (1/4 : ℝ)) 4, ← Real.rpow_mul hη0]
    norm_num
  obtain ⟨u, hu0, hu1, hδu, hue⟩ :
      ∃ u : ℝ, 0 ≤ u ∧ u ≤ 1 ∧ δ = u ^ 8 ∧ δ ^ (1/8 : ℝ) = u :=
    ⟨δ ^ (1/8 : ℝ), hu0', hu1', hδu', rfl⟩
  obtain ⟨v, hv0, hv1, hηv, hve⟩ :
      ∃ v : ℝ, 0 ≤ v ∧ v ≤ 1 ∧ η = v ^ 4 ∧ η ^ (1/4 : ℝ) = v :=
    ⟨η ^ (1/4 : ℝ), hv0', hv1', hηv', rfl⟩
  rw [hue, hve, hδu, hηv]
  exact pasting_error_numeric_aux C u v hC hu0 hu1 hv0 hv1

end MIPStarRE.QPBT
