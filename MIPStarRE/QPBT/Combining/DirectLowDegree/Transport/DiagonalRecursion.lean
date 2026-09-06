import MIPStarRE.QPBT.Combining.DirectLowDegree.Transport.BranchComparison

/-!
# Diagonal branches of the coordinate strategies of the direct low-degree game

The LDT `j`-restricted diagonal sampler decodes to a direct direction with
vanishing prefix below the reversed index `i = Fin.rev j`, and the transported
question of `Transport.Questions` carries the leading index of that direction.
On the generic event that the direction is nonzero at `i`, the leading index
is `i` and the question is the canonical direct question of the direct sample
`(p, i, v)`, where the LDT defect is bounded by the direct rejection.
Otherwise the restricted direction is also the restriction at the next index,
so the LDT quantity recurses to that index with the factor `q⁻¹`, the
probability that the sampled coordinate vanishes; at the last index the zero
direction has the last coordinate as its leading index by convention and no
recursion occurs.  Summing the recursion shows that each LDT diagonal branch
is at most `q / (q - 1) ≤ 2` times the corresponding branch rejection of the
direct game.  The factor is genuine: a strategy that answers the canonical
question of a direction badly and the non-canonical questions of the same
geometric line well has LDT diagonal failure exceeding the direct branch
rejection.

## References

- `references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:214-458`
- `references/ldt-paper/test_definition.tex:49-65,130-151`
- Blueprint `def:ld-question-distribution`, `lem:ld-aline-level`,
  `lem:ld-dline-level`, `lem:ld-question-typed-cl`, `lem:alnf`, and `lem:dlnf`
- `docs/paper-gaps/qpbt_ld-dimension-divisibility.tex`
-/

open scoped BigOperators MatrixOrder Matrix ComplexOrder

namespace MIPStarRE.QPBT

open MIPStarRE.LDT
open MIPStarRE.Quantum

noncomputable section

/-! ## Direction coordinates and the one-coordinate recursion

The LDT `j`-restricted diagonal sampler decodes to a direct direction with
vanishing prefix below the reversed index `i = Fin.rev j`, and the transported
question carries the leading index of that direction.  On the generic event
that the direction is nonzero at `i`, the leading index is `i` and the
question is the canonical direct question of the direct sample `(p, i, v)`.
Otherwise the restricted direction is also the restriction at the next index,
so the LDT quantity recurses with the factor `q⁻¹`, the probability that
the sampled coordinate vanishes.  At the last index the zero direction has the
last coordinate as its leading index by convention, and no recursion occurs. -/

section DirectionCoordinates

variable (D : DirectLdParams)

/-- Restricting at an index where the direction vanishes is restricting at the
next index. -/
private theorem directPrefixProjection_succ_of_zero
    (i i' : Fin D.m) (hi : i'.val = i.val + 1)
    (v : Fin D.m → DirectScalarQ D) (hv : v i = 0) :
    directPrefixProjection i v = directPrefixProjection i' v := by
  funext j
  unfold directPrefixProjection
  by_cases hj : j.val < i.val
  · rw [if_pos hj, if_pos (by omega)]
  · by_cases hj' : j.val < i'.val
    · rw [if_neg hj, if_pos hj']
      have hji : j = i := Fin.ext (by omega)
      rw [hji, hv]
    · rw [if_neg hj, if_neg hj']

/-- Restriction beyond a coordinate ignores translation along that
coordinate. -/
private theorem directPrefixProjection_add_single
    (i i' : Fin D.m) (hi : i.val < i'.val)
    (v : Fin D.m → DirectScalarQ D) (c : DirectScalarQ D) :
    directPrefixProjection i' (v + c • Pi.single i (1 : DirectScalarQ D)) =
      directPrefixProjection i' v := by
  funext j
  unfold directPrefixProjection
  by_cases hj : j.val < i'.val
  · rw [if_pos hj, if_pos hj]
  · rw [if_neg hj, if_neg hj]
    have hji : j ≠ i := by
      intro h
      apply hj
      rw [h]
      exact hi
    simp [Pi.single_eq_of_ne hji]

/-- At the last coordinate the restricted direction has that coordinate as
its leading index: either the direction is nonzero there, or the restricted
direction is zero and the leading index of the zero direction is the last
coordinate by convention. -/
private theorem directDiagonalIndexOf_prefixProjection_last
    (i : Fin D.m) (hi : i.val + 1 = D.m) (v : Fin D.m → DirectScalarQ D) :
    directDiagonalIndexOf D (directPrefixProjection i v) = i := by
  by_cases hv : v i = 0
  · have hzero : directPrefixProjection i v = 0 := by
      funext j
      unfold directPrefixProjection
      by_cases hj : j.val < i.val
      · rw [if_pos hj]
        rfl
      · rw [if_neg hj]
        have hji : j = i := Fin.ext (by have := j.isLt; omega)
        rw [hji, hv]
        rfl
    rw [hzero]
    have hsupp : ¬ (directionSupport D (0 : Fin D.m → DirectScalarQ D)).Nonempty := by
      rintro ⟨j, hj⟩
      exact (mem_directionSupport D 0 j).mp hj rfl
    unfold directDiagonalIndexOf
    rw [dif_neg hsupp]
    apply Fin.ext
    rw [Fin.val_rev]
    simp only [DirectLdParams.firstIndex]
    omega
  · exact directDiagonalIndexOf_prefixProjection D i v hv

/-- Restricting to the vanishing of a coordinate below the restriction index
scales the uniform average by the inverse field size: translation along that
coordinate permutes the directions and preserves the restriction. -/
private theorem avgOver_uniform_coord_zero (i i' : Fin D.m) (hi : i.val < i'.val)
    (G : (Fin D.m → DirectScalarQ D) → ℝ) :
    avgOver (uniformDistribution (Fin D.m → DirectScalarQ D))
        (fun v => if v i = 0 then G (directPrefixProjection i' v) else 0) =
      (Fintype.card (DirectScalarQ D) : ℝ)⁻¹ *
        avgOver (uniformDistribution (Fin D.m → DirectScalarQ D))
          (fun v => G (directPrefixProjection i' v)) := by
  classical
  have hshift : ∀ c : DirectScalarQ D,
      (∑ v : Fin D.m → DirectScalarQ D,
        if v i = c then G (directPrefixProjection i' v) else 0) =
      ∑ v : Fin D.m → DirectScalarQ D,
        if v i = 0 then G (directPrefixProjection i' v) else 0 := by
    intro c
    refine Fintype.sum_equiv
      (Equiv.addRight ((-c) • Pi.single i (1 : DirectScalarQ D))) _ _ ?_
    intro v
    rw [Equiv.coe_addRight, directPrefixProjection_add_single D i i' hi]
    simp only [Pi.add_apply, Pi.smul_apply, Pi.single_eq_same, smul_eq_mul, mul_one,
      add_neg_eq_zero]
  have hsum : (∑ v : Fin D.m → DirectScalarQ D, G (directPrefixProjection i' v)) =
      (Fintype.card (DirectScalarQ D) : ℝ) *
        ∑ v : Fin D.m → DirectScalarQ D,
          if v i = 0 then G (directPrefixProjection i' v) else 0 := by
    calc
      (∑ v : Fin D.m → DirectScalarQ D, G (directPrefixProjection i' v)) =
          ∑ v : Fin D.m → DirectScalarQ D, ∑ c : DirectScalarQ D,
            if v i = c then G (directPrefixProjection i' v) else 0 := by
        refine Finset.sum_congr rfl fun v _ => ?_
        rw [Finset.sum_ite_eq]
        simp
      _ = ∑ c : DirectScalarQ D, ∑ v : Fin D.m → DirectScalarQ D,
            if v i = c then G (directPrefixProjection i' v) else 0 :=
        Finset.sum_comm
      _ = ∑ c : DirectScalarQ D, ∑ v : Fin D.m → DirectScalarQ D,
            if v i = 0 then G (directPrefixProjection i' v) else 0 :=
        Finset.sum_congr rfl fun c _ => hshift c
      _ = _ := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have hq : (Fintype.card (DirectScalarQ D) : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  rw [avgOver_uniform_eq_inv_card_mul_sum, avgOver_uniform_eq_inv_card_mul_sum, hsum,
    mul_left_comm, ← mul_assoc ((Fintype.card (DirectScalarQ D) : ℝ)⁻¹)
      (Fintype.card (DirectScalarQ D) : ℝ), inv_mul_cancel₀ hq, one_mul]

/-- Split a direct direction into the LDT free coordinates of the
`j`-restricted diagonal test, read in reversed coordinate order, and the
coordinates below the reversed index. -/
private def restrictedDirectionEquiv (j : Fin D.m) :
    (Fin D.m → DirectScalarQ D) ≃
      (Fin (j.val + 1) → Fq D.toLDTParameters) ×
        (Fin (Fin.rev j).val → DirectScalarQ D) where
  toFun v :=
    (fun c => directScalarEquiv D (v ⟨D.m - 1 - c.val, by have := D.hm; omega⟩),
      fun c => v ⟨c.val, by
        have h1 := c.isLt
        have h2 := Fin.val_rev j
        omega⟩)
  invFun x := fun c =>
    if h : c.val < (Fin.rev j).val then x.2 ⟨c.val, h⟩
    else (directScalarEquiv D).symm
      (x.1 ⟨D.m - 1 - c.val, by
        have h1 := c.isLt
        have h2 := j.isLt
        have h3 := Fin.val_rev j
        omega⟩)
  left_inv v := by
    funext c
    by_cases h : c.val < (Fin.rev j).val
    · simp only [dif_pos h, Fin.eta]
    · simp only [dif_neg h, Equiv.symm_apply_apply]
      refine congrArg v (Fin.ext ?_)
      change D.m - 1 - (D.m - 1 - c.val) = c.val
      have h1 := c.isLt
      have h2 := D.hm
      omega
  right_inv x := by
    refine Prod.ext ?_ ?_
    · funext c
      have h1 := c.isLt
      have h2 := j.isLt
      have h3 := Fin.val_rev j
      have hc : ¬ (D.m - 1 - c.val < (Fin.rev j).val) := by omega
      simp only [dif_neg hc, Equiv.apply_symm_apply]
      refine congrArg x.1 (Fin.ext ?_)
      change D.m - 1 - (D.m - 1 - c.val) = c.val
      omega
    · funext c
      simp only [dif_pos c.isLt, Fin.eta]

/-- The decoded `j`-restricted LDT direction of the free coordinates is the
restriction of the direction at the reversed index. -/
private theorem ldtPointToDirect_extend_restrictedDirectionEquiv (j : Fin D.m)
    (v : Fin D.m → DirectScalarQ D) :
    letI := D.toLDTFieldModel
    ldtPointToDirect D
        (extendRestrictedDirection j (restrictedDirectionEquiv D j v).1) =
      directPrefixProjection (Fin.rev j) v := by
  letI := D.toLDTFieldModel
  funext c
  by_cases hc : c.val < (Fin.rev j).val
  · rw [ldtPointToDirect_extendRestrictedDirection_prefix_zero D j _ c hc]
    unfold directPrefixProjection
    rw [if_pos hc]
  · have hrevj := Fin.val_rev j
    have hrevc := Fin.val_rev c
    have hcm := c.isLt
    have hle : (Fin.rev c).val ≤ j.val := by omega
    unfold directPrefixProjection
    rw [if_neg hc]
    simp only [ldtPointToDirect, directPointEquiv_symm_apply, extendRestrictedDirection,
      dif_pos hle, restrictedDirectionEquiv, Equiv.coe_fn_mk, Equiv.symm_apply_apply]
    refine congrArg v (Fin.ext ?_)
    change D.m - 1 - (Fin.rev c).val = c.val
    have hm := D.hm
    omega

/-- Averaging over the LDT `j`-restricted diagonal sample is averaging over
a direct point and a direct direction restricted at the reversed index. -/
private theorem avgOver_restrictedDiagonalSample_eq (j : Fin D.m)
    (H : (Fin D.m → DirectScalarQ D) → (Fin D.m → DirectScalarQ D) → ℝ) :
    letI := D.toLDTFieldModel
    avgOver (uniformDistribution (RestrictedDiagonalSample D.toLDTParameters j))
        (fun s => H (ldtPointToDirect D s.1)
          (ldtPointToDirect D (extendRestrictedDirection j s.2))) =
      avgOver (uniformDistribution
          ((Fin D.m → DirectScalarQ D) × (Fin D.m → DirectScalarQ D)))
        (fun pv => H pv.1 (directPrefixProjection (Fin.rev j) pv.2)) := by
  letI := D.toLDTFieldModel
  rw [avgOver_uniform_prod (fun u free => H (ldtPointToDirect D u)
      (ldtPointToDirect D (extendRestrictedDirection j free))),
    avgOver_uniform_prod (fun p v => H p (directPrefixProjection (Fin.rev j) v)),
    avgOver_uniform_equiv (directPointEquiv D)]
  apply avgOver_congr
  intro u
  rw [← avgOver_uniform_equiv_fst (restrictedDirectionEquiv D j)
    (fun free => H (ldtPointToDirect D u)
      (ldtPointToDirect D (extendRestrictedDirection j free)))]
  apply avgOver_congr
  intro v
  change H (ldtPointToDirect D u)
      (ldtPointToDirect D (extendRestrictedDirection j (restrictedDirectionEquiv D j v).1)) =
    H ((directPointEquiv D).symm u) (directPrefixProjection (Fin.rev j) v)
  rw [ldtPointToDirect_extend_restrictedDirectionEquiv]

end DirectionCoordinates

/-- Geometric-series bookkeeping for the one-coordinate recursion.  If every
term is at most its rejection term plus `q⁻¹` times the term at the next
index, and the term at the last index is at most its rejection term, then the
sum is at most twice the sum of the rejection terms once `q ≥ 2`. -/
private theorem sum_le_two_mul_sum_of_recursion {m : ℕ} (t r : Fin m → ℝ) (q : ℝ)
    (hq : 2 ≤ q) (ht : ∀ i, 0 ≤ t i)
    (hstep : ∀ i i' : Fin m, i'.val = i.val + 1 → t i ≤ r i + q⁻¹ * t i')
    (hlast : ∀ i : Fin m, i.val + 1 = m → t i ≤ r i) :
    ∑ i, t i ≤ 2 * ∑ i, r i := by
  classical
  have hq0 : (0 : ℝ) < q := by linarith
  have hqinv : q⁻¹ ≤ (2 : ℝ)⁻¹ := inv_anti₀ (by norm_num) hq
  have hqinv0 : (0 : ℝ) ≤ q⁻¹ := inv_nonneg.mpr hq0.le
  let succSum : Fin m → ℝ := fun i =>
    ∑ i' : Fin m, if i'.val = i.val + 1 then t i' else 0
  have hbound : ∀ i, t i ≤ r i + q⁻¹ * succSum i := by
    intro i
    by_cases h : i.val + 1 < m
    · have hsucc : succSum i = t ⟨i.val + 1, h⟩ := by
        simp only [succSum]
        rw [Finset.sum_eq_single ⟨i.val + 1, h⟩]
        · simp
        · intro b _ hb
          rw [if_neg]
          intro hb'
          exact hb (Fin.ext hb')
        · intro habs
          exact absurd (Finset.mem_univ _) habs
      rw [hsucc]
      exact hstep i ⟨i.val + 1, h⟩ rfl
    · have hlast' : i.val + 1 = m := by
        have := i.isLt
        omega
      have hsucc : succSum i = 0 := by
        simp only [succSum]
        refine Finset.sum_eq_zero fun i' _ => ?_
        rw [if_neg]
        intro h'
        have := i'.isLt
        omega
      rw [hsucc, mul_zero, add_zero]
      exact hlast i hlast'
  have hsuccSum : ∑ i, succSum i ≤ ∑ i, t i := by
    simp only [succSum]
    rw [Finset.sum_comm]
    refine Finset.sum_le_sum fun i' _ => ?_
    rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
    have hcard :
        ((Finset.univ.filter fun i : Fin m => i'.val = i.val + 1).card : ℝ) ≤ 1 := by
      have h1 : (Finset.univ.filter fun i : Fin m => i'.val = i.val + 1).card ≤ 1 := by
        rw [Finset.card_le_one]
        intro a ha b hb
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha hb
        exact Fin.ext (by omega)
      exact_mod_cast h1
    calc ((Finset.univ.filter fun i : Fin m => i'.val = i.val + 1).card : ℝ) * t i'
        ≤ 1 * t i' := mul_le_mul_of_nonneg_right hcard (ht i')
      _ = t i' := one_mul _
  have htotal : ∑ i, t i ≤ ∑ i, r i + q⁻¹ * ∑ i, t i := by
    calc ∑ i, t i ≤ ∑ i, (r i + q⁻¹ * succSum i) := Finset.sum_le_sum fun i _ => hbound i
      _ = ∑ i, r i + q⁻¹ * ∑ i, succSum i := by
        rw [Finset.sum_add_distrib, Finset.mul_sum]
      _ ≤ ∑ i, r i + q⁻¹ * ∑ i, t i := by
        linarith [mul_le_mul_of_nonneg_left hsuccSum hqinv0]
  have hT : 0 ≤ ∑ i, t i := Finset.sum_nonneg fun i _ => ht i
  have hhalf : q⁻¹ * ∑ i, t i ≤ (2 : ℝ)⁻¹ * ∑ i, t i :=
    mul_le_mul_of_nonneg_right hqinv hT
  linarith

section DiagonalRecursion

variable (D : DirectLdParams)

/-- One step of the recursion at a fixed point.  On the generic event the
leading index is the sampled index and the LDT defect is bounded by the
direct rejection there; on the vanishing event the restriction agrees with the
restriction at the next index. -/
private theorem diagonal_recursion_step
    (dd : (Fin D.m → DirectScalarQ D) → ℝ)
    (rj : Fin D.m → (Fin D.m → DirectScalarQ D) → ℝ)
    (hrj : ∀ i v, 0 ≤ rj i v)
    (hdd : ∀ v, dd v ≤ rj (directDiagonalIndexOf D v) v)
    (i i' : Fin D.m) (hi : i'.val = i.val + 1) :
    avgOver (uniformDistribution (Fin D.m → DirectScalarQ D))
        (fun v => dd (directPrefixProjection i v)) ≤
      avgOver (uniformDistribution (Fin D.m → DirectScalarQ D))
          (fun v => rj i (directPrefixProjection i v)) +
        (Fintype.card (DirectScalarQ D) : ℝ)⁻¹ *
          avgOver (uniformDistribution (Fin D.m → DirectScalarQ D))
            (fun v => dd (directPrefixProjection i' v)) := by
  classical
  have hsplit : ∀ v : Fin D.m → DirectScalarQ D,
      dd (directPrefixProjection i v) =
        (if v i = 0 then 0 else dd (directPrefixProjection i v)) +
          (if v i = 0 then dd (directPrefixProjection i' v) else 0) := by
    intro v
    by_cases hv : v i = 0
    · rw [if_pos hv, if_pos hv, zero_add,
        directPrefixProjection_succ_of_zero D i i' hi v hv]
    · rw [if_neg hv, if_neg hv, add_zero]
  rw [avgOver_congr _ _ _ hsplit, avgOver_add,
    avgOver_uniform_coord_zero D i i' (by omega) dd]
  refine add_le_add ?_ le_rfl
  refine avgOver_mono _ _ _ fun v => ?_
  by_cases hv : v i = 0
  · rw [if_pos hv]
    exact hrj i _
  · rw [if_neg hv]
    calc dd (directPrefixProjection i v) ≤
        rj (directDiagonalIndexOf D (directPrefixProjection i v))
          (directPrefixProjection i v) := hdd _
      _ = rj i (directPrefixProjection i v) := by
        rw [directDiagonalIndexOf_prefixProjection D i v hv]

/-- At the last index the LDT defect is bounded by the direct rejection
without recursion. -/
private theorem diagonal_recursion_last
    (dd : (Fin D.m → DirectScalarQ D) → ℝ)
    (rj : Fin D.m → (Fin D.m → DirectScalarQ D) → ℝ)
    (hdd : ∀ v, dd v ≤ rj (directDiagonalIndexOf D v) v)
    (i : Fin D.m) (hi : i.val + 1 = D.m) :
    avgOver (uniformDistribution (Fin D.m → DirectScalarQ D))
        (fun v => dd (directPrefixProjection i v)) ≤
      avgOver (uniformDistribution (Fin D.m → DirectScalarQ D))
        (fun v => rj i (directPrefixProjection i v)) := by
  refine avgOver_mono _ _ _ fun v => ?_
  calc dd (directPrefixProjection i v) ≤
      rj (directDiagonalIndexOf D (directPrefixProjection i v))
        (directPrefixProjection i v) := hdd _
    _ = rj i (directPrefixProjection i v) := by
      rw [directDiagonalIndexOf_prefixProjection_last D i hi v]

/-- Summed over the restriction index, the LDT diagonal quantities at a
fixed point are at most twice the direct rejections. -/
private theorem diagonal_sum_le
    (dd : (Fin D.m → DirectScalarQ D) → ℝ)
    (rj : Fin D.m → (Fin D.m → DirectScalarQ D) → ℝ)
    (hdd0 : ∀ v, 0 ≤ dd v) (hrj : ∀ i v, 0 ≤ rj i v)
    (hdd : ∀ v, dd v ≤ rj (directDiagonalIndexOf D v) v) :
    ∑ i : Fin D.m, avgOver (uniformDistribution (Fin D.m → DirectScalarQ D))
        (fun v => dd (directPrefixProjection i v)) ≤
      2 * ∑ i : Fin D.m, avgOver (uniformDistribution (Fin D.m → DirectScalarQ D))
        (fun v => rj i (directPrefixProjection i v)) := by
  have hcard : 2 ≤ Fintype.card (DirectScalarQ D) := Fintype.one_lt_card
  refine sum_le_two_mul_sum_of_recursion _ _ (Fintype.card (DirectScalarQ D) : ℝ)
    (by exact_mod_cast hcard) ?_ ?_ ?_
  · intro i
    exact avgOver_nonneg _ _ fun v => hdd0 _
  · intro i i' hi
    exact diagonal_recursion_step D dd rj hrj hdd i i' hi
  · intro i hi
    exact diagonal_recursion_last D dd rj hdd i hi

end DiagonalRecursion

/-! ## The diagonal-line branches -/

section DiagonalBranches

variable (D : DirectLdParams) (S : Strategy (directLdGame D))
  (hS : S.IsProjective) (r : Fin D.k)

/-- The rejected direct mass at the diagonal question of a direct sample with
the line on the left. -/
private def diagonalLinePointRejection (p : Fin D.m → DirectScalarQ D) (i : Fin D.m)
    (v : Fin D.m → DirectScalarQ D) : ℝ :=
  directRejectedMass D S (.dline, ⟨lineRepMap v p, i, v⟩) (directLdPointQuestionOf D p)

/-- The rejected direct mass at the diagonal question of a direct sample with
the point on the left. -/
private def diagonalPointLineRejection (p : Fin D.m → DirectScalarQ D) (i : Fin D.m)
    (v : Fin D.m → DirectScalarQ D) : ℝ :=
  directRejectedMass D S (directLdPointQuestionOf D p) (.dline, ⟨lineRepMap v p, i, v⟩)

/-- The LDT diagonal defect with the line on the left, as a function of the
decoded base point and decoded direction of the LDT line. -/
private def diagonalLinePointDefect (p v : Fin D.m → DirectScalarQ D) : ℝ :=
  letI := D.toLDTFieldModel
  qBipartiteConsDefect (directCoordinateProjStrat D S hS r).state
    (postprocess ((directCoordinateProjStrat D S hS r).diagonalMeasurementA
      (ldtDiagonalLineOf D ⟨p, D.firstIndex, v⟩)).toSubMeas (fun g => g zeroCoord))
    ((directCoordinateProjStrat D S hS r).pointMeasurementB
      (directPointEquiv D p)).toSubMeas

/-- The LDT diagonal defect with the point on the left, as a function of the
decoded base point and decoded direction of the LDT line. -/
private def diagonalPointLineDefect (p v : Fin D.m → DirectScalarQ D) : ℝ :=
  letI := D.toLDTFieldModel
  qBipartiteConsDefect (directCoordinateProjStrat D S hS r).state
    ((directCoordinateProjStrat D S hS r).pointMeasurementA
      (directPointEquiv D p)).toSubMeas
    (postprocess ((directCoordinateProjStrat D S hS r).diagonalMeasurementB
      (ldtDiagonalLineOf D ⟨p, D.firstIndex, v⟩)).toSubMeas (fun g => g zeroCoord))

/-- The canonical direct question of the LDT line of a direct sample. -/
private theorem directDiagonalQuestionOf_ldtDiagonalLineOf_eq
    (p v : Fin D.m → DirectScalarQ D) :
    directDiagonalQuestionOf D (ldtDiagonalLineOf D ⟨p, D.firstIndex, v⟩) =
      (.dline, ⟨lineRepMap v p, directDiagonalIndexOf D v, v⟩) := by
  simp [directDiagonalQuestionOf, ldtDiagonalLineOf, ldtPointToDirect]

private theorem directPointQuestionOf_directPointEquiv (p : Fin D.m → DirectScalarQ D) :
    directPointQuestionOf D (directPointEquiv D p) = directLdPointQuestionOf D p := by
  simp [directPointQuestionOf, ldtPointToDirect]

/-- The LDT diagonal defect is at most the direct rejection at the
canonical question carrying the leading index. -/
private theorem diagonalLinePointDefect_le (p v : Fin D.m → DirectScalarQ D) :
    diagonalLinePointDefect D S hS r p v ≤
      diagonalLinePointRejection D S p (directDiagonalIndexOf D v) v := by
  letI := D.toLDTFieldModel
  have h := qBipartiteConsDefect_le_directRejectedMass D S hS
    (directDiagonalQuestionOf D (ldtDiagonalLineOf D ⟨p, D.firstIndex, v⟩))
    (directPointQuestionOf D (directPointEquiv D p))
    (fun a => directDiagonalAnswerReadout D r
      (ldtDiagonalLineOf D ⟨p, D.firstIndex, v⟩) a zeroCoord)
    (directPointAnswerReadout D r)
    (fun a b hab => directDiagonalAnswerReadout_zeroCoord_eq_of_win D r
      (ldtDiagonalLineOf D ⟨p, D.firstIndex, v⟩) a b hab)
  unfold diagonalLinePointDefect diagonalLinePointRejection
  change qBipartiteConsDefect (strategyQuantumState S)
      (postprocess
        (ProjMeas.postprocess
          (matrixMeasurementToLDTProjMeas
            (S.A (directDiagonalQuestionOf D (ldtDiagonalLineOf D ⟨p, D.firstIndex, v⟩)))
            (hS.1 _))
          (directDiagonalAnswerReadout D r
            (ldtDiagonalLineOf D ⟨p, D.firstIndex, v⟩))).toSubMeas
        (fun g => g zeroCoord))
      (ProjMeas.postprocess
        (matrixMeasurementToLDTProjMeas
          (S.B (directPointQuestionOf D (directPointEquiv D p))) (hS.2 _))
        (directPointAnswerReadout D r)).toSubMeas ≤ _
  simp only [ProjMeas.postprocess_toSubMeas, SubMeas.postprocess_comp] at h ⊢
  refine le_trans h (le_of_eq ?_)
  rw [directDiagonalQuestionOf_ldtDiagonalLineOf_eq, directPointQuestionOf_directPointEquiv]

/-- The LDT diagonal defect with the point on the left is at most the
direct rejection at the canonical question carrying the leading index. -/
private theorem diagonalPointLineDefect_le (p v : Fin D.m → DirectScalarQ D) :
    diagonalPointLineDefect D S hS r p v ≤
      diagonalPointLineRejection D S p (directDiagonalIndexOf D v) v := by
  letI := D.toLDTFieldModel
  have h := qBipartiteConsDefect_le_directRejectedMass D S hS
    (directPointQuestionOf D (directPointEquiv D p))
    (directDiagonalQuestionOf D (ldtDiagonalLineOf D ⟨p, D.firstIndex, v⟩))
    (directPointAnswerReadout D r)
    (fun b => directDiagonalAnswerReadout D r
      (ldtDiagonalLineOf D ⟨p, D.firstIndex, v⟩) b zeroCoord)
    (fun a b hab => directPointAnswerReadout_eq_diagonal_zeroCoord_of_win D r
      (ldtDiagonalLineOf D ⟨p, D.firstIndex, v⟩) a b hab)
  unfold diagonalPointLineDefect diagonalPointLineRejection
  change qBipartiteConsDefect (strategyQuantumState S)
      (ProjMeas.postprocess
        (matrixMeasurementToLDTProjMeas
          (S.A (directPointQuestionOf D (directPointEquiv D p))) (hS.1 _))
        (directPointAnswerReadout D r)).toSubMeas
      (postprocess
        (ProjMeas.postprocess
          (matrixMeasurementToLDTProjMeas
            (S.B (directDiagonalQuestionOf D (ldtDiagonalLineOf D ⟨p, D.firstIndex, v⟩)))
            (hS.2 _))
          (directDiagonalAnswerReadout D r
            (ldtDiagonalLineOf D ⟨p, D.firstIndex, v⟩))).toSubMeas
        (fun g => g zeroCoord)) ≤ _
  simp only [ProjMeas.postprocess_toSubMeas, SubMeas.postprocess_comp] at h ⊢
  refine le_trans h (le_of_eq ?_)
  rw [directDiagonalQuestionOf_ldtDiagonalLineOf_eq, directPointQuestionOf_directPointEquiv]

/-- Formalization-only decomposition of a fixed ordered branch rejection into
the stored index and the remaining point-direction pair of a direct sample.
This supports the direct-to-LDT comparison corresponding to
`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:214-458`. -/
theorem directLdBranchRejectionProbability_eq_index_avg (types : LdType × LdType) :
    directLdBranchRejectionProbability D S types =
      avgOver (uniformDistribution (Fin D.m)) fun i =>
        avgOver (uniformDistribution
            ((Fin D.m → DirectScalarQ D) × (Fin D.m → DirectScalarQ D))) fun pv =>
          directRejectedMass D S
            (types.1, directLdMap D types.1 (⟨pv.1, i, pv.2⟩ : DirectLdSpace D))
            (types.2, directLdMap D types.2 (⟨pv.1, i, pv.2⟩ : DirectLdSpace D)) := by
  rw [directLdBranchRejectionProbability_eq_avgOver,
    avgOver_uniform_equiv_prod (directLdSpaceIndexEquiv D)]
  rfl

/-- The LDT line of the decoded data of an LDT line is that line. -/
private theorem ldtDiagonalLineOf_decode (u w : Point D.toLDTParameters) :
    ldtDiagonalLineOf D
        ⟨ldtPointToDirect D u, D.firstIndex, ldtPointToDirect D w⟩ =
      { base := u, direction := w } := by
  simp [ldtDiagonalLineOf, ldtPointToDirect]

/-- The LDT `j`-restricted diagonal branch with the line on the left, as
an average of the decoded defect over the point-direction pair. -/
private theorem diagonal_line_point_term_eq (j : Fin D.m) :
    letI := D.toLDTFieldModel
    bipartiteConsError (directCoordinateProjStrat D S hS r).state
        (uniformDistribution (RestrictedDiagonalSample D.toLDTParameters j))
        ((directCoordinateProjStrat D S hS r).diagonalLineAnswerFamilyA j)
        ((directCoordinateProjStrat D S hS r).diagonalPointAnswerFamilyB j) =
      avgOver (uniformDistribution
          ((Fin D.m → DirectScalarQ D) × (Fin D.m → DirectScalarQ D))) fun pv =>
        diagonalLinePointDefect D S hS r pv.1 (directPrefixProjection (Fin.rev j) pv.2) := by
  letI := D.toLDTFieldModel
  rw [← avgOver_restrictedDiagonalSample_eq D j (diagonalLinePointDefect D S hS r)]
  unfold bipartiteConsError
  apply avgOver_congr
  intro s
  unfold diagonalLinePointDefect
  rw [ldtDiagonalLineOf_decode, (directPointEquiv D).apply_symm_apply]
  rfl

/-- The LDT `j`-restricted diagonal branch with the point on the left, as
an average of the decoded defect over the point-direction pair. -/
private theorem diagonal_point_line_term_eq (j : Fin D.m) :
    letI := D.toLDTFieldModel
    bipartiteConsError (directCoordinateProjStrat D S hS r).state
        (uniformDistribution (RestrictedDiagonalSample D.toLDTParameters j))
        ((directCoordinateProjStrat D S hS r).diagonalPointAnswerFamilyA j)
        ((directCoordinateProjStrat D S hS r).diagonalLineAnswerFamilyB j) =
      avgOver (uniformDistribution
          ((Fin D.m → DirectScalarQ D) × (Fin D.m → DirectScalarQ D))) fun pv =>
        diagonalPointLineDefect D S hS r pv.1 (directPrefixProjection (Fin.rev j) pv.2) := by
  letI := D.toLDTFieldModel
  rw [← avgOver_restrictedDiagonalSample_eq D j (diagonalPointLineDefect D S hS r)]
  unfold bipartiteConsError
  apply avgOver_congr
  intro s
  unfold diagonalPointLineDefect
  rw [ldtDiagonalLineOf_decode, (directPointEquiv D).apply_symm_apply]
  rfl

/-- Summing a decoded diagonal quantity over the reversed index is summing it
over the direct index, and the point average may be taken outside. -/
private theorem sum_rev_avgOver_eq
    (F : (Fin D.m → DirectScalarQ D) → Fin D.m → (Fin D.m → DirectScalarQ D) → ℝ) :
    ∑ j : Fin D.m, avgOver (uniformDistribution
        ((Fin D.m → DirectScalarQ D) × (Fin D.m → DirectScalarQ D)))
        (fun pv => F pv.1 (Fin.rev j) (directPrefixProjection (Fin.rev j) pv.2)) =
      avgOver (uniformDistribution (Fin D.m → DirectScalarQ D)) fun p =>
        ∑ i : Fin D.m, avgOver (uniformDistribution (Fin D.m → DirectScalarQ D))
          (fun v => F p i (directPrefixProjection i v)) := by
  rw [avgOver_sum]
  have hrev := Equiv.sum_comp Fin.revPerm (fun i =>
    avgOver (uniformDistribution (Fin D.m → DirectScalarQ D)) fun p =>
      avgOver (uniformDistribution (Fin D.m → DirectScalarQ D))
        (fun v => F p i (directPrefixProjection i v)))
  simp only [Fin.revPerm_apply] at hrev
  rw [← hrev]
  refine Finset.sum_congr rfl fun j _ => ?_
  exact avgOver_uniform_prod (fun p v => F p (Fin.rev j) (directPrefixProjection (Fin.rev j) v))

/-- The direct index average of a diagonal quantity, with the point average
taken outside. -/
private theorem avgOver_index_eq
    (F : Fin D.m →
      ((Fin D.m → DirectScalarQ D) × (Fin D.m → DirectScalarQ D)) → ℝ) :
    avgOver (uniformDistribution (Fin D.m)) (fun i =>
        avgOver (uniformDistribution
          ((Fin D.m → DirectScalarQ D) × (Fin D.m → DirectScalarQ D)))
          (F i)) =
      (D.m : ℝ)⁻¹ * avgOver (uniformDistribution (Fin D.m → DirectScalarQ D)) fun p =>
        ∑ i : Fin D.m, avgOver (uniformDistribution (Fin D.m → DirectScalarQ D))
          (fun v => F i (p, v)) := by
  rw [avgOver_uniform_eq_inv_card_mul_sum, Fintype.card_fin, avgOver_sum]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  exact avgOver_uniform_prod (fun p v => F i (p, v))

/-- The diagonal-line failure with the line on the left is at most twice the
diagonal-line/point branch rejection of the direct game. -/
theorem directCoordinate_diagonal_line_point_le :
    letI := D.toLDTFieldModel
    (directCoordinateProjStrat D S hS r).diagonalLineLeftPointRightFailureProbability ≤
      2 * directLdBranchRejectionProbability D S (.dline, .point) := by
  letI := D.toLDTFieldModel
  unfold ProjStrat.diagonalLineLeftPointRightFailureProbability
  rw [directLdBranchRejectionProbability_eq_index_avg, avgOver_index_eq,
    Finset.sum_congr rfl (fun j _ => diagonal_line_point_term_eq D S hS r j),
    sum_rev_avgOver_eq D (fun p _ v => diagonalLinePointDefect D S hS r p v), one_div]
  have hmain :
      avgOver (uniformDistribution (Fin D.m → DirectScalarQ D)) (fun p =>
          ∑ i : Fin D.m, avgOver (uniformDistribution (Fin D.m → DirectScalarQ D))
            (fun v => diagonalLinePointDefect D S hS r p (directPrefixProjection i v))) ≤
        avgOver (uniformDistribution (Fin D.m → DirectScalarQ D)) (fun p =>
          2 * ∑ i : Fin D.m, avgOver (uniformDistribution (Fin D.m → DirectScalarQ D))
            (fun v => diagonalLinePointRejection D S p i (directPrefixProjection i v))) := by
    refine avgOver_mono _ _ _ fun p => ?_
    exact diagonal_sum_le D (fun v => diagonalLinePointDefect D S hS r p v)
      (fun i v => diagonalLinePointRejection D S p i v)
      (fun v => qBipartiteConsDefect_nonneg _ _ _)
      (fun i v => directRejectedMass_nonneg D S _ _)
      (fun v => diagonalLinePointDefect_le D S hS r p v)
  rw [avgOver_const_mul] at hmain
  have hm : (0 : ℝ) ≤ (D.m : ℝ)⁻¹ := by positivity
  calc (D.m : ℝ)⁻¹ * _ ≤ (D.m : ℝ)⁻¹ * (2 * _) := mul_le_mul_of_nonneg_left hmain hm
    _ = _ := by
      simp only [diagonalLinePointRejection, directLdMap, directLdPointQuestionOf]
      ring

/-- The diagonal-line failure with the point on the left is at most twice the
point/diagonal-line branch rejection of the direct game. -/
theorem directCoordinate_diagonal_point_line_le :
    letI := D.toLDTFieldModel
    (directCoordinateProjStrat D S hS r).diagonalPointLeftLineRightFailureProbability ≤
      2 * directLdBranchRejectionProbability D S (.point, .dline) := by
  letI := D.toLDTFieldModel
  unfold ProjStrat.diagonalPointLeftLineRightFailureProbability
  rw [directLdBranchRejectionProbability_eq_index_avg, avgOver_index_eq,
    Finset.sum_congr rfl (fun j _ => diagonal_point_line_term_eq D S hS r j),
    sum_rev_avgOver_eq D (fun p _ v => diagonalPointLineDefect D S hS r p v), one_div]
  have hmain :
      avgOver (uniformDistribution (Fin D.m → DirectScalarQ D)) (fun p =>
          ∑ i : Fin D.m, avgOver (uniformDistribution (Fin D.m → DirectScalarQ D))
            (fun v => diagonalPointLineDefect D S hS r p (directPrefixProjection i v))) ≤
        avgOver (uniformDistribution (Fin D.m → DirectScalarQ D)) (fun p =>
          2 * ∑ i : Fin D.m, avgOver (uniformDistribution (Fin D.m → DirectScalarQ D))
            (fun v => diagonalPointLineRejection D S p i (directPrefixProjection i v))) := by
    refine avgOver_mono _ _ _ fun p => ?_
    exact diagonal_sum_le D (fun v => diagonalPointLineDefect D S hS r p v)
      (fun i v => diagonalPointLineRejection D S p i v)
      (fun v => qBipartiteConsDefect_nonneg _ _ _)
      (fun i v => directRejectedMass_nonneg D S _ _)
      (fun v => diagonalPointLineDefect_le D S hS r p v)
  rw [avgOver_const_mul] at hmain
  have hm : (0 : ℝ) ≤ (D.m : ℝ)⁻¹ := by positivity
  calc (D.m : ℝ)⁻¹ * _ ≤ (D.m : ℝ)⁻¹ * (2 * _) := mul_le_mul_of_nonneg_left hmain hm
    _ = _ := by
      simp only [diagonalPointLineRejection, directLdMap, directLdPointQuestionOf]
      ring

end DiagonalBranches

end

end MIPStarRE.QPBT
