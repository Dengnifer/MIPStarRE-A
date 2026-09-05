import MIPStarRE.QPBT.Combining.Points.Closeness
import MIPStarRE.QPBT.Combining.Witnesses

/-!
# Combining the point measurements

This module proves the construction of the joint X/Z point measurements
and defines their scalar linear coarse-graining.  The latter is
the genuine postprocessing of a complete measurement on each heterogeneous
player space.

## References

The construction is `lem:qld-4-10` in
`blueprint/src/chapter/ch15_qpbt_combining.tex`, with paper source
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:689-709`.
The coarse-graining is `lem:qld-4-12` in the same blueprint, with paper source
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:993-1011`.
-/

open scoped BigOperators Matrix MatrixOrder ComplexOrder

namespace MIPStarRE.QPBT

open MIPStarRE.LDT hiding Measurement
open MIPStarRE.Quantum

noncomputable section

/-- A pair of source points and the two scalar coefficients used by the
extended point measurement. -/
abbrev ExtendedPointQuestion (P : AdmissibleParams) :=
  ((Fin P.m -> PauliScalar P) × (Fin P.m -> PauliScalar P)) ×
    (PauliScalar P × PauliScalar P)

namespace CombinedPointsWitness

/-- Coarse-grain a joint point measurement by `(a,b) |-> alpha*a + beta*b`
on the selected player side.  This is the concrete measurement of
`lem:qld-4-12`, paper lines 993--1011. -/
noncomputable def extendedQ {P : AdmissibleParams} {ε δ : ℝ}
    {S : ProjectiveSetting P ε} (points : CombinedPointsWitness S δ)
    (side : PlayerSide) (x z : Fin P.m -> PauliScalar P)
    (alpha beta : PauliScalar P) :
    Measurement (PauliScalar P) (S.ExpandedLocalSpace side) :=
  (points.Q side x z).postprocess fun ab => alpha * ab.1 + beta * ab.2

end CombinedPointsWitness

/-- Formalization-only auxiliary for `lem:qld-4-12`: the squared norm of a
sum over one fiber of a map, summed over all fibers, is the double
inner-product sum restricted to pairs lying in a common fiber.  Blueprint
`blueprint/src/chapter/ch15_qpbt_combining.tex:1102-1145`, paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:993-1011`. -/
private theorem sum_fiber_norm_sq_aux {α κ E : Type*}
    [Fintype α] [DecidableEq α] [Fintype κ] [DecidableEq κ]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (g : α → κ) (v : α → E) :
    ∑ c : κ, ‖∑ p ∈ Finset.univ.filter (fun p => g p = c), v p‖ ^ 2 =
      ∑ p : α, ∑ r : α, if g p = g r then inner ℝ (v p) (v r) else 0 := by
  classical
  have h1 : ∀ c : κ,
      ‖∑ p ∈ Finset.univ.filter (fun p => g p = c), v p‖ ^ 2 =
        ∑ p ∈ Finset.univ.filter (fun p => g p = c),
          ∑ r ∈ Finset.univ.filter (fun p => g p = c),
            inner ℝ (v p) (v r) := by
    intro c
    rw [← real_inner_self_eq_norm_sq, sum_inner]
    exact Finset.sum_congr rfl fun p _ => inner_sum _ _ _
  have h2 : ∀ c : κ, ∀ p ∈ Finset.univ.filter (fun p => g p = c),
      (∑ r ∈ Finset.univ.filter (fun p => g p = c), inner ℝ (v p) (v r)) =
        ∑ r : α, if g p = g r then inner ℝ (v p) (v r) else 0 := by
    intro c p hp
    have hgp : g p = c := (Finset.mem_filter.mp hp).2
    rw [Finset.sum_filter]
    exact Finset.sum_congr rfl fun r _ => by
      by_cases h : g r = c
      · simp [h, hgp]
      · simp [h, hgp, Ne.symm h]
  calc
    ∑ c : κ, ‖∑ p ∈ Finset.univ.filter (fun p => g p = c), v p‖ ^ 2
        = ∑ c : κ, ∑ p ∈ Finset.univ.filter (fun p => g p = c),
            ∑ r : α, if g p = g r then inner ℝ (v p) (v r) else 0 := by
          refine Finset.sum_congr rfl fun c _ => ?_
          rw [h1 c]
          exact Finset.sum_congr rfl (h2 c)
    _ = ∑ p : α, ∑ r : α, if g p = g r then inner ℝ (v p) (v r) else 0 :=
          Finset.sum_fiberwise Finset.univ g _

/-- Formalization-only auxiliary for `lem:qld-4-12`: a nontrivial linear
equation in the two scalar coefficients of `def:combine-map` has exactly `q`
solutions.  Blueprint
`blueprint/src/chapter/ch15_qpbt_combining.tex:1102-1145`, paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:993-1011`. -/
private theorem card_filter_linear {K : Type*} [Field K] [Fintype K]
    [DecidableEq K] (d1 d2 : K) (hd : ¬(d1 = 0 ∧ d2 = 0)) :
    (Finset.univ.filter (fun ab : K × K => ab.1 * d1 + ab.2 * d2 = 0)).card =
      Fintype.card K := by
  classical
  by_cases h1 : d1 = 0
  · have h2 : d2 ≠ 0 := by tauto
    have hset :
        (Finset.univ.filter (fun ab : K × K => ab.1 * d1 + ab.2 * d2 = 0)) =
          Finset.univ.image (fun t : K => (t, (0 : K))) := by
      ext ab
      constructor
      · intro hab
        have h := (Finset.mem_filter.mp hab).2
        rw [h1, mul_zero, zero_add] at h
        have hab2 : ab.2 = 0 := by
          rcases mul_eq_zero.mp h with h' | h'
          · exact h'
          · exact absurd h' h2
        exact Finset.mem_image.mpr ⟨ab.1, Finset.mem_univ _,
          Prod.ext rfl hab2.symm⟩
      · intro hab
        obtain ⟨t, -, rfl⟩ := Finset.mem_image.mp hab
        refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
        simp [h1]
    rw [hset, Finset.card_image_of_injective _ (fun a b hab => by
      simpa using congrArg Prod.fst hab), Finset.card_univ]
  · have hset :
        (Finset.univ.filter (fun ab : K × K => ab.1 * d1 + ab.2 * d2 = 0)) =
          Finset.univ.image (fun t : K => (-(t * d2) / d1, t)) := by
      ext ab
      constructor
      · intro hab
        have h := (Finset.mem_filter.mp hab).2
        refine Finset.mem_image.mpr ⟨ab.2, Finset.mem_univ _, Prod.ext ?_ rfl⟩
        rw [div_eq_iff h1]
        linear_combination -h
      · intro hab
        obtain ⟨t, -, rfl⟩ := Finset.mem_image.mp hab
        refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
        field_simp
        ring
    rw [hset, Finset.card_image_of_injective _ (fun a b hab => by
      simpa using congrArg Prod.snd hab), Finset.card_univ]

/-- Formalization-only auxiliary for `lem:qld-4-12`: summing over the scalar
pair `(alpha, beta)` the squared norms of the coarse-grained family
`c |-> sum over alpha a + beta b = c` returns `q` times the squared norm of the
total plus `q^2 - q` times the sum of the individual squared norms.  This is
the exact form of the data-processing step of `lem:qld-4-12`, blueprint
`blueprint/src/chapter/ch15_qpbt_combining.tex:1102-1145`, paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:993-1011`; it
uses `fact:data-processing` only through the counting of the fibers. -/
private theorem sum_linearFiber_norm_sq {K E : Type*} [Field K] [Fintype K]
    [DecidableEq K] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (v : K × K → E) :
    ∑ ab : K × K, ∑ c : K,
        ‖∑ p ∈ Finset.univ.filter
            (fun p : K × K => ab.1 * p.1 + ab.2 * p.2 = c), v p‖ ^ 2 =
      (Fintype.card K : ℝ) * ‖∑ p : K × K, v p‖ ^ 2 +
        ((Fintype.card K : ℝ) ^ 2 - (Fintype.card K : ℝ)) *
          ∑ p : K × K, ‖v p‖ ^ 2 := by
  have hexp : ∀ ab : K × K,
      ∑ c : K, ‖∑ p ∈ Finset.univ.filter
          (fun p : K × K => ab.1 * p.1 + ab.2 * p.2 = c), v p‖ ^ 2 =
        ∑ p : K × K, ∑ r : K × K,
          if ab.1 * p.1 + ab.2 * p.2 = ab.1 * r.1 + ab.2 * r.2 then
            inner ℝ (v p) (v r) else 0 :=
    fun ab => sum_fiber_norm_sq_aux (fun p : K × K => ab.1 * p.1 + ab.2 * p.2) v
  have hpoint : ∀ p r : K × K,
      (∑ ab : K × K, if ab.1 * p.1 + ab.2 * p.2 = ab.1 * r.1 + ab.2 * r.2 then
          inner ℝ (v p) (v r) else 0) =
        ((Fintype.card K : ℝ) +
            (if p = r then (Fintype.card K : ℝ) ^ 2 - (Fintype.card K : ℝ)
              else 0)) * inner ℝ (v p) (v r) := by
    intro p r
    have hcond : ∀ ab : K × K,
        (ab.1 * p.1 + ab.2 * p.2 = ab.1 * r.1 + ab.2 * r.2) =
          (ab.1 * (p.1 - r.1) + ab.2 * (p.2 - r.2) = 0) := by
      intro ab
      refine propext ⟨fun h => by linear_combination h,
        fun h => by linear_combination h⟩
    simp_rw [hcond]
    rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
    by_cases hpr : p = r
    · subst hpr
      have huniv : (Finset.univ.filter
          (fun ab : K × K => ab.1 * (p.1 - p.1) + ab.2 * (p.2 - p.2) = 0)) =
          Finset.univ := by
        ext ab
        simp
      rw [huniv, Finset.card_univ, Fintype.card_prod, if_pos rfl]
      push_cast
      ring
    · have hd : ¬(p.1 - r.1 = 0 ∧ p.2 - r.2 = 0) := by
        rintro ⟨h1, h2⟩
        exact hpr (Prod.ext (by linear_combination h1)
          (by linear_combination h2))
      rw [card_filter_linear (p.1 - r.1) (p.2 - r.2) hd, if_neg hpr]
      ring
  have hswap : ∑ ab : K × K, ∑ p : K × K, ∑ r : K × K,
        (if ab.1 * p.1 + ab.2 * p.2 = ab.1 * r.1 + ab.2 * r.2 then
          inner ℝ (v p) (v r) else 0) =
      ∑ p : K × K, ∑ r : K × K, ∑ ab : K × K,
        (if ab.1 * p.1 + ab.2 * p.2 = ab.1 * r.1 + ab.2 * r.2 then
          inner ℝ (v p) (v r) else 0) := by
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun p _ => Finset.sum_comm
  have hnormsum : ∑ p : K × K, ∑ r : K × K, inner ℝ (v p) (v r) =
      ‖∑ p : K × K, v p‖ ^ 2 := by
    rw [← real_inner_self_eq_norm_sq, sum_inner]
    exact Finset.sum_congr rfl fun p _ => (inner_sum _ _ _).symm
  have hstep : ∀ p : K × K,
      (∑ r : K × K, ∑ ab : K × K,
          (if ab.1 * p.1 + ab.2 * p.2 = ab.1 * r.1 + ab.2 * r.2 then
            inner ℝ (v p) (v r) else 0)) =
        (Fintype.card K : ℝ) * (∑ r : K × K, inner ℝ (v p) (v r)) +
          ((Fintype.card K : ℝ) ^ 2 - (Fintype.card K : ℝ)) * ‖v p‖ ^ 2 := by
    intro p
    simp_rw [hpoint, add_mul, ite_mul, zero_mul]
    rw [Finset.sum_add_distrib, ← Finset.mul_sum,
      Finset.sum_ite_eq Finset.univ p
        (fun r => ((Fintype.card K : ℝ) ^ 2 - (Fintype.card K : ℝ)) *
          inner ℝ (v p) (v r))]
    simp
  simp_rw [hexp]
  rw [hswap]
  simp_rw [hstep]
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, hnormsum]

/-- Formalization-only auxiliary for `lem:qld-4-12`: for two operator families
with the same total, the average over `(alpha, beta)` of the squared distance
between their linear coarse-grainings is at most the squared distance between
the families themselves.  Blueprint
`blueprint/src/chapter/ch15_qpbt_combining.tex:1102-1145`, paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:993-1011`. -/
private theorem avgOver_linearFiber_le {K ι : Type*} [Field K] [Fintype K]
    [DecidableEq K] [Nonempty K] [Fintype ι] [DecidableEq ι]
    (A B : K × K → Op ι) (ψ : EuclideanSpace ℂ ι)
    (hsum : ∑ p : K × K, A p = ∑ p : K × K, B p) :
    avgOver (uniformDistribution (K × K)) (fun ab : K × K =>
        ∑ c : K, ‖applyOperatorToState
          ((∑ p ∈ Finset.univ.filter
              (fun p : K × K => ab.1 * p.1 + ab.2 * p.2 = c), A p) -
            (∑ p ∈ Finset.univ.filter
              (fun p : K × K => ab.1 * p.1 + ab.2 * p.2 = c), B p)) ψ‖ ^ 2) ≤
      ∑ p : K × K, ‖applyOperatorToState (A p - B p) ψ‖ ^ 2 := by
  classical
  have hlin : ∀ s : Finset (K × K),
      applyOperatorToState ((∑ p ∈ s, A p) - (∑ p ∈ s, B p)) ψ =
        ∑ p ∈ s, applyOperatorToState (A p - B p) ψ := by
    intro s
    rw [← Finset.sum_sub_distrib]
    unfold applyOperatorToState
    simp only [map_sum, LinearMap.sum_apply]
  have hzero : ∑ p : K × K, applyOperatorToState (A p - B p) ψ = 0 := by
    rw [← hlin Finset.univ, hsum, sub_self]
    unfold applyOperatorToState
    simp
  have hid := sum_linearFiber_norm_sq
    (v := fun p : K × K => applyOperatorToState (A p - B p) ψ)
  rw [hzero] at hid
  rw [avgOver_uniform_eq_inv_card_mul_sum]
  simp_rw [hlin]
  rw [hid, Fintype.card_prod]
  have hq : 0 < (Fintype.card K : ℝ) := by exact_mod_cast Fintype.card_pos
  have hS : 0 ≤ ∑ p : K × K, ‖applyOperatorToState (A p - B p) ψ‖ ^ 2 :=
    Finset.sum_nonneg fun p _ => by positivity
  push_cast
  rw [norm_zero]
  have h1 : ((Fintype.card K : ℝ) ^ 2 - (Fintype.card K : ℝ)) *
      (∑ p : K × K, ‖applyOperatorToState (A p - B p) ψ‖ ^ 2) ≤
      (Fintype.card K : ℝ) ^ 2 *
        (∑ p : K × K, ‖applyOperatorToState (A p - B p) ψ‖ ^ 2) :=
    mul_le_mul_of_nonneg_right (by linarith) hS
  calc ((Fintype.card K : ℝ) * (Fintype.card K : ℝ))⁻¹ *
        ((Fintype.card K : ℝ) * (0 : ℝ) ^ 2 +
          ((Fintype.card K : ℝ) ^ 2 - (Fintype.card K : ℝ)) *
            ∑ p : K × K, ‖applyOperatorToState (A p - B p) ψ‖ ^ 2)
      = ((Fintype.card K : ℝ) * (Fintype.card K : ℝ))⁻¹ *
          (((Fintype.card K : ℝ) ^ 2 - (Fintype.card K : ℝ)) *
            ∑ p : K × K, ‖applyOperatorToState (A p - B p) ψ‖ ^ 2) := by ring
    _ ≤ ((Fintype.card K : ℝ) * (Fintype.card K : ℝ))⁻¹ *
          ((Fintype.card K : ℝ) ^ 2 *
            ∑ p : K × K, ‖applyOperatorToState (A p - B p) ψ‖ ^ 2) :=
        mul_le_mul_of_nonneg_left h1 (by positivity)
    _ = ∑ p : K × K, ‖applyOperatorToState (A p - B p) ψ‖ ^ 2 := by
        field_simp

/-- Formalization-only auxiliary for `lem:qld-4-12`: coarse-graining two
oppositely placed families of the same total by `(a,b) |-> alpha a + beta b`,
and averaging the fresh scalars uniformly along with the source points,
preserves the operator-distance bound.  This is `fact:data-processing` in the
form used by the proof of `lem:qld-4-12`, blueprint
`blueprint/src/chapter/ch15_qpbt_combining.tex:1102-1145`, paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:993-1011`. -/
private theorem opFamilyDistSq_linearCoarseGrain_le {P : AdmissibleParams}
    {ε δ : ℝ} {S : ProjectiveSetting P ε} (p1 p2 : Placement)
    (A : ((Fin P.m -> PauliScalar P) × (Fin P.m -> PauliScalar P)) ->
      (PauliScalar P × PauliScalar P) -> Op (S.ExpandedLocalSpace p1.side))
    (B : ((Fin P.m -> PauliScalar P) × (Fin P.m -> PauliScalar P)) ->
      (PauliScalar P × PauliScalar P) -> Op (S.ExpandedLocalSpace p2.side))
    (hA : ∀ xz, ∑ ab : PauliScalar P × PauliScalar P, A xz ab = 1)
    (hB : ∀ xz, ∑ ab : PauliScalar P × PauliScalar P, B xz ab = 1)
    (hbound : opFamilyDistSq
      (uniformDistribution
        ((Fin P.m -> PauliScalar P) × (Fin P.m -> PauliScalar P)))
      (fun xz ab => S.place p1 (A xz ab))
      (fun xz ab => S.place p2 (B xz ab)) S.psiHat <= δ) :
    opFamilyDistSq (uniformDistribution (ExtendedPointQuestion P))
      (fun question c => S.place p1
        (∑ ab ∈ Finset.univ.filter (fun ab : PauliScalar P × PauliScalar P =>
            question.2.1 * ab.1 + question.2.2 * ab.2 = c), A question.1 ab))
      (fun question c => S.place p2
        (∑ ab ∈ Finset.univ.filter (fun ab : PauliScalar P × PauliScalar P =>
            question.2.1 * ab.1 + question.2.2 * ab.2 = c), B question.1 ab))
      S.psiHat <= δ := by
  refine le_trans ?_ hbound
  unfold opFamilyDistSq
  rw [avgOver_uniform_prod
    (α := (Fin P.m -> PauliScalar P) × (Fin P.m -> PauliScalar P))
    (β := PauliScalar P × PauliScalar P)
    (fun xz ab => ∑ c : PauliScalar P, ‖applyOperatorToState
      (S.place p1 (∑ q ∈ Finset.univ.filter
          (fun q : PauliScalar P × PauliScalar P =>
            ab.1 * q.1 + ab.2 * q.2 = c), A xz q) -
        S.place p2 (∑ q ∈ Finset.univ.filter
          (fun q : PauliScalar P × PauliScalar P =>
            ab.1 * q.1 + ab.2 * q.2 = c), B xz q)) S.psiHat‖ ^ 2)]
  refine avgOver_mono _ _ _ fun xz => ?_
  have hsum : ∑ ab : PauliScalar P × PauliScalar P, S.place p1 (A xz ab) =
      ∑ ab : PauliScalar P × PauliScalar P, S.place p2 (B xz ab) := by
    rw [← ProjectiveSetting.place_finsetSum, ← ProjectiveSetting.place_finsetSum,
      hA xz, hB xz, ProjectiveSetting.place_one, ProjectiveSetting.place_one]
  have h := avgOver_linearFiber_le (K := PauliScalar P)
    (fun ab => S.place p1 (A xz ab)) (fun ab => S.place p2 (B xz ab))
    S.psiHat hsum
  simp_rw [ProjectiveSetting.place_finsetSum]
  exact h


/-- Construction of the projective joint point measurements of
`lem:qld-4-10`, paper lines 689--709.  The witness retains both ordered
products and all four directed heterogeneous placement comparisons.

The construction works on the original expanded local spaces: the sandwich
POVM `M^Z_b M^X_a M^Z_b`, formed directly with outcomes in `F_q × F_q`, is
close to the ordered product by the field-valued commutation estimate
(`expPoint_comm`), self-consistent between opposite placements
(`sandwich_offDiagonal_le_sandwichDefectBound`), and is made projective for
each point pair by the orthonormalization lemma
(`exists_projective_close_sandwich`); the three consistency conclusions follow
by the triangle inequality (`chain_bounds`).  The source's route through the
binary refinements and the quantum linearity theorem is not used, because
that route needs zero-state padding of the strategy, which is not part of the
setting; see `rem:linearity-import` and
`docs/paper-gaps/qpbt_linearity-theorem-quotation.tex`.  The error is
`K ε^{1/8}` for a universal constant `K`. -/
theorem exists_combinedPointsWitness :
    ∃ deltaQ : ℝ -> ℝ, IsPolyErr deltaQ ∧
      ∀ (P : AdmissibleParams) (ε : ℝ) (S : ProjectiveSetting P ε),
        Nonempty (CombinedPointsWitness S (deltaQ ε)) := by
  obtain ⟨C₀, hC₀, h₀⟩ := ProjectiveSetting.avg_sandwichDefectBound_le
  obtain ⟨C₁, hC₁, h₁⟩ := ProjectiveSetting.sandwichPoint_ordered_dist_le
  obtain ⟨C₂, hC₂, h₂⟩ := ProjectiveSetting.expPoint_comm
  obtain ⟨C₃, hC₃, h₃⟩ := ProjectiveSetting.ordered_cross_dist_le
  -- the universal constant of the final error `K ε^{1/8}`
  set K : ℝ := 12 * (440 * (2 * C₀)) + 20 * C₁ + 16 * C₃ + 4 * C₂ with hK
  have hK4 : (4 : ℝ) ≤ K := by rw [hK]; nlinarith
  refine ⟨fun ε => K * Real.rpow ε (1 / 8 : ℝ),
    ⟨K, 1 / 8, by linarith, by norm_num, fun x hx =>
      ⟨mul_nonneg (by linarith) (Real.rpow_nonneg hx _), le_rfl⟩⟩, ?_⟩
  intro P ε S
  have hε : (0 : ℝ) ≤ ε := by
    have hv := WinImplications.strategy_value_le_one S.toStrategy
    have hw := S.win
    linarith
  obtain ⟨Qa, hQa, hQaR⟩ := S.exists_projective_close_sandwich_alice
  obtain ⟨Qb, hQb, hQbR⟩ := S.exists_projective_close_sandwich_bob
  -- the joint measurements on the two sides
  let Q : (side : PlayerSide) → PointPair P →
      Measurement (PauliScalar P × PauliScalar P) (S.ExpandedLocalSpace side) :=
    fun side => match side with
      | .alice => Qa
      | .bob => Qb
  have hQproj : ∀ side xz, MIPStarRE.QPBT.Measurement.IsProjective (Q side xz) := by
    intro side xz
    cases side
    · exact hQa xz
    · exact hQb xz
  -- the closeness of `Q` to the sandwich on every placement
  set η : ℝ := 440 * Real.rpow (C₀ * (ε + Real.sqrt ε)) (1 / 4 : ℝ) with hη
  have hbound : ∀ p₁ p₂ : Placement, p₁.IsOpposite p₂ →
      220 * Real.rpow (avgOver (uniformDistribution (PointPair P))
        (S.sandwichDefectBound p₁ p₂)) (1 / 4 : ℝ) ≤ η := by
    intro p₁ p₂ hopp
    have hnn : 0 ≤ avgOver (uniformDistribution (PointPair P))
        (S.sandwichDefectBound p₁ p₂) :=
      avgOver_nonneg _ _ (S.sandwichDefectBound_nonneg p₁ p₂)
    have hr : Real.rpow (avgOver (uniformDistribution (PointPair P))
        (S.sandwichDefectBound p₁ p₂)) (1 / 4 : ℝ) ≤
        Real.rpow (C₀ * (ε + Real.sqrt ε)) (1 / 4 : ℝ) :=
      Real.rpow_le_rpow hnn (h₀ P ε S p₁ p₂ hopp) (by norm_num)
    have hr0 : 0 ≤ Real.rpow (C₀ * (ε + Real.sqrt ε)) (1 / 4 : ℝ) :=
      Real.rpow_nonneg (by positivity) _
    rw [hη]
    nlinarith
  have hQR : ∀ p : Placement, opFamilyDistSq (uniformDistribution (PointPair P))
      (fun xz (ab : PauliScalar P × PauliScalar P) =>
        S.place p ((Q p.side xz).effect ab))
      (fun xz ab => S.place p ((S.sandwichPoint p.side xz.1 xz.2).effect ab))
      S.psiHat ≤ η := by
    intro p
    cases p
    · exact le_trans hQaR (hbound .AA' .BA'' trivial)
    · exact le_trans hQbR (hbound .BA'' .AA' trivial)
    · rw [ProjectiveSetting.opFamilyDistSq_place_BB'_eq_BA'']
      exact le_trans hQbR (hbound .BA'' .AA' trivial)
    · rw [ProjectiveSetting.opFamilyDistSq_place_AB''_eq_AA']
      exact le_trans hQaR (hbound .AA' .BA'' trivial)
  have hchain := fun (p₁ p₂ : Placement) (hopp : p₁.IsOpposite p₂) =>
    S.chain_bounds Q η C₁ C₂ C₃ hQR (h₁ P ε S) (h₂ P ε S) (h₃ P ε S) p₁ p₂ hopp
  -- the numeric bound on the longest chain, in the two regimes of `ε`
  have hηnn : 0 ≤ η := by
    rw [hη]
    exact mul_nonneg (by norm_num)
      (Real.rpow_nonneg (mul_nonneg (by linarith) (add_nonneg hε (Real.sqrt_nonneg ε))) _)
  have hs : 0 ≤ Real.sqrt ε := Real.sqrt_nonneg ε
  have htotal : 12 * η + 20 * (C₁ * Real.sqrt ε) + 16 * (C₃ * ε) +
      4 * (C₂ * Real.sqrt ε) ≤ K * Real.rpow ε (1 / 8 : ℝ) ∨ 1 < ε := by
    by_cases hε1 : ε ≤ 1
    · left
      obtain ⟨hε8, hs8, hq8⟩ := error_terms_le_rpow_eighth hε hε1 hC₀
      rw [hη, hK]
      nlinarith [mul_le_mul_of_nonneg_left hq8 (by norm_num : (0 : ℝ) ≤ 440),
        mul_le_mul_of_nonneg_left hs8 (by linarith : (0 : ℝ) ≤ C₁),
        mul_le_mul_of_nonneg_left hs8 (by linarith : (0 : ℝ) ≤ C₂),
        mul_le_mul_of_nonneg_left hε8 (by linarith : (0 : ℝ) ≤ C₃)]
    · right
      exact lt_of_not_ge hε1
  have hK8 : 1 < ε → (4 : ℝ) ≤ K * Real.rpow ε (1 / 8 : ℝ) := by
    intro hε1
    have h1 : (1 : ℝ) ≤ Real.rpow ε (1 / 8 : ℝ) :=
      Real.one_le_rpow (le_of_lt hε1) (by norm_num)
    nlinarith
  have hsub1 : 2 * η + 4 * (C₁ * Real.sqrt ε) + 4 * (C₃ * ε) ≤
      12 * η + 20 * (C₁ * Real.sqrt ε) + 16 * (C₃ * ε) + 4 * (C₂ * Real.sqrt ε) := by
    nlinarith
  have hsub2 : 4 * η + 8 * (C₁ * Real.sqrt ε) + 8 * (C₃ * ε) + 2 * (C₂ * Real.sqrt ε) ≤
      12 * η + 20 * (C₁ * Real.sqrt ε) + 16 * (C₃ * ε) + 4 * (C₂ * Real.sqrt ε) := by
    nlinarith
  -- square-summability of the families, for the trivial bound
  have hsqQ : ∀ (p : Placement) (xz : PointPair P),
      ∑ ab : PauliScalar P × PauliScalar P,
        (S.place p ((Q p.side xz).effect ab))ᴴ * S.place p ((Q p.side xz).effect ab) ≤ 1 :=
    fun p xz => S.sum_place_effect_conjTranspose_mul_self_le_one p _ (hQproj p.side xz)
  have hsqXZ : ∀ (p : Placement) (xz : PointPair P),
      ∑ ab : PauliScalar P × PauliScalar P,
        (S.place p ((S.pointMeasExp p.side .X xz.1).effect ab.1 *
          (S.pointMeasExp p.side .Z xz.2).effect ab.2))ᴴ *
        S.place p ((S.pointMeasExp p.side .X xz.1).effect ab.1 *
          (S.pointMeasExp p.side .Z xz.2).effect ab.2) ≤ 1 := by
    intro p xz
    refine le_of_eq ?_
    simp only [ProjectiveSetting.place_mul]
    exact sum_mul_conjTranspose_mul_self_eq_one
      (S.placedMeasurement p (S.pointMeasExp p.side .X xz.1))
      (S.placedMeasurement p (S.pointMeasExp p.side .Z xz.2))
      (S.placedMeasurement_isProjective p _ (S.pointMeasExp_isProjective _ _ _))
      (S.placedMeasurement_isProjective p _ (S.pointMeasExp_isProjective _ _ _))
  have hsqZX : ∀ (p : Placement) (xz : PointPair P),
      ∑ ab : PauliScalar P × PauliScalar P,
        (S.place p ((S.pointMeasExp p.side .Z xz.2).effect ab.2 *
          (S.pointMeasExp p.side .X xz.1).effect ab.1))ᴴ *
        S.place p ((S.pointMeasExp p.side .Z xz.2).effect ab.2 *
          (S.pointMeasExp p.side .X xz.1).effect ab.1) ≤ 1 := by
    intro p xz
    refine le_of_eq ?_
    simp only [ProjectiveSetting.place_mul]
    exact sum_mul_conjTranspose_mul_self_eq_one'
      (S.placedMeasurement p (S.pointMeasExp p.side .X xz.1))
      (S.placedMeasurement p (S.pointMeasExp p.side .Z xz.2))
      (S.placedMeasurement_isProjective p _ (S.pointMeasExp_isProjective _ _ _))
      (S.placedMeasurement_isProjective p _ (S.pointMeasExp_isProjective _ _ _))
  refine ⟨CombinedPointsWitness.mk (fun side x z => Q side (x, z)) ?_ ?_ ?_ ?_⟩
  · intro side x z
    exact hQproj side (x, z)
  · intro p₁ p₂ hopp
    rcases htotal with htot | hε1
    · exact le_trans (hchain p₁ p₂ hopp).2.2 htot
    · exact le_trans (opFamilyDistSq_uniform_le_four _ _ S.psiHat S.psiHat_norm
        (fun xz => hsqQ p₁ xz) (fun xz => hsqQ p₂ xz)) (hK8 hε1)
  · intro p₁ p₂ hopp
    rcases htotal with htot | hε1
    · exact le_trans (hchain p₁ p₂ hopp).1 (le_trans hsub1 htot)
    · exact le_trans (opFamilyDistSq_uniform_le_four _ _ S.psiHat S.psiHat_norm
        (fun xz => hsqQ p₁ xz) (fun xz => hsqXZ p₂ xz)) (hK8 hε1)
  · intro p₁ p₂ hopp
    rcases htotal with htot | hε1
    · exact le_trans (hchain p₁ p₂ hopp).2.1 (le_trans hsub2 htot)
    · exact le_trans (opFamilyDistSq_uniform_le_four _ _ S.psiHat S.psiHat_norm
        (fun xz => hsqQ p₁ xz) (fun xz => hsqZX p₂ xz)) (hK8 hε1)

/-- Projectivity and the three data-processed consistency guarantees for
`CombinedPointsWitness.extendedQ`.  This is `lem:qld-4-12`, paper lines
993--1011; the `XZ` and `ZX` source products remain separate. -/
theorem extendedQ_spec {P : AdmissibleParams} {ε δ : ℝ}
    {S : ProjectiveSetting P ε} (points : CombinedPointsWitness S δ) :
    (∀ side x z alpha beta,
      Measurement.IsProjective (points.extendedQ side x z alpha beta)) ∧
    (∀ p1 p2 : Placement, p1.IsOpposite p2 ->
      opFamilyDistSq (uniformDistribution (ExtendedPointQuestion P))
        (fun question c => S.place p1
          ((points.extendedQ p1.side question.1.1 question.1.2
            question.2.1 question.2.2).effect c))
        (fun question c => S.place p2
          ((points.extendedQ p2.side question.1.1 question.1.2
            question.2.1 question.2.2).effect c))
        S.psiHat <= δ) ∧
    (∀ p1 p2 : Placement, p1.IsOpposite p2 ->
      opFamilyDistSq (uniformDistribution (ExtendedPointQuestion P))
        (fun question c => S.place p1
          ((points.extendedQ p1.side question.1.1 question.1.2
            question.2.1 question.2.2).effect c))
        (fun question c => S.place p2
          (∑ ab ∈ Finset.univ.filter (fun ab : PauliScalar P × PauliScalar P =>
              question.2.1 * ab.1 + question.2.2 * ab.2 = c),
            (S.pointMeasExp p2.side .X question.1.1).effect ab.1 *
              (S.pointMeasExp p2.side .Z question.1.2).effect ab.2))
        S.psiHat <= δ) ∧
    ∀ p1 p2 : Placement, p1.IsOpposite p2 ->
      opFamilyDistSq (uniformDistribution (ExtendedPointQuestion P))
        (fun question c => S.place p1
          ((points.extendedQ p1.side question.1.1 question.1.2
            question.2.1 question.2.2).effect c))
        (fun question c => S.place p2
          (∑ ab ∈ Finset.univ.filter (fun ab : PauliScalar P × PauliScalar P =>
              question.2.1 * ab.1 + question.2.2 * ab.2 = c),
            (S.pointMeasExp p2.side .Z question.1.2).effect ab.2 *
              (S.pointMeasExp p2.side .X question.1.1).effect ab.1))
        S.psiHat <= δ := by
  have hprodX : ∀ (side : PlayerSide) (x z : Fin P.m -> PauliScalar P),
      ∑ ab : PauliScalar P × PauliScalar P,
          (S.pointMeasExp side .X x).effect ab.1 *
            (S.pointMeasExp side .Z z).effect ab.2 = 1 := by
    intro side x z
    rw [Fintype.sum_prod_type]
    simp_rw [← Finset.mul_sum]
    rw [← Finset.sum_mul, (S.pointMeasExp side .X x).sum_eq_one,
      (S.pointMeasExp side .Z z).sum_eq_one, one_mul]
  have hprodZ : ∀ (side : PlayerSide) (x z : Fin P.m -> PauliScalar P),
      ∑ ab : PauliScalar P × PauliScalar P,
          (S.pointMeasExp side .Z z).effect ab.2 *
            (S.pointMeasExp side .X x).effect ab.1 = 1 := by
    intro side x z
    rw [Fintype.sum_prod_type]
    simp_rw [← Finset.sum_mul]
    rw [← Finset.mul_sum, (S.pointMeasExp side .X x).sum_eq_one,
      (S.pointMeasExp side .Z z).sum_eq_one, one_mul]
  refine ⟨fun side x z alpha beta =>
      WinImplications.postprocess_isProjective _ (points.projective side x z) _,
    ?_, ?_, ?_⟩
  · intro p1 p2 hopp
    exact opFamilyDistSq_linearCoarseGrain_le p1 p2
      (fun xz ab => (points.Q p1.side xz.1 xz.2).effect ab)
      (fun xz ab => (points.Q p2.side xz.1 xz.2).effect ab)
      (fun xz => (points.Q p1.side xz.1 xz.2).sum_eq_one)
      (fun xz => (points.Q p2.side xz.1 xz.2).sum_eq_one)
      (points.self_consistent p1 p2 hopp)
  · intro p1 p2 hopp
    exact opFamilyDistSq_linearCoarseGrain_le p1 p2
      (fun xz ab => (points.Q p1.side xz.1 xz.2).effect ab)
      (fun xz ab => (S.pointMeasExp p2.side .X xz.1).effect ab.1 *
        (S.pointMeasExp p2.side .Z xz.2).effect ab.2)
      (fun xz => (points.Q p1.side xz.1 xz.2).sum_eq_one)
      (fun xz => hprodX p2.side xz.1 xz.2)
      (points.consistent_XZ p1 p2 hopp)
  · intro p1 p2 hopp
    exact opFamilyDistSq_linearCoarseGrain_le p1 p2
      (fun xz ab => (points.Q p1.side xz.1 xz.2).effect ab)
      (fun xz ab => (S.pointMeasExp p2.side .Z xz.2).effect ab.2 *
        (S.pointMeasExp p2.side .X xz.1).effect ab.1)
      (fun xz => (points.Q p1.side xz.1 xz.2).sum_eq_one)
      (fun xz => hprodZ p2.side xz.1 xz.2)
      (points.consistent_ZX p1 p2 hopp)

end


end MIPStarRE.QPBT
