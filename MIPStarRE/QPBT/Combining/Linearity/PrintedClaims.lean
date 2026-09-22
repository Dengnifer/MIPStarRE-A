import MIPStarRE.QPBT.Combining.Linearity.Stability

/-!
# Printed linearity claims and the four-point obstruction

The universal propositions below retain the bound printed in Theorem 10 of
Natarajan--Vidick. Neither is asserted or used as a construction input. The first uses
the conventional single-density operator distance; the second also retains the
duplicated density in the printed distance definition. The scalar pure-state
counterexample applies to both readings, on every finite ancillary extension.

## References

* `references/nv-paper/fullpaper.tex:873-875,1074-1088`, `thm:qblr`.
* `docs/paper-gaps/qpbt_linearity-distance-normalization.tex`, issue #694.
-/

open scoped BigOperators Matrix MatrixOrder ComplexOrder

namespace MIPStarRE.QPBT

open MIPStarRE.LDT MIPStarRE.Quantum

noncomputable section

/-- **Source statement, unasserted:** Theorem 10, `thm:qblr`, at
`references/nv-paper/fullpaper.tex:1074-1088`, with the standard single-density
reading of the operator distance. All finite-dimensional input spaces and
ancillary spaces are quantified, as stipulated at source line 732. No bound on
the real error or positivity restriction on the index length is inserted.
The real part encodes the source's real averaged correlation, not an additional
hypothesis. The output ancilla is existential after the input family.

The bound is the printed `δ`, not the proved `2 * δ`. This proposition is never
an input to the corrected theorem. The literally duplicated density of source
lines 873-875 is separately retained by `PrintedLinearityLiteralDistanceClaim`.
See `docs/paper-gaps/qpbt_linearity-distance-normalization.tex`, issue #694. -/
def PrintedLinearityClaim : Prop :=
  ∀ (t : ℕ) (δ : ℝ) (ι : Type) [Fintype ι] [DecidableEq ι]
    (ρ : Op ι), ρ.PosSemidef → ρ.trace = 1 →
    ∀ (O : (Fin t → ZMod 2) → Op ι), (∀ u, IsBinaryObservable (O u)) →
      1 - δ ≤ blrCorrelation O ρ →
      ∃ (ι' : Type) (_ : Fintype ι') (_ : DecidableEq ι')
          (anc : EuclideanSpace ℂ ι'),
        ‖anc‖ = 1 ∧ ∃ L : (Fin t → ZMod 2) → Op (ι × ι'),
          (∀ u, IsBinaryObservable (L u)) ∧
          (∀ u v, L u * L v = L (u + v)) ∧
          avgOver (uniformDistribution (Fin t → ZMod 2))
            (fun u => stateDepDistSq (L u) (heteroKron (O u) (1 : Op ι'))
              (heteroKron ρ (ancProj anc))) ≤ δ

/-- **Source statement, unasserted:** The same universal printed theorem with
the literal distance of `references/nv-paper/fullpaper.tex:873-875`:
`Tr_ρ ((S-T)†(S-T)ρ)`, where `Tr_ρ X = Tr (ρX)`. Cyclicity of trace gives
`stateDepDistSq S T (ρ * ρ)`. This retains the separate duplicated-density
typographical issue instead of silently identifying it with the standard
distance. The quantifiers and arbitrary pure ancillary extension are those of
`thm:qblr`, lines 1074-1088. See the normalization note, issue #694. -/
def PrintedLinearityLiteralDistanceClaim : Prop :=
  ∀ (t : ℕ) (δ : ℝ) (ι : Type) [Fintype ι] [DecidableEq ι]
    (ρ : Op ι), ρ.PosSemidef → ρ.trace = 1 →
    ∀ (O : (Fin t → ZMod 2) → Op ι), (∀ u, IsBinaryObservable (O u)) →
      1 - δ ≤ blrCorrelation O ρ →
      ∃ (ι' : Type) (_ : Fintype ι') (_ : DecidableEq ι')
          (anc : EuclideanSpace ℂ ι'),
        ‖anc‖ = 1 ∧ ∃ L : (Fin t → ZMod 2) → Op (ι × ι'),
          (∀ u, IsBinaryObservable (L u)) ∧
          (∀ u v, L u * L v = L (u + v)) ∧
          avgOver (uniformDistribution (Fin t → ZMod 2))
            (fun u => stateDepDistSq (L u) (heteroKron (O u) (1 : Op ι'))
              (heteroKron ρ (ancProj anc) * heteroKron ρ (ancProj anc))) ≤ δ

/-- The scalar sign pattern `(+1,+1,+1,-1)` on the Boolean square, amplified
to any finite-dimensional space. It is the four-point counterexample in
`docs/paper-gaps/qpbt_linearity-distance-normalization.tex`. -/
def fourPointObservable {ι : Type} [Fintype ι] [DecidableEq ι]
    (u : Fin 2 → ZMod 2) : Op ι :=
  if u 0 = 1 ∧ u 1 = 1 then -1 else 1

/-- Each member of the four-point family is a Hermitian involution. -/
theorem fourPointObservable_isBinaryObservable {ι : Type}
    [Fintype ι] [DecidableEq ι] (u : Fin 2 → ZMod 2) :
    IsBinaryObservable (fourPointObservable (ι := ι) u) := by
  unfold fourPointObservable
  split_ifs
  · exact ⟨Matrix.isHermitian_one.neg, by simp⟩
  · exact IsBinaryObservable.one

private theorem avg_boolean_square (f : (Fin 2 → ZMod 2) → ℝ) :
    avgOver (uniformDistribution (Fin 2 → ZMod 2)) f =
      (f ![0, 0] + f ![0, 1] + f ![1, 0] + f ![1, 1]) / 4 := by
  rw [avgOver_uniform_eq_inv_card_mul_sum]
  have huniv : (Finset.univ : Finset (Fin 2 → ZMod 2)) =
      {![0, 0], ![0, 1], ![1, 0], ![1, 1]} := by decide
  norm_num [huniv]
  ring

/-- The four-point family's two-query correlation is `1/4`, in every density
operator. In particular the hypothesis of `thm:qblr` holds with `δ = 3/4`. -/
theorem blrCorrelation_fourPointObservable {ι : Type}
    [Fintype ι] [DecidableEq ι] (ρ : Op ι) (htrace : ρ.trace = 1) :
    blrCorrelation (fourPointObservable (ι := ι)) ρ = 1 / 4 := by
  unfold blrCorrelation
  have havg := avgOver_uniform_prod (fun (u v : Fin 2 → ZMod 2) =>
    (Matrix.trace (fourPointObservable (ι := ι) u * fourPointObservable v *
      fourPointObservable (u + v) * ρ)).re)
  rw [havg]
  simp_rw [avg_boolean_square]
  norm_num [fourPointObservable, show (2 : ZMod 2) ≠ 1 by decide,
    htrace, Matrix.trace_neg]

private theorem four_point_gram {ι : Type} [Fintype ι] [DecidableEq ι]
    (X Y : Op ι) (hX : IsBinaryObservable X) (hY : IsBinaryObservable Y)
    (hcomm : X * Y = Y * X) :
    ((1 - X) * (1 - Y))ᴴ * ((1 - X) * (1 - Y)) =
      (4 : ℂ) • (1 - X - Y + X * Y) := by
  have hXX : (1 - X) * (1 - X) = (2 : ℂ) • (1 - X) := by
    calc
      _ = 1 - X - X + X * X := by noncomm_ring
      _ = _ := by rw [hX.2]; module
  have hYY : (1 - Y) * (1 - Y) = (2 : ℂ) • (1 - Y) := by
    calc
      _ = 1 - Y - Y + Y * Y := by noncomm_ring
      _ = _ := by rw [hY.2]; module
  have hswap : (1 - Y) * (1 - X) = (1 - X) * (1 - Y) := by
    noncomm_ring [hcomm]
  rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_sub, Matrix.conjTranspose_sub,
    Matrix.conjTranspose_one, hX.1.eq, hY.1.eq]
  calc
    _ = (1 - Y) * ((1 - X) * (1 - X)) * (1 - Y) := by noncomm_ring
    _ = (2 : ℂ) • ((1 - Y) * (1 - X) * (1 - Y)) := by
      rw [hXX]; simp only [mul_smul_comm, smul_mul_assoc]
    _ = (2 : ℂ) • ((1 - X) * ((1 - Y) * (1 - Y))) := by
      rw [hswap, Matrix.mul_assoc]
    _ = (4 : ℂ) • ((1 - X) * (1 - Y)) := by
      rw [hYY, mul_smul_comm, smul_smul]; norm_num
    _ = _ := by congr 1; noncomm_ring

/-- Every exactly linear binary family has average squared operator distance
at least `1` from the four-point family. The space and density are arbitrary,
so this lower bound also covers every ancillary extension allowed in the
printed theorem. The proof uses the positive Gram matrix
`((1-X)(1-Y))†((1-X)(1-Y)) = 4(1-X-Y+XY)` for its two generators. -/
theorem one_le_avg_fourPointObservable_distance {ι : Type}
    [Fintype ι] [DecidableEq ι] (ρ : Op ι) (hρ : ρ.PosSemidef)
    (htrace : ρ.trace = 1) (L : (Fin 2 → ZMod 2) → Op ι)
    (hL : ∀ u, IsBinaryObservable (L u))
    (hlin : ∀ u v, L u * L v = L (u + v)) :
    1 ≤ avgOver (uniformDistribution (Fin 2 → ZMod 2))
      (fun u => stateDepDistSq (L u) (fourPointObservable u) ρ) := by
  have hzero : L ![0, 0] = 1 := by
    have h := hlin ![0, 0] ![0, 0]
    have hz : (![0, 0] : Fin 2 → ZMod 2) + ![0, 0] = ![0, 0] := by decide
    rw [(hL _).2, hz] at h
    exact h.symm
  have hprod : L ![1, 0] * L ![0, 1] = L ![1, 1] := by
    rw [hlin, show (![1, 0] : Fin 2 → ZMod 2) + ![0, 1] = ![1, 1] by decide]
  have hcomm : L ![1, 0] * L ![0, 1] = L ![0, 1] * L ![1, 0] := by
    rw [hlin, hlin, add_comm]
  have hpos := trace_mul_nonneg_of_nonneg
    (A := ((1 - L ![1, 0]) * (1 - L ![0, 1]))ᴴ *
      ((1 - L ![1, 0]) * (1 - L ![0, 1])))
    (B := ρ) (Matrix.posSemidef_conjTranspose_mul_self _).nonneg hρ.nonneg
  rw [four_point_gram _ _ (hL _) (hL _) hcomm, hprod] at hpos
  simp only [smul_mul_assoc, Matrix.sub_mul, Matrix.add_mul, one_mul,
    Matrix.trace_smul, Matrix.trace_sub, Matrix.trace_add, htrace, smul_eq_mul] at hpos
  norm_num [Complex.mul_re] at hpos
  simp_rw [stateDepDistSq_eq_two_sub_two_mul_correlation _ _ _ (hL _)
    (fourPointObservable_isBinaryObservable _) hρ htrace]
  rw [avg_boolean_square]
  norm_num [fourPointObservable, hzero, htrace, Matrix.trace_neg]
  linarith

/-- The lower bound `1` is attained by the constant identity representation.
Thus this single example forces a coefficient of at least `4/3`, not `2`. -/
theorem avg_fourPointObservable_distance_one {ι : Type}
    [Fintype ι] [DecidableEq ι] (ρ : Op ι) (hρ : ρ.PosSemidef)
    (htrace : ρ.trace = 1) :
    avgOver (uniformDistribution (Fin 2 → ZMod 2))
      (fun u => stateDepDistSq (1 : Op ι) (fourPointObservable u) ρ) = 1 := by
  simp_rw [stateDepDistSq_eq_two_sub_two_mul_correlation _ _ _
    IsBinaryObservable.one (fourPointObservable_isBinaryObservable _) hρ htrace]
  rw [avg_boolean_square]
  norm_num [fourPointObservable, htrace, Matrix.trace_neg]

private theorem heteroKron_fourPointObservable {ι ι' : Type}
    [Fintype ι] [DecidableEq ι] [Fintype ι'] [DecidableEq ι']
    (u : Fin 2 → ZMod 2) :
    heteroKron (fourPointObservable (ι := ι) u) (1 : Op ι') =
      fourPointObservable (ι := ι × ι') u := by
  unfold fourPointObservable
  split_ifs
  · ext i j
    by_cases hi : i.1 = j.1 <;> by_cases hj : i.2 = j.2 <;>
      simp [heteroKron, Matrix.kroneckerMap_apply, Matrix.one_apply, Matrix.neg_apply,
        Prod.ext_iff, hi, hj]
  · exact Matrix.one_kronecker_one

/-- The standard-distance reading of the printed universal assertion is false,
including its arbitrary finite pure ancillary extension. -/
theorem not_printedLinearityClaim : ¬ PrintedLinearityClaim := by
  intro h
  have htrace : (1 : Op Unit).trace = 1 := by simp [Matrix.trace]
  have hc : 1 - (3 / 4 : ℝ) ≤
      blrCorrelation (fourPointObservable (ι := Unit)) 1 := by
    rw [blrCorrelation_fourPointObservable _ htrace]; norm_num
  obtain ⟨ι', _, _, anc, hanc, L, hL, hlin, hdist⟩ :=
    h 2 (3 / 4) Unit 1 Matrix.PosSemidef.one htrace
      fourPointObservable fourPointObservable_isBinaryObservable hc
  have hlower := one_le_avg_fourPointObservable_distance
    (heteroKron (1 : Op Unit) (ancProj anc))
    (heteroKron_ancProj_posSemidef Matrix.PosSemidef.one anc)
    (trace_heteroKron_ancProj _ htrace anc hanc) L hL hlin
  simp_rw [heteroKron_fourPointObservable] at hdist
  linarith

private theorem ancProj_mul_self_of_norm_one {ι : Type} [Fintype ι]
    (anc : EuclideanSpace ℂ ι) (hanc : ‖anc‖ = 1) :
    ancProj anc * ancProj anc = ancProj anc := by
  have hnorm := inner_self_eq_norm_sq_to_K (𝕜 := ℂ) anc
  rw [EuclideanSpace.inner_eq_star_dotProduct, hanc] at hnorm
  norm_num at hnorm
  unfold ancProj
  rw [Matrix.vecMulVec_mul_vecMulVec, dotProduct_comm]
  change Matrix.vecMulVec anc.ofLp ((anc.ofLp ⬝ᵥ star anc.ofLp) • star anc.ofLp) = _
  rw [hnorm, one_smul]
  rfl

/-- The literal printed distance also fails: for the pure scalar input and any
unit pure ancilla, the extended density is idempotent, so its duplication has
no effect on the four-point obstruction. -/
theorem not_printedLinearityLiteralDistanceClaim :
    ¬ PrintedLinearityLiteralDistanceClaim := by
  intro h
  have htrace : (1 : Op Unit).trace = 1 := by simp [Matrix.trace]
  have hc : 1 - (3 / 4 : ℝ) ≤
      blrCorrelation (fourPointObservable (ι := Unit)) 1 := by
    rw [blrCorrelation_fourPointObservable _ htrace]; norm_num
  obtain ⟨ι', _, _, anc, hanc, L, hL, hlin, hdist⟩ :=
    h 2 (3 / 4) Unit 1 Matrix.PosSemidef.one htrace
      fourPointObservable fourPointObservable_isBinaryObservable hc
  have hidem : heteroKron (1 : Op Unit) (ancProj anc) *
      heteroKron (1 : Op Unit) (ancProj anc) =
      heteroKron (1 : Op Unit) (ancProj anc) := by
    simp only [heteroKron, Matrix.kronecker, ← Matrix.mul_kronecker_mul,
      one_mul, ancProj_mul_self_of_norm_one anc hanc]
  have hlower := one_le_avg_fourPointObservable_distance
    (heteroKron (1 : Op Unit) (ancProj anc))
    (heteroKron_ancProj_posSemidef Matrix.PosSemidef.one anc)
    (trace_heteroKron_ancProj _ htrace anc hanc) L hL hlin
  simp_rw [hidem, heteroKron_fourPointObservable] at hdist
  linarith

end

end MIPStarRE.QPBT
