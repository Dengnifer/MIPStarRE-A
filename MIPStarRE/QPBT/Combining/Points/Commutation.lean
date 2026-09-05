import MIPStarRE.QPBT.Combining.Points.Placement

/-!
# Approximate commutation of the field-valued expanded point measurements

The approximate commutation of `lem:qld-comm-cons` is stated for the binary
refinements `M^{(Point,W),u,r}_b` of the expanded point measurements.  The
combined point measurements of `lem:qld-4-10` are built here directly from the
`F_q`-valued measurements `M^{(Point,W),u}_a`, so the commutation estimate is
transferred to them.  The transfer is exact: since
`M^{(Point,X),x}_a = E_r (-1)^{tr(ar)} X^r(x)` and
`M^{(Point,Z),z}_b = E_s (-1)^{tr(bs)} Z^s(z)`, the commutator of the two
measurement effects is the Fourier transform, in the outcome pair `(a, b)`,
of the commutators of the expanded observables, and Parseval's identity for
the additive characters of `F_q` turns the sum over `(a, b)` of the squared
norms into the average over `(r, s)` of the squared norms of the observable
commutators.  No factor depending on `q` is lost.

## Main results

* `sum_norm_sum_smul_sq_of_orthogonal`: Parseval's identity for an orthogonal
  system of coefficients.
* `sum_fixedCharacter_mul`: Fourier cancellation for the fixed trace character.
* `expPoint_comm`: the field-valued expanded point measurements approximately
  commute on every register placement, with the error of
  `lem:qld-comm-cons`.

## References

The commutation estimate for the binary refinements is item 2 of
`lem:qld-comm-cons`, blueprint
`blueprint/src/chapter/ch14_qpbt_observables.tex:1139-1210`, paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:466-505`; the
Fourier form of the point effects is `def:expanded-point-measurement`, paper
lines 384--418.  The role of the transfer in the proof of `lem:qld-4-10` is
explained in `docs/paper-gaps/qpbt_linearity-theorem-quotation.tex`.
-/

open scoped BigOperators Matrix MatrixOrder ComplexOrder

namespace MIPStarRE.QPBT

open MIPStarRE.LDT hiding Measurement
open MIPStarRE.Quantum
open MIPStarRE.LDT.Preliminaries

noncomputable section

/-- A pair of points, one for the `X` basis and one for the `Z` basis.  This
is the question pair `(x, z)` of `lem:qld-4-10`, paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:689-709`. -/
abbrev PointPair (P : AdmissibleParams) :=
  (Fin P.m → PauliScalar P) × (Fin P.m → PauliScalar P)

/-! ## Parseval's identity for an orthogonal system of coefficients -/

/-- Formalization-only auxiliary for `lem:qld-4-10`: if the coefficient
vectors `i ↦ c j i`, `j` ranging over a finite set, are orthogonal with common
squared norm `N`, then the squared norms of the weighted sums
`∑ i, c j i • v i` add up to `N` times the squared norms of the `v i`. -/
theorem sum_norm_sum_smul_sq_of_orthogonal {I J E : Type*} [Fintype I]
    [DecidableEq I] [Fintype J] [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (c : J → I → ℂ) (N : ℝ)
    (horth : ∀ i i', ∑ j, (starRingEnd ℂ) (c j i) * c j i' =
      if i = i' then (N : ℂ) else 0)
    (v : I → E) :
    ∑ j, ‖∑ i, c j i • v i‖ ^ 2 = N * ∑ i, ‖v i‖ ^ 2 := by
  have hnorm : ∀ x : E, ‖x‖ ^ 2 = (inner ℂ x x).re := fun x => by
    simpa using (inner_self_eq_norm_sq (𝕜 := ℂ) x).symm
  have hj : ∀ j, ‖∑ i, c j i • v i‖ ^ 2 =
      (∑ i, ∑ i', ((starRingEnd ℂ) (c j i) * c j i') *
        inner ℂ (v i) (v i')).re := by
    intro j
    rw [hnorm, sum_inner]
    simp only [inner_sum, inner_smul_left, inner_smul_right]
    congr 1
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun i' _ => ?_
    ring
  have hsum : ∑ j, ∑ i, ∑ i', ((starRingEnd ℂ) (c j i) * c j i') *
      inner ℂ (v i) (v i') = ∑ i, (N : ℂ) * inner ℂ (v i) (v i) := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_comm]
    calc ∑ i', ∑ j, ((starRingEnd ℂ) (c j i) * c j i') * inner ℂ (v i) (v i')
        = ∑ i', (∑ j, (starRingEnd ℂ) (c j i) * c j i') *
            inner ℂ (v i) (v i') := by
          refine Finset.sum_congr rfl fun i' _ => ?_
          rw [Finset.sum_mul]
      _ = ∑ i', (if i = i' then (N : ℂ) else 0) * inner ℂ (v i) (v i') := by
          refine Finset.sum_congr rfl fun i' _ => ?_
          rw [horth]
      _ = (N : ℂ) * inner ℂ (v i) (v i) := by
          simp [ite_mul]
  calc ∑ j, ‖∑ i, c j i • v i‖ ^ 2
      = (∑ j, ∑ i, ∑ i', ((starRingEnd ℂ) (c j i) * c j i') *
          inner ℂ (v i) (v i')).re := by
        rw [Complex.re_sum]
        exact Finset.sum_congr rfl fun j _ => hj j
    _ = (∑ i, (N : ℂ) * inner ℂ (v i) (v i)).re := by rw [hsum]
    _ = N * ∑ i, ‖v i‖ ^ 2 := by
        rw [Complex.re_sum, Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Complex.re_ofReal_mul, ← hnorm]

/-! ## The fixed trace character -/

section Characters

variable {P : AdmissibleParams}

/-- The phase induced by the fixed binary trace is an additive character.
Paper `references/qpbt-paper/04_preliminaries.tex:1052-1081`. -/
theorem fixedCharacter_mul (x y : PauliScalar P) :
    phaseSign (fixedBinTrace P.model x) * phaseSign (fixedBinTrace P.model y) =
      phaseSign (fixedBinTrace P.model (x + y)) := by
  rw [fixedBinTrace, map_add, phaseSign_eq_ffChar, phaseSign_eq_ffChar,
    phaseSign_eq_ffChar]
  exact ((ZMod.stdAddChar (N := 2)).map_add_eq_mul _ _).symm

/-- The fixed trace character is even: negation acts trivially on the binary
trace. -/
theorem fixedCharacter_neg (x : PauliScalar P) :
    phaseSign (fixedBinTrace P.model (-x)) =
      phaseSign (fixedBinTrace P.model x) := by
  rw [fixedBinTrace, map_neg, ZMod.neg_eq_self_mod_two]

/-- Fourier cancellation for the fixed trace character: the character sums to
the field size at `0` and to zero elsewhere.  This is `lem:cancellation` for
the one-dimensional space, blueprint
`blueprint/src/chapter/ch11_qpbt_algebra.tex:686`, paper
`references/qpbt-paper/04_preliminaries.tex:1124-1132`. -/
theorem sum_fixedCharacter_mul (c : PauliScalar P) :
    ∑ a : PauliScalar P, phaseSign (fixedBinTrace P.model (a * c)) =
      if c = 0 then (Fintype.card (PauliScalar P) : ℂ) else 0 := by
  have h : (𝔼 r : PauliScalar P, phaseSign (fixedBinTrace P.model (r * c))) =
      if c = 0 then (1 : ℂ) else 0 := by
    simpa only [fixedBinTrace, phaseSign_eq_ffChar,
      MIPStarRE.LDT.Preliminaries.ffChar_apply] using
      (fourier_fact_scalar (p := 2) (F := PauliScalar P) c)
  rw [Finset.expect_eq_sum_div_card] at h
  have hcard : (Fintype.card (PauliScalar P) : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  rw [Finset.card_univ, div_eq_iff hcard] at h
  rw [h]
  split_ifs <;> simp

/-- Orthogonality of two fixed trace characters. -/
theorem sum_fixedCharacter_mul_fixedCharacter (r r' : PauliScalar P) :
    ∑ a : PauliScalar P, phaseSign (fixedBinTrace P.model (a * r)) *
        phaseSign (fixedBinTrace P.model (a * r')) =
      if r = r' then (Fintype.card (PauliScalar P) : ℂ) else 0 := by
  have hterm : ∀ a : PauliScalar P,
      phaseSign (fixedBinTrace P.model (a * r)) *
          phaseSign (fixedBinTrace P.model (a * r')) =
        phaseSign (fixedBinTrace P.model (a * (r' - r))) := by
    intro a
    rw [← fixedCharacter_neg (a * r), fixedCharacter_mul]
    congr 2
    ring
  simp_rw [hterm, sum_fixedCharacter_mul]
  by_cases h : r = r'
  · simp [h]
  · rw [if_neg h, if_neg]
    intro h'
    exact h (sub_eq_zero.mp h').symm

/-- The two-dimensional character system `(a, b) ↦ χ(a r) χ(b s)` is orthogonal
with common squared norm `q ^ 2`. -/
theorem sum_pairCharacter_mul_pairCharacter
    (rs rs' : PauliScalar P × PauliScalar P) :
    ∑ ab : PauliScalar P × PauliScalar P,
        (starRingEnd ℂ) (phaseSign (fixedBinTrace P.model (ab.1 * rs.1)) *
            phaseSign (fixedBinTrace P.model (ab.2 * rs.2))) *
          (phaseSign (fixedBinTrace P.model (ab.1 * rs'.1)) *
            phaseSign (fixedBinTrace P.model (ab.2 * rs'.2))) =
      if rs = rs' then
        (((Fintype.card (PauliScalar P) : ℝ) ^ 2 : ℝ) : ℂ) else 0 := by
  have hstar : ∀ t : ZMod 2, (starRingEnd ℂ) (phaseSign t) = phaseSign t := by
    intro t
    rw [← Complex.star_def]
    exact star_phaseSign' t
  simp_rw [map_mul, hstar]
  rw [Fintype.sum_prod_type]
  calc ∑ a : PauliScalar P, ∑ b : PauliScalar P,
        phaseSign (fixedBinTrace P.model (a * rs.1)) *
            phaseSign (fixedBinTrace P.model (b * rs.2)) *
          (phaseSign (fixedBinTrace P.model (a * rs'.1)) *
            phaseSign (fixedBinTrace P.model (b * rs'.2)))
      = (∑ a : PauliScalar P, phaseSign (fixedBinTrace P.model (a * rs.1)) *
            phaseSign (fixedBinTrace P.model (a * rs'.1))) *
          ∑ b : PauliScalar P, phaseSign (fixedBinTrace P.model (b * rs.2)) *
            phaseSign (fixedBinTrace P.model (b * rs'.2)) := by
        rw [Finset.sum_mul_sum]
        refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
        ring
    _ = _ := by
        rw [sum_fixedCharacter_mul_fixedCharacter,
          sum_fixedCharacter_mul_fixedCharacter]
        by_cases h1 : rs.1 = rs'.1 <;> by_cases h2 : rs.2 = rs'.2
        · rw [if_pos h1, if_pos h2, if_pos (Prod.ext h1 h2)]
          push_cast
          ring
        · rw [if_pos h1, if_neg h2, if_neg (fun h => h2 (congrArg Prod.snd h))]
          simp
        · rw [if_neg h1, if_pos h2, if_neg (fun h => h1 (congrArg Prod.fst h))]
          simp
        · rw [if_neg h1, if_neg h2, if_neg (fun h => h1 (congrArg Prod.fst h))]
          simp

end Characters

/-! ## Fourier form of the point effects and of their commutator -/

/-- A uniform operator average is the normalized sum. -/
theorem averageOperatorOverDistribution_uniform_eq_inv_card_smul_sum
    {α ι : Type*} [Fintype α] [DecidableEq α] [Nonempty α]
    [Fintype ι] [DecidableEq ι] (f : α → Op ι) :
    averageOperatorOverDistribution (uniformDistribution α) f =
      (Fintype.card α : ℂ)⁻¹ • ∑ a, f a := by
  ext i j
  simp only [averageOperatorOverDistribution, uniformDistribution,
    Distribution.uniformOnFinset, Finset.mem_univ, if_true, Matrix.sum_apply,
    Matrix.smul_apply, Complex.real_smul, smul_eq_mul,
    Finset.card_univ, one_div, Complex.ofReal_inv, Complex.ofReal_natCast]
  rw [Finset.mul_sum]

namespace ProjectiveSetting

variable {P : AdmissibleParams} {ε : ℝ}

/-- The Fourier form of an expanded point effect as a normalized character
sum of the expanded observables.  This is the first display of
`def:expanded-point-measurement`, paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:384-418`. -/
theorem expPointOp_eq_inv_card_smul_sum (S : ProjectiveSetting P ε)
    (side : PlayerSide) (W : PauliKind) (u : Fin P.m → PauliScalar P)
    (a : PauliScalar P) :
    S.expPointOp side W u a =
      (Fintype.card (PauliScalar P) : ℂ)⁻¹ •
        ∑ r, phaseSign (fixedBinTrace P.model (a * r)) • S.expObs side W r u := by
  unfold expPointOp
  rw [averageOperatorOverDistribution_uniform_eq_inv_card_smul_sum]

/-- Formalization-only auxiliary: the product of two normalized weighted sums
is the normalized double sum of the weighted products, indexed by pairs. -/
theorem smul_sum_mul_smul_sum {ι K : Type*} [Fintype K] [Fintype ι]
    (c : ℂ) (α β : K → ℂ) (X Z : K → Op ι) :
    (c • ∑ r, α r • X r) * (c • ∑ s, β s • Z s) =
      (c * c) • ∑ rs : K × K, (α rs.1 * β rs.2) • (X rs.1 * Z rs.2) := by
  rw [Fintype.sum_prod_type, smul_mul_smul_comm, Finset.sum_mul_sum]
  congr 1
  refine Finset.sum_congr rfl fun r _ => Finset.sum_congr rfl fun s _ => ?_
  rw [smul_mul_smul_comm]

/-- Formalization-only auxiliary: the product of two normalized weighted sums
in the opposite order, indexed by the same pairs. -/
theorem smul_sum_mul_smul_sum_swap {ι K : Type*} [Fintype K] [Fintype ι]
    (c : ℂ) (α β : K → ℂ) (X Z : K → Op ι) :
    (c • ∑ s, β s • Z s) * (c • ∑ r, α r • X r) =
      (c * c) • ∑ rs : K × K, (α rs.1 * β rs.2) • (Z rs.2 * X rs.1) := by
  rw [Fintype.sum_prod_type_right, smul_mul_smul_comm, Finset.sum_mul_sum]
  congr 1
  refine Finset.sum_congr rfl fun s _ => Finset.sum_congr rfl fun r _ => ?_
  rw [smul_mul_smul_comm, mul_comm (β s)]

/-- The commutator of two field-valued point effects is the Fourier transform
of the commutators of the expanded observables. -/
theorem expPointOp_commutator_eq (S : ProjectiveSetting P ε) (side : PlayerSide)
    (x z : Fin P.m → PauliScalar P) (a b : PauliScalar P) :
    S.expPointOp side .X x a * S.expPointOp side .Z z b -
        S.expPointOp side .Z z b * S.expPointOp side .X x a =
      ((Fintype.card (PauliScalar P) : ℂ)⁻¹ *
          (Fintype.card (PauliScalar P) : ℂ)⁻¹) •
        ∑ rs : PauliScalar P × PauliScalar P,
          (phaseSign (fixedBinTrace P.model (a * rs.1)) *
              phaseSign (fixedBinTrace P.model (b * rs.2))) •
            (S.expObs side .X rs.1 x * S.expObs side .Z rs.2 z -
              S.expObs side .Z rs.2 z * S.expObs side .X rs.1 x) := by
  rw [expPointOp_eq_inv_card_smul_sum, expPointOp_eq_inv_card_smul_sum,
    smul_sum_mul_smul_sum, smul_sum_mul_smul_sum_swap, ← smul_sub,
    ← Finset.sum_sub_distrib]
  congr 1
  refine Finset.sum_congr rfl fun rs _ => ?_
  rw [smul_sub]

/-- Formalization-only auxiliary: an operator applied to a state is linear in
the operator over finite sums. -/
theorem applyOperatorToState_finsetSum {ι γ : Type*} [Fintype ι] [DecidableEq ι]
    (s : Finset γ) (M : γ → Op ι) (ψ : EuclideanSpace ℂ ι) :
    applyOperatorToState (∑ x ∈ s, M x) ψ =
      ∑ x ∈ s, applyOperatorToState (M x) ψ := by
  unfold applyOperatorToState
  simp only [map_sum, LinearMap.sum_apply]

/-- Parseval transfer, pointwise in the point pair: the summed squared norms of
the placed commutators of the field-valued point effects equal the average over
`(r, s)` of the squared norms of the placed commutators of the expanded
observables. -/
theorem sum_norm_place_expPointOp_commutator_sq (S : ProjectiveSetting P ε)
    (p : Placement) (x z : Fin P.m → PauliScalar P) :
    ∑ ab : PauliScalar P × PauliScalar P,
        ‖applyOperatorToState (S.place p
          (S.expPointOp p.side .X x ab.1 * S.expPointOp p.side .Z z ab.2 -
            S.expPointOp p.side .Z z ab.2 * S.expPointOp p.side .X x ab.1))
          S.psiHat‖ ^ 2 =
      avgOver (uniformDistribution (PauliScalar P × PauliScalar P))
        (fun rs => ‖applyOperatorToState (S.place p
          (S.expObs p.side .X rs.1 x * S.expObs p.side .Z rs.2 z -
            S.expObs p.side .Z rs.2 z * S.expObs p.side .X rs.1 x))
          S.psiHat‖ ^ 2) := by
  set v : PauliScalar P × PauliScalar P →
      EuclideanSpace ℂ (SixReg P S.toStrategy.ιA S.toStrategy.ιB) :=
    fun rs => applyOperatorToState (S.place p
      (S.expObs p.side .X rs.1 x * S.expObs p.side .Z rs.2 z -
        S.expObs p.side .Z rs.2 z * S.expObs p.side .X rs.1 x)) S.psiHat
  set c : ℂ := (Fintype.card (PauliScalar P) : ℂ)⁻¹
  have hpt : ∀ ab : PauliScalar P × PauliScalar P,
      applyOperatorToState (S.place p
          (S.expPointOp p.side .X x ab.1 * S.expPointOp p.side .Z z ab.2 -
            S.expPointOp p.side .Z z ab.2 * S.expPointOp p.side .X x ab.1))
          S.psiHat =
        (c * c) • ∑ rs : PauliScalar P × PauliScalar P,
          (phaseSign (fixedBinTrace P.model (ab.1 * rs.1)) *
              phaseSign (fixedBinTrace P.model (ab.2 * rs.2))) • v rs := by
    intro ab
    rw [expPointOp_commutator_eq, place_smul, place_finsetSum,
      WinImplications.applyOperatorToState_smul_op, applyOperatorToState_finsetSum]
    congr 1
    refine Finset.sum_congr rfl fun rs _ => ?_
    rw [place_smul, WinImplications.applyOperatorToState_smul_op]
  have hparseval := sum_norm_sum_smul_sq_of_orthogonal
    (fun (ab rs : PauliScalar P × PauliScalar P) =>
      phaseSign (fixedBinTrace P.model (ab.1 * rs.1)) *
        phaseSign (fixedBinTrace P.model (ab.2 * rs.2)))
    ((Fintype.card (PauliScalar P) : ℝ) ^ 2)
    (fun rs rs' => sum_pairCharacter_mul_pairCharacter rs rs') v
  have hq : (0 : ℝ) < (Fintype.card (PauliScalar P) : ℝ) := by
    exact_mod_cast Fintype.card_pos
  have hcnorm : ‖c * c‖ = ((Fintype.card (PauliScalar P) : ℝ) ^ 2)⁻¹ := by
    simp only [c, norm_mul, norm_inv, Complex.norm_natCast]
    rw [sq, mul_inv]
  calc ∑ ab : PauliScalar P × PauliScalar P,
        ‖applyOperatorToState (S.place p
          (S.expPointOp p.side .X x ab.1 * S.expPointOp p.side .Z z ab.2 -
            S.expPointOp p.side .Z z ab.2 * S.expPointOp p.side .X x ab.1))
          S.psiHat‖ ^ 2
      = ∑ ab : PauliScalar P × PauliScalar P,
          ‖c * c‖ ^ 2 * ‖∑ rs : PauliScalar P × PauliScalar P,
            (phaseSign (fixedBinTrace P.model (ab.1 * rs.1)) *
              phaseSign (fixedBinTrace P.model (ab.2 * rs.2))) • v rs‖ ^ 2 := by
        refine Finset.sum_congr rfl fun ab _ => ?_
        rw [hpt, norm_smul, mul_pow]
    _ = ‖c * c‖ ^ 2 * (((Fintype.card (PauliScalar P) : ℝ) ^ 2) *
          ∑ rs, ‖v rs‖ ^ 2) := by
        rw [← Finset.mul_sum, hparseval]
    _ = avgOver (uniformDistribution (PauliScalar P × PauliScalar P))
          (fun rs => ‖v rs‖ ^ 2) := by
        rw [avgOver_uniform_eq_inv_card_mul_sum, Fintype.card_prod, hcnorm]
        push_cast
        field_simp

/-- The field-valued expanded point measurements approximately commute on each
of the four register placements, with the error of item 2 of
`lem:qld-comm-cons`.  The estimate is transferred from the binary refinements
of the source by the Parseval identity, without loss in the field size.  Paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:466-505`,
blueprint `blueprint/src/chapter/ch14_qpbt_observables.tex:1139-1210`; the
role of this form in the proof of `lem:qld-4-10` is explained in
`docs/paper-gaps/qpbt_linearity-theorem-quotation.tex`. -/
theorem expPoint_comm :
    ∃ C : ℝ, 1 ≤ C ∧
      ∀ (P : AdmissibleParams) (ε : ℝ) (S : ProjectiveSetting P ε)
        (p : Placement),
        opFamilyDistSq (uniformDistribution (PointPair P))
          (fun xz (ab : PauliScalar P × PauliScalar P) => S.place p
            ((S.pointMeasExp p.side .X xz.1).effect ab.1 *
              (S.pointMeasExp p.side .Z xz.2).effect ab.2))
          (fun xz ab => S.place p
            ((S.pointMeasExp p.side .Z xz.2).effect ab.2 *
              (S.pointMeasExp p.side .X xz.1).effect ab.1))
          S.psiHat ≤ C * Real.sqrt ε := by
  obtain ⟨C, hC, h⟩ := exists_twistedCommutator_avg_le
  refine ⟨C, hC, ?_⟩
  intro P ε S p
  have hε : (0 : ℝ) ≤ ε := by
    have hv := WinImplications.strategy_value_le_one S.toStrategy
    have hw := S.win
    linarith
  have hnorm : ∀ (x z : Fin P.m → PauliScalar P)
      (rs : PauliScalar P × PauliScalar P),
      ‖applyOperatorToState (S.place p
          (S.expObs p.side .X rs.1 x * S.expObs p.side .Z rs.2 z -
            S.expObs p.side .Z rs.2 z * S.expObs p.side .X rs.1 x))
          S.psiHat‖ ^ 2 =
        ‖applyOperatorToState
          (S.placeStrategySide p.side (S.twistedCommutator p.side (x, z, rs.1, rs.2)))
          S.toStrategy.ψ‖ ^ 2 := by
    intro x z rs
    rw [expObs_commutator S p.side (x, z, rs.1, rs.2),
      norm_place_heteroKron_psiHat S p _ _ (tauX_mul_tauZ_isometry P (x, z, rs.1, rs.2))]
  have hfamily : opFamilyDistSq (uniformDistribution (PointPair P))
      (fun xz (ab : PauliScalar P × PauliScalar P) => S.place p
        ((S.pointMeasExp p.side .X xz.1).effect ab.1 *
          (S.pointMeasExp p.side .Z xz.2).effect ab.2))
      (fun xz ab => S.place p
        ((S.pointMeasExp p.side .Z xz.2).effect ab.2 *
          (S.pointMeasExp p.side .X xz.1).effect ab.1))
      S.psiHat =
      avgOver (uniformDistribution (PauliTuple P)) (fun ω =>
        ‖applyOperatorToState
          (S.placeStrategySide p.side (S.twistedCommutator p.side ω))
          S.toStrategy.ψ‖ ^ 2) := by
    unfold opFamilyDistSq
    calc avgOver (uniformDistribution (PointPair P)) (fun xz =>
          ∑ ab : PauliScalar P × PauliScalar P,
            ‖applyOperatorToState (S.place p
                ((S.pointMeasExp p.side .X xz.1).effect ab.1 *
                  (S.pointMeasExp p.side .Z xz.2).effect ab.2) -
              S.place p ((S.pointMeasExp p.side .Z xz.2).effect ab.2 *
                (S.pointMeasExp p.side .X xz.1).effect ab.1)) S.psiHat‖ ^ 2)
        = avgOver (uniformDistribution (PointPair P)) (fun xz =>
            avgOver (uniformDistribution (PauliScalar P × PauliScalar P))
              (fun rs => ‖applyOperatorToState
                (S.placeStrategySide p.side
                  (S.twistedCommutator p.side (xz.1, xz.2, rs.1, rs.2)))
                S.toStrategy.ψ‖ ^ 2)) := by
          refine avgOver_congr _ _ _ fun xz => ?_
          rw [← avgOver_congr _ _ _ (hnorm xz.1 xz.2),
            ← sum_norm_place_expPointOp_commutator_sq S p xz.1 xz.2]
          refine Finset.sum_congr rfl fun ab _ => ?_
          rw [place_sub]
          rfl
      _ = avgOver (uniformDistribution (PointPair P × (PauliScalar P × PauliScalar P)))
            (fun q => ‖applyOperatorToState
              (S.placeStrategySide p.side
                (S.twistedCommutator p.side (q.1.1, q.1.2, q.2.1, q.2.2)))
              S.toStrategy.ψ‖ ^ 2) :=
          (avgOver_uniform_prod (fun (xz : PointPair P)
            (rs : PauliScalar P × PauliScalar P) => ‖applyOperatorToState
              (S.placeStrategySide p.side
                (S.twistedCommutator p.side (xz.1, xz.2, rs.1, rs.2)))
              S.toStrategy.ψ‖ ^ 2)).symm
      _ = avgOver (uniformDistribution (PauliTuple P)) (fun ω =>
            ‖applyOperatorToState
              (S.placeStrategySide p.side (S.twistedCommutator p.side ω))
              S.toStrategy.ψ‖ ^ 2) := by
          rw [avgOver_uniform_equiv (Equiv.prodAssoc (Fin P.m → PauliScalar P)
            (Fin P.m → PauliScalar P) (PauliScalar P × PauliScalar P))]
          rfl
  rw [hfamily]
  exact h P ε S p.side hε

end ProjectiveSetting

end

end MIPStarRE.QPBT
