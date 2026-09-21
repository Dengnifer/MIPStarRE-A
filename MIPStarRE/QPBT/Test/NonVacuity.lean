import MIPStarRE.QPBT.Test.Soundness
import MIPStarRE.QPBT.Test.Soundness.ScalarAbsorption
import MIPStarRE.QPBT.Test.Completeness

/-!
# Non-vacuity of the Pauli basis test soundness theorem

`MIPStarRE.QPBT.pauli_soundness` is an implication: for every admissible
parameter tuple `P`, every `ε ≥ 0` and every strategy `S` for
`pauliBasisTest P` with `1 - ε ≤ S.value`, extraction data exist whose three
error quantities are bounded by `deltaQld a b ε P.m P.d P.q`.  A reader is
entitled to ask two questions about such a statement, and this module answers
both with citable declarations.  Nothing here changes or restates an existing
definition or theorem; every result is a corollary of material already on the
main development.

## Q1 — are the hypotheses satisfiable?

`AdmissibleParams` is inhabited (`nonVacuousParams`, and hence
`nonempty_admissibleParams`), and for *every* admissible `P` the honest
strategy of `lem:pauli-completeness` is a strategy for `pauliBasisTest P`
itself with value exactly `1` (`exists_pauliBasisTest_strategy_value_one`);
the symmetric presentation used by `exists_spcc_value_one` has
`pauliBasisTest P` as its underlying game definitionally
(`pauliBasisTestSymm_toGame`).  Consequently the hypothesis triple
`0 ≤ ε`, `S : Strategy (pauliBasisTest P)`, `1 - ε ≤ S.value` is jointly
satisfiable — with `ε = 0`, the strongest case
(`pauli_soundness_hypotheses_satisfiable`) — and `pauli_soundness` applied to
it yields an unconditional statement
(`pauli_soundness_applies_to_honest_strategy`).

## Q2 — is the conclusion non-trivial?

The bound is `deltaQld a b ε m d q = a * (m*d)^a * (ε^b + q^(-b) + 2^(-b*m*d))`
with `a, b` existentially quantified by the theorem, so no *single* numeric
value can be extracted.  What can be shown, and is shown here, is that
whatever the constants `a ≥ 1` and `0 < b < 1` produced by `pauli_soundness`
are, the bound is not vacuously large: along the explicit admissible family
`nonVacuousParams n` the error at `ε = 0` tends to `0`
(`tendsto_deltaQld_nonVacuousParams`), so for every `η > 0` there are
admissible parameters at which the soundness conclusion bounds all three
distances by less than `η` (`exists_admissibleParams_deltaQld_lt` and the
combined `pauli_soundness_nontrivial`).

**What is *not* shown.** This is a statement about the `ε = 0` section of
`deltaQld` for a *chosen* parameter family, not a uniform rate: it does not
locate a threshold `ε₀ > 0` below which the bound is small for a *fixed*
parameter tuple, and it does not compare `deltaQld` against the trivial bound
on `rawPauliOperatorDistanceA`/`rawPauliOperatorDistanceB` at fixed
parameters. It also does not assert anything about the numerical size of the
constants `a` and `b`, which the source theorem leaves implicit
(`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:1426-1447`).
Continuity of `deltaQld` in `ε` at `0` is recorded separately
(`tendsto_deltaQld_eps_zero`) so that a reader can see that the `ε = 0`
section is the limiting case of the `ε > 0` statement rather than a
degenerate one.

## References

Supports blueprint `thm:pauli` and `lem:pauli-completeness`; paper origin
`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:1426-1447`
and `:1229-1421`.  This module is formalization-only bookkeeping: it states no
new mathematics of the source and introduces no hypothesis.
-/

open scoped BigOperators Matrix ComplexOrder Topology

open Filter

namespace MIPStarRE.QPBT

open MIPStarRE.LDT
open MIPStarRE.Quantum

noncomputable section

/-! ### Q1: the hypotheses of `pauli_soundness` are satisfiable -/

/-- An explicit admissible parameter family: field size `q = 2^(2n+1)`,
ambient dimension `m = 1` and degree `d = n + 1`.  Admissibility is immediate —
`2n+1` is odd, `1 ∣ q`, and `1 ≤ n + 1` — so `AdmissibleParams` is inhabited
and, since `m * d = n + 1` and `q` both grow with `n`, the family is also the
one used for the quantitative statements below.  Formalization-only: it is a
witness, not a constraint added to `def:admissible`. -/
def nonVacuousParams (n : ℕ) : AdmissibleParams where
  q := 2 ^ (2 * n + 1)
  m := 1
  d := n + 1
  hd := Nat.succ_le_succ (Nat.zero_le n)
  hq := ⟨2 * n + 1, ⟨n, by ring⟩, rfl⟩
  hdvd := one_dvd _

@[simp] theorem nonVacuousParams_q (n : ℕ) : (nonVacuousParams n).q = 2 ^ (2 * n + 1) := rfl

@[simp] theorem nonVacuousParams_m (n : ℕ) : (nonVacuousParams n).m = 1 := rfl

@[simp] theorem nonVacuousParams_d (n : ℕ) : (nonVacuousParams n).d = n + 1 := rfl

/-- The parameter type of `thm:pauli` is inhabited; `nonVacuousParams 0` is the
tuple `q = 2`, `m = 1`, `d = 1`. -/
theorem nonempty_admissibleParams : Nonempty AdmissibleParams :=
  ⟨nonVacuousParams 0⟩

/-- Every admissible Pauli basis test has a strategy of value one *for the game
`pauliBasisTest P` itself*.  This is `exists_spcc_value_one` transported along
`pauliBasisTestSymm_toGame`, which holds definitionally; it is the form in
which the hypothesis `1 - ε ≤ S.value` of `thm:pauli` is met.  Blueprint
`lem:pauli-completeness`, paper
`08_classical_and_quantum_low_degree_tests.tex:1229-1421`. -/
theorem exists_pauliBasisTest_strategy_value_one (P : AdmissibleParams) :
    ∃ S : Strategy (pauliBasisTest P), S.value = 1 := by
  obtain ⟨S, -, hS⟩ := exists_spcc_value_one P
  exact ⟨S.toStrategy, hS⟩

/-- The hypotheses of `thm:pauli` are jointly satisfiable, and satisfiable in
the strongest case `ε = 0`: there are admissible parameters carrying a strategy
whose value is `1`, so `1 - ε ≤ S.value` holds for every `ε ≥ 0`. -/
theorem pauli_soundness_hypotheses_satisfiable :
    ∃ (P : AdmissibleParams) (S : Strategy (pauliBasisTest P)),
      ∀ ε : ℝ, 0 ≤ ε → 1 - ε ≤ S.value := by
  obtain ⟨S, hS⟩ := exists_pauliBasisTest_strategy_value_one (nonVacuousParams 0)
  refine ⟨nonVacuousParams 0, S, fun ε hε => ?_⟩
  rw [hS]
  linarith

/-- `thm:pauli` applied to hypotheses that are actually met: for the constants
it produces, *every* admissible parameter tuple carries a value-one strategy
for which the extraction data and the three error bounds exist at `ε = 0`.
The statement is unconditional — there is no hypothesis left for a reader to
doubt. -/
theorem pauli_soundness_applies_to_honest_strategy :
    ∃ a b : ℝ, 1 ≤ a ∧ 0 < b ∧ b < 1 ∧
      ∀ P : AdmissibleParams, ∃ S : Strategy (pauliBasisTest P), S.value = 1 ∧
        ∃ w : PauliSoundnessWitness P S,
          ‖isometryTensor w.φA w.φB S.ψ - idealState P w.aux‖ ≤
              deltaQld a b 0 P.m P.d P.q ∧
            (∀ W : PauliKind,
              rawPauliOperatorDistanceA P S w W ≤ deltaQld a b 0 P.m P.d P.q) ∧
            (∀ W : PauliKind,
              rawPauliOperatorDistanceB P S w W ≤ deltaQld a b 0 P.m P.d P.q) := by
  obtain ⟨a, b, ha, hb, hb1, hmain⟩ := pauli_soundness
  refine ⟨a, b, ha, hb, hb1, fun P => ?_⟩
  obtain ⟨S, hS⟩ := exists_pauliBasisTest_strategy_value_one P
  refine ⟨S, hS, hmain P 0 le_rfl S ?_⟩
  rw [hS]
  norm_num

/-! ### Q2: the error function is genuinely small in an explicit regime -/

/-- Formalization-only arithmetic: a negative real power of a power of two,
rewritten as an inverse integer power of `2^b`.  Used to put both `q`-dependent
and `md`-dependent summands of `deltaQld` on the same geometric scale. -/
private theorem two_pow_rpow_neg (b : ℝ) (M : ℕ) :
    ((2 ^ M : ℕ) : ℝ) ^ (-b) = (((2 : ℝ) ^ b) ^ M)⁻¹ := by
  have hcast : ((2 ^ M : ℕ) : ℝ) = (2 : ℝ) ^ (M : ℝ) := by
    rw [Real.rpow_natCast]
    push_cast
    ring
  rw [hcast, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2),
    ← Real.rpow_natCast ((2 : ℝ) ^ b) M,
    ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2),
    ← Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2)]
  congr 1
  ring

/-- Formalization-only arithmetic: the `2^(-b*md)` summand of `deltaQld` as an
inverse integer power of `2^b`. -/
private theorem two_rpow_neg_mul_natCast (b : ℝ) (M : ℕ) :
    (2 : ℝ) ^ (-(b * (M : ℝ))) = (((2 : ℝ) ^ b) ^ M)⁻¹ := by
  rw [← Real.rpow_natCast ((2 : ℝ) ^ b) M,
    ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2),
    ← Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2)]

/-- The error at `ε = 0` along the explicit family, bounded by a
polynomial-over-geometric expression.  Formalization-only: the bound is a
convenience for the limit below, not a statement of the source. -/
private theorem deltaQld_nonVacuousParams_le (a b : ℝ) (ha : 1 ≤ a) (hb : 0 < b) (n : ℕ) :
    deltaQld a b 0 (nonVacuousParams n).m (nonVacuousParams n).d (nonVacuousParams n).q ≤
      2 * a * (((n + 1 : ℕ) : ℝ) ^ ⌈a⌉₊ / ((2 : ℝ) ^ b) ^ (n + 1)) := by
  have ht1 : (1 : ℝ) < (2 : ℝ) ^ b :=
    Real.one_lt_rpow_iff_of_pos (by norm_num) |>.mpr (Or.inl ⟨by norm_num, hb⟩)
  have ht0 : (0 : ℝ) < (2 : ℝ) ^ b := lt_trans zero_lt_one ht1
  have hmd : ((nonVacuousParams n).m * (nonVacuousParams n).d : ℕ) = n + 1 := by
    simp
  have ha0 : (0 : ℝ) ≤ a := le_trans zero_le_one ha
  -- the three summands of the error bracket
  have hzero : (0 : ℝ) ^ b = 0 := Real.zero_rpow (ne_of_gt hb)
  have hq : (((nonVacuousParams n).q : ℕ) : ℝ) ^ (-b) = (((2 : ℝ) ^ b) ^ (2 * n + 1))⁻¹ := by
    rw [nonVacuousParams_q]
    exact two_pow_rpow_neg b (2 * n + 1)
  have hexp : (2 : ℝ) ^ (-(b * ((n + 1 : ℕ) : ℝ))) = (((2 : ℝ) ^ b) ^ (n + 1))⁻¹ :=
    two_rpow_neg_mul_natCast b (n + 1)
  -- geometric comparison: the `q` summand is the smaller one
  have hpow : ((2 : ℝ) ^ b) ^ (n + 1) ≤ ((2 : ℝ) ^ b) ^ (2 * n + 1) :=
    pow_le_pow_right₀ ht1.le (by omega)
  have hinv : (((2 : ℝ) ^ b) ^ (2 * n + 1))⁻¹ ≤ (((2 : ℝ) ^ b) ^ (n + 1))⁻¹ :=
    one_div_le_one_div_of_le (pow_pos ht0 _) hpow |>.trans_eq (by rw [one_div])
      |>.trans_eq' (by rw [one_div])
  have hinvpos : (0 : ℝ) < (((2 : ℝ) ^ b) ^ (n + 1))⁻¹ := inv_pos.mpr (pow_pos ht0 _)
  -- the prefactor
  have hbase : (1 : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Nat.succ_ne_zero n)
  have hceil : a ≤ (⌈a⌉₊ : ℝ) := Nat.le_ceil a
  have hpre : ((n + 1 : ℕ) : ℝ) ^ a ≤ ((n + 1 : ℕ) : ℝ) ^ ⌈a⌉₊ := by
    rw [← Real.rpow_natCast (((n + 1 : ℕ) : ℝ)) ⌈a⌉₊]
    exact Real.rpow_le_rpow_of_exponent_le hbase hceil
  have hprenn : (0 : ℝ) ≤ ((n + 1 : ℕ) : ℝ) ^ a := Real.rpow_nonneg (by linarith) a
  unfold deltaQld
  simp only [Real.rpow_eq_pow]
  rw [hmd, hzero, hq, hexp, zero_add]
  have hstep : (((2 : ℝ) ^ b) ^ (2 * n + 1))⁻¹ + (((2 : ℝ) ^ b) ^ (n + 1))⁻¹ ≤
      2 * (((2 : ℝ) ^ b) ^ (n + 1))⁻¹ := by linarith
  calc a * ((n + 1 : ℕ) : ℝ) ^ a *
        ((((2 : ℝ) ^ b) ^ (2 * n + 1))⁻¹ + (((2 : ℝ) ^ b) ^ (n + 1))⁻¹)
      ≤ a * ((n + 1 : ℕ) : ℝ) ^ ⌈a⌉₊ * (2 * (((2 : ℝ) ^ b) ^ (n + 1))⁻¹) :=
        mul_le_mul (mul_le_mul_of_nonneg_left hpre ha0) hstep
          (add_nonneg (inv_nonneg.mpr (pow_nonneg ht0.le _))
            (inv_nonneg.mpr (pow_nonneg ht0.le _)))
          (mul_nonneg ha0 (pow_nonneg (by linarith) _))
    _ = 2 * a * (((n + 1 : ℕ) : ℝ) ^ ⌈a⌉₊ / ((2 : ℝ) ^ b) ^ (n + 1)) := by
        rw [div_eq_mul_inv]
        ring

/-- **Q2, quantitative form.** For any constants `a ≥ 1` and `b > 0` — in
particular for the ones `thm:pauli` produces — the soundness error at `ε = 0`
tends to zero along the explicit admissible family `nonVacuousParams`.  The
`(md)^a` prefactor is polynomial in `n` while both remaining summands decay
geometrically, so the bound is far from the trivial one in this regime.
Formalization-only: the source does not state this, it answers the
non-triviality question about the shape of `deltaQld`. -/
theorem tendsto_deltaQld_nonVacuousParams (a b : ℝ) (ha : 1 ≤ a) (hb : 0 < b) :
    Tendsto (fun n : ℕ =>
        deltaQld a b 0 (nonVacuousParams n).m (nonVacuousParams n).d (nonVacuousParams n).q)
      atTop (𝓝 0) := by
  have ht1 : (1 : ℝ) < (2 : ℝ) ^ b :=
    Real.one_lt_rpow_iff_of_pos (by norm_num) |>.mpr (Or.inl ⟨by norm_num, hb⟩)
  have hbase : Tendsto (fun n : ℕ => ((n : ℝ) ^ ⌈a⌉₊ / ((2 : ℝ) ^ b) ^ n)) atTop (𝓝 0) :=
    tendsto_pow_const_div_const_pow_of_one_lt ⌈a⌉₊ ht1
  have hshift : Tendsto (fun n : ℕ =>
      (((n + 1 : ℕ) : ℝ) ^ ⌈a⌉₊ / ((2 : ℝ) ^ b) ^ (n + 1))) atTop (𝓝 0) :=
    hbase.comp (tendsto_add_atTop_nat 1)
  have hupper : Tendsto (fun n : ℕ =>
      2 * a * (((n + 1 : ℕ) : ℝ) ^ ⌈a⌉₊ / ((2 : ℝ) ^ b) ^ (n + 1))) atTop (𝓝 0) := by
    simpa using hshift.const_mul (2 * a)
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hupper
    (fun n => ?_) (fun n => deltaQld_nonVacuousParams_le a b ha hb n)
  exact deltaQld_nonneg (P := nonVacuousParams n) (le_trans zero_le_one ha) le_rfl

/-- **Q2, the form a reader asks for.** Whatever the constants, there are
admissible parameters at which the soundness error at `ε = 0` is below any
prescribed `η > 0`; in particular below `1`, and so below any trivial bound. -/
theorem exists_admissibleParams_deltaQld_lt (a b : ℝ) (ha : 1 ≤ a) (hb : 0 < b)
    {η : ℝ} (hη : 0 < η) :
    ∃ P : AdmissibleParams, deltaQld a b 0 P.m P.d P.q < η := by
  obtain ⟨n, hn⟩ :=
    ((tendsto_deltaQld_nonVacuousParams a b ha hb).eventually
      (eventually_lt_nhds hη)).exists
  exact ⟨nonVacuousParams n, hn⟩

/-- Formalization-only: `deltaQld` is continuous in `ε` at `0` from the right,
so the `ε = 0` section used above is the limiting case of the theorem's own
`ε > 0` statement and not a degenerate one. -/
theorem tendsto_deltaQld_eps_zero (a b : ℝ) (hb : 0 < b) (m d q : ℕ) :
    Tendsto (fun ε : ℝ => deltaQld a b ε m d q) (𝓝[≥] 0) (𝓝 (deltaQld a b 0 m d q)) := by
  have hrpow : Tendsto (fun ε : ℝ => Real.rpow ε b) (𝓝[≥] 0) (𝓝 (Real.rpow 0 b)) :=
    ((Real.continuousAt_rpow_const 0 b (Or.inr hb.le)).continuousWithinAt).tendsto
  unfold deltaQld
  exact ((hrpow.add tendsto_const_nhds).add tendsto_const_nhds).const_mul _

/-- **Q1 and Q2 together.** For the constants produced by `thm:pauli` and any
`η > 0` there are admissible parameters carrying a value-one strategy — so the
hypotheses hold — for which the theorem's conclusion bounds the state distance
and both operator distances by a quantity strictly below `η`.  The soundness
theorem is therefore neither vacuously hypothesised nor trivially concluded.
See the module docstring for what this does *not* establish (no uniform rate in
`ε` at fixed parameters). -/
theorem pauli_soundness_nontrivial :
    ∃ a b : ℝ, 1 ≤ a ∧ 0 < b ∧ b < 1 ∧
      ∀ η : ℝ, 0 < η → ∃ (P : AdmissibleParams) (S : Strategy (pauliBasisTest P)),
        S.value = 1 ∧ deltaQld a b 0 P.m P.d P.q < η ∧
        ∃ w : PauliSoundnessWitness P S,
          ‖isometryTensor w.φA w.φB S.ψ - idealState P w.aux‖ <  η ∧
            (∀ W : PauliKind, rawPauliOperatorDistanceA P S w W < η) ∧
            (∀ W : PauliKind, rawPauliOperatorDistanceB P S w W < η) := by
  obtain ⟨a, b, ha, hb, hb1, hmain⟩ := pauli_soundness
  refine ⟨a, b, ha, hb, hb1, fun η hη => ?_⟩
  obtain ⟨n, hn⟩ :=
    ((tendsto_deltaQld_nonVacuousParams a b ha hb).eventually
      (eventually_lt_nhds hη)).exists
  set P := nonVacuousParams n with hP
  obtain ⟨S, hS⟩ := exists_pauliBasisTest_strategy_value_one P
  obtain ⟨w, hstate, hA, hB⟩ := hmain P 0 le_rfl S (by rw [hS]; norm_num)
  exact ⟨P, S, hS, hn, w, lt_of_le_of_lt hstate hn,
    fun W => lt_of_le_of_lt (hA W) hn, fun W => lt_of_le_of_lt (hB W) hn⟩

end

end MIPStarRE.QPBT
