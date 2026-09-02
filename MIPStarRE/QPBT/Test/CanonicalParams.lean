import MIPStarRE.QPBT.Test.Soundness

/-!
# Canonical Pauli basis test parameters

This file defines the canonical admissible parameter tuple as a function of
the target register size and states its quantitative soundness estimate.

## References

The definitions and estimate correspond to `def:introparams` and
`lem:delta-bound` in
`blueprint/src/chapter/ch13_qpbt_test.tex:448-481`, from
`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:1503-1547`.
-/

namespace MIPStarRE.QPBT

noncomputable section

/-- The admissibility predicate for a parameter tuple `(q, m, d)`. -/
def IsAdmissibleTuple (t : ℕ × ℕ × ℕ) : Prop :=
  IsAdmissibleSize t.1 ∧ 1 ≤ t.2.1 ∧ 1 ≤ t.2.2 ∧ t.2.1 ∣ t.1

/-- Convert an admissible tuple to the parameter structure used by the
Pauli basis game. -/
def AdmissibleParams.ofTuple (t : ℕ × ℕ × ℕ)
    (h : IsAdmissibleTuple t) : AdmissibleParams where
  q := t.1
  m := t.2.1
  d := t.2.2
  hd := h.2.2.1
  hq := h.1
  hdvd := h.2.2.2

/-- The smallest even natural number represented by the ceiling prescription
in `def:introparams`. -/
noncomputable def introParamsC (a b : ℝ) : ℕ :=
  2 * ⌈(b + a) / (2 * b)⌉₊

/-- The canonical `(q, m, d)` tuple of `def:introparams`. -/
def introParamsTuple (c R : ℕ) : ℕ × ℕ × ℕ :=
  (2 ^ (c * Nat.clog 2 (Nat.clog 2 R) + 1),
    2 ^ Nat.log 2 (c * Nat.clog 2 R + 1), 1)

/-- The canonical tuple is admissible. This is the numerical
admissibility part of `lem:delta-bound`, blueprint
`ch13_qpbt_test.tex:459-478`, paper
`08_classical_and_quantum_low_degree_tests.tex:1521-1547`. -/
theorem introParamsTuple_isAdmissible (a b : ℝ) (R : ℕ) (hR : 4 ≤ R) :
    IsAdmissibleTuple (introParamsTuple (introParamsC a b) R) := by
  sorry

/-- The canonical admissible parameter structure of `def:introparams`,
blueprint `ch13_qpbt_test.tex:448-457`, paper
`08_classical_and_quantum_low_degree_tests.tex:1503-1520`. -/
noncomputable def introParams (a b : ℝ) (R : ℕ) (hR : 4 ≤ R) :
    AdmissibleParams :=
  AdmissibleParams.ofTuple _ (introParamsTuple_isAdmissible a b R hR)

/-- The canonical parameter dimension supplies at least `R` encoded
coordinates, as asserted in `lem:delta-bound`. -/
theorem le_two_pow_introParams_m (a b : ℝ) (ha : 1 ≤ a) (hb : 0 < b)
    (R : ℕ) (hR : 4 ≤ R) :
    R ≤ 2 ^ (introParams a b R hR).m := by
  sorry

/-- `lem:delta-bound`: the Pauli soundness error at the canonical parameters
has polylogarithmic dependence on `R`. Blueprint
`ch13_qpbt_test.tex:459-478`, paper
`08_classical_and_quantum_low_degree_tests.tex:1521-1547`.

**Local fix:** The third error term is bounded directly using the lower bound
on `m`, rather than the source's false intermediate comparison between the
field exponent and `m`. This discrepancy is documented in issue #16 and
`docs/paper-gaps/qpbt_delta-bound-exponent-comparison.tex`; see also
`rem:delta-bound-exponent-comparison`. -/
theorem exists_deltaQld_introParams_bound (a b : ℝ) (ha : 1 ≤ a)
    (hb : 0 < b) (hb' : b < 1) :
    ∃ a' b' : ℝ, 1 ≤ a' ∧ 0 < b' ∧ b' ≤ 1 ∧
      ∀ (R : ℕ) (hR : 4 ≤ R) (ε : ℝ),
        deltaQld a b ε (introParams a b R hR).m
            (introParams a b R hR).d (introParams a b R hR).q ≤
          a' * (Real.rpow (Real.logb 2 R) a' * Real.rpow ε b' +
            Real.rpow (Real.logb 2 R) (-b')) := by
  sorry

end

end MIPStarRE.QPBT
