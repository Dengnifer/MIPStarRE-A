import MIPStarRE.QPBT.Test.SoundnessDefs
import MIPStarRE.QPBT.Combining.DirectLowDegree.RejectionBounds

/-!
# Extending Pauli soundness bounds from `ε ≤ 1` to the full error domain

The Pauli basis test soundness statement quantifies over every error parameter
`0 ≤ ε`, while the extraction and isometry arguments that establish it are
carried out for `0 ≤ ε ≤ 1`.  This module supplies the two Lean-only facts that
bridge the two domains.

## Main results

* `deltaQld_mono_epsilon` — the error scale `deltaQld` is monotone in `ε`
  on `0 ≤ ε`; only the `ε ^ b` summand depends on `ε`.
* `pauli_isometry_bounds_extend_epsilon` — the soundness conclusion for every
  `ε` in `[0, 1]` implies the same conclusion for every `0 ≤ ε`, at the same
  universal constants `a` and `b`.

For `1 ≤ ε` the success hypothesis `1 - ε ≤ S.value` carries no information:
it already follows from `Strategy.value_nonneg` applied at `ε = 1`.  The
`ε ≤ 1` result is therefore instantiated at `ε = 1` and its conclusion pushed
up to the larger `ε` by monotonicity of `deltaQld`.  No trivial witness and no
uniform numeric bound are involved.

## References

These are formalization-only support results for blueprint `thm:pauli`, whose
statement is at paper
`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:1426-1447`
and whose isometry step is proved at
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1862-1876`.  The
source states the theorem for every `ε ≥ 0` and argues the substantive case
`ε ≤ 1`; the reduction recorded here is the bookkeeping that the source leaves
implicit.  It adds no hypothesis to `thm:pauli` and changes no constant.
-/

open scoped BigOperators Matrix ComplexOrder

namespace MIPStarRE.QPBT

open MIPStarRE.LDT
open MIPStarRE.Quantum

noncomputable section

/-- The Pauli-test error scale `deltaQld` is monotone in the error parameter `ε`
on `0 ≤ ε`.  Only the summand `ε ^ b` depends on `ε`, and the prefactor
`a * (m * d) ^ a` is nonnegative, so the bound follows from monotonicity of
`Real.rpow` in its base.

Unlike `deltaQld_mono`, which adjusts the universal constants `a` and `b` and is
therefore restricted to `ε ≤ 1`, this lemma keeps `a` and `b` fixed and holds on
the whole domain `0 ≤ ε` of blueprint `thm:pauli`, paper
`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:1426-1447`. -/
theorem deltaQld_mono_epsilon {P : AdmissibleParams} {a b ε ε' : ℝ}
    (ha : 1 ≤ a) (hb : 0 < b) (hε0 : 0 ≤ ε) (hle : ε ≤ ε') :
    deltaQld a b ε P.m P.d P.q ≤ deltaQld a b ε' P.m P.d P.q := by
  have hmd : (1 : ℝ) ≤ ((P.m * P.d : ℕ) : ℝ) :=
    Nat.one_le_cast.mpr (Nat.mul_pos P.one_le_m P.hd)
  have hmd0 : (0 : ℝ) ≤ ((P.m * P.d : ℕ) : ℝ) := by linarith
  unfold deltaQld
  simp only [Real.rpow_eq_pow]
  have hεb : ε ^ b ≤ ε' ^ b := Real.rpow_le_rpow hε0 hle hb.le
  have hpre : 0 ≤ a * ((P.m * P.d : ℕ) : ℝ) ^ a :=
    mul_nonneg (by linarith) (Real.rpow_nonneg hmd0 a)
  exact mul_le_mul_of_nonneg_left (by linarith) hpre

/-- Domain extension for the Pauli basis test soundness bounds: if the state and
operator estimates hold at fixed constants `a`, `b` for every error parameter in
`[0, 1]`, then they hold for every `0 ≤ ε`.

For `1 < ε` the hypothesis `1 - ε ≤ S.value` is weaker than the hypothesis at
`ε = 1`, which is `0 ≤ S.value` and holds for every strategy
(`Strategy.value_nonneg`).  The witness produced at `ε = 1` therefore serves at
`ε`, and its three bounds are pushed up by `deltaQld_mono_epsilon`.

This lemma is a Lean-only bridge between the domain of blueprint `thm:pauli`
(paper
`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:1426-1447`,
which assumes only `ε ≥ 0`) and the domain on which the isometry argument at
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1862-1876` is
carried out.  It mentions no unproved declaration and weakens nothing: the
conclusion is the source conclusion at the source's own `ε`.

A caller holding the `[0, 1]` result with the constants packaged existentially
destructures that existential first and applies this lemma to the resulting
`a`, `b`:

```
obtain ⟨a, b, ha, hb, hb1, hbounds⟩ := (the `[0, 1]` result)
exact ⟨a, b, ha, hb, hb1, pauli_isometry_bounds_extend_epsilon ha hb hbounds⟩
```

The existentially packaged form is deliberately not provided as a lemma of its
own: its hypothesis would be an inline existential matching the conclusion, the
proof-evasion pattern that `scripts/audit_conclusion_shaped_hypotheses.py`
(issue #493) exists to catch.  Keeping the constants explicit makes the domain
restriction `ε ≤ 1` — the only difference between hypothesis and conclusion —
visible in the binder structure. -/
theorem pauli_isometry_bounds_extend_epsilon {a b : ℝ} (ha : 1 ≤ a) (hb : 0 < b)
    (h : ∀ (P : AdmissibleParams) (ε : ℝ), 0 ≤ ε → ε ≤ 1 →
        ∀ S : Strategy (pauliBasisTest P), 1 - ε ≤ S.value →
          ∃ w : PauliSoundnessWitness P S,
            ‖isometryTensor w.φA w.φB S.ψ - idealState P w.aux‖ ≤
                deltaQld a b ε P.m P.d P.q ∧
            (∀ W : PauliKind,
              pauliOperatorDistanceA P S w W ≤ deltaQld a b ε P.m P.d P.q) ∧
            (∀ W : PauliKind,
              pauliOperatorDistanceB P S w W ≤ deltaQld a b ε P.m P.d P.q)) :
    ∀ (P : AdmissibleParams) (ε : ℝ), 0 ≤ ε →
      ∀ S : Strategy (pauliBasisTest P), 1 - ε ≤ S.value →
        ∃ w : PauliSoundnessWitness P S,
          ‖isometryTensor w.φA w.φB S.ψ - idealState P w.aux‖ ≤
              deltaQld a b ε P.m P.d P.q ∧
          (∀ W : PauliKind,
            pauliOperatorDistanceA P S w W ≤ deltaQld a b ε P.m P.d P.q) ∧
          (∀ W : PauliKind,
            pauliOperatorDistanceB P S w W ≤ deltaQld a b ε P.m P.d P.q) := by
  intro P ε hε S hS
  rcases le_or_gt ε 1 with hle | hgt
  · exact h P ε hε hle S hS
  · obtain ⟨w, hstate, hA, hB⟩ :=
      h P 1 zero_le_one le_rfl S (by simpa using S.value_nonneg)
    have hmono : deltaQld a b 1 P.m P.d P.q ≤ deltaQld a b ε P.m P.d P.q :=
      deltaQld_mono_epsilon ha hb zero_le_one hgt.le
    exact ⟨w, hstate.trans hmono, fun W => (hA W).trans hmono,
      fun W => (hB W).trans hmono⟩

end

end MIPStarRE.QPBT
