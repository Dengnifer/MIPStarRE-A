import MIPStarRE.QPBT.Observables.WinImplications.LowDegree

/-!
# Evaluation of line polynomials at a sampled point

This module records the elementary calculus of the partial evaluation
`evalOpt` of a coefficient-list line polynomial at a point: the evaluation of
a sum is the sum of the evaluations whenever both summands evaluate, a summand
of an evaluating sum evaluates whenever the other summand does, the value is
unique, and nothing evaluates at a point off the line. These facts underlie
the manipulation of the evaluation classes in items 2 and 3 of the
expanded-line consistency lemma.

Every declaration below is a formalization-only auxiliary: the source uses
these facts about evaluation without stating them.

## References

The evaluation classes `[eval_u(·) = a]` are `def:ideg-deg-polynomials`, paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:51-58`. They are
manipulated in `eq:qld-comm-line-pt-cons` and `eq:qld-comm-line-pt-cons2`,
paper `references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:534-545`.
-/

open scoped BigOperators

namespace MIPStarRE.QPBT

open MIPStarRE.LDT

/-- Coefficient-list evaluation is additive in the coefficient list. This
is the additivity behind the convolution of `def:expanded-line-measurement`. -/
theorem evalCoefficient_add {K : Type*} [Semiring K] {n : ℕ} (c d : Fin n → K)
    (t : K) : evalCoefficient (c + d) t = evalCoefficient c t + evalCoefficient d t := by
  unfold evalCoefficient
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Pi.add_apply, add_mul]

/-- A line polynomial has at most one value at a point of the line: if it
evaluates both to `a` and to `b`, then `a = b`. -/
theorem EvaluatesTo.unique {L : LdParams} {c : ℕ} {line : LineDesc L}
    {f : DegPoly L c} {u : Fin L.m → ScalarQ L} {a b : ScalarQ L}
    (ha : EvaluatesTo line f u a) (hb : EvaluatesTo line f u b) : a = b := by
  obtain ⟨t, ht⟩ := ha.1
  rw [← ha.2 t ht, ← hb.2 t ht]

/-- The sum of two evaluating line polynomials evaluates to the sum of
their values. This is why the convolution outcome `f = f' + f''` evaluates
whenever both convolution factors do. -/
theorem EvaluatesTo.add {L : LdParams} {c : ℕ} {line : LineDesc L}
    {f g : DegPoly L c} {u : Fin L.m → ScalarQ L} {a b : ScalarQ L}
    (hf : EvaluatesTo line f u a) (hg : EvaluatesTo line g u b) :
    EvaluatesTo line (f + g) u (a + b) :=
  ⟨hf.1, fun t ht => by rw [evalCoefficient_add, hf.2 t ht, hg.2 t ht]⟩

/-- If a sum and its second summand evaluate, the first summand evaluates to
the difference of their values. This is the converse direction used to identify
the convolution fibers of an evaluation class. -/
theorem EvaluatesTo.left_of_add {L : LdParams} {c : ℕ} {line : LineDesc L}
    {f g : DegPoly L c} {u : Fin L.m → ScalarQ L} {s b : ScalarQ L}
    (hfg : EvaluatesTo line (f + g) u s) (hg : EvaluatesTo line g u b) :
    EvaluatesTo line f u (s - b) :=
  ⟨hfg.1, fun t ht => by
    have h := hfg.2 t ht
    rw [evalCoefficient_add, hg.2 t ht] at h
    exact eq_sub_of_add_eq h⟩

/-- The partial evaluation returns `some a` exactly when the polynomial
evaluates to `a`. This is the characterization that makes `evalOpt` the total
form of the evaluation classes of `def:ideg-deg-polynomials`. -/
theorem evalOpt_eq_some_iff {L : LdParams} {c : ℕ} (line : LineDesc L)
    (u : Fin L.m → ScalarQ L) (f : DegPoly L c) (a : ScalarQ L) :
    evalOpt line u f = some a ↔ EvaluatesTo line f u a := by
  constructor
  · intro h
    unfold evalOpt at h
    by_cases hex : ∃ a : ScalarQ L, EvaluatesTo line f u a
    · rw [dif_pos hex, Option.some_inj] at h
      rw [← h]
      exact Classical.choose_spec hex
    · rw [dif_neg hex] at h
      exact absurd h (by simp)
  · exact WinImplications.evalOpt_eq_some_of_evaluatesTo line f u a

/-- The partial evaluation returns `none` exactly when no value is
determined. This is the outcome that completes the evaluation classes to a
measurement, written `[eval_u(·) = ⊥]` in `def:ideg-deg-polynomials`. -/
theorem evalOpt_eq_none_iff {L : LdParams} {c : ℕ} (line : LineDesc L)
    (u : Fin L.m → ScalarQ L) (f : DegPoly L c) :
    evalOpt line u f = none ↔ ¬ ∃ a : ScalarQ L, EvaluatesTo line f u a := by
  unfold evalOpt
  split_ifs with hex <;> simp [hex]

/-- The partial evaluation of a sum of two evaluating line polynomials is
the sum of their values. -/
theorem evalOpt_add_of_some {L : LdParams} {c : ℕ} {line : LineDesc L}
    {u : Fin L.m → ScalarQ L} {f g : DegPoly L c} {a b : ScalarQ L}
    (hf : evalOpt line u f = some a) (hg : evalOpt line u g = some b) :
    evalOpt line u (f + g) = some (a + b) :=
  (evalOpt_eq_some_iff line u _ _).mpr
    (((evalOpt_eq_some_iff line u f a).mp hf).add
      ((evalOpt_eq_some_iff line u g b).mp hg))

/-- If a sum and its second summand evaluate, so does the first summand,
with the difference of the two values. -/
theorem evalOpt_left_of_add_some {L : LdParams} {c : ℕ} {line : LineDesc L}
    {u : Fin L.m → ScalarQ L} {f g : DegPoly L c} {s b : ScalarQ L}
    (hfg : evalOpt line u (f + g) = some s) (hg : evalOpt line u g = some b) :
    evalOpt line u f = some (s - b) :=
  (evalOpt_eq_some_iff line u _ _).mpr
    (((evalOpt_eq_some_iff line u _ s).mp hfg).left_of_add
      ((evalOpt_eq_some_iff line u g b).mp hg))

/-- A point at which some line polynomial evaluates lies on the line. -/
theorem mem_pointSet_of_evalOpt_eq_some {L : LdParams} {c : ℕ}
    {line : LineDesc L} {u : Fin L.m → ScalarQ L} {f : DegPoly L c}
    {a : ScalarQ L} (h : evalOpt line u f = some a) : u ∈ line.pointSet :=
  ((evalOpt_eq_some_iff line u f a).mp h).1

/-- Off the line, no line polynomial evaluates, so every outcome falls in
the `none` class. -/
theorem evalOpt_eq_none_of_not_mem {L : LdParams} {c : ℕ} {line : LineDesc L}
    {u : Fin L.m → ScalarQ L} (hu : u ∉ line.pointSet) (f : DegPoly L c) :
    evalOpt line u f = none := by
  rw [evalOpt_eq_none_iff]
  rintro ⟨a, ha⟩
  exact hu ha.1

end MIPStarRE.QPBT
