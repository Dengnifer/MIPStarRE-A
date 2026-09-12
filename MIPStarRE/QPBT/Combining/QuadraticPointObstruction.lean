import MIPStarRE.QPBT.Combining.PointErrorObstruction

/-!
# An obstruction to discarding the combined point error

The deterministic joint point answer `(x^2, 0)` gives the combined answer
`alpha * x^2`. A degree-one polynomial cannot agree with this answer at more
than two field elements when `alpha` is nonzero. The same bound holds for
randomized polynomial answers, hence for the outcome probabilities of a POVM.

These are formalization-only counterexample calculations for issue #511, not
claims from the paper and not a proof of the negation of the full construction
assertion in `Apply.lean`.

## References

* `docs/paper-gaps/qpbt_combined-lines-error-term.tex`, subsection
  "Unrestricted point witnesses in the extended-line assertion".
* `references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1020-1034`
  (`lem:qld-4-13`) and 1140-1173 (`claim:17-1`). The source retains the
  error of its constructed points; the unrestricted auxiliary does not.
* Blueprint `lem:qld-4-13-established` and `rem:qld-4-13-source-defects`.
-/

open scoped BigOperators MatrixOrder ComplexOrder

namespace MIPStarRE.QPBT.QuadraticPointObstruction

open MIPStarRE.LDT hiding Measurement
open MIPStarRE.Quantum DistanceCalculus

noncomputable section

/-- A polynomial of degree at most one agrees with a nonzero multiple of
`x^2` at at most two points. This is the root-count calculation in the
counterexample to the unrestricted point-error interface, issue #511. -/
theorem card_affine_quadratic_agreement_le_two
    {K : Type*} [Field K] [Fintype K] [DecidableEq K]
    (f : Polynomial K) (hf : f.natDegree ≤ 1) (alpha : K) (ha : alpha ≠ 0) :
    (Finset.univ.filter fun x : K => f.eval x = alpha * x ^ 2).card ≤ 2 := by
  let p : Polynomial K := f - Polynomial.C alpha * Polynomial.X ^ 2
  have hp : p ≠ 0 := by
    intro h
    have hc := congrArg (fun g : Polynomial K => g.coeff 2) h
    have hf2 : f.coeff 2 = 0 := Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)
    simp [p, hf2] at hc
    exact ha hc
  have hd : p.natDegree ≤ 2 := by
    exact (Polynomial.natDegree_sub_le _ _).trans
      (max_le (hf.trans (by omega)) (by simp [Polynomial.natDegree_C_mul ha]))
  refine (Polynomial.card_le_degree_of_subset_roots (p := p) ?_).trans hd
  intro x hx
  apply (Polynomial.mem_roots hp).mpr
  have hx' := (Finset.mem_filter.mp hx).2
  simp [Polynomial.IsRoot, p, hx']

/-- Randomizing the degree-one answer cannot improve its agreement with a
nonzero quadratic beyond `2 / card K`. The weights may arise from an arbitrary
POVM and state; they must be chosen before sampling the field point. -/
theorem randomized_affine_quadratic_agreement_le
    {K A : Type*} [Field K] [Fintype K] [DecidableEq K] [Fintype A]
    (f : A → Polynomial K) (w : A → ℝ)
    (hw : ∀ a, 0 ≤ w a) (hsum : ∑ a, w a = 1)
    (hdegree : ∀ a, w a ≠ 0 → (f a).natDegree ≤ 1)
    (alpha : K) (ha : alpha ≠ 0) :
    avgOver (uniformDistribution K)
      (fun x => ∑ a, if (f a).eval x = alpha * x ^ 2 then w a else 0) ≤
        2 / (Fintype.card K : ℝ) := by
  classical
  rw [avgOver_sum]
  have hpoint (a : A) :
      avgOver (uniformDistribution K)
        (fun x => if (f a).eval x = alpha * x ^ 2 then w a else 0) ≤
          2 / (Fintype.card K : ℝ) * w a := by
    by_cases hwa : w a = 0
    · simp [hwa, avgOver]
    rw [avgOver_uniform_eq_inv_card_mul_sum, ← Finset.sum_filter]
    simp only [Finset.sum_const, nsmul_eq_mul]
    have hc : ((Finset.univ.filter fun x : K =>
        (f a).eval x = alpha * x ^ 2).card : ℝ) ≤ 2 := by
      exact_mod_cast card_affine_quadratic_agreement_le_two (f a) (hdegree a hwa) alpha ha
    calc
      _ ≤ (Fintype.card K : ℝ)⁻¹ * (2 * w a) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hc (hw a)) (by positivity)
      _ = _ := by ring
  calc
    _ ≤ ∑ a, 2 / (Fintype.card K : ℝ) * w a := Finset.sum_le_sum fun a _ => hpoint a
    _ = 2 / (Fintype.card K : ℝ) := by rw [← Finset.mul_sum, hsum, mul_one]

/-- The measurement that always returns `a`. In the counterexample it is
used with the answer `(x^2, 0)` and its scalar coarse-graining. -/
def deterministicMeasurement {A iota : Type*} [Fintype A] [DecidableEq A]
    [Fintype iota] [DecidableEq iota] (a : A) : Measurement A iota :=
  Measurement.ofSumEqOne (fun b => if b = a then 1 else 0)
    (fun b => by
      split_ifs
      · exact Matrix.PosSemidef.one.nonneg
      · exact le_refl 0) (by simp)

/-- Deterministic measurements are projective. -/
theorem deterministicMeasurement_projective
    {A iota : Type*} [Fintype A] [DecidableEq A]
    [Fintype iota] [DecidableEq iota] (a : A) :
    Measurement.IsProjective (deterministicMeasurement (iota := iota) a) := by
  intro b
  change IsProj (if b = a then 1 else 0)
  split_ifs
  · exact IsStarProjection.one _
  · exact IsStarProjection.zero _

/-- Postprocessing a deterministic measurement returns the image of its
deterministic answer, including when the new answer type is an `Option`. -/
theorem deterministicMeasurement_postprocess
    {A B iota : Type*} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
    [Fintype iota] [DecidableEq iota] (a : A) (f : A → B) :
    (deterministicMeasurement (iota := iota) a).postprocess f =
      deterministicMeasurement (f a) := by
  apply MIPStarRE.Quantum.Measurement.ext
  intro b
  rw [MIPStarRE.Quantum.Measurement.postprocess_effect]
  simp [deterministicMeasurement, Measurement.ofSumEqOne, eq_comm]

/-- The explicit quadratic joint answer on the first X coordinate, independent
of the Z question and the player. For `m = 1` this is exactly `(x^2, 0)` from
the counterexample recorded in issue #511. -/
def quadraticJointMeasurement {P : AdmissibleParams} {epsilon : ℝ}
    (S : ProjectiveSetting P epsilon) (side : PlayerSide)
    (x _z : Fin P.m → PauliScalar P) :
    Measurement (PauliScalar P × PauliScalar P) (S.ExpandedLocalSpace side) :=
  deterministicMeasurement (x ⟨0, Nat.lt_of_lt_of_le Nat.zero_lt_one P.one_le_m⟩ ^ 2, 0)

/-- The quadratic joint answers satisfy every field of `CombinedPointsWitness`
at some scalar error, for every projective setting. No completeness theorem or
admitted construction of combined points is used. -/
theorem exists_quadratic_point_witness
    {P : AdmissibleParams} {epsilon : ℝ} (S : ProjectiveSetting P epsilon) :
    ∃ delta : ℝ, ∃ points : CombinedPointsWitness S delta,
      points.Q = quadraticJointMeasurement S := by
  exact CombinedPointsWitness.exists_error_of_projective S (quadraticJointMeasurement S)
    (fun _ _ _ => deterministicMeasurement_projective _)

/-- The completed combined answer of the quadratic joint measurement is
exactly `some (alpha * x^2)`, in the answer convention of `ExtendedLinesWitness`.
The Z coordinate contributes zero. -/
theorem quadraticJointMeasurement_postprocess
    {P : AdmissibleParams} {epsilon : ℝ} (S : ProjectiveSetting P epsilon)
    (side : PlayerSide) (x z : Fin P.m → PauliScalar P) (alpha beta : PauliScalar P) :
    (quadraticJointMeasurement S side x z).postprocess
        (fun ab => some (alpha * ab.1 + beta * ab.2)) =
      deterministicMeasurement
        (some (alpha * x ⟨0, Nat.lt_of_lt_of_le Nat.zero_lt_one P.one_le_m⟩ ^ 2)) := by
  simp [quadraticJointMeasurement, deterministicMeasurement_postprocess]

/-- Any finite POVM supported on affine polynomials has defect at least
`1 - 2 / card K` against the deterministic quadratic answer. This uses the
repository's actual consistency defect, on an arbitrary unit state. -/
theorem affine_povm_quadratic_defect_ge
    {K A iota : Type*} [Field K] [Fintype K] [DecidableEq K]
    [Fintype A] [DecidableEq A] [Fintype iota] [DecidableEq iota]
    (M : Measurement A iota) (f : A → Polynomial K)
    (hdegree : ∀ a, M.effect a ≠ 0 → (f a).natDegree ≤ 1)
    (psi : EuclideanSpace ℂ iota) (hpsi : ‖psi‖ = 1)
    (alpha : K) (ha : alpha ≠ 0) :
    1 - 2 / (Fintype.card K : ℝ) ≤
      consistencyDefect (uniformDistribution K)
        (fun x a => (M.postprocess fun b => (f b).eval x).effect a)
        (fun x a => (deterministicMeasurement (alpha * x ^ 2)).effect a) psi := by
  have hweight : ∑ a, stateQForm psi (M.effect a) = 1 := by
    rw [← stateQForm_finset_sum, M.sum_eq_one, stateQForm_one, hpsi, one_pow]
  have hbound := randomized_affine_quadratic_agreement_le f
    (fun a => stateQForm psi (M.effect a))
    (fun a => stateQForm_nonneg psi (M.pos a)) hweight
    (fun a ha => hdegree a (by
      intro hz
      apply ha
      simp [hz, stateQForm, applyOperatorToState])) alpha ha
  rw [consistencyDefect_eq_one_sub_overlap _ _ _ psi
    (uniformDistribution_isProbability K) hpsi]
  suffices heq :
      avgOver (uniformDistribution K) (fun x =>
        ∑ a, stateQForm psi
          ((M.postprocess fun b => (f b).eval x).effect a *
            (deterministicMeasurement (alpha * x ^ 2)).effect a)) =
      avgOver (uniformDistribution K)
        (fun x => ∑ a, if (f a).eval x = alpha * x ^ 2
          then stateQForm psi (M.effect a) else 0) by
    rw [heq]
    exact sub_le_sub_left hbound 1
  apply avgOver_congr
  intro x
  rw [Finset.sum_eq_single (alpha * x ^ 2)]
  · simp only [deterministicMeasurement, Measurement.ofSumEqOne, ite_true, mul_one]
    rw [Measurement.postprocess_effect, stateQForm_finset_sum, Finset.sum_filter]
  · intro a _ hne
    simp [deterministicMeasurement, hne, Measurement.ofSumEqOne,
      stateQForm, applyOperatorToState]
  · simp

/-- Adding the completed answer `none` leaves the finite quadratic obstruction
unchanged: all these line evaluations and deterministic point answers lie in
the `some` part of the alphabet. This addresses the completed-answer convention
on nondegenerate axis lines in issue #511. -/
theorem affine_povm_completed_quadratic_defect_ge
    {K A iota : Type*} [Field K] [Fintype K] [DecidableEq K]
    [Fintype A] [DecidableEq A] [Fintype iota] [DecidableEq iota]
    (M : Measurement A iota) (f : A → Polynomial K)
    (hdegree : ∀ a, M.effect a ≠ 0 → (f a).natDegree ≤ 1)
    (psi : EuclideanSpace ℂ iota) (hpsi : ‖psi‖ = 1)
    (alpha : K) (ha : alpha ≠ 0) :
    1 - 2 / (Fintype.card K : ℝ) ≤
      consistencyDefect (uniformDistribution K)
        (fun x a => (M.postprocess fun b => some ((f b).eval x)).effect a)
        (fun x a => (deterministicMeasurement (some (alpha * x ^ 2))).effect a) psi := by
  have heq : consistencyDefect (uniformDistribution K)
      (fun x a => (M.postprocess fun b => some ((f b).eval x)).effect a)
      (fun x a => (deterministicMeasurement (some (alpha * x ^ 2))).effect a) psi =
    consistencyDefect (uniformDistribution K)
      (fun x a => (M.postprocess fun b => (f b).eval x).effect a)
      (fun x a => (deterministicMeasurement (alpha * x ^ 2)).effect a) psi := by
    unfold consistencyDefect
    apply avgOver_congr
    intro x
    have hnone : (M.postprocess fun b => some ((f b).eval x)).effect none = 0 := by
      rw [MIPStarRE.Quantum.Measurement.postprocess_effect]
      simp
    have hsome (a : K) : (M.postprocess fun b => some ((f b).eval x)).effect (some a) =
        (M.postprocess fun b => (f b).eval x).effect a := by
      simp only [MIPStarRE.Quantum.Measurement.postprocess_effect, Option.some.injEq]
    simp only [Fintype.sum_option]
    simp only [hnone, hsome]
    simp [deterministicMeasurement, Measurement.ofSumEqOne]
  rw [heq]
  exact affine_povm_quadratic_defect_ge M f hdegree psi hpsi alpha ha

/-- The defect against a deterministic answer is nonnegative, without a
commutation assumption: every term is either zero or the expectation of one
positive measurement effect. -/
theorem deterministic_defect_nonneg
    {X A iota : Type*} [Fintype X] [DecidableEq X]
    [Fintype A] [DecidableEq A] [Fintype iota] [DecidableEq iota]
    (mu : Distribution X) (M : X → Measurement A iota) (answer : X → A)
    (psi : EuclideanSpace ℂ iota) :
    0 ≤ consistencyDefect mu (fun x a => (M x).effect a)
      (fun x a => (deterministicMeasurement (answer x)).effect a) psi := by
  unfold consistencyDefect
  apply avgOver_nonneg
  intro x
  apply Finset.sum_nonneg
  intro a _
  apply Finset.sum_nonneg
  intro b _
  by_cases hab : a = b
  · simp [hab]
  by_cases hb : b = answer x
  · have hne : a ≠ answer x := by simpa [hb] using hab
    simpa [hab, hb, hne, deterministicMeasurement, Measurement.ofSumEqOne,
      ← consistency_term_eq_stateQForm] using stateQForm_nonneg psi ((M x).pos a)
  · simp [hab, hb, deterministicMeasurement, Measurement.ofSumEqOne]

/-- Averaging the coefficient `alpha` uniformly gives the lower bound
`(1 - 1/q) * (1 - 2/q)`. The line measurement may depend on `alpha` but is
chosen before `x`. This is the full scalar average on an X-axis component of
the counterexample, prior to its mixture weight in the extended line law. -/
theorem uniform_affine_povm_quadratic_defect_ge
    {K A iota : Type*} [Field K] [Fintype K] [DecidableEq K]
    [Fintype A] [DecidableEq A] [Fintype iota] [DecidableEq iota]
    (M : K → Measurement A iota) (f : A → Polynomial K)
    (hdegree : ∀ alpha a, (M alpha).effect a ≠ 0 → (f a).natDegree ≤ 1)
    (psi : EuclideanSpace ℂ iota) (hpsi : ‖psi‖ = 1) :
    (1 - 1 / (Fintype.card K : ℝ)) * (1 - 2 / (Fintype.card K : ℝ)) ≤
      avgOver (uniformDistribution K) (fun alpha =>
        consistencyDefect (uniformDistribution K)
          (fun x a => ((M alpha).postprocess fun b => (f b).eval x).effect a)
          (fun x a => (deterministicMeasurement (alpha * x ^ 2)).effect a) psi) := by
  let c : ℝ := 1 - 2 / (Fintype.card K : ℝ)
  have havg : avgOver (uniformDistribution K) (fun alpha => if alpha = 0 then 0 else c) =
      (1 - 1 / (Fintype.card K : ℝ)) * c := by
    rw [avgOver_uniform_eq_inv_card_mul_sum]
    have hsum : (∑ alpha : K, if alpha = 0 then 0 else c) =
        (Fintype.card K : ℝ) * c - c := by
      calc
        _ = ∑ alpha : K, (c - if alpha = 0 then c else 0) := by
          apply Finset.sum_congr rfl
          intro alpha _
          split_ifs <;> ring
        _ = _ := by simp [Finset.sum_sub_distrib]
    rw [hsum]
    have hcard : (Fintype.card K : ℝ) ≠ 0 := by positivity
    field_simp
  rw [← havg]
  apply avgOver_mono
  intro alpha
  by_cases ha : alpha = 0
  · rw [if_pos ha]
    exact deterministic_defect_nonneg _ _ _ psi
  · rw [if_neg ha]
    exact affine_povm_quadratic_defect_ge (M alpha) f (hdegree alpha) psi hpsi alpha ha

/-- An explicit admissible tuple over the eight-element field, with `m = d = 1`. -/
def eightElementParams : AdmissibleParams where
  q := 8
  m := 1
  d := 1
  hd := by decide
  hq := ⟨3, by decide, by decide⟩
  hdvd := by decide

/-- A finite obstruction over the actual canonical Pauli scalar field of size
eight. For any family of affine-answer POVMs, the averaged defect against
`alpha * x^2` is at least `21/32`. The corresponding X-axis mixture contribution
is `21/256`, because that component has mass `1/8` at extended dimension four.
This theorem establishes the scalar average, not its transport into the full
directly indexed line-point law. -/
theorem eight_element_affine_povm_obstruction
    {iota : Type*} [Fintype iota] [DecidableEq iota]
    (M : PauliScalar eightElementParams →
      Measurement (Fin 2 → PauliScalar eightElementParams) iota)
    (psi : EuclideanSpace ℂ iota) (hpsi : ‖psi‖ = 1) :
    (21 : ℝ) / 32 ≤
      avgOver (uniformDistribution (PauliScalar eightElementParams)) (fun alpha =>
        consistencyDefect (uniformDistribution (PauliScalar eightElementParams))
          (fun x a => ((M alpha).postprocess fun f => evalCoefficient f x).effect a)
          (fun x a => (deterministicMeasurement (alpha * x ^ 2)).effect a) psi) := by
  have hcard : Fintype.card (PauliScalar eightElementParams) = 8 :=
    eightElementParams.model.card
  have h := uniform_affine_povm_quadratic_defect_ge M
    (fun f => linePolynomialOfCoefficients (c := 1) f)
    (fun _ f _ => linePolynomialOfCoefficients_natDegree_le f) psi hpsi
  norm_num [hcard, linePolynomialOfCoefficients_eval] at h ⊢
  exact h

end

end MIPStarRE.QPBT.QuadraticPointObstruction
