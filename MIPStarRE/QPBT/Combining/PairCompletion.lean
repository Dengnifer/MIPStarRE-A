import MIPStarRE.QPBT.Combining.Defs
import MIPStarRE.QPBT.Games.Sandwich.Support

/-!
# Restricting and completing global polynomial-pair measurements

The combining map embeds pairs of bounded individual-degree polynomials into
extended polynomials. Restricting a measurement along this embedding produces a
submeasurement whose missing operator is the sum of the noncombined effects.
Relabeling those effects by one specified pair completes the measurement and
preserves projectivity.

These algebraic constructions do not establish the concentration estimate
`eq:qld-g-non-separable` or the point consistency required by
`exists_globalPairWitness`. Issue #513 retains those obligations.

## References

- Blueprint `lem:qld-4-7`.
- `references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1375-1404`,
  `eq:qld-sgg-completeness` and the final completion paragraph.
- Restriction and completion proofs recovered from commit `cb6d86d8`;
  the evaluation identity is from `3de03d0a`, as preserved at `aaa5cb48`.
-/

namespace MIPStarRE.QPBT

open scoped BigOperators MatrixOrder

noncomputable section

/-- Recover the two polynomial components by setting the unused block to zero
and the scalar coordinates to `(1,0)` or `(0,1)`. This algebraic substitution
is the left inverse implicit in the restriction to combined outcomes in
`eq:qld-sgg-completeness`, paper lines 1375--1380. Unlike evaluation as a
polynomial function on a finite field, it does not require a degree bound. -/
noncomputable def recoverCombinedPair {K : Type*} [CommSemiring K] {m : ℕ}
    (polynomial : MvPolynomial (Fin (2 * m + 2)) K) :
    MvPolynomial (Fin m) K × MvPolynomial (Fin m) K :=
  (MvPolynomial.eval₂ MvPolynomial.C (fun index =>
    match finCombineEquiv m index with
    | .inl (.inl coordinate) => MvPolynomial.X coordinate
    | .inl (.inr _) => 0
    | .inr scalar => if scalar = 0 then 1 else 0) polynomial,
   MvPolynomial.eval₂ MvPolynomial.C (fun index =>
    match finCombineEquiv m index with
    | .inl (.inl _) => 0
    | .inl (.inr coordinate) => MvPolynomial.X coordinate
    | .inr scalar => if scalar = 1 then 1 else 0) polynomial)

/-- Substitution recovers both components of a combined polynomial. This is
formalization support for the relabeling in `eq:qld-sgg-completeness`, paper
lines 1375--1380. -/
@[simp] theorem recoverCombinedPair_combinePoly {K : Type*} [CommSemiring K] {m : ℕ}
    (first second : MvPolynomial (Fin m) K) :
    recoverCombinedPair (combinePoly first second) = (first, second) := by
  simp [recoverCombinedPair, combinePoly, MvPolynomial.eval₂_rename,
    embX, embZ, alphaVar, betaVar, Function.comp_def, MvPolynomial.eval₂_eta]

/-- Distinct polynomial pairs label distinct combined outcomes. This justifies
restricting a measurement on extended polynomials to pairs without duplicating
an effect in `eq:qld-sgg-completeness`, paper lines 1375--1380. -/
theorem combinePoly_injective {K : Type*} [CommSemiring K] {m : ℕ} :
    Function.Injective (fun pair : MvPolynomial (Fin m) K × MvPolynomial (Fin m) K =>
      combinePoly pair.1 pair.2) := by
  exact (show Function.LeftInverse recoverCombinedPair
    (fun pair : MvPolynomial (Fin m) K × MvPolynomial (Fin m) K =>
      combinePoly pair.1 pair.2) from fun pair =>
        recoverCombinedPair_combinePoly pair.1 pair.2).injective

/-- The bounded polynomial-pair embedding used to restrict the global
measurement in `eq:qld-sgg-completeness`, paper lines 1375--1380. The degree
bound is inherited from `def:combine-map`; the two scalar coordinates have
degree one, allowed by admissibility. -/
noncomputable def combinedPolyEmbedding (P : AdmissibleParams) :
    PolyPair P ↪ MIPStarRE.LDT.Preliminaries.polyFunc (2 * P.m + 2) (PauliScalar P) P.d where
  toFun pair := ⟨combinePoly pair.1.1 pair.2.1,
    combinePoly_mem_polyFunc P.hd pair.1.2 pair.2.2⟩
  inj' := by
    intro first second heq
    have hpoly : combinePoly first.1.1 first.2.1 = combinePoly second.1.1 second.2.1 :=
      congrArg Subtype.val heq
    have hpair : (first.1.1, first.2.1) = (second.1.1, second.2.1) :=
      combinePoly_injective hpoly
    exact Prod.ext (Subtype.ext (congrArg Prod.fst hpair))
      (Subtype.ext (congrArg Prod.snd hpair))

/-- Evaluation of a combined outcome is the affine combination of its two
components.  This is the pointwise algebraic identity used when transferring
the global-pair measurement to the expanded point measurements in
`lem:qld-4-7`, paper `references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1364--1380`.
It is a formalization-only consequence of `def:combine-map`; it does not assert
any consistency or quantitative error estimate.
-/
theorem combinedPolyEmbedding_eval (P : AdmissibleParams)
    (u : Fin (2 * P.m + 2) → PauliScalar P) (pair : PolyPair P) :
    MvPolynomial.eval u (combinedPolyEmbedding P pair).1 =
      u (alphaVar P.m) * evalAt .X (projX u) pair +
        u (betaVar P.m) * evalAt .Z (projZ u) pair := by
  change MvPolynomial.eval u (combinePoly pair.1.1 pair.2.1) = _
  rw [combinePoly_eval]
  rfl

/-- Restrict an extended-polynomial measurement to combined outcomes, as in
`eq:qld-sgg-completeness`, paper lines 1375--1380. Injectivity of the combining
map ensures that the retained effects sum to at most the identity. This
construction does not assert the source's quantitative completeness bound. -/
noncomputable def combinedPairSubmeasurement (P : AdmissibleParams)
    {carrier : Type*} [Fintype carrier] [DecidableEq carrier]
    (measurement : Quantum.Measurement
      (MIPStarRE.LDT.Preliminaries.polyFunc (2 * P.m + 2) (PauliScalar P) P.d) carrier) :
    Quantum.Submeasurement (PolyPair P) carrier where
  effect pair := measurement.effect (combinedPolyEmbedding P pair)
  pos pair := measurement.pos _
  sum_le_one := by
    classical
    rw [← Finset.sum_image (fun first _ second _ heq =>
      (combinedPolyEmbedding P).injective heq)]
    exact (Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
      (fun outcome _ _ => measurement.pos outcome)).trans measurement.sum_le_one

/-- Restricting to combined outcomes preserves projectivity, as asserted
before `eq:qld-sgg-completeness`, paper lines 1375--1380. -/
theorem combinedPairSubmeasurement_projective (P : AdmissibleParams)
    {carrier : Type*} [Fintype carrier] [DecidableEq carrier]
    (measurement : Quantum.Measurement
      (MIPStarRE.LDT.Preliminaries.polyFunc (2 * P.m + 2) (PauliScalar P) P.d) carrier)
    (hprojective : Measurement.IsProjective measurement) :
    ∀ pair, Quantum.IsProj ((combinedPairSubmeasurement P measurement).effect pair) := by
  intro pair
  exact hprojective (combinedPolyEmbedding P pair)

/-- The missing operator of the polynomial-pair submeasurement is exactly the
sum of the effects outside the range of the combining map. This is the
operator identity underlying `eq:qld-sgg-completeness`, paper lines 1375--1380;
the bound on its state mass is a separate obligation. -/
theorem combinedPairSubmeasurement_missing (P : AdmissibleParams)
    {carrier : Type*} [Fintype carrier] [DecidableEq carrier]
    (measurement : Quantum.Measurement
      (MIPStarRE.LDT.Preliminaries.polyFunc (2 * P.m + 2) (PauliScalar P) P.d) carrier) :
    1 - (combinedPairSubmeasurement P measurement).total =
      ∑ polynomial ∈ Finset.univ.filter
        (fun polynomial => polynomial ∉ Set.range (combinedPolyEmbedding P)),
        measurement.effect polynomial := by
  classical
  have htotal : (combinedPairSubmeasurement P measurement).total =
      ∑ polynomial ∈ Finset.univ.filter
        (fun polynomial => polynomial ∈ Set.range (combinedPolyEmbedding P)),
        measurement.effect polynomial := by
    change (∑ pair, measurement.effect (combinedPolyEmbedding P pair)) = _
    rw [← Finset.sum_image (fun first _ second _ heq =>
      (combinedPolyEmbedding P).injective heq)]
    congr 1
    ext polynomial
    simp
  rw [htotal, ← measurement.sum_eq_one]
  apply sub_eq_iff_eq_add.mpr
  exact (Finset.sum_filter_add_sum_filter_not Finset.univ
    (fun polynomial => polynomial ∈ Set.range (combinedPolyEmbedding P))
    measurement.effect).symm.trans (add_comm _ _)

/-- Relabel a combined polynomial by its unique pair and send every other
polynomial to a specified pair. This implements the completion at an arbitrary
outcome in the last paragraph of `lem:qld-4-7`, paper lines 1402--1404. The
noncombined outcomes are retained at the completion outcome, not discarded. -/
noncomputable def completedPairLabel (P : AdmissibleParams) (completionPair : PolyPair P) :
    MIPStarRE.LDT.Preliminaries.polyFunc (2 * P.m + 2) (PauliScalar P) P.d → PolyPair P :=
  Function.extend (combinedPolyEmbedding P) id (fun _ => completionPair)

/-- Completion preserves every combined polynomial's pair label. -/
@[simp] theorem completedPairLabel_combinedPolyEmbedding (P : AdmissibleParams)
    (completionPair pair : PolyPair P) :
    completedPairLabel P completionPair (combinedPolyEmbedding P pair) = pair := by
  exact (combinedPolyEmbedding P).injective.extend_apply _ _ _

/-- All outcomes outside the combining map's range go to the completion pair. -/
theorem completedPairLabel_of_not_mem_range (P : AdmissibleParams)
    (completionPair : PolyPair P)
    (polynomial : MIPStarRE.LDT.Preliminaries.polyFunc (2 * P.m + 2) (PauliScalar P) P.d)
    (houtside : polynomial ∉ Set.range (combinedPolyEmbedding P)) :
    completedPairLabel P completionPair polynomial = completionPair := by
  exact Function.extend_apply' _ _ _ houtside

/-- The completed polynomial-pair measurement of the final paragraph of
`lem:qld-4-7`, paper lines 1402--1404, obtained by relabeling all extended
polynomial outcomes. No assertion about consistency is built into this
construction. -/
noncomputable def completedPairMeasurement (P : AdmissibleParams)
    {carrier : Type*} [Fintype carrier] [DecidableEq carrier]
    (measurement : Quantum.Measurement
      (MIPStarRE.LDT.Preliminaries.polyFunc (2 * P.m + 2) (PauliScalar P) P.d) carrier)
    (completionPair : PolyPair P) : Quantum.Measurement (PolyPair P) carrier :=
  measurement.postprocess (completedPairLabel P completionPair)

/-- Completing the pair measurement adds precisely its missing operator to
the specified outcome and leaves all other effects unchanged. This is the
completion formula of `lem:qld-4-7`, paper lines 1402--1404. -/
theorem completedPairMeasurement_effect (P : AdmissibleParams)
    {carrier : Type*} [Fintype carrier] [DecidableEq carrier]
    (measurement : Quantum.Measurement
      (MIPStarRE.LDT.Preliminaries.polyFunc (2 * P.m + 2) (PauliScalar P) P.d) carrier)
    (completionPair pair : PolyPair P) :
    (completedPairMeasurement P measurement completionPair).effect pair =
      (combinedPairSubmeasurement P measurement).effect pair +
        if pair = completionPair then 1 - (combinedPairSubmeasurement P measurement).total
        else 0 := by
  classical
  rw [completedPairMeasurement, Quantum.Measurement.postprocess_effect, Finset.sum_filter]
  rw [← Finset.sum_filter_add_sum_filter_not Finset.univ
    (fun polynomial => polynomial ∈ Set.range (combinedPolyEmbedding P))]
  have hgood :
      Finset.univ.filter (fun polynomial => polynomial ∈ Set.range (combinedPolyEmbedding P)) =
        Finset.univ.image (combinedPolyEmbedding P) := by
    ext polynomial
    simp
  rw [hgood, Finset.sum_image (fun first _ second _ heq =>
    (combinedPolyEmbedding P).injective heq)]
  simp only [completedPairLabel_combinedPolyEmbedding]
  rw [Finset.sum_ite_eq', if_pos (Finset.mem_univ pair)]
  congr 1
  have hbad :
      (∑ polynomial ∈ Finset.univ.filter
        (fun polynomial => polynomial ∉ Set.range (combinedPolyEmbedding P)),
        if completedPairLabel P completionPair polynomial = pair then
          measurement.effect polynomial else 0) =
      ∑ polynomial ∈ Finset.univ.filter
        (fun polynomial => polynomial ∉ Set.range (combinedPolyEmbedding P)),
        if completionPair = pair then measurement.effect polynomial else 0 := by
    apply Finset.sum_congr rfl
    intro polynomial hpolynomial
    rw [completedPairLabel_of_not_mem_range P completionPair polynomial
      (Finset.mem_filter.mp hpolynomial).2]
  rw [hbad]
  by_cases heq : pair = completionPair
  · simp [heq, combinedPairSubmeasurement_missing]
  · simp [heq, Ne.symm heq]

/-- The completed polynomial-pair measurement is projective whenever the
extended-polynomial measurement is projective. This proves the qualitative
completion step in `lem:qld-4-7`, paper lines 1402--1404, without assuming its
unproved consistency conclusion. -/
theorem completedPairMeasurement_projective (P : AdmissibleParams)
    {carrier : Type*} [Fintype carrier] [DecidableEq carrier]
    (measurement : Quantum.Measurement
      (MIPStarRE.LDT.Preliminaries.polyFunc (2 * P.m + 2) (PauliScalar P) P.d) carrier)
    (hprojective : Measurement.IsProjective measurement) (completionPair : PolyPair P) :
    Measurement.IsProjective (completedPairMeasurement P measurement completionPair) := by
  exact SandwichProduct.postprocess_isProjective measurement hprojective _

open MIPStarRE.Quantum DistanceCalculus

/-- Completion can only increase agreement with any evaluated reference
measurement on the opposite tensor factor. Consequently, its consistency
defect is at most the squared state norm minus the retained diagonal overlap.
This is the completion step of `lem:qld-4-7`, paper lines 1402--1404, for an
arbitrary outcome evaluation; it does not supply the preceding overlap bound.
Neither projectivity nor normalization of the state is needed. -/
theorem completedPairMeasurement_evaluated_defect_le (P : AdmissibleParams)
    {Answer Left Right : Type*} [Fintype Answer] [DecidableEq Answer]
    [Fintype Left] [DecidableEq Left] [Fintype Right] [DecidableEq Right]
    (measurement : Quantum.Measurement
      (MIPStarRE.LDT.Preliminaries.polyFunc (2 * P.m + 2) (PauliScalar P) P.d) Left)
    (completionPair : PolyPair P) (eval : PolyPair P → Answer)
    (reference : Quantum.Measurement Answer Right)
    (psi : EuclideanSpace ℂ (Left × Right)) :
    (∑ a : Answer, ∑ b : Answer, if a = b then 0 else
      stateQForm psi (heteroKron
        (((completedPairMeasurement P measurement completionPair).postprocess eval).effect a)
        (reference.effect b))) ≤
      ‖psi‖ ^ 2 - ∑ pair : PolyPair P, stateQForm psi
        (heteroKron ((combinedPairSubmeasurement P measurement).effect pair)
          (reference.effect (eval pair))) := by
  classical
  let completed := completedPairMeasurement P measurement completionPair
  have hdiag :
      (∑ a : Answer, stateQForm psi
        (heteroKron ((completed.postprocess eval).effect a) (reference.effect a))) =
        ∑ pair : PolyPair P, stateQForm psi
          (heteroKron (completed.effect pair) (reference.effect (eval pair))) := by
    simp_rw [Quantum.Measurement.postprocess_effect, heteroKron_finset_sum_left,
      stateQForm_finset_sum]
    calc
      _ = ∑ a : Answer, ∑ pair ∈ Finset.univ.filter (fun pair => eval pair = a),
          stateQForm psi
            (heteroKron (completed.effect pair) (reference.effect (eval pair))) := by
        apply Finset.sum_congr rfl
        intro a _
        apply Finset.sum_congr rfl
        intro pair hpair
        rw [(Finset.mem_filter.mp hpair).2]
      _ = _ := Finset.sum_fiberwise Finset.univ eval _
  have hretained :
      (∑ pair : PolyPair P, stateQForm psi
        (heteroKron ((combinedPairSubmeasurement P measurement).effect pair)
          (reference.effect (eval pair)))) ≤
        ∑ pair : PolyPair P, stateQForm psi
          (heteroKron (completed.effect pair) (reference.effect (eval pair))) := by
    apply Finset.sum_le_sum
    intro pair _
    dsimp [completed]
    rw [completedPairMeasurement_effect]
    by_cases hpair : pair = completionPair
    · rw [if_pos hpair, heteroKron_add_left, stateQForm_add]
      exact le_add_of_nonneg_right (stateQForm_nonneg psi
        (kronecker_nonneg
          (sub_nonneg.mpr (combinedPairSubmeasurement P measurement).total_le_one)
          (reference.pos (eval pair))))
    · simp [hpair]
  have hdefect := point_defect_eq
    (leftPlacedMeasurement (ιB := Right) (completed.postprocess eval))
    (rightPlacedMeasurement (ιA := Left) reference) psi
  simp only [leftPlacedMeasurement, rightPlacedMeasurement,
    Quantum.Measurement.ofSumEqOne] at hdefect
  simp_rw [placed_product_stateQForm_eq] at hdefect
  change _ ≤ _
  rw [hdefect, hdiag]
  exact sub_le_sub_left hretained _

/-- Uniformly averaging the completion estimate gives the consistency defect
needed for the point marginals in `lem:qld-4-7`, paper lines 1402--1404.
The retained overlap remains explicit and must be bounded from the source
strategy before this estimate can establish global-pair existence. -/
theorem completedPairMeasurement_consistencyDefect_le (P : AdmissibleParams)
    {Question Answer Left Right : Type*}
    [Fintype Question] [DecidableEq Question] [Nonempty Question]
    [Fintype Answer] [DecidableEq Answer]
    [Fintype Left] [DecidableEq Left] [Fintype Right] [DecidableEq Right]
    (measurement : Quantum.Measurement
      (MIPStarRE.LDT.Preliminaries.polyFunc (2 * P.m + 2) (PauliScalar P) P.d) Left)
    (completionPair : PolyPair P) (eval : Question → PolyPair P → Answer)
    (reference : Question → Quantum.Measurement Answer Right)
    (psi : EuclideanSpace ℂ (Left × Right)) :
    consistencyDefect (MIPStarRE.LDT.uniformDistribution Question)
      (fun x a => heteroKron
        (((completedPairMeasurement P measurement completionPair).postprocess (eval x)).effect a)
        (1 : Op Right))
      (fun x a => heteroKron (1 : Op Left) ((reference x).effect a)) psi ≤
      ‖psi‖ ^ 2 - MIPStarRE.LDT.avgOver (MIPStarRE.LDT.uniformDistribution Question)
        (fun x => ∑ pair : PolyPair P, stateQForm psi
          (heteroKron ((combinedPairSubmeasurement P measurement).effect pair)
            ((reference x).effect (eval x pair)))) := by
  rw [SandwichProduct.consistencyDefect_placed_eq_avg_point]
  have h := MIPStarRE.LDT.avgOver_mono (MIPStarRE.LDT.uniformDistribution Question) _ _
    (fun x => completedPairMeasurement_evaluated_defect_le P measurement completionPair
      (eval x) (reference x) psi)
  simpa only [MIPStarRE.LDT.avgOver_sub, MIPStarRE.LDT.avgOver_uniform_const] using h

end

end MIPStarRE.QPBT
