import MIPStarRE.QPBT.Combining.DirectLowDegree.Transport.Consistency.Defect

/-!
# Correlated-ancilla consistency compression

This module contains the correlated-state identities and the two valid
seed-fiber consistency-defect compression results.

## References

- `references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:393-458`
- `references/ldt-paper/test_definition.tex:180-202`
- `docs/paper-gaps/qpbt_ld-dimension-divisibility.tex`
-/

open scoped BigOperators Matrix MatrixOrder ComplexOrder

namespace MIPStarRE.QPBT

open MIPStarRE.LDT
open MIPStarRE.LDT.Preliminaries
open MIPStarRE.Quantum

noncomputable section

/-! ## Seed-fiber identities -/

/-- Reconstructing a seed-indexed point question in any residue block gives
the original point question. -/
@[simp] theorem seededLdQuestion_directLdPointQuestionOf
    (L : LdParams) (u : Fin L.m → ScalarQ L)
    (residue : Fin (L.q / L.m)) :
    seededLdQuestion L
        (directLdPointQuestionOf L.toDirectLdParams u) residue =
      ldPointQuestionOf L u :=
  rfl

/-- The direct point-answer readout agrees with the seed-indexed readout under
the canonical answer equivalence. -/
@[simp] theorem ldPointValuesOrZero_ldDirectAnswerEquiv_symm
    (L : LdParams) (a : DirectLdAnswer L.toDirectLdParams) :
    ldPointValuesOrZero L ((ldDirectAnswerEquiv L).symm a) =
      directLdPointValuesOrZero L.toDirectLdParams a := by
  cases a <;> rfl

private theorem seedFiberPointMeasurement
    (L : LdParams) {iota : Type*} [Fintype iota] [DecidableEq iota]
    (M : LdQuestion L →
      MIPStarRE.Quantum.Measurement (LdAnswer L) iota)
    (u : Fin L.m → ScalarQ L) :
    (blockDiagonalMeasurement fun residue =>
        matrixMeasurementTransport (ldDirectAnswerEquiv L)
          (M (seededLdQuestion L
            (directLdPointQuestionOf L.toDirectLdParams u) residue))).postprocess
        (directLdPointValuesOrZero L.toDirectLdParams) =
      blockDiagonalMeasurement fun _ =>
        (M (ldPointQuestionOf L u)).postprocess (ldPointValuesOrZero L) := by
  rw [blockDiagonalMeasurement_postprocess]
  apply congrArg blockDiagonalMeasurement
  funext residue
  rw [matrixMeasurementTransport_postprocess,
    seededLdQuestion_directLdPointQuestionOf]
  congr 1
  funext a
  cases a <;> rfl

/-- The point POVM of the seed-fiber lift of the strategy is the block-diagonal
amplification of Alice's original seed-indexed point POVM. -/
theorem ldStrategyToDirect_pointMeasurementA
    (L : LdParams) (S : Strategy (ldGame L))
    (u : Fin L.m → ScalarQ L) :
    (((ldStrategyToDirect L S).A
        (directLdPointQuestionOf L.toDirectLdParams u)).postprocess
      (directLdPointValuesOrZero L.toDirectLdParams)) =
      blockDiagonalMeasurement fun _ =>
        (S.A (ldPointQuestionOf L u)).postprocess (ldPointValuesOrZero L) := by
  change (blockDiagonalMeasurement fun residue =>
      matrixMeasurementTransport (ldDirectAnswerEquiv L)
        (S.A (seededLdQuestion L
          (directLdPointQuestionOf L.toDirectLdParams u) residue))).postprocess
      (directLdPointValuesOrZero L.toDirectLdParams) = _
  exact seedFiberPointMeasurement L S.A u

/-- The point POVM of the seed-fiber lift of the strategy is the block-diagonal
amplification of Bob's original seed-indexed point POVM. -/
theorem ldStrategyToDirect_pointMeasurementB
    (L : LdParams) (S : Strategy (ldGame L))
    (u : Fin L.m → ScalarQ L) :
    (((ldStrategyToDirect L S).B
        (directLdPointQuestionOf L.toDirectLdParams u)).postprocess
      (directLdPointValuesOrZero L.toDirectLdParams)) =
      blockDiagonalMeasurement fun _ =>
        (S.B (ldPointQuestionOf L u)).postprocess (ldPointValuesOrZero L) := by
  change (blockDiagonalMeasurement fun residue =>
      matrixMeasurementTransport (ldDirectAnswerEquiv L)
        (S.B (seededLdQuestion L
          (directLdPointQuestionOf L.toDirectLdParams u) residue))).postprocess
      (directLdPointValuesOrZero L.toDirectLdParams) = _
  exact seedFiberPointMeasurement L S.B u

private theorem correlated_ancilla_scale
    (block : Type*) [Fintype block] [Nonempty block] :
    (Real.sqrt (Fintype.card block : ℝ) : ℂ)⁻¹ *
        (starRingEnd ℂ)
          (Real.sqrt (Fintype.card block : ℝ) : ℂ)⁻¹ =
      (Fintype.card block : ℂ)⁻¹ := by
  rw [show (starRingEnd ℂ)
      (Real.sqrt (Fintype.card block : ℝ) : ℂ)⁻¹ =
        (Real.sqrt (Fintype.card block : ℝ) : ℂ)⁻¹ by simp]
  rw [← pow_two, inv_pow, ← Complex.ofReal_pow,
    Real.sq_sqrt (Nat.cast_nonneg (Fintype.card block))]
  norm_cast
  exact Complex.ofReal_inv _

private theorem correlatedState_compress_left
    {iotaA iotaB block : Type*}
    [Fintype iotaA] [DecidableEq iotaA]
    [Fintype iotaB] [DecidableEq iotaB]
    [Fintype block] [DecidableEq block] [Nonempty block]
    (psi : EuclideanSpace ℂ (iotaA × iotaB))
    (phi : EuclideanSpace ℂ ((iotaA × block) × (iotaB × block)))
    (hphi : ∀ i j r s, phi ((i, r), (j, s)) =
      if r = s then
        psi (i, j) * (Real.sqrt (Fintype.card block : ℝ) : ℂ)⁻¹
      else 0)
    (A : Op (iotaA × block)) (B : Op iotaB) :
    DistanceCalculus.stateQForm phi
        (heteroKron A (Matrix.blockDiagonal fun _ => B)) =
      DistanceCalculus.stateQForm psi
        (heteroKron (averageDiagonalBlock A) B) := by
  classical
  unfold DistanceCalculus.stateQForm
  apply congrArg Complex.re
  unfold applyOperatorToState heteroKron Matrix.kronecker averageDiagonalBlock
  simp_rw [EuclideanSpace.inner_eq_star_dotProduct]
  simp only [Matrix.toEuclideanLin, Matrix.toLpLin_apply, dotProduct,
    Matrix.mulVec]
  simp_rw [← Finset.univ_product_univ, Finset.sum_product]
  suffices h :
      (∑ i : iotaA, ∑ r : block, ∑ j : iotaB,
        ∑ i' : iotaA, ∑ j' : iotaB,
          (starRingEnd ℂ)
              (Real.sqrt (Fintype.card block : ℝ) : ℂ)⁻¹ *
            (starRingEnd ℂ) (psi (i, j)) *
              (B j j' * (A (i, r) (i', r) *
                ((Real.sqrt (Fintype.card block : ℝ) : ℂ)⁻¹ *
                  psi (i', j'))))) =
        ∑ i : iotaA, ∑ j : iotaB, ∑ i' : iotaA,
          ∑ j' : iotaB, ∑ r : block,
            (starRingEnd ℂ) (psi (i, j)) *
              (psi (i', j') * (B j j' *
                ((Fintype.card block : ℂ)⁻¹ * A (i, r) (i', r)))) by
    simpa [hphi, Matrix.blockDiagonal_apply, Matrix.kroneckerMap_apply,
      apply_ite, map_zero, ite_mul, zero_mul, Finset.sum_ite_eq,
      Finset.mem_univ, if_true, map_mul, Matrix.submatrix,
      Matrix.sum_apply, Matrix.of_apply, Finset.mul_sum, Finset.sum_mul,
      mul_assoc, mul_comm] using h
  apply Fintype.sum_congr
  intro i
  rw [Finset.sum_comm]
  apply Fintype.sum_congr
  intro j
  rw [Finset.sum_comm]
  apply Fintype.sum_congr
  intro i'
  rw [Finset.sum_comm]
  apply Fintype.sum_congr
  intro j'
  apply Fintype.sum_congr
  intro r
  ring_nf
  rw [correlated_ancilla_scale block]
  ring

private theorem correlatedState_compress_right
    {iotaA iotaB block : Type*}
    [Fintype iotaA] [DecidableEq iotaA]
    [Fintype iotaB] [DecidableEq iotaB]
    [Fintype block] [DecidableEq block] [Nonempty block]
    (psi : EuclideanSpace ℂ (iotaA × iotaB))
    (phi : EuclideanSpace ℂ ((iotaA × block) × (iotaB × block)))
    (hphi : ∀ i j r s, phi ((i, r), (j, s)) =
      if r = s then
        psi (i, j) * (Real.sqrt (Fintype.card block : ℝ) : ℂ)⁻¹
      else 0)
    (A : Op iotaA) (B : Op (iotaB × block)) :
    DistanceCalculus.stateQForm phi
        (heteroKron (Matrix.blockDiagonal fun _ => A) B) =
      DistanceCalculus.stateQForm psi
        (heteroKron A (averageDiagonalBlock B)) := by
  classical
  unfold DistanceCalculus.stateQForm
  apply congrArg Complex.re
  unfold applyOperatorToState heteroKron Matrix.kronecker averageDiagonalBlock
  simp_rw [EuclideanSpace.inner_eq_star_dotProduct]
  simp only [Matrix.toEuclideanLin, Matrix.toLpLin_apply, dotProduct,
    Matrix.mulVec]
  simp_rw [← Finset.univ_product_univ, Finset.sum_product]
  suffices h :
      (∑ i : iotaA, ∑ r : block, ∑ j : iotaB,
        ∑ i' : iotaA, ∑ j' : iotaB,
          (starRingEnd ℂ)
              (Real.sqrt (Fintype.card block : ℝ) : ℂ)⁻¹ *
            (starRingEnd ℂ) (psi (i, j)) *
              (A i i' * (B (j, r) (j', r) *
                ((Real.sqrt (Fintype.card block : ℝ) : ℂ)⁻¹ *
                  psi (i', j'))))) =
        ∑ i : iotaA, ∑ j : iotaB, ∑ i' : iotaA,
          ∑ j' : iotaB, ∑ r : block,
            (starRingEnd ℂ) (psi (i, j)) *
              (psi (i', j') * (A i i' *
                ((Fintype.card block : ℂ)⁻¹ * B (j, r) (j', r)))) by
    simpa [hphi, Matrix.blockDiagonal_apply, Matrix.kroneckerMap_apply,
      apply_ite, map_zero, ite_mul, zero_mul, Finset.sum_ite_eq,
      Finset.mem_univ, if_true, map_mul, Matrix.submatrix,
      Matrix.sum_apply, Matrix.of_apply, Finset.mul_sum, Finset.sum_mul,
      mul_assoc, mul_comm] using h
  apply Fintype.sum_congr
  intro i
  rw [Finset.sum_comm]
  apply Fintype.sum_congr
  intro j
  rw [Finset.sum_comm]
  apply Fintype.sum_congr
  intro i'
  rw [Finset.sum_comm]
  apply Fintype.sum_congr
  intro j'
  apply Fintype.sum_congr
  intro r
  ring_nf
  rw [correlated_ancilla_scale block]
  ring

/-- Compressing Alice's ancillary register preserves every correlation against
an operator on Bob's original carrier. -/
theorem seedFiberLiftedState_compress_left
    {G : Game} (S : Strategy G) (L : LdParams)
    (A : Op (S.ιA × Fin (L.q / L.m))) (B : Op S.ιB) :
    DistanceCalculus.stateQForm (seedFiberLiftedState S L)
        (heteroKron A (Matrix.blockDiagonal fun _ => B)) =
      DistanceCalculus.stateQForm S.ψ
        (heteroKron (averageDiagonalBlock A) B) := by
  classical
  letI : Nonempty (Fin (L.q / L.m)) :=
    Fin.pos_iff_nonempty.mp L.seedFiberCard_pos
  apply correlatedState_compress_left S.ψ (seedFiberLiftedState S L)
  intro i j r s
  exact seedFiberLiftedState_apply S L i j r s

/-- Compressing Bob's ancillary register preserves every correlation against
an operator on Alice's original carrier. -/
theorem seedFiberLiftedState_compress_right
    {G : Game} (S : Strategy G) (L : LdParams)
    (A : Op S.ιA) (B : Op (S.ιB × Fin (L.q / L.m))) :
    DistanceCalculus.stateQForm (seedFiberLiftedState S L)
        (heteroKron (Matrix.blockDiagonal fun _ => A) B) =
      DistanceCalculus.stateQForm S.ψ
        (heteroKron A (averageDiagonalBlock B)) := by
  classical
  letI : Nonempty (Fin (L.q / L.m)) :=
    Fin.pos_iff_nonempty.mp L.seedFiberCard_pos
  apply correlatedState_compress_right S.ψ (seedFiberLiftedState S L)
  intro i j r s
  exact seedFiberLiftedState_apply S L i j r s

/-- Compressing an arbitrary Alice family preserves its defect against a Bob
family that is constant on the correlated residue register. -/
theorem consistencyDefect_seedFiber_compress_left
    {G : Game} (S : Strategy G) (L : LdParams)
    {X alpha : Type*} [Fintype X] [DecidableEq X]
    [Fintype alpha] [DecidableEq alpha]
    (mu : Distribution X)
    (A : X → alpha → Op (S.ιA × Fin (L.q / L.m)))
    (B : X → alpha → Op S.ιB) :
    consistencyDefect mu
        (fun x a => heteroKron (A x a) 1)
        (fun x a => heteroKron 1 (Matrix.blockDiagonal fun _ => B x a))
        (seedFiberLiftedState S L) =
      consistencyDefect mu
        (fun x a => heteroKron (averageDiagonalBlock (A x a)) 1)
        (fun x a => heteroKron 1 (B x a)) S.ψ := by
  classical
  letI : Nonempty (Fin (L.q / L.m)) :=
    Fin.pos_iff_nonempty.mp L.seedFiberCard_pos
  unfold consistencyDefect avgOver
  simp_rw [DistanceCalculus.consistency_term_eq_stateQForm,
    DistanceCalculus.placed_product_stateQForm_eq]
  apply Finset.sum_congr rfl
  intro x _
  congr 1
  apply Fintype.sum_congr
  intro a
  apply Fintype.sum_congr
  intro b
  by_cases hab : a = b
  · simp [hab]
  · simp only [if_neg hab]
    exact seedFiberLiftedState_compress_left S L (A x a) (B x b)

/-- Compressing an arbitrary Bob family preserves its defect against an Alice
family that is constant on the correlated residue register. -/
theorem consistencyDefect_seedFiber_compress_right
    {G : Game} (S : Strategy G) (L : LdParams)
    {X alpha : Type*} [Fintype X] [DecidableEq X]
    [Fintype alpha] [DecidableEq alpha]
    (mu : Distribution X) (A : X → alpha → Op S.ιA)
    (B : X → alpha → Op (S.ιB × Fin (L.q / L.m))) :
    consistencyDefect mu
        (fun x a => heteroKron (Matrix.blockDiagonal fun _ => A x a) 1)
        (fun x a => heteroKron 1 (B x a)) (seedFiberLiftedState S L) =
      consistencyDefect mu
        (fun x a => heteroKron (A x a) 1)
        (fun x a => heteroKron 1 (averageDiagonalBlock (B x a))) S.ψ := by
  classical
  letI : Nonempty (Fin (L.q / L.m)) :=
    Fin.pos_iff_nonempty.mp L.seedFiberCard_pos
  unfold consistencyDefect avgOver
  simp_rw [DistanceCalculus.consistency_term_eq_stateQForm,
    DistanceCalculus.placed_product_stateQForm_eq]
  apply Finset.sum_congr rfl
  intro x _
  congr 1
  apply Fintype.sum_congr
  intro a
  apply Fintype.sum_congr
  intro b
  by_cases hab : a = b
  · simp [hab]
  · simp only [if_neg hab]
    exact seedFiberLiftedState_compress_right S L (A x a) (B x b)

/-- The point-on-Alice/global-on-Bob defect of the seed-fiber lift of the strategy is
exactly the defect of the compressed polynomial tuple on the original
seed-indexed strategy. -/
theorem ldStrategyToDirect_pointPolynomial_compression
    (L : LdParams) (S : Strategy (ldGame L))
    (GB : DirectPolyMeasTuple L.toDirectLdParams
      (S.ιB × Fin (L.q / L.m))) :
    consistencyDefect (uniformDistribution (Fin L.m → ScalarQ L))
        (fun u outcome =>
          heteroKron
            ((((ldStrategyToDirect L S).A
              (directLdPointQuestionOf L.toDirectLdParams u)).postprocess
                (directLdPointValuesOrZero L.toDirectLdParams)).effect outcome) 1)
        (fun u outcome => heteroKron 1
          ((GB.postprocess (evalDirectPolyTupleAt u)).effect outcome))
        (ldStrategyToDirect L S).ψ =
      consistencyDefect (uniformDistribution (Fin L.m → ScalarQ L))
        (fun u outcome => heteroKron
          (((S.A (ldPointQuestionOf L u)).postprocess
            (ldPointValuesOrZero L)).effect outcome) 1)
        (fun u outcome => heteroKron 1
          (((seedFiberCompressPolyMeasTuple L GB).postprocess
            (evalPolyTupleAt u)).effect outcome)) S.ψ := by
  rw [show (ldStrategyToDirect L S).ψ = seedFiberLiftedState S L by rfl]
  simp only [ldStrategyToDirect_pointMeasurementA,
    blockDiagonalMeasurement_effect,
    seedFiberCompressPolyMeasTuple_evaluation,
    seedFiberCompressMeasurement_effect]
  convert consistencyDefect_seedFiber_compress_right S L
    (X := Fin L.m → ScalarQ L) (alpha := Fin L.k → ScalarQ L)
    (uniformDistribution (Fin L.m → ScalarQ L))
    (fun u outcome =>
      ((S.A (ldPointQuestionOf L u)).postprocess
        (ldPointValuesOrZero L)).effect outcome)
    (fun u outcome =>
      (GB.postprocess (evalDirectPolyTupleAt u)).effect outcome) using 1
  apply consistencyDefect_congr <;> intros <;> rfl

/-- The global-on-Alice/point-on-Bob defect of the seed-fiber lift of the strategy is
exactly the defect of the compressed polynomial tuple on the original
seed-indexed strategy. -/
theorem ldStrategyToDirect_polynomialPoint_compression
    (L : LdParams) (S : Strategy (ldGame L))
    (GA : DirectPolyMeasTuple L.toDirectLdParams
      (S.ιA × Fin (L.q / L.m))) :
    consistencyDefect (uniformDistribution (Fin L.m → ScalarQ L))
        (fun u outcome => heteroKron
          ((GA.postprocess (evalDirectPolyTupleAt u)).effect outcome) 1)
        (fun u outcome =>
          heteroKron 1
            ((((ldStrategyToDirect L S).B
              (directLdPointQuestionOf L.toDirectLdParams u)).postprocess
                (directLdPointValuesOrZero L.toDirectLdParams)).effect outcome))
        (ldStrategyToDirect L S).ψ =
      consistencyDefect (uniformDistribution (Fin L.m → ScalarQ L))
        (fun u outcome => heteroKron
          (((seedFiberCompressPolyMeasTuple L GA).postprocess
            (evalPolyTupleAt u)).effect outcome) 1)
        (fun u outcome => heteroKron 1
          (((S.B (ldPointQuestionOf L u)).postprocess
            (ldPointValuesOrZero L)).effect outcome)) S.ψ := by
  rw [show (ldStrategyToDirect L S).ψ = seedFiberLiftedState S L by rfl]
  simp only [ldStrategyToDirect_pointMeasurementB,
    blockDiagonalMeasurement_effect,
    seedFiberCompressPolyMeasTuple_evaluation,
    seedFiberCompressMeasurement_effect]
  convert consistencyDefect_seedFiber_compress_left S L
    (X := Fin L.m → ScalarQ L) (alpha := Fin L.k → ScalarQ L)
    (uniformDistribution (Fin L.m → ScalarQ L))
    (fun u outcome =>
      (GA.postprocess (evalDirectPolyTupleAt u)).effect outcome)
    (fun u outcome =>
      ((S.B (ldPointQuestionOf L u)).postprocess
        (ldPointValuesOrZero L)).effect outcome) using 1
  all_goals
    apply consistencyDefect_congr <;> intros <;> rfl

end

end MIPStarRE.QPBT
