import MIPStarRE.QPBT.Combining.DirectLowDegree.Transport.Correspondence
import MIPStarRE.QPBT.State
import MIPStarRE.Quantum.FiniteMatrix.BlockDiagonal

/-!
# Seed-fiber dilation for the directly indexed low-degree game

This module dilates a seed-indexed low-degree strategy by a maximally
correlated residue register.  Block-diagonal projective measurements retain
arbitrary dependence on the seed within each `chiIndex` fiber.

## References

- `references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:31-458`
- `docs/paper-gaps/qpbt_ld-dimension-divisibility.tex`
-/

open scoped BigOperators MatrixOrder Matrix ComplexOrder

namespace MIPStarRE.QPBT

open MIPStarRE.LDT
open MIPStarRE.Quantum

noncomputable section

/-! ## Projective block measurements -/

/-- Relabel a matrix measurement along an equivalence of outcome alphabets. -/
noncomputable def matrixMeasurementTransport
    {alpha beta iota : Type*}
    [Fintype alpha] [Fintype beta] [Fintype iota] [DecidableEq iota]
    (e : alpha ≃ beta) (M : MIPStarRE.Quantum.Measurement alpha iota) :
    MIPStarRE.Quantum.Measurement beta iota :=
  MIPStarRE.Quantum.Measurement.ofSumEqOne
    (fun b => M.effect (e.symm b))
    (fun b => M.pos (e.symm b))
    (by
      calc
        ∑ b, M.effect (e.symm b) = ∑ a, M.effect a :=
          Equiv.sum_comp e.symm M.effect
        _ = 1 := M.sum_eq_one)

@[simp] theorem matrixMeasurementTransport_effect
    {alpha beta iota : Type*}
    [Fintype alpha] [Fintype beta] [Fintype iota] [DecidableEq iota]
    (e : alpha ≃ beta) (M : MIPStarRE.Quantum.Measurement alpha iota)
    (b : beta) :
    (matrixMeasurementTransport e M).effect b = M.effect (e.symm b) :=
  rfl

/-- Relabeling a projective matrix measurement preserves projectivity. -/
theorem matrixMeasurementTransport_isProjective
    {alpha beta iota : Type*}
    [Fintype alpha] [Fintype beta] [Fintype iota] [DecidableEq iota]
    (e : alpha ≃ beta) (M : MIPStarRE.Quantum.Measurement alpha iota)
    (hM : MIPStarRE.QPBT.Measurement.IsProjective M) :
    MIPStarRE.QPBT.Measurement.IsProjective (matrixMeasurementTransport e M) :=
  fun b => hM (e.symm b)

/-- Assemble a family of matrix measurements as diagonal blocks indexed by a
finite classical register. -/
noncomputable def blockDiagonalMeasurement
    {alpha iota block : Type*}
    [Fintype alpha] [Fintype iota] [DecidableEq iota]
    [Fintype block] [DecidableEq block]
    (M : block → MIPStarRE.Quantum.Measurement alpha iota) :
    MIPStarRE.Quantum.Measurement alpha (iota × block) :=
  MIPStarRE.Quantum.Measurement.ofSumEqOne
    (fun a => Matrix.blockDiagonal fun r => (M r).effect a)
    (fun a => Matrix.blockDiagonal_nonneg
      (fun r => (M r).effect a) (fun r => (M r).pos a))
    (by
      ext ⟨i, r⟩ ⟨j, s⟩
      simp only [Matrix.sum_apply, Matrix.blockDiagonal_apply]
      by_cases hrs : r = s
      · subst s
        simp only [if_pos]
        calc
          ∑ x, (M r).effect x i j = (1 : Matrix iota iota ℂ) i j :=
            by
              simpa only [Matrix.sum_apply] using
                congrFun (congrFun (M r).sum_eq_one i) j
          _ = (1 : Matrix (iota × block) (iota × block) ℂ)
              (i, r) (j, r) := by
                change (if i = j then 1 else 0) =
                  (if (i, r) = (j, r) then 1 else 0)
                simp
      · simp [hrs])

@[simp] theorem blockDiagonalMeasurement_effect
    {alpha iota block : Type*}
    [Fintype alpha] [Fintype iota] [DecidableEq iota]
    [Fintype block] [DecidableEq block]
    (M : block → MIPStarRE.Quantum.Measurement alpha iota)
    (a : alpha) :
    (blockDiagonalMeasurement M).effect a =
      Matrix.blockDiagonal (fun r => (M r).effect a) :=
  rfl

/-- A block-diagonal family of projective measurements is projective. -/
theorem blockDiagonalMeasurement_isProjective
    {alpha iota block : Type*}
    [Fintype alpha] [Fintype iota] [DecidableEq iota]
    [Fintype block] [DecidableEq block]
    (M : block → MIPStarRE.Quantum.Measurement alpha iota)
    (hM : ∀ r, MIPStarRE.QPBT.Measurement.IsProjective (M r)) :
    MIPStarRE.QPBT.Measurement.IsProjective (blockDiagonalMeasurement M) := by
  intro a
  constructor
  · change Matrix.blockDiagonal (fun r => (M r).effect a) *
        Matrix.blockDiagonal (fun r => (M r).effect a) =
      Matrix.blockDiagonal (fun r => (M r).effect a)
    rw [← Matrix.blockDiagonal_mul]
    congr 1
    funext r
    exact (hM r a).isIdempotentElem.eq
  · change (Matrix.blockDiagonal (fun r => (M r).effect a))ᴴ =
      Matrix.blockDiagonal (fun r => (M r).effect a)
    rw [Matrix.blockDiagonal_conjTranspose]
    congr 1
    funext r
    exact (hM r a).isSelfAdjoint.star_eq

/-! ## The correlated residue state -/

/-- The normalized maximally correlated state on the common seed-fiber
residue. -/
noncomputable def seedResidueAncilla (L : LdParams) :
    EuclideanSpace ℂ
      (Fin (L.q / L.m) × Fin (L.q / L.m)) := by
  letI : Nonempty (Fin (L.q / L.m)) :=
    Fin.pos_iff_nonempty.mp L.seedFiberCard_pos
  exact eprState (Fin (L.q / L.m))

/-- The seed-residue ancilla has unit norm. -/
theorem seedResidueAncilla_norm (L : LdParams) :
    ‖seedResidueAncilla L‖ = 1 := by
  letI : Nonempty (Fin (L.q / L.m)) :=
    Fin.pos_iff_nonempty.mp L.seedFiberCard_pos
  exact eprState_norm (Fin (L.q / L.m))

/-- Tensor the original strategy state with the maximally correlated residue
state and shuffle the factors back into the two local carriers. -/
noncomputable def seedFiberLiftedState
    {G : Game} (S : Strategy G) (L : LdParams) :
    EuclideanSpace ℂ
      ((S.ιA × Fin (L.q / L.m)) × (S.ιB × Fin (L.q / L.m))) :=
  reindexState prodShuffle (vecTensor S.ψ (seedResidueAncilla L))

/-- The correlated seed-fiber lift preserves normalization of the strategy
state. -/
theorem seedFiberLiftedState_norm
    {G : Game} (S : Strategy G) (L : LdParams) :
    ‖seedFiberLiftedState S L‖ = 1 := by
  rw [seedFiberLiftedState, reindexState_norm_eq, vecTensor_norm_eq,
    S.ψ_norm, seedResidueAncilla_norm, one_mul]

/-! ## From the seed-indexed game to the direct game -/

/-- The seed-indexed question selected in one residue block of a direct
question.  Applying `ldCL` ensures that irrelevant ambient coordinates are
canonicalized exactly as in the source game. -/
noncomputable def seededLdQuestion (L : LdParams)
    (q : DirectLdQuestion L.toDirectLdParams)
    (residue : Fin (L.q / L.m)) : LdQuestion L :=
  (q.1, ldCL L q.1 (ldSpaceOfDirectResidue L q.2 residue))

/-- Dilate a strategy for the seed-indexed low-degree game to the directly
indexed game.  The two local carriers receive correlated copies of the seed
residue, and each measurement is block diagonal in that residue. -/
noncomputable def ldStrategyToDirect (L : LdParams)
    (S : Strategy (ldGame L)) : Strategy (directLdGame L.toDirectLdParams) where
  ιA := S.ιA × Fin (L.q / L.m)
  ιB := S.ιB × Fin (L.q / L.m)
  ψ := seedFiberLiftedState S L
  ψ_norm := seedFiberLiftedState_norm S L
  A q := blockDiagonalMeasurement fun residue =>
    matrixMeasurementTransport (ldDirectAnswerEquiv L)
      (S.A (seededLdQuestion L q residue))
  B q := blockDiagonalMeasurement fun residue =>
    matrixMeasurementTransport (ldDirectAnswerEquiv L)
      (S.B (seededLdQuestion L q residue))

/-- Projectivity is preserved by the correlated seed-fiber dilation. -/
theorem ldStrategyToDirect_isProjective (L : LdParams)
    (S : Strategy (ldGame L)) (hS : S.IsProjective) :
    (ldStrategyToDirect L S).IsProjective := by
  constructor
  · intro q
    apply blockDiagonalMeasurement_isProjective
    intro residue
    apply matrixMeasurementTransport_isProjective
    exact hS.1 (seededLdQuestion L q residue)
  · intro q
    apply blockDiagonalMeasurement_isProjective
    intro residue
    apply matrixMeasurementTransport_isProjective
    exact hS.2 (seededLdQuestion L q residue)

@[simp] theorem ldStrategyToDirect_A_effect (L : LdParams)
    (S : Strategy (ldGame L))
    (q : DirectLdQuestion L.toDirectLdParams)
    (answer : DirectLdAnswer L.toDirectLdParams) :
    ((ldStrategyToDirect L S).A q).effect answer =
      Matrix.blockDiagonal fun residue =>
        (S.A (seededLdQuestion L q residue)).effect
          ((ldDirectAnswerEquiv L).symm answer) :=
  rfl

@[simp] theorem ldStrategyToDirect_B_effect (L : LdParams)
    (S : Strategy (ldGame L))
    (q : DirectLdQuestion L.toDirectLdParams)
    (answer : DirectLdAnswer L.toDirectLdParams) :
    ((ldStrategyToDirect L S).B q).effect answer =
      Matrix.blockDiagonal fun residue =>
        (S.B (seededLdQuestion L q residue)).effect
          ((ldDirectAnswerEquiv L).symm answer) :=
  rfl

/-- A direct question reconstructed in a residue block parses back to its
canonical direct form. -/
theorem parse_seededLdQuestion (L : LdParams)
    (q : DirectLdQuestion L.toDirectLdParams)
    (residue : Fin (L.q / L.m)) :
    parseLdQuestion L (seededLdQuestion L q residue) =
      (q.1, directLdMap L.toDirectLdParams q.1 q.2) := by
  exact parseLdQuestion_ldCL_ofDirectResidue L q.1 q.2 residue

/-- Coordinate formula for the correlated residue lift. -/
theorem seedFiberLiftedState_apply
    {G : Game} (S : Strategy G) (L : LdParams)
    (i : S.ιA) (j : S.ιB)
    (r s : Fin (L.q / L.m)) :
    seedFiberLiftedState S L ((i, r), (j, s)) =
      if r = s then
        S.ψ (i, j) * (Real.sqrt (Fintype.card (Fin (L.q / L.m)) : ℝ) : ℂ)⁻¹
      else 0 := by
  letI : Nonempty (Fin (L.q / L.m)) :=
    Fin.pos_iff_nonempty.mp L.seedFiberCard_pos
  simp [seedFiberLiftedState, reindexState, vecTensor, seedResidueAncilla,
    eprState, prodShuffle]

end

end MIPStarRE.QPBT
