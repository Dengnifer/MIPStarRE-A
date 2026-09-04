import MIPStarRE.QPBT.Combining.DirectLowDegree.Transport.Strategy

/-!
# Low-degree consistency transport

This module identifies the low individual degree polynomial outcomes with the
bounded polynomial representatives used by the directly indexed QPBT game.  It
also transports complete measurements and their evaluation postprocessings
without changing either coordinate order or consistency error.

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

/-! ## Polynomial outcomes -/

private theorem directPolynomialRename_degreeOf_le
    (D : DirectLdParams) (p : MvPolynomial (Fin D.m) (DirectScalarQ D))
    (hp : ∀ i, MvPolynomial.degreeOf i p ≤ D.d) (i : Fin D.m) :
    MvPolynomial.degreeOf i (MvPolynomial.rename Fin.rev p) ≤ D.d := by
  rw [← Fin.rev_rev i,
    MvPolynomial.degreeOf_rename_of_injective Fin.rev_injective]
  exact hp (Fin.rev i)

private theorem ldtPolynomial_ext
    {params : Parameters} [FieldModel params.q]
    {g h : MIPStarRE.LDT.Polynomial params} (hpoly : g.poly = h.poly) : g = h := by
  cases g with
  | mk gp hg =>
      cases h with
      | mk hp hh =>
          simp only at hpoly
          subst hp
          rfl

/-- Bounded QPBT polynomial representatives are equivalent to LDT
polynomial outcomes.  The variable renaming is the same coordinate reversal
as `directPointEquiv`, so evaluation retains the direct coordinate order. -/
noncomputable def directPolyEquivPolynomial (D : DirectLdParams) :
    letI := D.toLDTFieldModel
    PolyIndex D.m (DirectScalarQ D) D.d ≃
      MIPStarRE.LDT.Polynomial D.toLDTParameters := by
  letI := D.toLDTFieldModel
  refine
    { toFun := fun g =>
        { poly := MvPolynomial.rename Fin.rev g.1
          lowIndividualDegree := directPolynomialRename_degreeOf_le D g.1
            (degreeOf_le_of_mem_polyFunc g.2) }
      invFun := fun g =>
        ⟨MvPolynomial.rename Fin.rev g.poly, ?_⟩
      left_inv := ?_
      right_inv := ?_ }
  · rw [MvPolynomial.mem_restrictDegree]
    intro s hs i
    exact (MvPolynomial.degreeOf_le_iff.mp
      (directPolynomialRename_degreeOf_le D g.poly g.lowIndividualDegree i)) s hs
  · intro g
    apply Subtype.ext
    change MvPolynomial.rename Fin.rev
      (MvPolynomial.rename Fin.rev g.1) = g.1
    rw [MvPolynomial.rename_rename]
    rw [show Fin.rev ∘ Fin.rev = id by funext i; simp]
    exact MvPolynomial.rename_id_apply g.1
  · intro g
    cases g with
    | mk p hp =>
        have hpoly : MvPolynomial.rename Fin.rev
            (MvPolynomial.rename Fin.rev p) = p := by
          rw [MvPolynomial.rename_rename]
          rw [show Fin.rev ∘ Fin.rev = id by funext i; simp]
          exact MvPolynomial.rename_id_apply p
        apply ldtPolynomial_ext
        exact hpoly

@[simp] theorem directPolyEquivPolynomial_poly
    (D : DirectLdParams) (g : PolyIndex D.m (DirectScalarQ D) D.d) :
    letI := D.toLDTFieldModel
    (directPolyEquivPolynomial D g).poly = MvPolynomial.rename Fin.rev g.1 := by
  letI := D.toLDTFieldModel
  rfl

/-- The polynomial equivalence commutes with evaluation after the direct point
and scalar codings. -/
@[simp] theorem directPolyEquivPolynomial_apply
    (D : DirectLdParams) (g : PolyIndex D.m (DirectScalarQ D) D.d)
    (u : Fin D.m → DirectScalarQ D) :
    letI := D.toLDTFieldModel
    directPolyEquivPolynomial D g (directPointEquiv D u) =
      directScalarEquiv D (MvPolynomial.eval u g.1) := by
  letI := D.toLDTFieldModel
  unfold MIPStarRE.LDT.Polynomial.toFun evalPolynomialModel
  rw [directPolyEquivPolynomial_poly]
  unfold decodePoint
  rw [MvPolynomial.eval_rename]
  congr 1
  apply congrArg (fun v : Fin D.m → DirectScalarQ D =>
    MvPolynomial.eval v g.1)
  funext i
  simp only [Function.comp_apply, directPointEquiv_apply, Fin.rev_rev]
  change (directScalarEquiv D).symm (directScalarEquiv D (u i)) = u i
  exact (directScalarEquiv D).symm_apply_apply (u i)

/-! ## Complete measurements -/

/-- Regard a complete LDT measurement as a matrix-valued QPBT
measurement, with exactly the same effects. -/
noncomputable def ldtMeasurementToMatrixMeasurement
    {alpha iota : Type*} [Fintype alpha] [Fintype iota] [DecidableEq iota]
    (M : MIPStarRE.LDT.Measurement alpha iota) :
    MIPStarRE.Quantum.Measurement alpha iota :=
  MIPStarRE.Quantum.Measurement.ofSumEqOne M.outcome M.outcome_pos (by
    rw [M.sum_eq_total, M.total_eq_one])

@[simp] theorem ldtMeasurementToMatrixMeasurement_effect
    {alpha iota : Type*} [Fintype alpha] [Fintype iota] [DecidableEq iota]
    (M : MIPStarRE.LDT.Measurement alpha iota) (a : alpha) :
    (ldtMeasurementToMatrixMeasurement M).effect a = M.outcome a :=
  rfl

/-- Relabel an LDT polynomial projective measurement by direct QPBT
polynomial representatives. -/
noncomputable def directPolynomialMeasurement
    (D : DirectLdParams) :
    letI := D.toLDTFieldModel
    {iota : Type*} → [Fintype iota] → [DecidableEq iota] →
      ProjMeas (MIPStarRE.LDT.Polynomial D.toLDTParameters) iota →
        PolyMeas D.m (DirectScalarQ D) D.d iota := by
  letI := D.toLDTFieldModel
  intro iota _ _ G
  exact matrixMeasurementTransport (directPolyEquivPolynomial D).symm
    (ldtMeasurementToMatrixMeasurement G.toMeasurement)

@[simp] theorem directPolynomialMeasurement_effect
    (D : DirectLdParams) :
    letI := D.toLDTFieldModel
    ∀ {iota : Type*} [Fintype iota] [DecidableEq iota]
      (G : ProjMeas (MIPStarRE.LDT.Polynomial D.toLDTParameters) iota)
      (g : PolyIndex D.m (DirectScalarQ D) D.d),
      (directPolynomialMeasurement D G).effect g =
        G.outcome (directPolyEquivPolynomial D g) := by
  letI := D.toLDTFieldModel
  intro iota _ _ G g
  rfl

/-- Extract one polynomial coordinate from a direct polynomial-tuple POVM. -/
noncomputable def directPolyMeasTupleMarginal
    (D : DirectLdParams) {iota : Type*} [Fintype iota] [DecidableEq iota]
    (G : DirectPolyMeasTuple D iota) (r : Fin D.k) :
    PolyMeas D.m (DirectScalarQ D) D.d iota :=
  G.postprocess (fun tuple => tuple r)

/-- Extract one polynomial coordinate from a seed-indexed polynomial-tuple
POVM. -/
noncomputable def polyMeasTupleMarginal
    (L : LdParams) {iota : Type*} [Fintype iota] [DecidableEq iota]
    (G : PolyMeasTuple L iota) (r : Fin L.k) :
    PolyMeas L.m (ScalarQ L) L.d iota :=
  G.postprocess (fun tuple => tuple r)

/-- Evaluating a direct polynomial tuple and then selecting coordinate `r`
agrees with evaluating the `r`-th polynomial marginal. -/
theorem directPolyMeasTuple_evaluation_marginal
    (D : DirectLdParams) {iota : Type*} [Fintype iota] [DecidableEq iota]
    (G : DirectPolyMeasTuple D iota) (r : Fin D.k)
    (u : Fin D.m → DirectScalarQ D) :
    (G.postprocess (evalDirectPolyTupleAt u)).postprocess (fun values => values r) =
      (directPolyMeasTupleMarginal D G r).postprocess
        (fun g => MvPolynomial.eval u g.1) := by
  unfold directPolyMeasTupleMarginal
  rw [MIPStarRE.Quantum.Measurement.postprocess_comp,
    MIPStarRE.Quantum.Measurement.postprocess_comp]
  rfl

/-- Evaluating a seed-indexed polynomial tuple and then selecting coordinate
`r` agrees with evaluating the `r`-th polynomial marginal. -/
theorem polyMeasTuple_evaluation_marginal
    (L : LdParams) {iota : Type*} [Fintype iota] [DecidableEq iota]
    (G : PolyMeasTuple L iota) (r : Fin L.k)
    (u : Fin L.m → ScalarQ L) :
    (G.postprocess (evalPolyTupleAt u)).postprocess (fun values => values r) =
      (polyMeasTupleMarginal L G r).postprocess
        (fun g => MvPolynomial.eval u g.1) := by
  unfold polyMeasTupleMarginal
  rw [MIPStarRE.Quantum.Measurement.postprocess_comp,
    MIPStarRE.Quantum.Measurement.postprocess_comp]
  rfl

/-- Evaluating the transported polynomial measurement is the relabeling of
the LDT evaluation postprocessing through `directScalarEquiv`. -/
theorem directPolynomialMeasurement_evaluation_effect
    (D : DirectLdParams) :
    letI := D.toLDTFieldModel
    ∀ {iota : Type*} [Fintype iota] [DecidableEq iota]
      (G : ProjMeas (MIPStarRE.LDT.Polynomial D.toLDTParameters) iota)
      (u : Fin D.m → DirectScalarQ D) (a : DirectScalarQ D),
      ((directPolynomialMeasurement D G).postprocess
        (fun g => MvPolynomial.eval u g.1)).effect a =
        (ldtMeasurementToMatrixMeasurement
          (ProjMeas.postprocess G
            (fun g => g (directPointEquiv D u))).toMeasurement).effect
            (directScalarEquiv D a) := by
  letI := D.toLDTFieldModel
  intro iota _ _ G u a
  classical
  rw [MIPStarRE.Quantum.Measurement.postprocess_effect]
  rw [ldtMeasurementToMatrixMeasurement_effect,
    ProjMeas.postprocess, SubMeas.postprocess_outcome]
  apply Finset.sum_bij (fun g _ => directPolyEquivPolynomial D g)
  · intro g hg
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hg ⊢
    simpa only [directPolyEquivPolynomial_apply] using
      congrArg (directScalarEquiv D) hg
  · intro g₁ _ g₂ _ h
    exact (directPolyEquivPolynomial D).injective h
  · intro g hg
    refine ⟨(directPolyEquivPolynomial D).symm g, ?_, ?_⟩
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hg ⊢
      have heval := directPolyEquivPolynomial_apply D
        ((directPolyEquivPolynomial D).symm g) u
      rw [(directPolyEquivPolynomial D).apply_symm_apply] at heval
      exact (directScalarEquiv D).injective (heval.symm.trans hg)
    · exact (directPolyEquivPolynomial D).apply_symm_apply g
  · intro g _
    rw [directPolynomialMeasurement_effect]

/-! ## Correlated-ancilla compression -/

/-!
The diagonal-block conditional expectation preserves either mixed defect
exactly because the point measurement on the opposite carrier is constant on
the residue register.  It does not yield a global/global compression theorem:
the lifted state pairs equal residues, whereas separately compressing both
polynomial measurements produces an independent double average over residues.
Neither quantity bounds the other in general.  This open obstruction is
recorded in `docs/paper-gaps/qpbt_ld-dimension-divisibility.tex`.
-/

/-- The normalized diagonal-block average of an operator on a carrier with a
finite ancillary register.  This is the local conditional expectation used to
discard one half of the correlated seed-residue ancilla. -/
noncomputable def averageDiagonalBlock
    {iota block : Type*} [Fintype iota] [Fintype block]
    (A : Op (iota × block)) : Op iota := by
  classical
  exact (Fintype.card block : ℝ)⁻¹ •
    ∑ r, A.submatrix (fun i => (i, r)) (fun i => (i, r))

/-- Compress a POVM through the normalized diagonal-block average.  The
nonemptiness assumption says precisely that the normalized finite average is
defined over at least one ancillary basis element. -/
noncomputable def correlatedAncillaCompressMeasurement
    {alpha iota block : Type*}
    [Fintype alpha] [Fintype iota] [DecidableEq iota]
    [Fintype block] [DecidableEq block] [Nonempty block]
    (M : MIPStarRE.Quantum.Measurement alpha (iota × block)) :
    MIPStarRE.Quantum.Measurement alpha iota :=
  MIPStarRE.Quantum.Measurement.ofSumEqOne
    (fun a => averageDiagonalBlock (M.effect a))
    (fun a => by
      unfold averageDiagonalBlock
      apply smul_nonneg
      · positivity
      · exact Finset.sum_nonneg fun r _ =>
          Matrix.nonneg_iff_posSemidef.mpr
            ((Matrix.nonneg_iff_posSemidef.mp (M.pos a)).submatrix
              (fun i => (i, r))))
    (by
      classical
      ext i j
      simp only [averageDiagonalBlock, Matrix.sum_apply, Matrix.smul_apply,
        Matrix.submatrix_apply]
      calc
        ∑ a, (Fintype.card block : ℝ)⁻¹ •
              ∑ r, M.effect a (i, r) (j, r) =
            (Fintype.card block : ℝ)⁻¹ •
              ∑ a, ∑ r, M.effect a (i, r) (j, r) := by
                rw [Finset.smul_sum]
        _ = (Fintype.card block : ℝ)⁻¹ •
              ∑ r, ∑ a, M.effect a (i, r) (j, r) := by
                rw [Finset.sum_comm]
        _ = (Fintype.card block : ℝ)⁻¹ •
              ∑ r, (1 : Op (iota × block)) (i, r) (j, r) := by
                congr 1
                apply Finset.sum_congr rfl
                intro r _
                simpa only [Matrix.sum_apply] using
                  congrFun (congrFun M.sum_eq_one (i, r)) (j, r)
        _ = (1 : Op iota) i j := by
              simp [Matrix.one_apply, Fintype.card_ne_zero])

@[simp] theorem correlatedAncillaCompressMeasurement_effect
    {alpha iota block : Type*}
    [Fintype alpha] [Fintype iota] [DecidableEq iota]
    [Fintype block] [DecidableEq block] [Nonempty block]
    (M : MIPStarRE.Quantum.Measurement alpha (iota × block)) (a : alpha) :
    (correlatedAncillaCompressMeasurement M).effect a =
      averageDiagonalBlock (M.effect a) :=
  rfl

private theorem averageDiagonalBlock_finset_sum
    {alpha iota block : Type*} [Fintype iota] [Fintype block]
    (s : Finset alpha) (A : alpha → Op (iota × block)) :
    averageDiagonalBlock (∑ a ∈ s, A a) =
      ∑ a ∈ s, averageDiagonalBlock (A a) := by
  classical
  ext i j
  simp only [averageDiagonalBlock, Matrix.smul_apply, Matrix.sum_apply,
    Matrix.submatrix_apply]
  simp_rw [Finset.smul_sum]
  rw [Finset.sum_comm]

/-- Normalized diagonal-block compression commutes with deterministic outcome
postprocessing. -/
theorem correlatedAncillaCompressMeasurement_postprocess
    {alpha beta iota block : Type*}
    [Fintype alpha] [DecidableEq alpha]
    [Fintype beta] [DecidableEq beta]
    [Fintype iota] [DecidableEq iota]
    [Fintype block] [DecidableEq block] [Nonempty block]
    (M : MIPStarRE.Quantum.Measurement alpha (iota × block))
    (f : alpha → beta) :
    correlatedAncillaCompressMeasurement (M.postprocess f) =
      (correlatedAncillaCompressMeasurement M).postprocess f := by
  classical
  apply MIPStarRE.Quantum.Measurement.ext
  intro b
  rw [MIPStarRE.Quantum.Measurement.postprocess_effect,
    correlatedAncillaCompressMeasurement_effect,
    MIPStarRE.Quantum.Measurement.postprocess_effect]
  exact averageDiagonalBlock_finset_sum
    (Finset.univ.filter (fun a => f a = b)) M.effect

/-- Specialize ancillary compression to the nonempty residue fiber supplied by
the divisibility data of `LdParams`. -/
noncomputable def seedFiberCompressMeasurement
    (L : LdParams) {alpha iota : Type*}
    [Fintype alpha] [Fintype iota] [DecidableEq iota]
    (M : MIPStarRE.Quantum.Measurement alpha
      (iota × Fin (L.q / L.m))) :
    MIPStarRE.Quantum.Measurement alpha iota := by
  letI : Nonempty (Fin (L.q / L.m)) :=
    Fin.pos_iff_nonempty.mp L.seedFiberCard_pos
  exact correlatedAncillaCompressMeasurement M

@[simp] theorem seedFiberCompressMeasurement_effect
    (L : LdParams) {alpha iota : Type*}
    [Fintype alpha] [Fintype iota] [DecidableEq iota]
    (M : MIPStarRE.Quantum.Measurement alpha
      (iota × Fin (L.q / L.m))) (a : alpha) :
    (seedFiberCompressMeasurement L M).effect a =
      averageDiagonalBlock (M.effect a) :=
  rfl

/-- Seed-fiber compression commutes with deterministic outcome
postprocessing. -/
theorem seedFiberCompressMeasurement_postprocess
    (L : LdParams) {alpha beta iota : Type*}
    [Fintype alpha] [DecidableEq alpha]
    [Fintype beta] [DecidableEq beta]
    [Fintype iota] [DecidableEq iota]
    (M : MIPStarRE.Quantum.Measurement alpha
      (iota × Fin (L.q / L.m))) (f : alpha → beta) :
    seedFiberCompressMeasurement L (M.postprocess f) =
      (seedFiberCompressMeasurement L M).postprocess f := by
  letI : Nonempty (Fin (L.q / L.m)) :=
    Fin.pos_iff_nonempty.mp L.seedFiberCard_pos
  exact correlatedAncillaCompressMeasurement_postprocess M f

/-- Compress a direct polynomial-tuple POVM from the correlated seed-residue
carrier to the corresponding seed-indexed polynomial POVM. -/
noncomputable def seedFiberCompressPolyMeasTuple
    (L : LdParams) {iota : Type*} [Fintype iota] [DecidableEq iota]
    (G : DirectPolyMeasTuple L.toDirectLdParams
      (iota × Fin (L.q / L.m))) : PolyMeasTuple L iota := by
  exact seedFiberCompressMeasurement L G

@[simp] theorem seedFiberCompressPolyMeasTuple_effect
    (L : LdParams) {iota : Type*} [Fintype iota] [DecidableEq iota]
    (G : DirectPolyMeasTuple L.toDirectLdParams
      (iota × Fin (L.q / L.m))) (g : PolyTuple L) :
    (seedFiberCompressPolyMeasTuple L G).effect g =
      averageDiagonalBlock (G.effect g) :=
  rfl

/-- Polynomial evaluation commutes exactly with compression of the correlated
seed-residue carrier. -/
theorem seedFiberCompressPolyMeasTuple_evaluation
    (L : LdParams) {iota : Type*} [Fintype iota] [DecidableEq iota]
    (G : DirectPolyMeasTuple L.toDirectLdParams
      (iota × Fin (L.q / L.m))) (u : Fin L.m → ScalarQ L) :
    (seedFiberCompressPolyMeasTuple L G).postprocess (evalPolyTupleAt u) =
      seedFiberCompressMeasurement L
        (G.postprocess (evalDirectPolyTupleAt u)) := by
  exact (seedFiberCompressMeasurement_postprocess L G
    (evalDirectPolyTupleAt u)).symm

/-- Block-diagonal assembly commutes with deterministic outcome
postprocessing. -/
theorem blockDiagonalMeasurement_postprocess
    {alpha beta iota block : Type*}
    [Fintype alpha] [DecidableEq alpha]
    [Fintype beta] [DecidableEq beta]
    [Fintype iota] [DecidableEq iota]
    [Fintype block] [DecidableEq block]
    (M : block → MIPStarRE.Quantum.Measurement alpha iota)
    (f : alpha → beta) :
    (blockDiagonalMeasurement M).postprocess f =
      blockDiagonalMeasurement (fun r => (M r).postprocess f) := by
  classical
  apply MIPStarRE.Quantum.Measurement.ext
  intro b
  ext ⟨i, r⟩ ⟨j, s⟩
  simp only [MIPStarRE.Quantum.Measurement.postprocess_effect,
    blockDiagonalMeasurement_effect, Matrix.sum_apply,
    Matrix.blockDiagonal_apply]
  by_cases hrs : r = s
  · subst s
    simp only [if_pos]
  · simp [hrs]

private theorem matrixMeasurementTransport_eq_postprocess
    {alpha beta iota : Type*}
    [Fintype alpha] [DecidableEq alpha]
    [Fintype beta] [DecidableEq beta]
    [Fintype iota] [DecidableEq iota]
    (e : alpha ≃ beta) (M : MIPStarRE.Quantum.Measurement alpha iota) :
    matrixMeasurementTransport e M = M.postprocess e := by
  classical
  apply MIPStarRE.Quantum.Measurement.ext
  intro b
  rw [MIPStarRE.Quantum.Measurement.postprocess_effect]
  rw [Finset.sum_eq_single (e.symm b)]
  · simp
  · intro a haMem ha
    have hea : e a = b := (Finset.mem_filter.mp haMem).2
    exact (ha (e.injective (hea.trans (e.apply_symm_apply b).symm))).elim
  · simp

/-- Relabeling along an outcome equivalence commutes with subsequent
postprocessing. -/
theorem matrixMeasurementTransport_postprocess
    {alpha beta gamma iota : Type*}
    [Fintype alpha] [DecidableEq alpha]
    [Fintype beta] [DecidableEq beta]
    [Fintype gamma] [DecidableEq gamma]
    [Fintype iota] [DecidableEq iota]
    (e : alpha ≃ beta) (M : MIPStarRE.Quantum.Measurement alpha iota)
    (f : beta → gamma) :
    (matrixMeasurementTransport e M).postprocess f =
      M.postprocess (fun a => f (e a)) := by
  rw [matrixMeasurementTransport_eq_postprocess,
    MIPStarRE.Quantum.Measurement.postprocess_comp]

end

end MIPStarRE.QPBT
