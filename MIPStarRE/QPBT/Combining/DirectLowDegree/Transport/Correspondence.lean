import MIPStarRE.LDT.Test.StrategyCore
import MIPStarRE.QPBT.Combining.DirectLowDegree.Game

/-!
# Question correspondence for the directly indexed low-degree game

The finite-field coordinates, polynomial answers, and question law of the
directly indexed game are equivalent to their seed-indexed and low individual
degree counterparts.

## References

- `references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:31-458`
- `references/ldt-paper/test_definition.tex:98-151`
- `docs/paper-gaps/qpbt_ld-dimension-divisibility.tex`
-/

open scoped BigOperators MatrixOrder Matrix ComplexOrder

namespace MIPStarRE.QPBT

open MIPStarRE.LDT
open MIPStarRE.Quantum

noncomputable section

/-! ## Parameters and finite-field coordinates -/

/-- Regard direct-game parameters as parameters of the mature LDT interface.
The field size, dimension, and degree are unchanged. -/
@[reducible] def DirectLdParams.toLDTParameters (D : DirectLdParams) : Parameters where
  m := D.m
  q := D.q
  d := D.d
  hm := lt_of_lt_of_le Nat.zero_lt_one D.hm
  hq := by
    obtain ⟨n, hn, hq⟩ := D.hq
    rw [hq]
    exact Nat.pow_pos (by decide)
  hqPrimePower := by
    obtain ⟨n, hn, hq⟩ := D.hq
    exact ⟨2, n, Nat.prime_two, hn.pos, hq⟩

/-- The fixed QPBT field model, viewed as the model used by the mature LDT
interface. -/
@[reducible] noncomputable def DirectLdParams.toLDTFieldModel (D : DirectLdParams) :
    FieldModel D.toLDTParameters.q :=
  D.model.toFieldModel

/-- Coordinate coding from the direct scalar field to the mature LDT carrier. -/
noncomputable def directScalarEquiv (D : DirectLdParams) :
    DirectScalarQ D ≃ Fq D.toLDTParameters :=
  binaryRepresentation D.model

/-- Coordinate coding identifies direct points with mature LDT points, with
the coordinate order reversed: direct coordinate `j` is mature coordinate
`Fin.rev j`.  The direct game zeroes a *prefix* of a sampled diagonal
direction (`directPrefixProjection`, paper equation `eq:cl-dlnf`), whereas
the mature test zeroes a *suffix* (`extendRestrictedDirection`,
`references/ldt-paper/test_definition.tex:49-65`).  Reversing the coordinate
order aligns the two restriction conventions, as required by the game
correspondence in `docs/paper-gaps/qpbt_ld-dimension-divisibility.tex`. -/
noncomputable def directPointEquiv (D : DirectLdParams) :
    (Fin D.m → DirectScalarQ D) ≃ Point D.toLDTParameters where
  toFun u i := directScalarEquiv D (u (Fin.rev i))
  invFun u j := (directScalarEquiv D).symm (u (Fin.rev j))
  left_inv u := by
    funext j
    simp
  right_inv u := by
    funext i
    simp

@[simp] theorem directPointEquiv_apply (D : DirectLdParams)
    (u : Fin D.m → DirectScalarQ D) (i : Fin D.m) :
    directPointEquiv D u i = directScalarEquiv D (u (Fin.rev i)) :=
  rfl

@[simp] theorem directPointEquiv_symm_apply (D : DirectLdParams)
    (u : Point D.toLDTParameters) (j : Fin D.m) :
    (directPointEquiv D).symm u j =
      (directScalarEquiv D).symm (u (Fin.rev j)) :=
  rfl

/-! ## Bounded coefficient vectors -/

/-- Turn a coefficient vector into its polynomial of degree at most `n`. -/
private noncomputable def coefficientPolynomial
    {K : Type*} [Field K] (n : ℕ) (c : Fin (n + 1) → K) : Polynomial K :=
  ((Polynomial.degreeLTEquiv K (n + 1)).symm c).1

private theorem coefficientPolynomial_degree_le
    {K : Type*} [Field K] (n : ℕ) (c : Fin (n + 1) → K) :
    (coefficientPolynomial n c).natDegree ≤ n := by
  let p := (Polynomial.degreeLTEquiv K (n + 1)).symm c
  have hp : p.1 ∈ Polynomial.degreeLE K n := by
    rw [← Polynomial.degreeLT_succ_eq_degreeLE]
    exact p.2
  have hdegree : p.1.degree ≤ n := Polynomial.mem_degreeLE.mp hp
  by_cases hzero : p.1 = 0
  · simp [coefficientPolynomial, p, hzero]
  · exact Polynomial.natDegree_le_iff_degree_le.mpr hdegree

@[simp] private theorem coefficientPolynomial_coeff
    {K : Type*} [Field K] (n : ℕ) (c : Fin (n + 1) → K)
    (i : Fin (n + 1)) :
    (coefficientPolynomial n c).coeff i = c i := by
  exact congrFun ((Polynomial.degreeLTEquiv K (n + 1)).apply_symm_apply c) i

private theorem coefficientPolynomial_eval
    {K : Type*} [Field K] (n : ℕ) (c : Fin (n + 1) → K) (t : K) :
    (coefficientPolynomial n c).eval t = evalCoefficient c t := by
  simpa [coefficientPolynomial, evalCoefficient] using
    (Polynomial.eval_eq_sum_degreeLTEquiv
      (((Polynomial.degreeLTEquiv K (n + 1)).symm c).2) t)

/-- Direct axis-line coefficients are equivalent to mature bounded axis-line
polynomials over the fixed field model. -/
noncomputable def directAxisAnswerEquiv (D : DirectLdParams) :
    letI := D.toLDTFieldModel
    DirectDegPoly D D.d ≃ AxisLinePolynomial D.toLDTParameters := by
  letI := D.toLDTFieldModel
  refine
    { toFun := fun c =>
        { poly := coefficientPolynomial D.d c
          degreeBounded := coefficientPolynomial_degree_le D.d c }
      invFun := fun f i => f.poly.coeff i
      left_inv := ?_
      right_inv := ?_ }
  · intro c
    funext i
    exact coefficientPolynomial_coeff D.d c i
  · intro f
    apply AxisLinePolynomial.ext
    apply linePolynomial_coeff_fin_injective D.toLDTParameters
      (coefficientPolynomial_degree_le D.d fun i => f.poly.coeff i)
      f.degreeBounded
    intro i
    exact coefficientPolynomial_coeff D.d (fun j => f.poly.coeff j) i

/-- Direct diagonal-line coefficients are equivalent to mature bounded
diagonal-line polynomials over the fixed field model. -/
noncomputable def directDiagonalAnswerEquiv (D : DirectLdParams) :
    letI := D.toLDTFieldModel
    DirectDegPoly D (D.m * D.d) ≃ DiagonalLinePolynomial D.toLDTParameters := by
  letI := D.toLDTFieldModel
  refine
    { toFun := fun c =>
        { poly := coefficientPolynomial (D.m * D.d) c
          degreeBounded := coefficientPolynomial_degree_le (D.m * D.d) c }
      invFun := fun f i => f.poly.coeff i
      left_inv := ?_
      right_inv := ?_ }
  · intro c
    funext i
    exact coefficientPolynomial_coeff (D.m * D.d) c i
  · intro f
    apply DiagonalLinePolynomial.ext
    apply linePolynomial_coeff_fin_injective D.toLDTParameters
      (coefficientPolynomial_degree_le (D.m * D.d) fun i => f.poly.coeff i)
      f.degreeBounded
    intro i
    exact coefficientPolynomial_coeff (D.m * D.d) (fun j => f.poly.coeff j) i

/-- Coefficient evaluation agrees with evaluation of the corresponding mature
axis-line polynomial. -/
theorem directAxisAnswerEquiv_apply (D : DirectLdParams)
    (c : DirectDegPoly D D.d) (t : DirectScalarQ D) :
    letI := D.toLDTFieldModel
    directAxisAnswerEquiv D c (directScalarEquiv D t) =
      directScalarEquiv D (evalCoefficient c t) := by
  letI := D.toLDTFieldModel
  simp only [directAxisAnswerEquiv, AxisLinePolynomial.toFun,
    evalLinePolynomialModel]
  rw [show decodeScalar (directScalarEquiv D t) = t by
    exact (FieldModel.equiv (q := D.q)).symm_apply_apply t]
  change encodeScalar ((coefficientPolynomial D.d c).eval t) =
    directScalarEquiv D (evalCoefficient c t)
  exact congrArg (FieldModel.equiv (q := D.q))
    (coefficientPolynomial_eval D.d c t)

/-- Coefficient evaluation agrees with evaluation of the corresponding mature
diagonal-line polynomial. -/
theorem directDiagonalAnswerEquiv_apply (D : DirectLdParams)
    (c : DirectDegPoly D (D.m * D.d)) (t : DirectScalarQ D) :
    letI := D.toLDTFieldModel
    directDiagonalAnswerEquiv D c (directScalarEquiv D t) =
      directScalarEquiv D (evalCoefficient c t) := by
  letI := D.toLDTFieldModel
  simp only [directDiagonalAnswerEquiv, DiagonalLinePolynomial.toFun,
    evalLinePolynomialModel]
  rw [show decodeScalar (directScalarEquiv D t) = t by
    exact (FieldModel.equiv (q := D.q)).symm_apply_apply t]
  change encodeScalar ((coefficientPolynomial (D.m * D.d) c).eval t) =
    directScalarEquiv D (evalCoefficient c t)
  exact congrArg (FieldModel.equiv (q := D.q))
    (coefficientPolynomial_eval (D.m * D.d) c t)

/-! ## Parameters and answers of the two QPBT game presentations -/

/-- Forget the divisibility field and expose the directly indexed parameters. -/
def LdParams.toDirectLdParams (L : LdParams) : DirectLdParams where
  q := L.q
  m := L.m
  d := L.d
  k := L.k
  hm := L.hm
  hd := L.hd
  hk := L.hk
  hq := L.hq

@[simp] theorem LdParams.toDirectLdParams_model (L : LdParams) :
    L.toDirectLdParams.model = L.model := by
  unfold DirectLdParams.model LdParams.model LdParams.toDirectLdParams
  congr

/-- Constructor-preserving equivalence between answers of the seed-indexed
and directly indexed QPBT games. -/
noncomputable def ldDirectAnswerEquiv (L : LdParams) :
    LdAnswer L ≃ DirectLdAnswer L.toDirectLdParams where
  toFun
    | .pointVals a => .pointVals a
    | .alinePolys a => .alinePolys a
    | .dlinePolys a => .dlinePolys a
  invFun
    | .pointVals a => .pointVals a
    | .alinePolys a => .alinePolys a
    | .dlinePolys a => .dlinePolys a
  left_inv a := by cases a <;> rfl
  right_inv a := by cases a <;> rfl

/-! ## Parsing seed-indexed questions -/

/-- Parse a seed-indexed question into the directly indexed question carrying
the coordinate selected by `chiIndex`. -/
noncomputable def parseLdQuestion (L : LdParams) :
    LdQuestion L → DirectLdQuestion L.toDirectLdParams
  | (.point, z) =>
      (.point, ⟨z.point, L.toDirectLdParams.firstIndex, 0⟩)
  | (.aline, z) =>
      (.aline, ⟨z.point, chiIndex L z.seed, 0⟩)
  | (.dline, z) =>
      (.dline, ⟨z.point, chiIndex L z.seed, z.direction⟩)

/-- Embed a direct sample into the seed-indexed ambient space using the
specified residue in the selected seed fiber. -/
noncomputable def ldSpaceOfDirectResidue (L : LdParams)
    (sample : DirectLdSpace L.toDirectLdParams)
    (residue : Fin (L.q / L.m)) : LdSpace L
  | .inl (.inl i) => sample.point i
  | .inl (.inr _) => seedOfIndexResidue L sample.index residue
  | .inr i => sample.direction i

@[simp] theorem ldSpaceOfDirectResidue_point (L : LdParams)
    (sample : DirectLdSpace L.toDirectLdParams)
    (residue : Fin (L.q / L.m)) :
    (ldSpaceOfDirectResidue L sample residue).point = sample.point :=
  rfl

@[simp] theorem ldSpaceOfDirectResidue_seed (L : LdParams)
    (sample : DirectLdSpace L.toDirectLdParams)
    (residue : Fin (L.q / L.m)) :
    (ldSpaceOfDirectResidue L sample residue).seed =
      seedOfIndexResidue L sample.index residue :=
  rfl

@[simp] theorem ldSpaceOfDirectResidue_direction (L : LdParams)
    (sample : DirectLdSpace L.toDirectLdParams)
    (residue : Fin (L.q / L.m)) :
    (ldSpaceOfDirectResidue L sample residue).direction = sample.direction :=
  rfl

/-- The ambient seed-indexed sample space is a direct sample together with a
uniform residue in the selected seed fiber. -/
noncomputable def ldSpaceSeedFiberEquiv (L : LdParams) :
    LdSpace L ≃ DirectLdSpace L.toDirectLdParams × Fin (L.q / L.m) where
  toFun z :=
    (⟨z.point, (seedFiberEquiv L z.seed).1, z.direction⟩,
      (seedFiberEquiv L z.seed).2)
  invFun x := ldSpaceOfDirectResidue L x.1 x.2
  left_inv z := by
    funext i
    rcases i with (i | i)
    · rcases i with (i | i)
      · rfl
      · rcases i with ⟨⟩
        change (seedFiberEquiv L).symm (seedFiberEquiv L z.seed) = z.seed
        exact (seedFiberEquiv L).symm_apply_apply z.seed
    · rfl
  right_inv x := by
    rcases x with ⟨sample, residue⟩
    apply Prod.ext
    · cases sample with
      | mk point index direction =>
          simp only [ldSpaceOfDirectResidue_point,
            ldSpaceOfDirectResidue_seed, ldSpaceOfDirectResidue_direction]
          rw [seedFiberEquiv_seedOfIndexResidue]
    · simp [seedOfIndexResidue]

/-- Parsing a canonical seed-indexed question reconstructed from a direct
sample gives exactly the corresponding direct canonical question. -/
theorem parseLdQuestion_ldCL_ofDirectResidue (L : LdParams)
    (t : LdType) (sample : DirectLdSpace L.toDirectLdParams)
    (residue : Fin (L.q / L.m)) :
    parseLdQuestion L
        (t, ldCL L t (ldSpaceOfDirectResidue L sample residue)) =
      (t, directLdMap L.toDirectLdParams t sample) := by
  cases t with
  | point =>
    rfl
  | aline =>
      ext <;>
        simp only [parseLdQuestion, ldCL, ldALineCL, directLdMap,
          ldSpaceOfDirectResidue, ldSpaceOfDirectResidue_point, LdSpace.seed,
          chiIndex_seedOfIndexResidue]
      congr 1
  | dline =>
      ext <;>
        simp only [parseLdQuestion, ldCL, ldDLineCL, directLdMap,
          ldSpaceOfDirectResidue, ldSpaceOfDirectResidue_point,
          ldSpaceOfDirectResidue_direction, LdSpace.seed,
          LdSpace.direction, chiIndex_seedOfIndexResidue,
          prefixProjection]
      rfl

/-- The seed-indexed and direct predicates agree after parsing questions and
transporting answers. -/
theorem ldWinPredicate_parse (L : LdParams)
    (x y : LdQuestion L) (a b : LdAnswer L) :
    directLdWinPredicate L.toDirectLdParams
        (parseLdQuestion L x) (parseLdQuestion L y)
        (ldDirectAnswerEquiv L a) (ldDirectAnswerEquiv L b) =
      ldWinPredicate L x y a b := by
  rcases x with ⟨tx, x⟩
  rcases y with ⟨ty, y⟩
  cases tx <;> cases ty <;> cases a <;> cases b <;> rfl

/-! ## Exact question-law transport -/

/-- The common source sample is a direct common sample together with its
uniform seed-fiber residue. -/
noncomputable def ldQuestionSeedFiberEquiv (L : LdParams) :
    ((LdType × LdType) × LdSpace L) ≃
      (((LdType × LdType) × DirectLdSpace L.toDirectLdParams) ×
        Fin (L.q / L.m)) :=
  (Equiv.prodCongr (Equiv.refl (LdType × LdType))
    (ldSpaceSeedFiberEquiv L)).trans
      (Equiv.prodAssoc (LdType × LdType)
        (DirectLdSpace L.toDirectLdParams) (Fin (L.q / L.m))).symm

/-- Forget the seed residue while retaining the ordered question types and
the directly indexed common sample. -/
noncomputable def ldQuestionSampleProjection (L : LdParams) :
    ((LdType × LdType) × LdSpace L) →
      (LdType × LdType) × DirectLdSpace L.toDirectLdParams :=
  fun source => (source.1, (ldSpaceSeedFiberEquiv L source.2).1)

/-- Parse both questions in a seed-indexed question pair. -/
noncomputable def parseLdQuestionPair (L : LdParams) :
    (LdQuestion L × LdQuestion L) →
      (DirectLdQuestion L.toDirectLdParams ×
        DirectLdQuestion L.toDirectLdParams) :=
  fun questions =>
    (parseLdQuestion L questions.1, parseLdQuestion L questions.2)

private theorem parse_ldQuestionSample (L : LdParams)
    (source : (LdType × LdType) × LdSpace L) :
    parseLdQuestionPair L
        ((source.1.1, ldCL L source.1.1 source.2),
          (source.1.2, ldCL L source.1.2 source.2)) =
      let direct := ldQuestionSampleProjection L source
      ((direct.1.1, directLdMap L.toDirectLdParams direct.1.1 direct.2),
        (direct.1.2, directLdMap L.toDirectLdParams direct.1.2 direct.2)) := by
  let sample := (ldSpaceSeedFiberEquiv L source.2).1
  let residue := (ldSpaceSeedFiberEquiv L source.2).2
  have hsource :
      source.2 = ldSpaceOfDirectResidue L sample residue := by
    exact (ldSpaceSeedFiberEquiv L).symm_apply_apply source.2 |>.symm
  rw [hsource]
  apply Prod.ext
  · exact parseLdQuestion_ldCL_ofDirectResidue L source.1.1 sample residue
  · exact parseLdQuestion_ldCL_ofDirectResidue L source.1.2 sample residue

/-- Pushing the seed-indexed question law through the exact parser gives the
directly indexed question law, including the ordered type-pair weights. -/
theorem ldQuestionDistribution_map_parse (L : LdParams) :
    (ldQuestionDistribution L).map (parseLdQuestionPair L) =
      directLdQuestionDistribution L.toDirectLdParams := by
  letI : Nonempty (Fin (L.q / L.m)) :=
    Fin.pos_iff_nonempty.mp L.seedFiberCard_pos
  let sourceMap : ((LdType × LdType) × LdSpace L) →
      LdQuestion L × LdQuestion L := fun source =>
    ((source.1.1, ldCL L source.1.1 source.2),
      (source.1.2, ldCL L source.1.2 source.2))
  let directMap :
      ((LdType × LdType) × DirectLdSpace L.toDirectLdParams) →
        DirectLdQuestion L.toDirectLdParams ×
          DirectLdQuestion L.toDirectLdParams := fun source =>
    ((source.1.1, directLdMap L.toDirectLdParams source.1.1 source.2),
      (source.1.2, directLdMap L.toDirectLdParams source.1.2 source.2))
  have huniform :
      (uniformDistribution ((LdType × LdType) × LdSpace L)).map
          (ldQuestionSampleProjection L) =
        uniformDistribution
          ((LdType × LdType) × DirectLdSpace L.toDirectLdParams) := by
    apply uniformDistribution_map_fst_of_equiv (ldQuestionSeedFiberEquiv L)
    intro source
    rfl
  calc
    (ldQuestionDistribution L).map (parseLdQuestionPair L) =
        (uniformDistribution ((LdType × LdType) × LdSpace L)).map
          (parseLdQuestionPair L ∘ sourceMap) := by
      exact distribution_map_map_of_isProbability
        (uniformDistribution ((LdType × LdType) × LdSpace L))
        (uniformDistribution_isProbability _)
        sourceMap (parseLdQuestionPair L)
    _ = (uniformDistribution ((LdType × LdType) × LdSpace L)).map
        (directMap ∘ ldQuestionSampleProjection L) := by
      congr 1
      funext source
      exact parse_ldQuestionSample L source
    _ = ((uniformDistribution ((LdType × LdType) × LdSpace L)).map
          (ldQuestionSampleProjection L)).map directMap :=
      (distribution_map_map_of_isProbability
        (uniformDistribution ((LdType × LdType) × LdSpace L))
        (uniformDistribution_isProbability _)
        (ldQuestionSampleProjection L) directMap).symm
    _ = directLdQuestionDistribution L.toDirectLdParams := by
      rw [huniform]
      rfl

end

end MIPStarRE.QPBT
