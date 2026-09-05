import MIPStarRE.QPBT.Algebra.LowDegreeCode
import MIPStarRE.QPBT.Algebra.Pauli
import MIPStarRE.QPBT.Games.TypedCondLinear
import MIPStarRE.QPBT.Test.LowDegreeGame
import MIPStarRE.QPBT.Test.MagicSquare

/-!
# The Pauli basis test

This file supplies the finite question and answer alphabets, the typed
conditionally-linear question sampler, and the Boolean win predicate for the
Pauli basis test.  The quantitative soundness theorem is isolated in
`Soundness.lean`.

## References

The source-facing nodes are `def:admissible`, `def:pauli-question-distribution`,
and `def:pauli-win-predicate` in
`blueprint/src/chapter/ch13_qpbt_test.tex`; their paper origin is
`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:908-1225`.
-/

open scoped BigOperators

namespace MIPStarRE.QPBT

open MIPStarRE.LDT

noncomputable section

/-- The numerical admissible Pauli-test parameter tuple.  Its scalar carrier
uses the once-and-for-all model `fixedFieldModel q hq`, so the paper's fixed
self-dual-normal identification is not quantified in the test statement.  This
is `def:admissible` in
`blueprint/src/chapter/ch13_qpbt_test.tex`, paper origin
`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:958-961`.
-/
structure AdmissibleParams where
  q : ℕ
  m : ℕ
  d : ℕ
  hd : 1 ≤ d
  hq : IsAdmissibleSize q
  hdvd : m ∣ q

/-- Every admissible parameter tuple has positive ambient dimension. This
follows from positivity of the admissible field size and the divisibility
`P.m ∣ P.q` in `def:admissible`, blueprint
`blueprint/src/chapter/ch13_qpbt_test.tex`, paper origin
`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:958-961`.
-/
theorem AdmissibleParams.one_le_m (P : AdmissibleParams) : 1 ≤ P.m := by
  have hqpos : 0 < P.q := by
    rcases P.hq with ⟨k, _, hq⟩
    rw [hq]
    exact Nat.pow_pos (by decide)
  exact Nat.one_le_iff_ne_zero.mpr
    (ne_zero_of_dvd_ne_zero (Nat.ne_of_gt hqpos) P.hdvd)

/-- The fixed scalar model of an admissible parameter tuple.  It is a
compatibility view of the global `fixedFieldModel` selector, not an independently
quantified field representation.  This is the field representation of
`def:admissible`, blueprint `ch13_qpbt_test.tex`; paper
origin `references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:958-961`.
-/
noncomputable def AdmissibleParams.model (P : AdmissibleParams) : FixedFieldModel P.q :=
  fixedFieldModel P.q P.hq

/-- The low-degree parameter tuple determined by an admissible Pauli-test
tuple.  It is not an additional hypothesis of `thm:pauli`.  The low-degree
parameters are those of `def:ld-game`, blueprint
`blueprint/src/chapter/ch13_qpbt_test.tex`, paper origin
`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:958-961`.
-/
def AdmissibleParams.toLdParams (P : AdmissibleParams) : LdParams where
  q := P.q
  m := P.m
  d := P.d
  k := 1
  hm := P.one_le_m
  hd := P.hd
  hk := by decide
  hq := P.hq
  hdvd := P.hdvd

/-- The scalar carrier associated with an admissible parameter tuple.  It is
the globally fixed field carrier selected by `AdmissibleParams.model` in
`def:admissible`, blueprint
`blueprint/src/chapter/ch13_qpbt_test.tex`, paper origin
`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:958-961`.
-/
abbrev PauliScalar (P : AdmissibleParams) := P.model.K

/-- The six families of Pauli-test questions.  This is part of
`def:pauli-question-distribution`, blueprint `ch13_qpbt_test.tex`,
paper origin `references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:964-1120`.
-/
inductive PauliType where
  | point (W : PauliKind)
  | aline (W : PauliKind)
  | dline (W : PauliKind)
  | pauli (W : PauliKind)
  | pairW (W : PauliKind)
  | pair
  | ms (t : MsType)
  deriving DecidableEq, Repr, Inhabited, Fintype

/-- The register blocks used by the Pauli question space.  These are the
coordinates displayed in `def:pauli-question-distribution`, blueprint
`ch13_qpbt_test.tex`, paper origin
`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:964-1120`.
-/
abbrev PauliIndex (P : AdmissibleParams) :=
  (((((Fin P.m ⊕ Fin P.m) ⊕ Unit) ⊕ Fin P.m) ⊕ Unit) ⊕ Unit)

/-- The ambient Pauli question coefficient space (`def:pauli-question-distribution`,
blueprint `ch13_qpbt_test.tex`; paper origin
`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:964-1120`).
-/
abbrev PauliSpace (P : AdmissibleParams) := PauliIndex P → PauliScalar P

/-- The coefficient register indexed by the Boolean cube in
`def:generalized-pauli`, blueprint `ch11_qpbt_algebra.tex:587-631`, paper origin
`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:908-945`.
-/
abbrev PauliRegister (P : AdmissibleParams) := Cube P.m → PauliScalar P

/- The nested sum is the fixed register order
`V_X ⊕ V_Z ⊕ V_I ⊕ V_V ⊕ V_{R_X} ⊕ V_{R_Z}` from the blueprint. -/
/-- The `V_X` block of an ambient Pauli vector (`def:pauli-question-distribution`,
blueprint `ch13_qpbt_test.tex`; paper origin
`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:964-1120`). -/
def pauliXBlock {P : AdmissibleParams} (z : PauliSpace P) : Fin P.m → PauliScalar P :=
  fun i => z (.inl (.inl (.inl (.inl (.inl i)))))

/-- The `V_Z` block of an ambient Pauli vector in `def:pauli-question-distribution`,
blueprint `ch13_qpbt_test.tex`, paper origin
`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:964-1120`.
-/
def pauliZBlock {P : AdmissibleParams} (z : PauliSpace P) : Fin P.m → PauliScalar P :=
  fun i => z (.inl (.inl (.inl (.inl (.inr i)))))

/-- The scalar block `V_I` of an ambient Pauli vector in
`def:pauli-question-distribution`, blueprint `ch13_qpbt_test.tex`,
paper origin `references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:964-1120`.
-/
def pauliScalarBlock {P : AdmissibleParams} (z : PauliSpace P) : PauliScalar P :=
  z (.inl (.inl (.inl (.inr ()))))

/-- The direction block `V_V` of an ambient Pauli vector in
`def:pauli-question-distribution`, blueprint `ch13_qpbt_test.tex`,
paper origin `references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:964-1120`.
-/
def pauliDirectionBlock {P : AdmissibleParams} (z : PauliSpace P) : Fin P.m → PauliScalar P :=
  fun i => z (.inl (.inl (.inr i)))

/-- The `r_X` scalar block in the Pauli question content from
`def:pauli-question-distribution`, blueprint `ch13_qpbt_test.tex`,
paper origin `references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:964-1120`.
-/
def pauliRXBlock {P : AdmissibleParams} (z : PauliSpace P) : PauliScalar P :=
  z (.inl (.inr ()))

/-- The `r_Z` scalar block in the Pauli question content from
`def:pauli-question-distribution`, blueprint `ch13_qpbt_test.tex`,
paper origin `references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:964-1120`.
-/
def pauliRZBlock {P : AdmissibleParams} (z : PauliSpace P) : PauliScalar P :=
  z (.inr ())

/-- Select the basis-dependent point block from a Pauli question content in
`def:pauli-question-distribution`, blueprint `ch13_qpbt_test.tex`,
paper origin `references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:964-1120`.
-/
def pauliPointBlock {P : AdmissibleParams} (W : PauliKind) (z : PauliSpace P) :
    Fin P.m → PauliScalar P :=
  match W with
  | .X => pauliXBlock z
  | .Z => pauliZBlock z

/-- Read the low-degree register selected by a basis from an ambient Pauli
vector.  This is restriction to the basis-selected registers of
`def:pauli-question-distribution`, blueprint `ch13_qpbt_test.tex`, paper origin
`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:964-1120`.
-/
def pauliToLd (P : AdmissibleParams) (W : PauliKind) (z : PauliSpace P) :
    LdSpace P.toLdParams :=
  fun i => match i with
  | .inl (.inl j) => pauliPointBlock W z j
  | .inl (.inr _) => pauliScalarBlock z
  | .inr j => pauliDirectionBlock z j

/-- Embed a low-degree vector into the basis-selected Pauli blocks, clearing the
other basis and the two `r` registers.  This is extension into the
basis-selected registers of `def:pauli-question-distribution`, blueprint
`blueprint/src/chapter/ch13_qpbt_test.tex`, paper origin
`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:964-1120`.
-/
def embedLd (P : AdmissibleParams) (W : PauliKind)
    (u : LdSpace P.toLdParams) : PauliSpace P :=
  fun i => match i with
  | .inl (.inl (.inl (.inl (.inl j)))) =>
      match W with
      | .X => u (.inl (.inl j))
      | .Z => 0
  | .inl (.inl (.inl (.inl (.inr j)))) =>
      match W with
      | .X => 0
      | .Z => u (.inl (.inl j))
  | .inl (.inl (.inl (.inr _))) => u (.inl (.inr ()))
  | .inl (.inl (.inr j)) => u (.inr j)
  | .inl (.inr _) => 0
  | .inr _ => 0

/-- The type-4 projection retaining `V_X`, `V_Z`, `V_{R_X}`, and `V_{R_Z}` from
`def:pauli-question-distribution`, blueprint `ch13_qpbt_test.tex`, paper
origin `references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:964-1120`.
-/
def pauliSharedProjection {P : AdmissibleParams} (z : PauliSpace P) : PauliSpace P :=
  fun i => match i with
  | .inl (.inl (.inl (.inl (.inl j)))) => z (.inl (.inl (.inl (.inl (.inl j)))))
  | .inl (.inl (.inl (.inl (.inr j)))) => z (.inl (.inl (.inl (.inl (.inr j)))))
  | .inl (.inl (.inl (.inr _))) => 0
  | .inl (.inl (.inr _)) => 0
  | .inl (.inr _) => z (.inl (.inr ()))
  | .inr _ => z (.inr ())

/-- The source level attached to each typed Pauli CL map.  This records the
exact levels in items 1--5 of `def:pauli-question-distribution`: point, line,
and diagonal maps have levels 1, 2, and 3, the Pauli map has level 0, and the
shared projection has level 1.  Blueprint
`blueprint/src/chapter/ch13_qpbt_test.tex`; paper origin
`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:964-1120`.
-/
def pauliCLLevel : PauliType → ℕ
  | .point _ => 1
  | .aline _ => 2
  | .dline _ => 3
  | .pauli _ => 0
  | .pairW _ => 1
  | .pair => 1
  | .ms _ => 1

/-- The conditionally linear map attached to each Pauli question type.  The
point and line maps are the corresponding
low-degree maps embedded in the selected basis block; Pair, Magic Square, and
Pair/W types use the shared projection; Pauli/W is the zero-level map.  This
is the direct finite-space form of `def:pauli-question-distribution`,
blueprint `ch13_qpbt_test.tex`, paper origin
`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:964-1120`.
-/
noncomputable def pauliCL (P : AdmissibleParams) (t : PauliType) :
    PauliSpace P → PauliSpace P :=
  match t with
  | .point W => fun z => embedLd P W (ldPointCL P.toLdParams (pauliToLd P W z))
  | .aline W => fun z => embedLd P W (ldALineCL P.toLdParams (pauliToLd P W z))
  | .dline W => fun z => embedLd P W (ldDLineCL P.toLdParams (pauliToLd P W z))
  | .pauli _ => fun _ => 0
  | .pairW _ => pauliSharedProjection
  | .pair => pauliSharedProjection
  | .ms _ => pauliSharedProjection

/-- Formalization-only auxiliary: the type-4 projection of the ambient Pauli
coefficient space, presented as a linear map; see `pauliSharedProjection` and
`def:pauli-question-distribution`, blueprint `ch13_qpbt_test.tex`,
paper origin `references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:964-1120`. -/
private def pauliSharedProjectionLinear (P : AdmissibleParams) :
    PauliSpace P →ₗ[PauliScalar P] PauliSpace P where
  toFun z := pauliSharedProjection z
  map_add' x y := by
    funext i
    rcases i with ((((j | j) | u) | j) | u) | u <;> simp [pauliSharedProjection]
  map_smul' c x := by
    funext i
    rcases i with ((((j | j) | u) | j) | u) | u <;> simp [pauliSharedProjection]

/-- Formalization-only auxiliary: the inclusion of the low-degree register index
into the ambient Pauli register index selected by a basis.  It realizes the
natural embedding of the range of the low-degree maps described in
`def:pauli-question-distribution`, blueprint `ch13_qpbt_test.tex`,
paper origin `references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:964-1120`. -/
private def pauliLdIndex (P : AdmissibleParams) (W : PauliKind) :
    LdIndex P.toLdParams → PauliIndex P
  | .inl (.inl j) =>
      match W with
      | .X => .inl (.inl (.inl (.inl (.inl j))))
      | .Z => .inl (.inl (.inl (.inl (.inr j))))
  | .inl (.inr _) => .inl (.inl (.inl (.inr ())))
  | .inr j => .inl (.inl (.inr j))

/-- Formalization-only auxiliary: distinct low-degree registers are sent to
distinct ambient Pauli registers; see `pauliLdIndex`. -/
private theorem pauliLdIndex_injective (P : AdmissibleParams) (W : PauliKind) :
    Function.Injective (pauliLdIndex P W) := by
  intro a b hab
  cases W <;> rcases a with (j | u) | j <;> rcases b with (j' | u') | j' <;>
    simp_all [pauliLdIndex]

/-- Formalization-only auxiliary: reading the low-degree register out of an
ambient Pauli vector is restriction along `pauliLdIndex`; see
`def:pauli-question-distribution`, blueprint `ch13_qpbt_test.tex`,
paper origin `references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:964-1120`. -/
private theorem pauliToLd_eq (P : AdmissibleParams) (W : PauliKind)
    (z : PauliSpace P) :
    pauliToLd P W z = fun k => z (pauliLdIndex P W k) := by
  funext k
  rcases k with (j | u) | j <;> cases W <;> rfl

/-- Formalization-only auxiliary: writing a low-degree vector into the ambient
Pauli registers is extension by zero along `pauliLdIndex`; see
`def:pauli-question-distribution`, blueprint `ch13_qpbt_test.tex`,
paper origin `references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:964-1120`. -/
private theorem embedLd_eq (P : AdmissibleParams) (W : PauliKind)
    (w : LdSpace P.toLdParams) :
    embedLd P W w = Function.extend (pauliLdIndex P W) w 0 := by
  have hf := pauliLdIndex_injective P W
  have hz : ∀ i : PauliIndex P, (∀ k, pauliLdIndex P W k ≠ i) →
      Function.extend (pauliLdIndex P W) w (0 : PauliSpace P) i = 0 :=
    fun i hi => Function.extend_apply' w (0 : PauliSpace P) i
      (fun hex => hi hex.choose hex.choose_spec)
  funext i
  rcases i with ((((j | j) | u) | j) | u) | u
  · cases W
    · exact (hf.extend_apply w 0 (Sum.inl (Sum.inl j))).symm
    · exact (hz _ (by rintro ((j' | u') | j') <;> simp [pauliLdIndex])).symm
  · cases W
    · exact (hz _ (by rintro ((j' | u') | j') <;> simp [pauliLdIndex])).symm
    · exact (hf.extend_apply w 0 (Sum.inl (Sum.inl j))).symm
  · exact (hf.extend_apply w 0 (Sum.inl (Sum.inr ()))).symm
  · exact (hf.extend_apply w 0 (Sum.inr j)).symm
  · exact (hz _ (by
      intro k
      cases W <;> rcases k with (j' | u') | j' <;> simp [pauliLdIndex])).symm
  · exact (hz _ (by
      intro k
      cases W <;> rcases k with (j' | u') | j' <;> simp [pauliLdIndex])).symm

/-- Formalization-only auxiliary: the typed Pauli point, axis-line, and
diagonal-line maps are the corresponding low-degree maps reindexed along
`pauliLdIndex`.  This is items 1--3 of `def:pauli-question-distribution`,
blueprint `ch13_qpbt_test.tex`,
paper origin `references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:964-1120`. -/
private theorem pauliCL_reindex (P : AdmissibleParams) (W : PauliKind)
    (L : LdSpace P.toLdParams → LdSpace P.toLdParams) :
    (fun z : PauliSpace P => embedLd P W (L (pauliToLd P W z))) =
      fun z => Function.extend (pauliLdIndex P W)
        (L (fun k => z (pauliLdIndex P W k))) 0 := by
  funext z
  rw [embedLd_eq, pauliToLd_eq]

/-- Every Pauli question map is conditionally linear at its specified level:
point maps have level one, axis-line maps level two, diagonal-line maps level
three, Pauli maps level zero, and all pair and Magic Square maps level one.
This is `lem:pauli-question-cl-components` in
`blueprint/src/chapter/ch13_qpbt_test.tex`, with paper origin
`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:964-1120`.
The assertion concerns the individual levels and does not choose one common
level for the whole family. -/
theorem isCondLinear_pauliCL (P : AdmissibleParams) (t : PauliType) :
    IsCondLinearOn (PauliScalar P) Finset.univ (pauliCLLevel t) (pauliCL P t) := by
  have hshared : IsCondLinearOn (PauliScalar P) Finset.univ 1
      (pauliSharedProjection (P := P)) :=
    isCondLinearOn_one_of_linear (pauliSharedProjectionLinear P)
  cases t with
  | point W =>
      show IsCondLinearOn (PauliScalar P) Finset.univ 1
        (fun z : PauliSpace P =>
          embedLd P W (ldPointCL P.toLdParams (pauliToLd P W z)))
      rw [pauliCL_reindex P W (ldPointCL P.toLdParams)]
      exact isCondLinearOn_reindex (pauliLdIndex_injective P W)
        (isCondLinear_ldPointCL P.toLdParams)
  | aline W =>
      show IsCondLinearOn (PauliScalar P) Finset.univ 2
        (fun z : PauliSpace P =>
          embedLd P W (ldALineCL P.toLdParams (pauliToLd P W z)))
      rw [pauliCL_reindex P W (ldALineCL P.toLdParams)]
      exact isCondLinearOn_reindex (pauliLdIndex_injective P W)
        (isCondLinear_ldALineCL P.toLdParams)
  | dline W =>
      show IsCondLinearOn (PauliScalar P) Finset.univ 3
        (fun z : PauliSpace P =>
          embedLd P W (ldDLineCL P.toLdParams (pauliToLd P W z)))
      rw [pauliCL_reindex P W (ldDLineCL P.toLdParams)]
      exact isCondLinearOn_reindex (pauliLdIndex_injective P W)
        (isCondLinear_ldDLineCL P.toLdParams)
  | pauli W => exact ⟨.zero, trivial, rfl⟩
  | pairW W => exact hshared
  | pair => exact hshared
  | ms s => exact hshared

/-- The Pauli question maps form a typed family of three-level conditionally
linear functions after each component is raised from its specified level. This
is `lem:pauli-question-cl-family` in
`blueprint/src/chapter/ch13_qpbt_test.tex`, with paper origin
`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:1084-1120`.
-/
theorem isTypedCondLinearFamily_pauliCL (P : AdmissibleParams) :
    IsTypedCondLinearFamily (PauliScalar P) PauliType 3 (pauliCL P) := by
  intro t
  exact IsCondLinearOn.mono_level (isCondLinear_pauliCL P t) (by
    cases t <;> simp [pauliCLLevel])

/-- A finite edge set for the typed Pauli question graph.  The self-loops and
the displayed type-incidence families are the graph used by the sampler in
`def:pauli-question-distribution`, blueprint `ch13_qpbt_test.tex`, paper origin
`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:964-1120`.
-/
def pauliEdges : Finset (Sym2 PauliType) :=
  let loops := Finset.univ.image (fun t : PauliType => Sym2.mk t t)
  let lineEdges :=
    (Finset.univ : Finset PauliKind).image (fun W =>
      Sym2.mk (.point W) (.aline W)) ∪
      (Finset.univ : Finset PauliKind).image (fun W =>
        Sym2.mk (.point W) (.dline W)) ∪
      (Finset.univ : Finset PauliKind).image (fun W =>
        Sym2.mk (.point W) (.pauli W))
  let basisEdges :=
    (Finset.univ : Finset PauliKind).image (fun W =>
      Sym2.mk (.point W) (.pairW W)) ∪
      ({Sym2.mk (.point .X) (.ms (.var ⟨0, by decide⟩)),
        Sym2.mk (.point .Z) (.ms (.var ⟨4, by decide⟩))} : Finset (Sym2 PauliType))
  let pairEdges :=
    (Finset.univ : Finset PauliKind).image (fun W =>
      Sym2.mk (.pairW W) .pair)
  let msEdges' :=
    (Finset.univ : Finset (MsType × MsType)).filter (fun xy =>
      Sym2.mk xy.1 xy.2 ∈ msEdges) |>.image (fun xy =>
        Sym2.mk (.ms xy.1) (.ms xy.2))
  loops ∪ lineEdges ∪ basisEdges ∪ pairEdges ∪ msEdges'

/-- A Pauli question is a type together with a full ambient coefficient vector
(`def:pauli-question-distribution`, blueprint `ch13_qpbt_test.tex`; paper
origin `references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:964-1120`).
-/
abbrev PauliQuestion (P : AdmissibleParams) := PauliType × PauliSpace P

/-- The Pauli question carrying no additional coefficient data, as in
`def:pauli-win-predicate`, blueprint `ch13_qpbt_test.tex`, paper origin
`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:1006-1008`.
Its ambient coefficient vector is zero. -/
def pauliQuestion (P : AdmissibleParams) (W : PauliKind) : PauliQuestion P :=
  (.pauli W, 0)

/-- The ordered-edge subtype used by the Pauli question sampler.  This is
the finite carrier underlying `graphDistribution pauliEdges`, used to state
`def:pauli-question-distribution`, blueprint
`ch13_qpbt_test.tex`, paper origin
`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:964-1120`.
-/
abbrev PauliEdge :=
  {e : PauliType × PauliType // Sym2.mk e.1 e.2 ∈ pauliEdges}

/-- The Pauli graph has a loop, so its ordered-edge subtype is nonempty.  This
is a finite-carrier fact used only to instantiate the uniform source sampler
for `def:pauli-question-distribution`; the graph itself is the source-facing
object `pauliEdges` above (same blueprint and paper references).
-/
theorem pauliEdge_nonempty : Nonempty PauliEdge := by
  refine ⟨⟨(.point .X, .point .X), ?_⟩⟩
  simp [pauliEdges]

/-- The Pauli question distribution from `def:pauli-question-distribution`,
blueprint `ch13_qpbt_test.tex`, paper origin
`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:1070-1120`.
-/
noncomputable def pauliQuestionDistribution (P : AdmissibleParams) :
    Distribution (PauliQuestion P × PauliQuestion P) :=
  by
    classical
    letI : Nonempty PauliEdge := pauliEdge_nonempty
    exact
      Distribution.map
        (uniformDistribution (PauliEdge × PauliSpace P))
        (fun s =>
          ((s.1.1.1, pauliCL P s.1.1.1 s.2),
            (s.1.1.2, pauliCL P s.1.1.2 s.2)))

/-- The finite answer alphabet for the Pauli basis test.  Its constructors are
the seven answer forms in `def:pauli-win-predicate`, blueprint
`ch13_qpbt_test.tex`,
paper origin `references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:1126-1225`.
-/
inductive PauliAnswer (P : AdmissibleParams) where
  | value (a : PauliScalar P)
  | alinePoly (a : Fin (P.d + 1) → PauliScalar P)
  | dlinePoly (a : Fin (P.m * P.d + 1) → PauliScalar P)
  | pairBits (a : ZMod 2 × ZMod 2)
  | bit (a : ZMod 2)
  | msTriple (a : Fin 3 → ZMod 2)
  | pauliOutcome (a : PauliRegister P)
  deriving DecidableEq

/-- A formalization-only total relabeling from the global Pauli-test answer
alphabet to a Pauli register. It folds wrong-form answers into zero so that a
Pauli question yields a complete `PauliRegister`-indexed measurement. -/
def pauliAnswerOrZero {P : AdmissibleParams} : PauliAnswer P → PauliRegister P
  | .pauliOutcome u => u
  | _ => 0

/-- A finite sum code used only to construct the `Fintype` instance for the
answer alphabet in `def:pauli-win-predicate`, blueprint
`ch13_qpbt_test.tex`, paper origin
`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:1126-1225`.
-/
abbrev PauliAnswerCode (P : AdmissibleParams) :=
  PauliScalar P ⊕
    ((Fin (P.d + 1) → PauliScalar P) ⊕
      ((Fin (P.m * P.d + 1) → PauliScalar P) ⊕
        ((ZMod 2 × ZMod 2) ⊕
          (ZMod 2 ⊕ ((Fin 3 → ZMod 2) ⊕ PauliRegister P)))))

/-- The constructor-preserving finite-code equivalence for `PauliAnswer`.  It
is the finite encoding used to state `def:pauli-win-predicate`, blueprint
`ch13_qpbt_test.tex`, paper origin
`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:1126-1225`.
-/
noncomputable def pauliAnswerEquiv (P : AdmissibleParams) :
    PauliAnswer P ≃ PauliAnswerCode P where
  toFun
    | .value a => .inl a
    | .alinePoly a => .inr (.inl a)
    | .dlinePoly a => .inr (.inr (.inl a))
    | .pairBits a => .inr (.inr (.inr (.inl a)))
    | .bit a => .inr (.inr (.inr (.inr (.inl a))))
    | .msTriple a => .inr (.inr (.inr (.inr (.inr (.inl a)))))
    | .pauliOutcome a => .inr (.inr (.inr (.inr (.inr (.inr a)))))
  invFun
    | .inl a => .value a
    | .inr (.inl a) => .alinePoly a
    | .inr (.inr (.inl a)) => .dlinePoly a
    | .inr (.inr (.inr (.inl a))) => .pairBits a
    | .inr (.inr (.inr (.inr (.inl a)))) => .bit a
    | .inr (.inr (.inr (.inr (.inr (.inl a))))) => .msTriple a
    | .inr (.inr (.inr (.inr (.inr (.inr a))))) => .pauliOutcome a
  left_inv := by
    intro x
    cases x <;> rfl
  right_inv := by
    intro x
    cases x with
    | inl a => rfl
    | inr x =>
        cases x with
        | inl a => rfl
        | inr x =>
            cases x with
            | inl a => rfl
            | inr x =>
                cases x with
                | inl a => rfl
                | inr x =>
                    cases x with
                    | inl a => rfl
                    | inr x =>
                        cases x with
                        | inl a => rfl
                        | inr a => rfl

noncomputable instance (P : AdmissibleParams) : Fintype (PauliAnswer P) :=
  Fintype.ofEquiv (PauliAnswerCode P) (pauliAnswerEquiv P).symm

instance (P : AdmissibleParams) : Inhabited (PauliAnswer P) :=
  ⟨.bit 0⟩

/-- The phase bit `γ(u_X,u_Z,r_X,r_Z)` from `eq:gamma-value`.  It uses the
fixed trace selected by `P.model`, as required by the paper's fixed
self-dual-normal representation.  Blueprint
`blueprint/src/chapter/ch13_qpbt_test.tex`; paper origin
`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:1198-1212`.
-/
noncomputable def gammaValue (P : AdmissibleParams)
    (uX uZ : Fin P.m → PauliScalar P)
    (rX rZ : PauliScalar P) : ZMod 2 :=
  fixedBinTrace P.model
    (dotProduct (rX • indicatorVec uX) (rZ • indicatorVec uZ))

/-- The commutation bit attached to a full Pauli ambient question, from
`eq:gamma-value` in `def:pauli-win-predicate`, blueprint
`ch13_qpbt_test.tex`, paper origin
`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:1198-1212`.
-/
noncomputable def pauliPairGamma (P : AdmissibleParams) (z : PauliSpace P) : ZMod 2 :=
  gammaValue P (pauliXBlock z) (pauliZBlock z)
    (pauliRXBlock z) (pauliRZBlock z)

/-- The answer constructor prescribed by each Pauli question type; this is the
well-formedness part of `def:pauli-win-predicate`, blueprint
`ch13_qpbt_test.tex`, paper origin
`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:1126-1225`.
-/
def validPauliAnswer {P : AdmissibleParams} (t : PauliType) (a : PauliAnswer P) : Bool :=
  match t, a with
  | .point _, .value _ => true
  | .aline _, .alinePoly _ => true
  | .dline _, .dlinePoly _ => true
  | .pauli _, .pauliOutcome _ => true
  | .pairW _, .bit _ => true
  | .pair, .pairBits _ => true
  | .ms (.constraint _), .msTriple _ => true
  | .ms (.var _), .bit _ => true
  | _, _ => false

/-- The axis-line versus point relation used by `def:pauli-win-predicate`,
blueprint `ch13_qpbt_test.tex`, paper origin
`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:1126-1225`.
-/
def pauliAlinePointCondition (P : AdmissibleParams) (W : PauliKind)
    (line point : PauliSpace P) (f : Fin (P.d + 1) → PauliScalar P)
    (a : PauliScalar P) : Prop :=
  -- The universal form preserves the source's zero-direction convention.
  ∀ t : PauliScalar P,
    pauliPointBlock W point =
        pauliPointBlock W line + t • coordinateDirection
          (chiIndex P.toLdParams (pauliScalarBlock line)) →
      evalCoefficient f t = a

/-- The diagonal-line versus point relation used by `def:pauli-win-predicate`,
blueprint `ch13_qpbt_test.tex`, paper origin
`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:1126-1225`.
-/
def pauliDlinePointCondition (P : AdmissibleParams) (W : PauliKind)
    (line point : PauliSpace P) (f : Fin (P.m * P.d + 1) → PauliScalar P)
    (a : PauliScalar P) : Prop :=
  ∀ t : PauliScalar P,
    pauliPointBlock W point = pauliPointBlock W line +
        t • pauliDirectionBlock line →
      evalCoefficient f t = a

/-- The raw Pauli-versus-point consistency relation from `def:pauli-win-predicate`,
blueprint `ch13_qpbt_test.tex`, paper origin
`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:1126-1225`.
-/
def pauliPointPauliCondition (P : AdmissibleParams) (W : PauliKind)
    (point : PauliSpace P) (h : PauliRegister P) (a : PauliScalar P) : Prop :=
  lowDegreeEnc h (pauliPointBlock W point) = a

/-- The Pair/W consistency relation, including the one-sided gamma gate, from
`def:pauli-win-predicate`, blueprint `ch13_qpbt_test.tex`, paper origin
`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:1126-1225`.
-/
def pauliPairCondition (P : AdmissibleParams) (W : PauliKind)
    (z : PauliSpace P) (β : ZMod 2) (bits : ZMod 2 × ZMod 2) : Prop :=
  pauliPairGamma P z ≠ 0 ∨
    (match W with
    | .X => bits.1 = β
    | .Z => bits.2 = β)

/-- The point/Pair/W trace consistency relation from `def:pauli-win-predicate`,
blueprint `ch13_qpbt_test.tex`, paper origin
`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:1126-1225`.
-/
def pauliPointPairCondition (P : AdmissibleParams) (W : PauliKind)
    (z : PauliSpace P) (a : PauliScalar P) (β : ZMod 2) : Prop :=
  pauliPairGamma P z ≠ 0 ∨
    fixedBinTrace P.model
      (a * (match W with
      | .X => pauliRXBlock z
      | .Z => pauliRZBlock z)) = β

/-- The Point/Variable consistency clause of `def:pauli-win-predicate`.
The check is gated by `gamma = 0` and only uses Variable 1 in the X basis or
Variable 5 in the Z basis.  Blueprint
`blueprint/src/chapter/ch13_qpbt_test.tex`; paper origin
`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:1126-1225`.
-/
def pauliPointVariableCondition (P : AdmissibleParams) (W : PauliKind)
    (z : PauliSpace P) (j : Fin 9) (a : PauliScalar P) (β : ZMod 2) : Prop :=
  pauliPairGamma P z = 0 ∨
    (j = ⟨0, by decide⟩ ∧ W = .X ∧
        fixedBinTrace P.model (a * pauliRXBlock z) = β) ∨
    (j = ⟨4, by decide⟩ ∧ W = .Z ∧
        fixedBinTrace P.model (a * pauliRZBlock z) = β)

/-- The Pauli win predicate, with constructor-shape rejection.  This is
`def:pauli-win-predicate` in `blueprint/src/chapter/ch13_qpbt_test.tex`,
paper origin `references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:1126-1225`.
-/
noncomputable def pauliWinPredicate (P : AdmissibleParams) :
    PauliQuestion P → PauliQuestion P → PauliAnswer P → PauliAnswer P → Bool :=
  open Classical in
  fun (tA, xA) (tB, xB) a b =>
    if validPauliAnswer tA a && validPauliAnswer tB b then
      if tA = tB then
        decide (a = b)
      else
        match tA, tB, a, b with
      | .aline W, .point W', .alinePoly f, .value u =>
          if W = W' then decide (pauliAlinePointCondition P W xA xB f u) else true
      | .point W, .aline W', .value u, .alinePoly f =>
          if W = W' then decide (pauliAlinePointCondition P W xB xA f u) else true
      | .dline W, .point W', .dlinePoly f, .value u =>
          if W = W' then decide (pauliDlinePointCondition P W xA xB f u) else true
      | .point W, .dline W', .value u, .dlinePoly f =>
          if W = W' then decide (pauliDlinePointCondition P W xB xA f u) else true
      | .point W, .pauli W', .value u, .pauliOutcome h =>
          if W = W' then decide (pauliPointPauliCondition P W xA h u) else true
      | .pauli W, .point W', .pauliOutcome h, .value u =>
          if W = W' then decide (pauliPointPauliCondition P W xB h u) else true
      | .pairW W, .pair, .bit β, .pairBits bits =>
          decide (pauliPairCondition P W xA β bits)
      | .pair, .pairW W, .pairBits bits, .bit β =>
          decide (pauliPairCondition P W xB β bits)
      | .point W, .pairW W', .value u, .bit β =>
          if W = W' then decide (pauliPointPairCondition P W xB u β) else true
      | .pairW W, .point W', .bit β, .value u =>
          if W = W' then decide (pauliPointPairCondition P W xA u β) else true
      | .ms (.constraint i), .ms (.var j), .msTriple β, .bit γ =>
          if ∃ k : Fin 3, msConstraintVars i k = j then
            decide (pauliPairGamma P xA = 0 ∨
              msWinPredicate (.constraint i) (.var j) (.triple β) (.bit γ))
          else true
      | .ms (.var j), .ms (.constraint i), .bit γ, .msTriple β =>
          if ∃ k : Fin 3, msConstraintVars i k = j then
            decide (pauliPairGamma P xB = 0 ∨
              msWinPredicate (.var j) (.constraint i) (.bit γ) (.triple β))
          else true
      | .point W, .ms (.var j), .value u, .bit β =>
          decide (pauliPointVariableCondition P W xB j u β)
      | .ms (.var j), .point W, .bit β, .value u =>
          decide (pauliPointVariableCondition P W xA j u β)
        | _, _, _, _ => true
    else false

/-- The Pauli basis test determined by the question distribution
`pauliQuestionDistribution` and the win predicate `pauliWinPredicate`.  These
are `def:pauli-question-distribution` and `def:pauli-win-predicate` in
`blueprint/src/chapter/ch13_qpbt_test.tex`, with paper origin
`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:964-1225`.
-/
noncomputable def pauliBasisTest (P : AdmissibleParams) : Game where
  QuestionA := PauliQuestion P
  QuestionB := PauliQuestion P
  AnswerA := PauliAnswer P
  AnswerB := PauliAnswer P
  μ := pauliQuestionDistribution P
  μ_prob := by
    classical
    letI : Nonempty PauliEdge := pauliEdge_nonempty
    exact Distribution.IsProbability.map
      (uniformDistribution_isProbability (PauliEdge × PauliSpace P)) _
  decide := pauliWinPredicate P

end

end MIPStarRE.QPBT
