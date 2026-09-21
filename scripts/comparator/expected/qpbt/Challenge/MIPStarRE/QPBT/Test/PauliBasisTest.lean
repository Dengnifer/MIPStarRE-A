import Mathlib
import Challenge.MIPStarRE.QPBT.Algebra.LowDegreeCode
import Challenge.MIPStarRE.QPBT.Algebra.Pauli
import Challenge.MIPStarRE.QPBT.Games.TypedCondLinear
import Challenge.MIPStarRE.QPBT.Test.LowDegreeGame
import Challenge.MIPStarRE.QPBT.Test.MagicSquare

/-! Challenge mirror of `MIPStarRE/QPBT/Test/PauliBasisTest.lean`.

One challenge module per contributing library module, importing the
mirrors of the library modules this one imports.  The partition is
what makes Lean generate the same auxiliary declarations, under the
same names, as the library does. -/

open scoped BigOperators MatrixOrder Matrix ComplexOrder
namespace MIPStarRE.QPBT

-- elaboration context of MIPStarRE/QPBT/Test/PauliBasisTest.lean:28-741
noncomputable section
open MIPStarRE.LDT

-- source: MIPStarRE/QPBT/Test/PauliBasisTest.lean:30-43  (MIPStarRE.QPBT.AdmissibleParams)
/-- The numerical admissible Pauli-test parameter tuple.  Its scalar carrier
uses the once-and-for-all model `fixedFieldModel q hq`, so the paper's fixed
self-dual-normal identification is not quantified in the test statement.  This
is blueprint
`def:admissible`, paper origin
`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:958-961`.
-/
structure AdmissibleParams where
  q : ℕ
  m : ℕ
  d : ℕ
  hd : 1 ≤ d
  hq : IsAdmissibleSize q
  hdvd : m ∣ q

-- source: MIPStarRE/QPBT/Test/PauliBasisTest.lean:45-57  (MIPStarRE.QPBT.AdmissibleParams.one_le_m)
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

-- source: MIPStarRE/QPBT/Test/PauliBasisTest.lean:59-66  (MIPStarRE.QPBT.AdmissibleParams.model)
/-- The fixed scalar model of an admissible parameter tuple.  It is a
compatibility view of the global `fixedFieldModel` selector, not an independently
quantified field representation.  This is the field representation of
`def:admissible`, blueprint `ch13_qpbt_test.tex`; paper
origin `references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:958-961`.
-/
noncomputable def AdmissibleParams.model (P : AdmissibleParams) : FixedFieldModel P.q :=
  fixedFieldModel P.q P.hq

-- source: MIPStarRE/QPBT/Test/PauliBasisTest.lean:68-83  (MIPStarRE.QPBT.AdmissibleParams.toLdParams)
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

-- source: MIPStarRE/QPBT/Test/PauliBasisTest.lean:85-91  (MIPStarRE.QPBT.PauliScalar)
/-- The scalar carrier associated with an admissible parameter tuple.  It is
the globally fixed field carrier selected by `AdmissibleParams.model` in
blueprint
`def:admissible`, paper origin
`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:958-961`.
-/
abbrev PauliScalar (P : AdmissibleParams) := P.model.K

-- source: MIPStarRE/QPBT/Test/PauliBasisTest.lean:93-105  (MIPStarRE.QPBT.PauliType.ctorElim)
/-- The six families of Pauli-test questions.  This is part of
blueprint `def:pauli-question-distribution`,
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

-- source: MIPStarRE/QPBT/Test/PauliBasisTest.lean:107-113  (MIPStarRE.QPBT.PauliIndex)
/-- The register blocks used by the Pauli question space.  These are the
coordinates displayed in blueprint
`def:pauli-question-distribution`, paper origin
`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:964-1120`.
-/
abbrev PauliIndex (P : AdmissibleParams) :=
  (((((Fin P.m ⊕ Fin P.m) ⊕ Unit) ⊕ Fin P.m) ⊕ Unit) ⊕ Unit)

-- source: MIPStarRE/QPBT/Test/PauliBasisTest.lean:115-119  (MIPStarRE.QPBT.PauliSpace)
/-- The ambient Pauli question coefficient space (blueprint
`def:pauli-question-distribution`; paper origin
`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:964-1120`).
-/
abbrev PauliSpace (P : AdmissibleParams) := PauliIndex P → PauliScalar P

-- source: MIPStarRE/QPBT/Test/PauliBasisTest.lean:121-125  (MIPStarRE.QPBT.PauliRegister)
/-- The coefficient register indexed by the Boolean cube in
blueprint `def:generalized-pauli`, paper origin
`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:908-945`.
-/
abbrev PauliRegister (P : AdmissibleParams) := Cube P.m → PauliScalar P

-- source: MIPStarRE/QPBT/Test/PauliBasisTest.lean:129-133  (MIPStarRE.QPBT.pauliXBlock)
/-- The `V_X` block of an ambient Pauli vector (blueprint
`def:pauli-question-distribution`; paper origin
`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:964-1120`). -/
def pauliXBlock {P : AdmissibleParams} (z : PauliSpace P) : Fin P.m → PauliScalar P :=
  fun i => z (.inl (.inl (.inl (.inl (.inl i)))))

-- source: MIPStarRE/QPBT/Test/PauliBasisTest.lean:135-140  (MIPStarRE.QPBT.pauliZBlock)
/-- The `V_Z` block of an ambient Pauli vector in blueprint
`def:pauli-question-distribution`, paper origin
`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:964-1120`.
-/
def pauliZBlock {P : AdmissibleParams} (z : PauliSpace P) : Fin P.m → PauliScalar P :=
  fun i => z (.inl (.inl (.inl (.inl (.inr i)))))

-- source: MIPStarRE/QPBT/Test/PauliBasisTest.lean:142-147  (MIPStarRE.QPBT.pauliScalarBlock)
/-- The scalar block `V_I` of an ambient Pauli vector in
blueprint `def:pauli-question-distribution`,
paper origin `references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:964-1120`.
-/
def pauliScalarBlock {P : AdmissibleParams} (z : PauliSpace P) : PauliScalar P :=
  z (.inl (.inl (.inl (.inr ()))))

-- source: MIPStarRE/QPBT/Test/PauliBasisTest.lean:149-154  (MIPStarRE.QPBT.pauliDirectionBlock)
/-- The direction block `V_V` of an ambient Pauli vector in
blueprint `def:pauli-question-distribution`,
paper origin `references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:964-1120`.
-/
def pauliDirectionBlock {P : AdmissibleParams} (z : PauliSpace P) : Fin P.m → PauliScalar P :=
  fun i => z (.inl (.inl (.inr i)))

-- source: MIPStarRE/QPBT/Test/PauliBasisTest.lean:156-161  (MIPStarRE.QPBT.pauliRXBlock)
/-- The `r_X` scalar block in the Pauli question content from
blueprint `def:pauli-question-distribution`,
paper origin `references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:964-1120`.
-/
def pauliRXBlock {P : AdmissibleParams} (z : PauliSpace P) : PauliScalar P :=
  z (.inl (.inr ()))

-- source: MIPStarRE/QPBT/Test/PauliBasisTest.lean:163-168  (MIPStarRE.QPBT.pauliRZBlock)
/-- The `r_Z` scalar block in the Pauli question content from
blueprint `def:pauli-question-distribution`,
paper origin `references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:964-1120`.
-/
def pauliRZBlock {P : AdmissibleParams} (z : PauliSpace P) : PauliScalar P :=
  z (.inr ())

-- source: MIPStarRE/QPBT/Test/PauliBasisTest.lean:170-178  (MIPStarRE.QPBT.pauliPointBlock)
/-- Select the basis-dependent point block from a Pauli question content in
blueprint `def:pauli-question-distribution`,
paper origin `references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:964-1120`.
-/
def pauliPointBlock {P : AdmissibleParams} (W : PauliKind) (z : PauliSpace P) :
    Fin P.m → PauliScalar P :=
  match W with
  | .X => pauliXBlock z
  | .Z => pauliZBlock z

-- source: MIPStarRE/QPBT/Test/PauliBasisTest.lean:180-190  (MIPStarRE.QPBT.pauliToLd)
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

-- source: MIPStarRE/QPBT/Test/PauliBasisTest.lean:192-212  (MIPStarRE.QPBT.embedLd)
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

-- source: MIPStarRE/QPBT/Test/PauliBasisTest.lean:214-225  (MIPStarRE.QPBT.pauliSharedProjection)
/-- The type-4 projection retaining `V_X`, `V_Z`, `V_{R_X}`, and `V_{R_Z}` from
blueprint `def:pauli-question-distribution`, paper
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

-- source: MIPStarRE/QPBT/Test/PauliBasisTest.lean:243-260  (MIPStarRE.QPBT.pauliCL)
/-- The conditionally linear map attached to each Pauli question type.  The
point and line maps are the corresponding
low-degree maps embedded in the selected basis block; Pair, Magic Square, and
Pair/W types use the shared projection; Pauli/W is the zero-level map.  This
is the direct finite-space form of blueprint
`def:pauli-question-distribution`, paper origin
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

-- source: MIPStarRE/QPBT/Test/PauliBasisTest.lean:402-428  (MIPStarRE.QPBT.pauliEdges)
/-- A finite edge set for the typed Pauli question graph.  The self-loops and
the displayed type-incidence families are the graph used by the sampler in
blueprint `def:pauli-question-distribution`, paper origin
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

-- source: MIPStarRE/QPBT/Test/PauliBasisTest.lean:430-434  (MIPStarRE.QPBT.PauliQuestion)
/-- A Pauli question is a type together with a full ambient coefficient vector
(blueprint `def:pauli-question-distribution`; paper
origin `references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:964-1120`).
-/
abbrev PauliQuestion (P : AdmissibleParams) := PauliType × PauliSpace P

-- source: MIPStarRE/QPBT/Test/PauliBasisTest.lean:436-441  (MIPStarRE.QPBT.pauliQuestion)
/-- The Pauli question carrying no additional coefficient data, as in
blueprint `def:pauli-win-predicate`, paper origin
`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:1006-1008`.
Its ambient coefficient vector is zero. -/
def pauliQuestion (P : AdmissibleParams) (W : PauliKind) : PauliQuestion P :=
  (.pauli W, 0)

-- source: MIPStarRE/QPBT/Test/PauliBasisTest.lean:443-450  (MIPStarRE.QPBT.PauliEdge)
/-- The ordered-edge subtype used by the Pauli question sampler.  This is
the finite carrier underlying `graphDistribution pauliEdges`, used to state
`def:pauli-question-distribution`, blueprint
`ch13_qpbt_test.tex`, paper origin
`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:964-1120`.
-/
abbrev PauliEdge :=
  {e : PauliType × PauliType // Sym2.mk e.1 e.2 ∈ pauliEdges}

-- source: MIPStarRE/QPBT/Test/PauliBasisTest.lean:452-459  (MIPStarRE.QPBT.pauliEdge_nonempty)
/-- The Pauli graph has a loop, so its ordered-edge subtype is nonempty.  This
is a finite-carrier fact used only to instantiate the uniform source sampler
for `def:pauli-question-distribution`; the graph itself is the source-facing
object `pauliEdges` above (same blueprint and paper references).
-/
theorem pauliEdge_nonempty : Nonempty PauliEdge := by
  refine ⟨⟨(.point .X, .point .X), ?_⟩⟩
  simp [pauliEdges]

-- source: MIPStarRE/QPBT/Test/PauliBasisTest.lean:461-475  (MIPStarRE.QPBT.pauliQuestionDistribution)
/-- The Pauli question distribution from blueprint
`def:pauli-question-distribution`, paper origin
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

-- source: MIPStarRE/QPBT/Test/PauliBasisTest.lean:477-489  (MIPStarRE.QPBT.PauliAnswer)
/-- The finite answer alphabet for the Pauli basis test.  Its constructors are
the seven answer forms in blueprint `def:pauli-win-predicate`,
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

-- source: MIPStarRE/QPBT/Test/PauliBasisTest.lean:498-508  (MIPStarRE.QPBT.PauliAnswerCode)
/-- A finite sum code used only to construct the `Fintype` instance for the
answer alphabet in blueprint
`def:pauli-win-predicate`, paper origin
`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:1126-1225`.
-/
abbrev PauliAnswerCode (P : AdmissibleParams) :=
  PauliScalar P ⊕
    ((Fin (P.d + 1) → PauliScalar P) ⊕
      ((Fin (P.m * P.d + 1) → PauliScalar P) ⊕
        ((ZMod 2 × ZMod 2) ⊕
          (ZMod 2 ⊕ ((Fin 3 → ZMod 2) ⊕ PauliRegister P)))))

-- source: MIPStarRE/QPBT/Test/PauliBasisTest.lean:510-555  (MIPStarRE.QPBT.pauliAnswerEquiv)
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

-- source: MIPStarRE/QPBT/Test/PauliBasisTest.lean:557-558  (MIPStarRE.QPBT.instFintypePauliAnswer)
noncomputable instance (P : AdmissibleParams) : Fintype (PauliAnswer P) :=
  Fintype.ofEquiv (PauliAnswerCode P) (pauliAnswerEquiv P).symm

-- source: MIPStarRE/QPBT/Test/PauliBasisTest.lean:563-573  (MIPStarRE.QPBT.gammaValue)
/-- The phase bit `γ(u_X,u_Z,r_X,r_Z)` from `eq:gamma-value`.  It uses the
fixed trace selected by `P.model`, as required by the paper's fixed
self-dual-normal representation.  Blueprint
`eq:gamma-value`; paper origin
`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:1198-1212`.
-/
noncomputable def gammaValue (P : AdmissibleParams)
    (uX uZ : Fin P.m → PauliScalar P)
    (rX rZ : PauliScalar P) : ZMod 2 :=
  fixedBinTrace P.model
    (dotProduct (rX • indicatorVec uX) (rZ • indicatorVec uZ))

-- source: MIPStarRE/QPBT/Test/PauliBasisTest.lean:575-582  (MIPStarRE.QPBT.pauliPairGamma)
/-- The commutation bit attached to a full Pauli ambient question, from
`eq:gamma-value` in blueprint
`def:pauli-win-predicate`, paper origin
`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:1198-1212`.
-/
noncomputable def pauliPairGamma (P : AdmissibleParams) (z : PauliSpace P) : ZMod 2 :=
  gammaValue P (pauliXBlock z) (pauliZBlock z)
    (pauliRXBlock z) (pauliRZBlock z)

-- source: MIPStarRE/QPBT/Test/PauliBasisTest.lean:584-599  (MIPStarRE.QPBT.validPauliAnswer)
/-- The answer constructor prescribed by each Pauli question type; this is the
well-formedness part of blueprint
`def:pauli-win-predicate`, paper origin
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

-- source: MIPStarRE/QPBT/Test/PauliBasisTest.lean:601-613  (MIPStarRE.QPBT.pauliAlinePointCondition)
/-- The axis-line versus point relation used by blueprint
`def:pauli-win-predicate`, paper origin
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

-- source: MIPStarRE/QPBT/Test/PauliBasisTest.lean:615-625  (MIPStarRE.QPBT.pauliDlinePointCondition)
/-- The diagonal-line versus point relation used by blueprint
`def:pauli-win-predicate`, paper origin
`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:1126-1225`.
-/
def pauliDlinePointCondition (P : AdmissibleParams) (W : PauliKind)
    (line point : PauliSpace P) (f : Fin (P.m * P.d + 1) → PauliScalar P)
    (a : PauliScalar P) : Prop :=
  ∀ t : PauliScalar P,
    pauliPointBlock W point = pauliPointBlock W line +
        t • pauliDirectionBlock line →
      evalCoefficient f t = a

-- source: MIPStarRE/QPBT/Test/PauliBasisTest.lean:627-633  (MIPStarRE.QPBT.pauliPointPauliCondition)
/-- The raw Pauli-versus-point consistency relation from blueprint
`def:pauli-win-predicate`, paper origin
`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:1126-1225`.
-/
def pauliPointPauliCondition (P : AdmissibleParams) (W : PauliKind)
    (point : PauliSpace P) (h : PauliRegister P) (a : PauliScalar P) : Prop :=
  lowDegreeEnc h (pauliPointBlock W point) = a

-- source: MIPStarRE/QPBT/Test/PauliBasisTest.lean:635-644  (MIPStarRE.QPBT.pauliPairCondition)
/-- The Pair/W consistency relation, including the one-sided gamma gate, from
blueprint `def:pauli-win-predicate`, paper origin
`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:1126-1225`.
-/
def pauliPairCondition (P : AdmissibleParams) (W : PauliKind)
    (z : PauliSpace P) (β : ZMod 2) (bits : ZMod 2 × ZMod 2) : Prop :=
  pauliPairGamma P z ≠ 0 ∨
    (match W with
    | .X => bits.1 = β
    | .Z => bits.2 = β)

-- source: MIPStarRE/QPBT/Test/PauliBasisTest.lean:646-656  (MIPStarRE.QPBT.pauliPointPairCondition)
/-- The point/Pair/W trace consistency relation from blueprint
`def:pauli-win-predicate`, paper origin
`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:1126-1225`.
-/
def pauliPointPairCondition (P : AdmissibleParams) (W : PauliKind)
    (z : PauliSpace P) (a : PauliScalar P) (β : ZMod 2) : Prop :=
  pauliPairGamma P z ≠ 0 ∨
    fixedBinTrace P.model
      (a * (match W with
      | .X => pauliRXBlock z
      | .Z => pauliRZBlock z)) = β

-- source: MIPStarRE/QPBT/Test/PauliBasisTest.lean:658-670  (MIPStarRE.QPBT.pauliPointVariableCondition)
/-- The Point/Variable consistency clause of `def:pauli-win-predicate`.
The check is gated by `gamma = 0` and only uses Variable 1 in the X basis or
Variable 5 in the Z basis.  Blueprint
`def:pauli-win-predicate`; paper origin
`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:1126-1225`.
-/
def pauliPointVariableCondition (P : AdmissibleParams) (W : PauliKind)
    (z : PauliSpace P) (j : Fin 9) (a : PauliScalar P) (β : ZMod 2) : Prop :=
  pauliPairGamma P z = 0 ∨
    (j = ⟨0, by decide⟩ ∧ W = .X ∧
        fixedBinTrace P.model (a * pauliRXBlock z) = β) ∨
    (j = ⟨4, by decide⟩ ∧ W = .Z ∧
        fixedBinTrace P.model (a * pauliRZBlock z) = β)

-- source: MIPStarRE/QPBT/Test/PauliBasisTest.lean:672-720  (MIPStarRE.QPBT.pauliWinPredicate)
/-- The Pauli win predicate, with constructor-shape rejection.  This is
blueprint `def:pauli-win-predicate`,
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

-- source: MIPStarRE/QPBT/Test/PauliBasisTest.lean:722-739  (MIPStarRE.QPBT.pauliBasisTest)
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
end  -- module scope
end MIPStarRE.QPBT
