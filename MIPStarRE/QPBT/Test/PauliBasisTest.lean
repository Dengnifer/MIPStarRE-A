import MIPStarRE.QPBT.Algebra.LowDegreeCode
import MIPStarRE.QPBT.Algebra.Pauli
import MIPStarRE.QPBT.Test.LowDegreeGame
import MIPStarRE.QPBT.Test.MagicSquare

/-!
# The Pauli basis test

This file supplies the finite question and answer alphabets, the typed
conditionally-linear question sampler, and the Boolean win predicate for the
Pauli basis test.  The quantitative soundness theorem is isolated in
`Soundness.lean`.

## References

The source-facing nodes are blueprint `def:admissible`,
`def:pauli-question-distribution`, and `def:pauli-win-predicate`; their paper origin is
`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:908-1225`.
-/

open scoped BigOperators

namespace MIPStarRE.QPBT

open MIPStarRE.LDT

noncomputable section

/-- The numerical admissible Pauli-test parameter package.  Its scalar carrier
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

/-- The positivity of the ambient dimension is a proof obligation implicit in
the admissibility convention blueprint
`def:admissible`, paper origin
`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:958-961`.
-/
theorem AdmissibleParams.one_le_m (P : AdmissibleParams) : 1 ≤ P.m := by
  sorry

/-- The fixed model accessor for an admissible parameter package.  It is a
compatibility view of the global `fixedFieldModel` selector, not an independently
quantified field representation.  Blueprint `def:admissible`; paper
origin `references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:958-961`.
-/
noncomputable def AdmissibleParams.model (P : AdmissibleParams) : FixedFieldModel P.q :=
  fixedFieldModel P.q P.hq

/-- The low-degree parameter view of an admissible Pauli-test package.  This is
a Lean-only bridge supporting the statement closure; it is not an additional
hypothesis of `thm:pauli`.  Blueprint
`def:ld-game`, paper origin
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

/-- The scalar carrier associated with an admissible parameter package.  It is
the globally fixed field carrier selected by `AdmissibleParams.model` in
blueprint
`def:admissible`, paper origin
`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:958-961`.
-/
abbrev PauliScalar (P : AdmissibleParams) := P.model.K

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

/-- The register blocks used by the Pauli question space.  These are the
coordinates displayed in blueprint
`def:pauli-question-distribution`, paper origin
`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:964-1120`.
-/
abbrev PauliIndex (P : AdmissibleParams) :=
  (((((Fin P.m ⊕ Fin P.m) ⊕ Unit) ⊕ Fin P.m) ⊕ Unit) ⊕ Unit)

/-- The ambient Pauli question coefficient space (blueprint
`def:pauli-question-distribution`; paper origin
`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:964-1120`).
-/
abbrev PauliSpace (P : AdmissibleParams) := PauliIndex P → PauliScalar P

/-- The coefficient register indexed by the Boolean cube in
blueprint `def:generalized-pauli`, paper origin
`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:908-945`.
-/
abbrev PauliRegister (P : AdmissibleParams) := Cube P.m → PauliScalar P

/- The nested sum is the fixed register order
`V_X ⊕ V_Z ⊕ V_I ⊕ V_V ⊕ V_{R_X} ⊕ V_{R_Z}` from the blueprint. -/
/-- The `V_X` block of an ambient Pauli vector (blueprint
`def:pauli-question-distribution`; paper origin
`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:964-1120`). -/
def pauliXBlock {P : AdmissibleParams} (z : PauliSpace P) : Fin P.m → PauliScalar P :=
  fun i => z (.inl (.inl (.inl (.inl (.inl i)))))

/-- The `V_Z` block of an ambient Pauli vector in blueprint
`def:pauli-question-distribution`, paper origin
`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:964-1120`.
-/
def pauliZBlock {P : AdmissibleParams} (z : PauliSpace P) : Fin P.m → PauliScalar P :=
  fun i => z (.inl (.inl (.inl (.inl (.inr i)))))

/-- The scalar block `V_I` of an ambient Pauli vector in
blueprint `def:pauli-question-distribution`,
paper origin `references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:964-1120`.
-/
def pauliScalarBlock {P : AdmissibleParams} (z : PauliSpace P) : PauliScalar P :=
  z (.inl (.inl (.inl (.inr ()))))

/-- The direction block `V_V` of an ambient Pauli vector in
blueprint `def:pauli-question-distribution`,
paper origin `references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:964-1120`.
-/
def pauliDirectionBlock {P : AdmissibleParams} (z : PauliSpace P) : Fin P.m → PauliScalar P :=
  fun i => z (.inl (.inl (.inr i)))

/-- The `r_X` scalar block in the Pauli question content from
blueprint `def:pauli-question-distribution`,
paper origin `references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:964-1120`.
-/
def pauliRXBlock {P : AdmissibleParams} (z : PauliSpace P) : PauliScalar P :=
  z (.inl (.inr ()))

/-- The `r_Z` scalar block in the Pauli question content from
blueprint `def:pauli-question-distribution`,
paper origin `references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:964-1120`.
-/
def pauliRZBlock {P : AdmissibleParams} (z : PauliSpace P) : PauliScalar P :=
  z (.inr ())

/-- Select the basis-dependent point block from a Pauli question content in
blueprint `def:pauli-question-distribution`,
paper origin `references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:964-1120`.
-/
def pauliPointBlock {P : AdmissibleParams} (W : PauliKind) (z : PauliSpace P) :
    Fin P.m → PauliScalar P :=
  match W with
  | .X => pauliXBlock z
  | .Z => pauliZBlock z

/-- Read the low-degree register selected by a basis from an ambient Pauli
vector.  Lean-only coordinate plumbing for blueprint
`def:pauli-question-distribution`, paper origin
`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:964-1120`.
-/
def pauliToLd (P : AdmissibleParams) (W : PauliKind) (z : PauliSpace P) :
    LdSpace P.toLdParams :=
  fun i => match i with
  | .inl (.inl j) => pauliPointBlock W z j
  | .inl (.inr _) => pauliScalarBlock z
  | .inr j => pauliDirectionBlock z j

/-- Embed a low-degree vector into the basis-selected Pauli blocks, clearing the
other basis and the two `r` registers.  This is Lean-only coordinate plumbing
for blueprint
`def:pauli-question-distribution`, paper origin
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

/-- The source level attached to each typed Pauli CL map.  This records the
exact levels in items 1--5 of `def:pauli-question-distribution`: point, line,
and diagonal maps have levels 1, 2, and 3, the Pauli map has level 0, and the
shared projection has level 1.  Blueprint
`def:pauli-question-distribution`; paper origin
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

/-- The typed CL dispatcher.  The point/line maps are the corresponding
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

/-- Level assertions for the typed Pauli CL maps.  These are Lean-only
proof obligations corresponding to the prose following `def:pauli-question-distribution`
(`def:pauli-question-distribution`; paper
`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:964-1120`).
Together they are the typed-family assertion required by the source statement
`lem:pauli-question-typed-cl`; the proof below is open, tracked by issue #180.
-/
theorem isCondLinear_pauliCL (P : AdmissibleParams) (t : PauliType) :
    IsCondLinearOn (PauliScalar P) Finset.univ (pauliCLLevel t) (pauliCL P t) := by
  sorry

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

/-- A Pauli question is a type together with a full ambient coefficient vector
(blueprint `def:pauli-question-distribution`; paper
origin `references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:964-1120`).
-/
abbrev PauliQuestion (P : AdmissibleParams) := PauliType × PauliSpace P

/-- The Pauli question carrying no additional coefficient data, as in
blueprint `def:pauli-win-predicate`, paper origin
`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:1006-1008`.
Its ambient coefficient vector is zero. -/
def pauliQuestion (P : AdmissibleParams) (W : PauliKind) : PauliQuestion P :=
  (.pauli W, 0)

/-- The ordered-edge subtype used by the Pauli question sampler.  This is
the finite carrier underlying `graphDistribution pauliEdges`; it is Lean-only
infrastructure for blueprint
`def:pauli-question-distribution`, paper origin
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

/-- A formalization-only total relabeling from the global Pauli-test answer
alphabet to a Pauli register. It folds wrong-form answers into zero so that a
Pauli question yields a complete `PauliRegister`-indexed measurement. -/
def pauliAnswerOrZero {P : AdmissibleParams} : PauliAnswer P → PauliRegister P
  | .pauliOutcome u => u
  | _ => 0

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

/-- The constructor-preserving finite-code equivalence for `PauliAnswer`.
Lean-only infrastructure for blueprint
`def:pauli-win-predicate`, paper origin
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
`eq:gamma-value`; paper origin
`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:1198-1212`.
-/
noncomputable def gammaValue (P : AdmissibleParams)
    (uX uZ : Fin P.m → PauliScalar P)
    (rX rZ : PauliScalar P) : ZMod 2 :=
  fixedBinTrace P.model
    (dotProduct (rX • indicatorVec uX) (rZ • indicatorVec uZ))

/-- The commutation bit attached to a full Pauli ambient question, from
`eq:gamma-value` in blueprint
`def:pauli-win-predicate`, paper origin
`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:1198-1212`.
-/
noncomputable def pauliPairGamma (P : AdmissibleParams) (z : PauliSpace P) : ZMod 2 :=
  gammaValue P (pauliXBlock z) (pauliZBlock z)
    (pauliRXBlock z) (pauliRZBlock z)

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

/-- The raw Pauli-versus-point consistency relation from blueprint
`def:pauli-win-predicate`, paper origin
`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:1126-1225`.
-/
def pauliPointPauliCondition (P : AdmissibleParams) (W : PauliKind)
    (point : PauliSpace P) (h : PauliRegister P) (a : PauliScalar P) : Prop :=
  lowDegreeEnc h (pauliPointBlock W point) = a

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

/-- The Pauli basis test game packages blueprint
`def:pauli-question-distribution` and `def:pauli-win-predicate` as a symmetric game;
paper origin
`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:964-1225`.
-/
noncomputable def pauliBasisTest (P : AdmissibleParams) : Game where
  QuestionA := PauliQuestion P
  QuestionB := PauliQuestion P
  AnswerA := PauliAnswer P
  AnswerB := PauliAnswer P
  μ := pauliQuestionDistribution P
  μ_prob := by sorry
  decide := pauliWinPredicate P

end

end MIPStarRE.QPBT
