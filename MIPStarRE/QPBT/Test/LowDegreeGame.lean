import MIPStarRE.QPBT.Algebra.FieldBasis
import MIPStarRE.QPBT.Algebra.Lines
import MIPStarRE.QPBT.Games.CondLinear
import MIPStarRE.QPBT.Games.Defs

/-!
# The low-degree game

This file introduces the finite question and answer alphabets used by the
low-degree component of the Pauli basis test.  The maps are explicit maps on
the ambient coefficient space; their conditional-linearity and distribution
invariants are recorded as proof-level obligations for later stages.

## References

The source-facing nodes are `def:ld-game`, `def:ld-question-distribution`, and
`def:ld-win-predicate` in
`blueprint/src/chapter/ch13_qpbt_test.tex:17-105`; their paper origin is
`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:31-391`.
-/

open scoped BigOperators

namespace MIPStarRE.QPBT

open MIPStarRE.LDT

noncomputable section

/-- Numerical parameters for the low-degree game.  The ambient coefficient
space uses the once-and-for-all model `fixedFieldModel P.q P.hq`, rather than a
model supplied by each parameter record.  This is the Lean carrier for
`def:ld-game` in
`blueprint/src/chapter/ch13_qpbt_test.tex:17-105`, with paper origin
`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:31-391`.
-/
structure LdParams where
  q : ℕ
  m : ℕ
  d : ℕ
  k : ℕ
  hm : 1 ≤ m
  hd : 1 ≤ d
  hk : 1 ≤ k
  hq : IsAdmissibleSize q
  hdvd : m ∣ q

/-- The positive dimension in `LdParams` supplies the finite coordinate type
used by the uniform axis and prefix-index marginals. -/
instance (L : LdParams) : Nonempty (Fin L.m) :=
  ⟨⟨0, lt_of_lt_of_le Nat.zero_lt_one L.hm⟩⟩

/-- The fixed model accessor for an `LdParams` record.  It is a compatibility
view of the global `fixedFieldModel` selector, not an independently quantified
parameter.  Blueprint `ch13_qpbt_test.tex:17-31`; paper origin
`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:31-391`.
-/
noncomputable def LdParams.model (P : LdParams) : FixedFieldModel P.q :=
  fixedFieldModel P.q P.hq

/-- The scalar carrier selected by an `LdParams` record; this is the fixed
field carrier in `def:ld-game`, selected globally by `LdParams.model`.
Blueprint `ch13_qpbt_test.tex:17-31`, paper origin
`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:31-391`.
-/
abbrev ScalarQ (P : LdParams) := (P.model).K

/-- The three low-degree question types of `def:ld-game`, blueprint
`blueprint/src/chapter/ch13_qpbt_test.tex:17-31`, paper origin
`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:31-391`.
-/
inductive LdType where
  | point
  | aline
  | dline
  deriving DecidableEq, Repr, Inhabited, Fintype

/-- The register index used by the low-degree game (`def:ld-game`, blueprint
`ch13_qpbt_test.tex:17-31`; paper origin
`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:31-391`).
-/
abbrev LdIndex (P : LdParams) := (Fin P.m ⊕ Unit) ⊕ Fin P.m

/-- The full ambient low-degree coefficient space (`def:ld-game`, blueprint
`ch13_qpbt_test.tex:17-31`; paper origin
`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:31-391`).
-/
abbrev LdSpace (P : LdParams) := LdIndex P → ScalarQ P

/-- The point coordinates of an ambient low-degree vector in
`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:31-391`.
-/
def LdSpace.point {P : LdParams} (z : LdSpace P) : Fin P.m → ScalarQ P :=
  fun i => z (.inl (.inl i))

/-- The shared scalar coordinate of an ambient low-degree vector in
`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:31-391`.
-/
def LdSpace.seed {P : LdParams} (z : LdSpace P) : ScalarQ P :=
  z (.inl (.inr ()) )

/-- The direction coordinates of an ambient low-degree vector in
`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:31-391`.
-/
def LdSpace.direction {P : LdParams} (z : LdSpace P) : Fin P.m → ScalarQ P :=
  fun i => z (.inr i)

/-- The integer-coordinate map `χ` from the fixed field representation.  This
is `eq:chi-func` in `def:ld-question-distribution`, blueprint
`blueprint/src/chapter/ch13_qpbt_test.tex:38-49`, paper origin
`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:31-391`.
-/
noncomputable def chiIndex (P : LdParams) (s : ScalarQ P) : Fin P.m := by
  letI : NeZero P.m := ⟨by
    exact Nat.ne_of_gt (lt_of_lt_of_le Nat.zero_lt_one P.hm)⟩
  exact Fin.ofNat P.m ((binaryRepresentation P.model s).val / (P.q / P.m))

/-- The projection used in the diagonal-line map zeroes coordinates before the
chosen index and retains the suffix of the direction vector.  This is the
prefix restriction in `def:ld-question-distribution`, blueprint
`blueprint/src/chapter/ch13_qpbt_test.tex:38-49`, paper origin
`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:31-391`.
-/
def prefixProjection {P : LdParams} (i : Fin P.m) (v : Fin P.m → ScalarQ P) :
    Fin P.m → ScalarQ P :=
  fun j => if j.val < i.val then 0 else v j

/-- The point CL map, retaining the point block and clearing the auxiliary
blocks.  It is the map `L_point` of `def:ld-question-distribution`, blueprint
`blueprint/src/chapter/ch13_qpbt_test.tex:38-49`, paper origin
`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:31-391`.
-/
def ldPointCL (P : LdParams) (z : LdSpace P) : LdSpace P :=
  fun i => match i with
  | .inl (.inl j) => z (.inl (.inl j))
  | .inl (.inr _) => 0
  | .inr _ => 0

/-- The affine-line CL map.  The direction block is put through the canonical
line representative map from `def:line-representative`, while the point block
is retained (blueprint `blueprint/src/chapter/ch13_qpbt_test.tex:38-49`; paper
origin `references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:31-391`).
-/
noncomputable def ldALineCL (P : LdParams) (z : LdSpace P) : LdSpace P :=
  let i := chiIndex P (z.seed)
  let rep := lineRepMap (coordinateDirection i)
  fun i => match i with
  | .inl (.inl j) => (rep (z.point)) j
  | .inl (.inr _) => z (.inl (.inr ()))
  | .inr _ => 0

/-- The diagonal-line CL map, using the same canonical representative interface
for the direction block.  This is the `L_DLine` clause of
`def:ld-question-distribution` (blueprint
`blueprint/src/chapter/ch13_qpbt_test.tex:38-49`; paper origin
`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:31-391`).
-/
noncomputable def ldDLineCL (P : LdParams) (z : LdSpace P) : LdSpace P :=
  let i := chiIndex P (z.seed)
  let direction := prefixProjection i (z.direction)
  let rep := lineRepMap direction
  fun i => match i with
  | .inl (.inl j) => (rep (z.point)) j
  | .inl (.inr _) => z (.inl (.inr ()))
  | .inr j => direction j

/-- Dispatch the three low-degree CL maps by question type.  This is the typed
construction in `def:ld-question-distribution`, blueprint
`blueprint/src/chapter/ch13_qpbt_test.tex:38-49`, paper origin
`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:31-391`.
-/
noncomputable def ldCL (P : LdParams) : LdType → LdSpace P → LdSpace P
  | .point => ldPointCL P
  | .aline => ldALineCL P
  | .dline => ldDLineCL P

/-- The conditional-linearity level of the affine-line map.  This is a named
Lean proof obligation for the prose assertion in `def:ld-question-distribution`,
blueprint `blueprint/src/chapter/ch13_qpbt_test.tex:38-49`, paper
`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:31-391`.
-/
theorem isCondLinear_ldALineCL (P : LdParams) :
    IsCondLinearOn (ScalarQ P) Finset.univ 2 (ldALineCL P) := by
  sorry

/-- The conditional-linearity level of the diagonal-line map.  This is the
level-3 assertion in `def:ld-question-distribution`, blueprint
`blueprint/src/chapter/ch13_qpbt_test.tex:38-49`, paper origin
`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:31-391`.
-/
theorem isCondLinear_ldDLineCL (P : LdParams) :
    IsCondLinearOn (ScalarQ P) Finset.univ 3 (ldDLineCL P) := by
  sorry

/-- The question alphabet for the low-degree game (`def:ld-game`, blueprint
`ch13_qpbt_test.tex:17-31`; paper origin
`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:31-391`).
-/
abbrev LdQuestion (P : LdParams) := LdType × LdSpace P

/-- The typed CL question distribution.  This is the inlined construction in
`def:ld-question-distribution`, blueprint `ch13_qpbt_test.tex:38-49`; paper
origin `references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:31-391`.
-/
noncomputable def ldQuestionDistribution (P : LdParams) :
    Distribution (LdQuestion P × LdQuestion P) :=
  Distribution.map
    (uniformDistribution ((LdType × LdType) × LdSpace P))
    (fun s =>
      ((s.1.1, ldCL P s.1.1 s.2), (s.1.2, ldCL P s.1.2 s.2)))

/-- The coefficient-tuple answer alphabet of the low-degree game.  Polynomial
answers are representatives with exactly the coefficient lengths printed in
the paper, as required by `def:ld-win-predicate` (blueprint
`blueprint/src/chapter/ch13_qpbt_test.tex:56-105`; paper
`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:31-391`).
-/
inductive LdAnswer (P : LdParams) where
  | pointVals (a : Fin P.k → ScalarQ P)
  | alinePolys (a : Fin P.k → Fin (P.d + 1) → ScalarQ P)
  | dlinePolys (a : Fin P.k → Fin (P.m * P.d + 1) → ScalarQ P)
  deriving DecidableEq

/-- A finite sum code used only to provide the answer alphabet's `Fintype`
instance; the public constructors are those of `def:ld-win-predicate`,
blueprint `ch13_qpbt_test.tex:56-105`, paper origin
`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:31-391`.
-/
abbrev LdAnswerCode (P : LdParams) :=
  (Fin P.k → ScalarQ P) ⊕
    ((Fin P.k → Fin (P.d + 1) → ScalarQ P) ⊕
      (Fin P.k → Fin (P.m * P.d + 1) → ScalarQ P))

/-- The constructor-preserving code equivalence for `LdAnswer` (Lean-only
finite-carrier infrastructure for `def:ld-win-predicate`, blueprint
`blueprint/src/chapter/ch13_qpbt_test.tex:56-105`, paper origin
`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:31-391`).
-/
noncomputable def ldAnswerEquiv (P : LdParams) :
    LdAnswer P ≃ LdAnswerCode P where
  toFun
    | .pointVals a => .inl a
    | .alinePolys a => .inr (.inl a)
    | .dlinePolys a => .inr (.inr a)
  invFun
    | .inl a => .pointVals a
    | .inr (.inl a) => .alinePolys a
    | .inr (.inr a) => .dlinePolys a
  left_inv := by intro x; cases x <;> rfl
  right_inv := by
    intro x
    cases x with
    | inl a => rfl
    | inr x =>
        cases x with
        | inl a => rfl
        | inr a => rfl

instance (P : LdParams) : Inhabited (LdAnswer P) :=
  ⟨.pointVals (fun _ => 0)⟩

noncomputable instance (P : LdParams) : Fintype (LdAnswer P) :=
  Fintype.ofEquiv (LdAnswerCode P) (ldAnswerEquiv P).symm

/-- Evaluation of a coefficient tuple at a field element.  This is the
representative convention used by the line answers in `def:ld-win-predicate`,
blueprint `blueprint/src/chapter/ch13_qpbt_test.tex:56-105`, paper origin
`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:31-391`.
-/
def evalCoefficient {K : Type*} [Semiring K] {n : ℕ}
    (c : Fin n → K) (t : K) : K :=
  ∑ i : Fin n, c i * t ^ i.val

/-- Check that an answer has the constructor prescribed by its question type;
Lean encoding of the rejection clause in `def:ld-win-predicate`, blueprint
`ch13_qpbt_test.tex:56-105`, paper origin
`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:31-391`.
-/
def validLdAnswer {P : LdParams} (t : LdType) (a : LdAnswer P) : Bool :=
  match t, a with
  | .point, .pointVals _ => true
  | .aline, .alinePolys _ => true
  | .dline, .dlinePolys _ => true
  | _, _ => false

/-- The axis-parallel line/point relation in `def:ld-win-predicate`, blueprint
`ch13_qpbt_test.tex:56-105`, paper origin
`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:31-391`.
-/
def alinePointCondition (P : LdParams) (line point : LdSpace P)
    (f : Fin P.k → Fin (P.d + 1) → ScalarQ P)
    (a : Fin P.k → ScalarQ P) : Prop :=
  -- Universal quantification follows the zero-direction convention in
  -- `rem:ld-win-zero-direction`.
  ∀ t : ScalarQ P,
    point.point = line.point + t • coordinateDirection (chiIndex P line.seed) →
      ∀ j : Fin P.k, evalCoefficient (f j) t = a j

/-- The diagonal line/point relation in `def:ld-win-predicate`, blueprint
`ch13_qpbt_test.tex:56-105`, paper origin
`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:31-391`.
-/
def dlinePointCondition (P : LdParams) (line point : LdSpace P)
    (f : Fin P.k → Fin (P.m * P.d + 1) → ScalarQ P)
    (a : Fin P.k → ScalarQ P) : Prop :=
  ∀ t : ScalarQ P,
    point.point = line.point + t • line.direction →
      ∀ j : Fin P.k, evalCoefficient (f j) t = a j

/-- The low-degree consistency predicate, rejecting answers of the wrong
constructor shape.  This is `def:ld-win-predicate` in
`blueprint/src/chapter/ch13_qpbt_test.tex:56-105`, paper origin
`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:31-391`.
-/
noncomputable def ldWinPredicate (P : LdParams) :
    LdQuestion P → LdQuestion P → LdAnswer P → LdAnswer P → Bool :=
  open Classical in
  fun (tA, xA) (tB, xB) a b =>
      if validLdAnswer tA a && validLdAnswer tB b then
        match tA, tB, a, b with
        | .point, .point, .pointVals u, .pointVals v => decide (u = v)
        | .aline, .point, .alinePolys f, .pointVals u =>
            decide (alinePointCondition P xA xB f u)
        | .point, .aline, .pointVals u, .alinePolys f =>
            decide (alinePointCondition P xB xA f u)
        | .dline, .point, .dlinePolys f, .pointVals u =>
            decide (dlinePointCondition P xA xB f u)
        | .point, .dline, .pointVals u, .dlinePolys f =>
            decide (dlinePointCondition P xB xA f u)
        | .aline, .aline, .alinePolys f, .alinePolys g => decide (f = g)
        | .dline, .dline, .dlinePolys f, .dlinePolys g => decide (f = g)
        | _, _, _, _ => true
      else false

/-- The low-degree game packaged as a `Game`.  This is `def:ld-game` in
`blueprint/src/chapter/ch13_qpbt_test.tex:17-105`, paper origin
`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:31-391`.
-/
noncomputable def ldGame (P : LdParams) : Game where
  QuestionA := LdQuestion P
  QuestionB := LdQuestion P
  AnswerA := LdAnswer P
  AnswerB := LdAnswer P
  μ := ldQuestionDistribution P
  μ_prob := by sorry
  decide := ldWinPredicate P

end

end MIPStarRE.QPBT
