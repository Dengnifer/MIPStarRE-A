import MIPStarRE.QPBT.Test.LowDegreeGameTheorems
import MIPStarRE.QPBT.Test.PauliBasisTest

/-!
# The directly indexed low-degree game

The low-degree game used by the Pauli-basis combining argument is needed in
dimension `2 * m + 2`.  The existing conditionally linear game represents a
coordinate index by an equally sized fiber in the scalar field and therefore
requires the dimension to divide the field size.  This file gives the separate
analysis-only variant which samples that index directly.

The geometric line carrier records the sampled coordinate, and line evaluation
uses an `Option` outcome rather than assigning a value when a point does not
determine one.  The game retains the point, axis-line, and diagonal-line answer
formats and the nine ordered type branches of the original low-degree game.

## References

The underlying game is `def:ld-game` in
`blueprint/src/chapter/ch13_qpbt_test.tex:17-105`, with source origin
`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:31-391`.
The need for the directly indexed repair in Chapter 15 is explained around
`rem:qld-4-7-divisibility` in
`blueprint/src/chapter/ch15_qpbt_combining.tex:1257-1293` and in
`docs/paper-gaps/qpbt_ld-dimension-divisibility.tex`.
-/

open scoped BigOperators

namespace MIPStarRE.QPBT

open MIPStarRE.LDT
open MIPStarRE.LDT.Preliminaries
open MIPStarRE.Quantum

noncomputable section

/-- Parameters for the directly indexed low-degree game.  Unlike `LdParams`,
this analysis-only carrier has no divisibility field: its coordinate index is
sampled from `Fin m` rather than encoded by fibers of `chiIndex`.

This is the direct-index repair described in
`docs/paper-gaps/qpbt_ld-dimension-divisibility.tex`; it is not a second
definition of the source verifier game. -/
structure DirectLdParams where
  q : ℕ
  m : ℕ
  d : ℕ
  k : ℕ
  hm : 1 ≤ m
  hd : 1 ≤ d
  hk : 1 ≤ k
  hq : IsAdmissibleSize q

/-- The canonical scalar model for directly indexed parameters. -/
noncomputable def DirectLdParams.model (D : DirectLdParams) : FixedFieldModel D.q :=
  fixedFieldModel D.q D.hq

/-- The scalar field of a directly indexed low-degree game. -/
abbrev DirectScalarQ (D : DirectLdParams) := D.model.K

/-- The first coordinate, available because directly indexed dimensions are
positive. -/
def DirectLdParams.firstIndex (D : DirectLdParams) : Fin D.m :=
  ⟨0, lt_of_lt_of_le Nat.zero_lt_one D.hm⟩

instance (D : DirectLdParams) : Nonempty (Fin D.m) := ⟨D.firstIndex⟩

/-- The direct game used at the extended dimension of the combining map.  Its
field, degree, and simultaneity parameters are inherited from `P`, while its
dimension is `2 * P.m + 2`; no divisibility assertion is introduced.

This is Lean-only infrastructure for the repair of
`rem:qld-4-7-divisibility`, blueprint
`blueprint/src/chapter/ch15_qpbt_combining.tex:1257-1293`, paper context
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1020-1116`.
-/
def AdmissibleParams.extendedDirectLd (P : AdmissibleParams) : DirectLdParams where
  q := P.q
  m := 2 * P.m + 2
  d := P.d
  k := 1
  hm := by omega
  hd := P.hd
  hk := by decide
  hq := P.hq

/-- A common random sample for the directly indexed question distribution.
The point, coordinate index, and unrestricted direction are mutually uniform. -/
structure DirectLdSpace (D : DirectLdParams) where
  point : Fin D.m → DirectScalarQ D
  index : Fin D.m
  direction : Fin D.m → DirectScalarQ D
  deriving DecidableEq, Fintype

instance (D : DirectLdParams) : Nonempty (DirectLdSpace D) :=
  ⟨⟨0, D.firstIndex, 0⟩⟩

/-- Zero the coordinates preceding the directly sampled prefix index. -/
def directPrefixProjection {D : DirectLdParams} (i : Fin D.m)
    (v : Fin D.m → DirectScalarQ D) : Fin D.m → DirectScalarQ D :=
  fun j => if j.val < i.val then 0 else v j

/-- Canonical line descriptions whose coordinate index is stored directly.
Coordinates are numbered from zero, so `index = i` represents coordinate
`i + 1` in the paper. -/
inductive DirectLineDesc (D : DirectLdParams) where
  | axis (base : Fin D.m → DirectScalarQ D) (index : Fin D.m)
      (baseFixed : lineRepMap (coordinateDirection index) base = base)
  | diagonal (base : Fin D.m → DirectScalarQ D) (index : Fin D.m)
      (direction : Fin D.m → DirectScalarQ D)
      (baseFixed : lineRepMap direction base = base)
      (prefixZero : ∀ j : Fin D.m, j.val < index.val → direction j = 0)
  deriving DecidableEq

/-- The kind of a directly indexed line. -/
def DirectLineDesc.kind {D : DirectLdParams} : DirectLineDesc D → LineKind
  | .axis _ _ _ => .axis
  | .diagonal _ _ _ _ _ => .diagonal

/-- The coordinate index stored in a directly indexed line. -/
def DirectLineDesc.index {D : DirectLdParams} : DirectLineDesc D → Fin D.m
  | .axis _ index _ => index
  | .diagonal _ index _ _ _ => index

/-- The canonical base point of a directly indexed line. -/
def DirectLineDesc.base {D : DirectLdParams} :
    DirectLineDesc D → Fin D.m → DirectScalarQ D
  | .axis base _ _ => base
  | .diagonal base _ _ _ _ => base

/-- The geometric direction of a directly indexed line. -/
def DirectLineDesc.direction {D : DirectLdParams} (line : DirectLineDesc D) :
    Fin D.m → DirectScalarQ D :=
  match line with
  | .axis _ index _ => coordinateDirection index
  | .diagonal _ _ direction _ _ => direction

/-- The base of a directly indexed description is fixed by its geometric
direction. -/
theorem DirectLineDesc.base_fixed {D : DirectLdParams} (line : DirectLineDesc D) :
    lineRepMap line.direction line.base = line.base := by
  cases line with
  | axis base index baseFixed => exact baseFixed
  | diagonal base index direction baseFixed prefixZero => exact baseFixed

/-- Every directly indexed diagonal description retains its prefix-zero
invariant. -/
theorem DirectLineDesc.diagonal_prefix_zero {D : DirectLdParams}
    (line : DirectLineDesc D) (hline : line.kind = .diagonal) :
    ∀ j : Fin D.m, j.val < line.index.val → line.direction j = 0 := by
  cases line with
  | axis base index baseFixed => simp [DirectLineDesc.kind] at hline
  | diagonal base index direction baseFixed prefixZero => exact prefixZero

/-- The point set represented by a directly indexed line. -/
noncomputable def DirectLineDesc.pointSet {D : DirectLdParams}
    (line : DirectLineDesc D) : Set (Fin D.m → DirectScalarQ D) :=
  linePoints line.base line.direction

/-- Turn a direct sample into its canonical axis-line description. -/
noncomputable def directALineDescOf (D : DirectLdParams)
    (sample : DirectLdSpace D) : DirectLineDesc D :=
  let direction := coordinateDirection sample.index
  let base := lineRepMap direction sample.point
  .axis base sample.index (lineRepMap_apply_self direction sample.point)

/-- Turn a direct sample into its canonical diagonal-line description. -/
noncomputable def directDLineDescOf (D : DirectLdParams)
    (sample : DirectLdSpace D) : DirectLineDesc D :=
  let direction := directPrefixProjection sample.index sample.direction
  let base := lineRepMap direction sample.point
  .diagonal base sample.index direction
    (lineRepMap_apply_self direction sample.point) (by
      intro j hj
      change directPrefixProjection sample.index sample.direction j = 0
      rw [directPrefixProjection, if_pos hj])

/-- The axis-line/point law with a directly sampled coordinate index. -/
noncomputable def directALinePointDist (D : DirectLdParams) :
    Distribution (DirectLineDesc D × (Fin D.m → DirectScalarQ D)) :=
  (uniformDistribution (DirectLdSpace D)).map fun sample =>
    (directALineDescOf D sample, sample.point)

/-- The diagonal-line/point law with a directly sampled prefix index. -/
noncomputable def directDLinePointDist (D : DirectLdParams) :
    Distribution (DirectLineDesc D × (Fin D.m → DirectScalarQ D)) :=
  (uniformDistribution (DirectLdSpace D)).map fun sample =>
    (directDLineDescOf D sample, sample.point)

/-- The equal mixture of the directly indexed axis and diagonal line-point
laws.  This is the replacement for the otherwise undefined extended-dimension
instance used at paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1020-1116`. -/
noncomputable def directLinePointDist (D : DirectLdParams) :
    Distribution (DirectLineDesc D × (Fin D.m → DirectScalarQ D)) :=
  Distribution.mix (1 / 2) (by norm_num) (by norm_num)
    (directALinePointDist D) (directDLinePointDist D)

/-- The directly indexed axis-line/point law is probabilistic. -/
theorem directALinePointDist_isProbability (D : DirectLdParams) :
    (directALinePointDist D).IsProbability := by
  exact (uniformDistribution_isProbability (DirectLdSpace D)).map _

/-- The directly indexed diagonal-line/point law is probabilistic. -/
theorem directDLinePointDist_isProbability (D : DirectLdParams) :
    (directDLinePointDist D).IsProbability := by
  exact (uniformDistribution_isProbability (DirectLdSpace D)).map _

/-- The directly indexed line-point mixture is probabilistic. -/
theorem directLinePointDist_isProbability (D : DirectLdParams) :
    (directLinePointDist D).IsProbability := by
  exact Distribution.mix_isProbability _ _ _
    (directALinePointDist_isProbability D) (directDLinePointDist_isProbability D)
    (by norm_num) (by norm_num)

/-- The point and stored-index marginals of the direct axis-line law are
uniform.  This is a Lean-only direct-index analogue of `lem:alnf`, required by
the repair described in `docs/paper-gaps/qpbt_ld-dimension-divisibility.tex`;
the source distribution is at
`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:243-257`.
-/
theorem directALinePointDist_point_index_marginal_uniform (D : DirectLdParams) :
    (directALinePointDist D).map Prod.snd =
        uniformDistribution (Fin D.m → DirectScalarQ D) ∧
      (directALinePointDist D).map (fun sample => sample.1.index) =
        uniformDistribution (Fin D.m) := by
  sorry

/-- Every sampled direct axis line contains its paired point.  This is the
Lean-only direct-index incidence obligation corresponding to `lem:alnf` and
the repair in `docs/paper-gaps/qpbt_ld-dimension-divisibility.tex`. -/
theorem directALinePointDist_mem_line (D : DirectLdParams) :
    ∀ sample ∈ (directALinePointDist D).support,
      sample.2 ∈ sample.1.pointSet := by
  sorry

/-- The point and stored-index marginals of the direct diagonal-line law are
uniform.  This is the direct-index analogue of `lem:dlnf`, paper
`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:261-272`,
and is a named obligation in the dimension-divisibility repair. -/
theorem directDLinePointDist_point_index_marginal_uniform (D : DirectLdParams) :
    (directDLinePointDist D).map Prod.snd =
        uniformDistribution (Fin D.m → DirectScalarQ D) ∧
      (directDLinePointDist D).map (fun sample => sample.1.index) =
        uniformDistribution (Fin D.m) := by
  sorry

/-- Every sampled direct diagonal line contains its paired point.  This is the
Lean-only direct-index incidence obligation corresponding to `lem:dlnf`. -/
theorem directDLinePointDist_mem_line (D : DirectLdParams) :
    ∀ sample ∈ (directDLinePointDist D).support,
      sample.2 ∈ sample.1.pointSet := by
  sorry

/-- A sampled direct diagonal direction vanishes below its stored prefix
index.  This is the direct counterpart of the third conclusion of
`lem:dlnf`, paper
`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:261-272`.
-/
theorem directDLinePointDist_prefix_zero (D : DirectLdParams) :
    ∀ sample ∈ (directDLinePointDist D).support,
      ∀ j : Fin D.m, j.val < sample.1.index.val →
        sample.1.direction j = 0 := by
  sorry

/-- Coefficient lists for a univariate polynomial of degree at most `c` in the
direct scalar field. -/
abbrev DirectDegPoly (D : DirectLdParams) (c : ℕ) :=
  Fin (c + 1) → DirectScalarQ D

/-- A direct line polynomial evaluates to `a` at `u` when `u` lies on the line
and every parameter presenting `u` gives value `a`.  The universal clause
keeps the zero-direction case explicit. -/
def DirectEvaluatesTo {D : DirectLdParams} {c : ℕ} (line : DirectLineDesc D)
    (f : DirectDegPoly D c) (u : Fin D.m → DirectScalarQ D)
    (a : DirectScalarQ D) : Prop :=
  (∃ t : DirectScalarQ D, u = line.base + t • line.direction) ∧
    ∀ t : DirectScalarQ D, u = line.base + t • line.direction →
      evalCoefficient f t = a

/-- Option-completed evaluation of a direct line polynomial.  `none` is an
explicit outcome when the point does not determine an evaluation; no field
value is used as a fallback. -/
noncomputable def directEvalOpt {D : DirectLdParams} {c : ℕ}
    (line : DirectLineDesc D) (u : Fin D.m → DirectScalarQ D)
    (f : DirectDegPoly D c) : Option (DirectScalarQ D) := by
  classical
  exact if h : ∃ a : DirectScalarQ D, DirectEvaluatesTo line f u a then
    some (Classical.choose h)
  else none

/-- The typed question alphabet of the directly indexed game. -/
abbrev DirectLdQuestion (D : DirectLdParams) := LdType × DirectLdSpace D

/-- Canonicalize a common direct sample for one question type.  Irrelevant
coordinates are fixed, so point questions reveal no sampled line index and
axis-line questions reveal no diagonal direction. -/
noncomputable def directLdMap (D : DirectLdParams) :
    LdType → DirectLdSpace D → DirectLdSpace D
  | .point, sample => ⟨sample.point, D.firstIndex, 0⟩
  | .aline, sample =>
      let direction := coordinateDirection sample.index
      ⟨lineRepMap direction sample.point, sample.index, 0⟩
  | .dline, sample =>
      let direction := directPrefixProjection sample.index sample.direction
      ⟨lineRepMap direction sample.point, sample.index, direction⟩

/-- The directly indexed question distribution.  It has the same uniform
ordered type-pair branches as `ldQuestionDistribution`, but its common sample
contains an actual coordinate index rather than a field seed. -/
noncomputable def directLdQuestionDistribution (D : DirectLdParams) :
    Distribution (DirectLdQuestion D × DirectLdQuestion D) :=
  (uniformDistribution ((LdType × LdType) × DirectLdSpace D)).map fun sample =>
    ((sample.1.1, directLdMap D sample.1.1 sample.2),
      (sample.1.2, directLdMap D sample.1.2 sample.2))

/-- The directly indexed question law is probabilistic. -/
theorem directLdQuestionDistribution_isProbability (D : DirectLdParams) :
    (directLdQuestionDistribution D).IsProbability := by
  exact (uniformDistribution_isProbability
    ((LdType × LdType) × DirectLdSpace D)).map _

/-- The answer alphabet of the directly indexed game. -/
inductive DirectLdAnswer (D : DirectLdParams) where
  | pointVals (a : Fin D.k → DirectScalarQ D)
  | alinePolys (a : Fin D.k → Fin (D.d + 1) → DirectScalarQ D)
  | dlinePolys (a : Fin D.k → Fin (D.m * D.d + 1) → DirectScalarQ D)
  deriving DecidableEq

/-- A finite code for the directly indexed answer alphabet. -/
abbrev DirectLdAnswerCode (D : DirectLdParams) :=
  (Fin D.k → DirectScalarQ D) ⊕
    ((Fin D.k → Fin (D.d + 1) → DirectScalarQ D) ⊕
      (Fin D.k → Fin (D.m * D.d + 1) → DirectScalarQ D))

/-- Constructor-preserving equivalence used only for finite-answer
infrastructure. -/
noncomputable def directLdAnswerEquiv (D : DirectLdParams) :
    DirectLdAnswer D ≃ DirectLdAnswerCode D where
  toFun
    | .pointVals a => .inl a
    | .alinePolys a => .inr (.inl a)
    | .dlinePolys a => .inr (.inr a)
  invFun
    | .inl a => .pointVals a
    | .inr (.inl a) => .alinePolys a
    | .inr (.inr a) => .dlinePolys a
  left_inv := by intro answer; cases answer <;> rfl
  right_inv := by
    intro answer
    rcases answer with a | a
    · rfl
    · rcases a with a | a <;> rfl

instance (D : DirectLdParams) : Inhabited (DirectLdAnswer D) :=
  ⟨.pointVals 0⟩

noncomputable instance (D : DirectLdParams) : Fintype (DirectLdAnswer D) :=
  Fintype.ofEquiv (DirectLdAnswerCode D) (directLdAnswerEquiv D).symm

/-- Check that a direct-game answer has the constructor required by its
question type. -/
def validDirectLdAnswer {D : DirectLdParams} (t : LdType)
    (answer : DirectLdAnswer D) : Bool :=
  match t, answer with
  | .point, .pointVals _ => true
  | .aline, .alinePolys _ => true
  | .dline, .dlinePolys _ => true
  | _, _ => false

/-- The directly indexed axis-line versus point acceptance relation. -/
def directAlinePointCondition (D : DirectLdParams)
    (line point : DirectLdSpace D)
    (f : Fin D.k → Fin (D.d + 1) → DirectScalarQ D)
    (a : Fin D.k → DirectScalarQ D) : Prop :=
  ∀ t : DirectScalarQ D,
    point.point = line.point + t • coordinateDirection line.index →
      ∀ j : Fin D.k, evalCoefficient (f j) t = a j

/-- The directly indexed diagonal-line versus point acceptance relation. -/
def directDlinePointCondition (D : DirectLdParams)
    (line point : DirectLdSpace D)
    (f : Fin D.k → Fin (D.m * D.d + 1) → DirectScalarQ D)
    (a : Fin D.k → DirectScalarQ D) : Prop :=
  ∀ t : DirectScalarQ D,
    point.point = line.point + t • line.direction →
      ∀ j : Fin D.k, evalCoefficient (f j) t = a j

/-- The directly indexed low-degree win predicate.  It differs from
`ldWinPredicate` only by reading the coordinate index directly from each line
question. -/
noncomputable def directLdWinPredicate (D : DirectLdParams) :
    DirectLdQuestion D → DirectLdQuestion D →
      DirectLdAnswer D → DirectLdAnswer D → Bool :=
  open Classical in
  fun (tA, xA) (tB, xB) a b =>
    if validDirectLdAnswer tA a && validDirectLdAnswer tB b then
      match tA, tB, a, b with
      | .point, .point, .pointVals u, .pointVals v => decide (u = v)
      | .aline, .point, .alinePolys f, .pointVals u =>
          decide (directAlinePointCondition D xA xB f u)
      | .point, .aline, .pointVals u, .alinePolys f =>
          decide (directAlinePointCondition D xB xA f u)
      | .dline, .point, .dlinePolys f, .pointVals u =>
          decide (directDlinePointCondition D xA xB f u)
      | .point, .dline, .pointVals u, .dlinePolys f =>
          decide (directDlinePointCondition D xB xA f u)
      | .aline, .aline, .alinePolys f, .alinePolys g => decide (f = g)
      | .dline, .dline, .dlinePolys f, .dlinePolys g => decide (f = g)
      | _, _, _, _ => true
    else false

/-- The directly indexed low-degree game at an arbitrary positive dimension.
It is an internal analysis game, not the conditionally linear verifier game
`ldGame`. -/
noncomputable def directLdGame (D : DirectLdParams) : Game where
  QuestionA := DirectLdQuestion D
  QuestionB := DirectLdQuestion D
  AnswerA := DirectLdAnswer D
  AnswerB := DirectLdAnswer D
  μ := directLdQuestionDistribution D
  μ_prob := directLdQuestionDistribution_isProbability D
  decide := directLdWinPredicate D

/-- The canonical point question associated with a geometric point. -/
def directLdPointQuestionOf (D : DirectLdParams)
    (u : Fin D.m → DirectScalarQ D) : DirectLdQuestion D :=
  (.point, ⟨u, D.firstIndex, 0⟩)

/-- Total point-answer relabeling used in the direct soundness conclusion.
Wrong-form answers are folded into the zero tuple, exactly as for
`ldPointValuesOrZero`. -/
def directLdPointValuesOrZero (D : DirectLdParams) :
    DirectLdAnswer D → Fin D.k → DirectScalarQ D
  | .pointVals values => values
  | .alinePolys _ => 0
  | .dlinePolys _ => 0

/-- A simultaneous tuple of bounded polynomials for the directly indexed
game. -/
noncomputable abbrev DirectPolyTuple (D : DirectLdParams) :=
  Fin D.k → PolyIndex D.m (DirectScalarQ D) D.d

/-- A polynomial-tuple POVM for the directly indexed game. -/
noncomputable abbrev DirectPolyMeasTuple (D : DirectLdParams) (ι : Type*)
    [Fintype ι] [DecidableEq ι] :=
  Measurement (DirectPolyTuple D) ι

/-- Evaluate every component of a direct polynomial tuple at a point. -/
def evalDirectPolyTupleAt {D : DirectLdParams}
    (u : Fin D.m → DirectScalarQ D) (g : DirectPolyTuple D) :
    Fin D.k → DirectScalarQ D :=
  fun j => MvPolynomial.eval u (g j).1

/-- Quantum soundness obligation for the directly indexed low-degree game.
This is the repaired import form proposed in
`docs/paper-gaps/qpbt_ld-dimension-divisibility.tex`, needed by the Chapter 15
combining argument at paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1267-1288`.

This is a Lean-only proof obligation, not the source-labelled
`lem:ld-soundness`.  Its proof must establish the game-correspondence and
auxiliary-parameter bounds catalogued in the cited gap note; neither is hidden
as a hypothesis here. -/
theorem exists_direct_ld_soundness :
    ∃ a b : ℝ, 1 ≤ a ∧ 0 < b ∧ b ≤ 1 ∧
      ∀ (D : DirectLdParams) (ε : ℝ), 0 < ε →
        ∀ S : Strategy (directLdGame D), S.IsProjective → 1 - ε ≤ S.value →
          ∃ GA : DirectPolyMeasTuple D S.ιA,
            ∃ GB : DirectPolyMeasTuple D S.ιB,
              consistencyDefect
                  (uniformDistribution (Fin D.m → DirectScalarQ D))
                  (fun u outcome =>
                    heteroKron
                      (((S.A (directLdPointQuestionOf D u)).postprocess
                        (directLdPointValuesOrZero D)).effect outcome) 1)
                  (fun u outcome =>
                    heteroKron 1
                      ((GB.postprocess (evalDirectPolyTupleAt u)).effect outcome))
                  S.ψ ≤ deltaLd a b ε D.q D.m D.d D.k ∧
              consistencyDefect
                  (uniformDistribution (Fin D.m → DirectScalarQ D))
                  (fun u outcome =>
                    heteroKron
                      ((GA.postprocess (evalDirectPolyTupleAt u)).effect outcome) 1)
                  (fun u outcome =>
                    heteroKron 1
                      (((S.B (directLdPointQuestionOf D u)).postprocess
                        (directLdPointValuesOrZero D)).effect outcome))
                  S.ψ ≤ deltaLd a b ε D.q D.m D.d D.k ∧
              consistencyDefect (uniformDistribution Unit)
                  (fun _ g => heteroKron (GA.effect g) 1)
                  (fun _ g => heteroKron 1 (GB.effect g))
                  S.ψ ≤ deltaLd a b ε D.q D.m D.d D.k := by
  sorry

end

end MIPStarRE.QPBT
