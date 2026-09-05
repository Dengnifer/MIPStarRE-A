import MIPStarRE.QPBT.Combining.DirectLowDegree.Transport.Combining.Answers
import MIPStarRE.QPBT.Combining.DirectLowDegree.Transport.Questions
import MIPStarRE.QPBT.Games.Sandwich.Support

/-!
# The combined strategy of the simultaneity reduction

`def:ld-combined-strategy` turns a projective strategy for the directly indexed
low-degree game at parameters `D` into a projective strategy for the same game
at the combined parameters `D.combined` of `def:ld-combining-parameters`, on
the same state and the same two Hilbert spaces.  Each question of the combined
game is answered by measuring one question of the original strategy and
relabelling its outcome; the question measured and the relabelling are fixed by
the type of the combined question and by whether its stored coordinate index is
a point coordinate or a combining coordinate.

Writing a point of the combined space as `(u, α)` with `u` its point part and
`α` its combining part, the five cases are:

1. a point question at `(u, α)` measures the point question at `u` and answers
   the combined value `∑ r, α r * b r`;
2. an axis-parallel line question whose stored index is the point coordinate
   `j` measures the canonical axis-parallel line question of the original game
   at `u` with index `j`, and answers the combination `∑ r, α r * f r` of the
   measured line answers;
3. an axis-parallel line question whose stored index is a combining coordinate
   measures the point question at `u`: the line lies in the fiber of the
   projection to the point coordinates through `u`, so the combined polynomial
   restricted to it is the affine function of the parameter determined by the
   `k` values at `u`;
4. a diagonal line question whose stored index is the point coordinate `j`
   measures the canonical diagonal line question of the original game at `u`
   with index `j` and the point part of the direction, and answers
   `t ↦ ∑ r, (α r + t * w r) * f r (t + s)`;
5. a diagonal line question whose stored index is a combining coordinate
   measures the point question at `u`, its direction having vanishing point
   part, and answers as in case 3.

The affine shift `s` of cases 2 and 4 is `directCombinedRebaseParameter`, the
change of parameter between the presentation of the image line by the point
part of the combined canonical base and its presentation by its own canonical
base; the two need not agree, since the canonical base of a line of the
combined space need not project to the canonical base of its image.

Each case measures a single measurement of the original strategy and relabels
its outcome, so the combined strategy is again projective; this is
`directCombinedStrategy_isProjective`.

## Main definitions

* `directCombinedMeasuredQuestion` — the question of the original game measured
  on a question of the combined game.
* `directCombinedAnswerMap` — the relabelling of the measured outcome.
* `directCombinedStrategy` — `def:ld-combined-strategy`.

## References

* `references/neexp-paper/05_quantum_preliminaries.tex:1409-1503`
* `references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:413-458`
* `blueprint/src/chapter/ch13_qpbt_test.tex:420-472`
-/

open scoped BigOperators MatrixOrder Matrix ComplexOrder

namespace MIPStarRE.QPBT

open MIPStarRE.LDT
open MIPStarRE.LDT.Preliminaries
open MIPStarRE.Quantum

noncomputable section

/-! ## Coordinates of a combined question -/

/-- The point part of a point of the combined space, at the combined
parameters of `def:ld-combining-parameters`. -/
def directCombinedPointPart (D : DirectLdParams)
    (z : Fin D.combined.m → DirectScalarQ D) : Fin D.m → DirectScalarQ D :=
  combinedPointPart (m := D.m) (k := D.k) z

/-- The combining part of a point of the combined space. -/
def directCombinedCoefficientPart (D : DirectLdParams)
    (z : Fin D.combined.m → DirectScalarQ D) : Fin D.k → DirectScalarQ D :=
  combinedCoefficientPart (m := D.m) (k := D.k) z

@[simp] theorem directCombinedPointPart_combinedPoint (D : DirectLdParams)
    (u : Fin D.m → DirectScalarQ D) (α : Fin D.k → DirectScalarQ D) :
    directCombinedPointPart D (combinedPoint u α) = u :=
  combinedPointPart_combinedPoint u α

@[simp] theorem directCombinedCoefficientPart_combinedPoint (D : DirectLdParams)
    (u : Fin D.m → DirectScalarQ D) (α : Fin D.k → DirectScalarQ D) :
    directCombinedCoefficientPart D (combinedPoint u α) = α :=
  combinedCoefficientPart_combinedPoint u α

/-- A coordinate of the combined dimension is either a point coordinate or a
combining coordinate. -/
def directCombinedIndexSplit (D : DirectLdParams) (i : Fin D.combined.m) :
    Fin D.m ⊕ Fin D.k :=
  finSumFinEquiv.symm i

@[simp] theorem directCombinedIndexSplit_combinedPointVar (D : DirectLdParams)
    (j : Fin D.m) :
    directCombinedIndexSplit D (combinedPointVar D.m D.k j) = Sum.inl j := by
  simp [directCombinedIndexSplit, combinedPointVar]

@[simp] theorem directCombinedIndexSplit_combinedCoefficientVar
    (D : DirectLdParams) (r : Fin D.k) :
    directCombinedIndexSplit D (combinedCoefficientVar D.m D.k r) = Sum.inr r := by
  simp [directCombinedIndexSplit, combinedCoefficientVar]

/-- The geometric direction of the line carried by a question of the combined
game; the zero direction on point questions. -/
def directCombinedQuestionDirection (D : DirectLdParams)
    (q : DirectLdQuestion D.combined) : Fin D.combined.m → DirectScalarQ D :=
  match q.1 with
  | .point => 0
  | .aline => coordinateDirection q.2.index
  | .dline => q.2.direction

/-! ## The measured question -/

/-- The direction of the line of the original game measured on a question of
the combined game.  It is the coordinate direction of the stored point
coordinate for an axis-parallel question, and the prefix projection of the
point part of the combined direction for a diagonal question; on the three
cases measuring a point question it is the zero direction. -/
def directCombinedMeasuredDirection (D : DirectLdParams)
    (q : DirectLdQuestion D.combined) : Fin D.m → DirectScalarQ D :=
  match q.1, directCombinedIndexSplit D q.2.index with
  | .aline, .inl j => coordinateDirection j
  | .dline, .inl j =>
      directPrefixProjection j (directCombinedPointPart D q.2.direction)
  | _, _ => 0

/-- The change of parameter between the presentation of the measured line by
the point part of the canonical base of the combined line and its presentation
by its own canonical base.  It is the canonical rebase parameter of
`Transport.Questions`; it is needed because the canonical base of a line of the
combined space need not project to the canonical base of its image line. -/
def directCombinedRebaseParameter (D : DirectLdParams)
    (q : DirectLdQuestion D.combined) : DirectScalarQ D :=
  directLineRepParameter (directCombinedMeasuredDirection D q)
    (directCombinedPointPart D q.2.point)

/-- The question of the original game measured by the combined strategy on a
question of the combined game.  This is the case distinction of
`def:ld-combined-strategy`: cases 1, 3 and 5 measure a point question, case 2
an axis-parallel line question, and case 4 a diagonal line question. -/
def directCombinedMeasuredQuestion (D : DirectLdParams)
    (q : DirectLdQuestion D.combined) : DirectLdQuestion D :=
  match q.1, directCombinedIndexSplit D q.2.index with
  | .aline, .inl j =>
      (.aline, directLdMap D .aline
        ⟨directCombinedPointPart D q.2.point, j, 0⟩)
  | .dline, .inl j =>
      (.dline, directLdMap D .dline
        ⟨directCombinedPointPart D q.2.point, j,
          directCombinedPointPart D q.2.direction⟩)
  | _, _ => directLdPointQuestionOf D (directCombinedPointPart D q.2.point)

/-! ## The relabelling of the measured outcome -/

/-- The relabelling by which the combined strategy answers a question of the
combined game from the outcome of the measured question of the original game.
An outcome whose constructor does not match the measured question type is sent
to the zero answer of the constructor required by the combined question type,
which the combined win predicate treats exactly as the original win predicate
treats the mismatched outcome. -/
def directCombinedAnswerMap (D : DirectLdParams)
    (q : DirectLdQuestion D.combined) (a : DirectLdAnswer D) :
    DirectLdAnswer D.combined :=
  let α := directCombinedCoefficientPart D q.2.point
  let w := directCombinedCoefficientPart D (directCombinedQuestionDirection D q)
  let s := directCombinedRebaseParameter D q
  match q.1, directCombinedIndexSplit D q.2.index with
  | .point, _ =>
      .pointVals fun _ =>
        match a with
        | .pointVals b => ∑ r : Fin D.k, α r * b r
        | .alinePolys _ => 0
        | .dlinePolys _ => 0
  | .aline, .inl _ =>
      .alinePolys fun _ =>
        match a with
        | .alinePolys f =>
            coefficientsOfPolynomial D.combined.d (combinedAxisPolynomial α s f)
        | .pointVals _ => 0
        | .dlinePolys _ => 0
  | .aline, .inr _ =>
      .alinePolys fun _ =>
        match a with
        | .pointVals b =>
            coefficientsOfPolynomial D.combined.d (fiberLinePolynomial α w b)
        | .alinePolys _ => 0
        | .dlinePolys _ => 0
  | .dline, .inl _ =>
      .dlinePolys fun _ =>
        match a with
        | .dlinePolys f =>
            coefficientsOfPolynomial (D.combined.m * D.combined.d)
              (combinedDiagonalPolynomial α w s f)
        | .pointVals _ => 0
        | .alinePolys _ => 0
  | .dline, .inr _ =>
      .dlinePolys fun _ =>
        match a with
        | .pointVals b =>
            coefficientsOfPolynomial (D.combined.m * D.combined.d)
              (fiberLinePolynomial α w b)
        | .alinePolys _ => 0
        | .dlinePolys _ => 0

/-! ## The combined strategy -/

/-- The combined strategy of `def:ld-combined-strategy`: the same state and the
same two Hilbert spaces, each question of the combined game answered by
measuring `directCombinedMeasuredQuestion` and relabelling its outcome by
`directCombinedAnswerMap`. -/
def directCombinedStrategy (D : DirectLdParams) (S : Strategy (directLdGame D)) :
    Strategy (directLdGame D.combined) where
  ιA := S.ιA
  ιB := S.ιB
  ψ := S.ψ
  ψ_norm := S.ψ_norm
  A := fun q =>
    (S.A (directCombinedMeasuredQuestion D q)).postprocess
      (directCombinedAnswerMap D q)
  B := fun q =>
    (S.B (directCombinedMeasuredQuestion D q)).postprocess
      (directCombinedAnswerMap D q)

@[simp] theorem directCombinedStrategy_state (D : DirectLdParams)
    (S : Strategy (directLdGame D)) : (directCombinedStrategy D S).ψ = S.ψ := rfl

@[simp] theorem directCombinedStrategy_A (D : DirectLdParams)
    (S : Strategy (directLdGame D)) (q : DirectLdQuestion D.combined) :
    (directCombinedStrategy D S).A q =
      (S.A (directCombinedMeasuredQuestion D q)).postprocess
        (directCombinedAnswerMap D q) := rfl

@[simp] theorem directCombinedStrategy_B (D : DirectLdParams)
    (S : Strategy (directLdGame D)) (q : DirectLdQuestion D.combined) :
    (directCombinedStrategy D S).B q =
      (S.B (directCombinedMeasuredQuestion D q)).postprocess
        (directCombinedAnswerMap D q) := rfl

/-- Projectivity transfer for `def:ld-combined-strategy`: each measurement of
the combined strategy is a coarse-graining of a measurement of the original
strategy, and coarse-graining preserves projectivity. -/
theorem directCombinedStrategy_isProjective (D : DirectLdParams)
    (S : Strategy (directLdGame D)) (hS : S.IsProjective) :
    (directCombinedStrategy D S).IsProjective := by
  refine ⟨fun q => ?_, fun q => ?_⟩
  · exact SandwichInternal.postprocess_isProjective _ (hS.1 _) _
  · exact SandwichInternal.postprocess_isProjective _ (hS.2 _) _

end

end MIPStarRE.QPBT
