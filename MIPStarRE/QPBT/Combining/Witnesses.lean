import MIPStarRE.QPBT.Combining.Defs
import MIPStarRE.QPBT.Combining.DirectLowDegree
import MIPStarRE.QPBT.Games.Consistency
import MIPStarRE.QPBT.Observables.LineMeasurement
import MIPStarRE.QPBT.Observables.WinImplications

/-!
# Witnesses for combining the Pauli bases

This module packages the five measurement and distribution witnesses used in
the combining argument.  Every measurement is indexed by the player side, so
Alice's and Bob's local spaces remain distinct.  The extended-dimensional
line objects use the directly indexed low-degree interface and therefore do
not require a dimension-divisibility hypothesis.

## References

The witnesses formalize `lem:qld-4-10`, `lem:qld-xz-lines`,
`lem:qld-sublines`, `lem:qld-4-13`, and `lem:qld-4-7` in
`blueprint/src/chapter/ch15_qpbt_combining.tex`.  Their paper source is
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:689-709,
882-894,1020-1069,1267-1274`.
-/

namespace MIPStarRE.QPBT

open MIPStarRE.LDT MIPStarRE.LDT.Preliminaries MIPStarRE.Quantum

noncomputable section

/-! ## The canonical scalar identification -/

/-- Identify the direct extended game's scalar field with the Pauli scalar
field.  Both are selected by `fixedFieldModel`; only their proof argument for
admissibility differs. -/
noncomputable def extendedDirectScalarEquiv (P : AdmissibleParams) :
    DirectScalarQ P.extendedDirectLd ≃+* PauliScalar P := by
  have h : P.extendedDirectLd.hq = P.hq := Subsingleton.elim _ _
  cases h
  exact RingEquiv.refl _

/-- Transport an extended direct point into the canonical Pauli scalar field. -/
def directPointToPauli (P : AdmissibleParams)
    (u : Fin P.extendedDirectLd.m -> DirectScalarQ P.extendedDirectLd) :
    Fin (2 * P.m + 2) -> PauliScalar P :=
  fun i => extendedDirectScalarEquiv P (u i)

/-! ## Finite direct-line carrier -/

/-- A finite code for directly indexed lines, omitting only proof fields. -/
private abbrev DirectLineDescCode (D : DirectLdParams) :=
  ((Fin D.m -> DirectScalarQ D) × Fin D.m) ⊕
    ((Fin D.m -> DirectScalarQ D) × Fin D.m ×
      (Fin D.m -> DirectScalarQ D))

/-- Encode a directly indexed line by its tag and mathematical data. -/
private def directLineDescCode (D : DirectLdParams) :
    DirectLineDesc D -> DirectLineDescCode D
  | .axis base index _ => .inl (base, index)
  | .diagonal base index direction _ _ => .inr (base, index, direction)

/-- The direct-line code is injective by proof irrelevance. -/
private theorem directLineDescCode_injective (D : DirectLdParams) :
    Function.Injective (directLineDescCode D) := by
  intro line line' h
  cases line with
  | axis base index baseFixed =>
      cases line' with
      | axis base' index' baseFixed' =>
          simp only [directLineDescCode, Sum.inl.injEq, Prod.mk.injEq] at h
          rcases h with ⟨rfl, rfl⟩
          rfl
      | diagonal => simp [directLineDescCode] at h
  | diagonal base index direction baseFixed prefixZero =>
      cases line' with
      | axis => simp [directLineDescCode] at h
      | diagonal base' index' direction' baseFixed' prefixZero' =>
          simp only [directLineDescCode, Sum.inr.injEq, Prod.mk.injEq] at h
          rcases h with ⟨rfl, rfl, rfl⟩
          rfl

/-- Directly indexed line descriptions form a finite type. -/
noncomputable instance directLineDescFintype (D : DirectLdParams) :
    Fintype (DirectLineDesc D) :=
  Fintype.ofInjective (directLineDescCode D) (directLineDescCode_injective D)

/-! ## Combined point and line measurements -/

/-- Projective joint point measurements and their ordered consistency
guarantees from `lem:qld-4-10`, paper lines 689--709.  The `XZ` and `ZX`
products are retained as distinct fields. -/
structure CombinedPointsWitness {P : AdmissibleParams} {ε : ℝ}
    (S : ProjectiveSetting P ε) (δ : ℝ) where
  /-- The complete joint measurement on each player's expanded local space. -/
  Q : (side : PlayerSide) ->
    (Fin P.m -> PauliScalar P) ->
    (Fin P.m -> PauliScalar P) ->
    Measurement (PauliScalar P × PauliScalar P) (S.ExpandedLocalSpace side)
  /-- Every joint point measurement is projective. -/
  projective : ∀ side x z, Measurement.IsProjective (Q side x z)
  /-- Joint point measurements agree across every directed opposite placement. -/
  self_consistent : ∀ p1 p2 : Placement, p1.IsOpposite p2 ->
    opFamilyDistSq
      (uniformDistribution
        ((Fin P.m -> PauliScalar P) × (Fin P.m -> PauliScalar P)))
      (fun xz ab => S.place p1 ((Q p1.side xz.1 xz.2).effect ab))
      (fun xz ab => S.place p2 ((Q p2.side xz.1 xz.2).effect ab))
      S.psiHat <= δ
  /-- Joint point measurements are close to the ordered `X`-then-`Z` product. -/
  consistent_XZ : ∀ p1 p2 : Placement, p1.IsOpposite p2 ->
    opFamilyDistSq
      (uniformDistribution
        ((Fin P.m -> PauliScalar P) × (Fin P.m -> PauliScalar P)))
      (fun xz ab => S.place p1 ((Q p1.side xz.1 xz.2).effect ab))
      (fun xz ab => S.place p2
        ((S.pointMeasExp p2.side .X xz.1).effect ab.1 *
          (S.pointMeasExp p2.side .Z xz.2).effect ab.2))
      S.psiHat <= δ
  /-- Joint point measurements are close to the ordered `Z`-then-`X` product. -/
  consistent_ZX : ∀ p1 p2 : Placement, p1.IsOpposite p2 ->
    opFamilyDistSq
      (uniformDistribution
        ((Fin P.m -> PauliScalar P) × (Fin P.m -> PauliScalar P)))
      (fun xz ab => S.place p1 ((Q p1.side xz.1 xz.2).effect ab))
      (fun xz ab => S.place p2
        ((S.pointMeasExp p2.side .Z xz.2).effect ab.2 *
          (S.pointMeasExp p2.side .X xz.1).effect ab.1))
      S.psiHat <= δ

/-- Joint line measurements and their evaluation consistency from
`lem:qld-xz-lines`, paper lines 882--894.  Evaluation uses explicit `Option`
outcomes, including the class of answers not determined at the sampled point. -/
structure CombinedLinesWitness {P : AdmissibleParams} {ε δQ : ℝ}
    (S : ProjectiveSetting P ε) (points : CombinedPointsWitness S δQ)
    (δ : ℝ) where
  /-- The complete paired-line measurement on each expanded local space. -/
  T : (side : PlayerSide) ->
    LineDesc P.toLdParams -> LineDesc P.toLdParams ->
    Measurement
      (DegPoly P.toLdParams (P.m * P.d) ×
        DegPoly P.toLdParams (P.m * P.d))
      (S.ExpandedLocalSpace side)
  /-- On an axis-parallel X line, outcomes outside degree `d` have zero effect. -/
  axis_degree_X : ∀ side lineX lineZ fX fZ,
    lineX.kind = .axis -> Not (DegPoly.FitsDegree P.d fX) ->
      (T side lineX lineZ).effect (fX, fZ) = 0
  /-- On an axis-parallel Z line, outcomes outside degree `d` have zero effect. -/
  axis_degree_Z : ∀ side lineX lineZ fX fZ,
    lineZ.kind = .axis -> Not (DegPoly.FitsDegree P.d fZ) ->
      (T side lineX lineZ).effect (fX, fZ) = 0
  /-- Evaluated line pairs are consistent with the completed point-pair
  measurement on every directed opposite placement. -/
  consistent : ∀ p1 p2 : Placement, p1.IsOpposite p2 ->
    consistencyDefect
      (Distribution.prod (linePointDist P.toLdParams)
        (linePointDist P.toLdParams))
      (fun sample answer => S.place p1
        (((T p1.side sample.1.1 sample.2.1).postprocess fun fs =>
          (evalOpt sample.1.1 sample.1.2 fs.1,
            evalOpt sample.2.1 sample.2.2 fs.2)).effect answer))
      (fun sample answer => S.place p2
        (((points.Q p2.side sample.1.2 sample.2.2).postprocess fun ab =>
          (some ab.1, some ab.2)).effect answer))
      S.psiHat <= δ

/-! ## The subline distribution -/

/-- A tuple consisting of an extended line and its projected X and Z lines. -/
abbrev SubLineTriple (P : AdmissibleParams) :=
  DirectLineDesc P.extendedDirectLd ×
    (LineDesc P.toLdParams × LineDesc P.toLdParams)

/-- An extended line tuple together with a point sampled uniformly on it. -/
abbrev SubLinePointSample (P : AdmissibleParams) :=
  SubLineTriple P ×
    (Fin P.extendedDirectLd.m -> DirectScalarQ P.extendedDirectLd)

/-- The shared restricted line kind and two coordinate indices in one mixture
component of the subline law. -/
abbrev SubLineComponent (P : AdmissibleParams) :=
  LineKind × (Fin P.m × Fin P.m)

/-- Select the restricted line-point distribution of a given kind and index. -/
noncomputable def restrictedLinePointDist (P : AdmissibleParams)
    (kind : LineKind) (i : Fin P.m) :
    Distribution (LineDesc P.toLdParams × (Fin P.m -> PauliScalar P)) :=
  match kind with
  | .axis => restrictedALineDist P.toLdParams i
  | .diagonal => restrictedDLineDist P.toLdParams i

/-- Sample a subline tuple and then a uniform affine parameter on its
extended line. -/
noncomputable def subLinePointDist (P : AdmissibleParams)
    (D : Distribution (SubLineTriple P)) :
    Distribution (SubLinePointSample P) :=
  (Distribution.prod D
    (uniformDistribution (DirectScalarQ P.extendedDirectLd))).map fun sample =>
      (sample.1, sample.1.1.base + sample.2 • sample.1.1.direction)

/-- Retain the projected line pair and the X projection of an extended point. -/
def subLineXProjection {P : AdmissibleParams} (sample : SubLinePointSample P) :
    (LineDesc P.toLdParams × LineDesc P.toLdParams) ×
      (Fin P.m -> PauliScalar P) :=
  (sample.1.2, projX (directPointToPauli P sample.2))

/-- Retain the projected line pair and the Z projection of an extended point. -/
def subLineZProjection {P : AdmissibleParams} (sample : SubLinePointSample P) :
    (LineDesc P.toLdParams × LineDesc P.toLdParams) ×
      (Fin P.m -> PauliScalar P) :=
  (sample.1.2, projZ (directPointToPauli P sample.2))

/-- The X-point marginal associated with one restricted product component. -/
noncomputable def subLineXComponentDist (P : AdmissibleParams)
    (component : SubLineComponent P) :
    Distribution
      ((LineDesc P.toLdParams × LineDesc P.toLdParams) ×
        (Fin P.m -> PauliScalar P)) :=
  (Distribution.prod
    (restrictedLinePointDist P component.1 component.2.1)
    ((restrictedLinePointDist P component.1 component.2.2).map Prod.fst)).map
      fun sample => ((sample.1.1, sample.2), sample.1.2)

/-- The Z-point marginal associated with one restricted product component. -/
noncomputable def subLineZComponentDist (P : AdmissibleParams)
    (component : SubLineComponent P) :
    Distribution
      ((LineDesc P.toLdParams × LineDesc P.toLdParams) ×
        (Fin P.m -> PauliScalar P)) :=
  (Distribution.prod
    ((restrictedLinePointDist P component.1 component.2.1).map Prod.fst)
    (restrictedLinePointDist P component.1 component.2.2)).map
      fun sample => ((sample.1, sample.2.1), sample.2.2)

/-- The subline distribution of `lem:qld-sublines`, paper lines 1063--1069.
Its source-mixture field records the X and Z point marginals separately; it
does not assert a joint conditional law for the pair of projected points. -/
structure SubLineWitness (P : AdmissibleParams) where
  /-- The actual distribution of an extended line and two projected lines. -/
  D : Distribution (SubLineTriple P)
  /-- The distribution has total mass one. -/
  isProbability : D.IsProbability
  /-- Its extended-line marginal is the direct line-point marginal. -/
  extended_marginal : D.map Prod.fst =
    (directLinePointDist P.extendedDirectLd).map Prod.fst
  /-- Every point of an extended line projects onto both stored source lines. -/
  incidence : ∀ sample ∈ D.support, ∀ u ∈ sample.1.pointSet,
    projX (directPointToPauli P u) ∈ sample.2.1.pointSet ∧
      projZ (directPointToPauli P u) ∈ sample.2.2.pointSet
  /-- Each line triple carries affine data sufficient for
  `combineLinePoly_spec`. -/
  compatibility : ∀ sample ∈ D.support,
    ∃ aX bX aZ bZ uAlpha vAlpha uBeta vBeta : PauliScalar P,
      IsCombineLineCompatible
        (directPointToPauli P sample.1.base)
        (directPointToPauli P sample.1.direction)
        sample.2.1.base sample.2.1.direction
        sample.2.2.base sample.2.2.direction
        aX bX aZ bZ uAlpha vAlpha uBeta vBeta
  /-- Each one-point projected marginal is a mixture of restricted product
  laws.  No equality for their joint conditional law is claimed. -/
  source_mixture : ∃ components : Distribution (SubLineComponent P),
    components.IsProbability ∧
      (subLinePointDist P D).map subLineXProjection =
        Distribution.bind components (subLineXComponentDist P) ∧
      (subLinePointDist P D).map subLineZProjection =
        Distribution.bind components (subLineZComponentDist P)
  /-- An extended axis line has axis-parallel projected lines. -/
  axis_closure : ∀ sample ∈ D.support, sample.1.kind = .axis ->
    sample.2.1.kind = .axis ∧ sample.2.2.kind = .axis

/-! ## Extended lines and global polynomial pairs -/

/-- Extended-line POVMs and the two source consistency displays from
`lem:qld-4-13`, paper lines 1020--1034.  The direct line carrier avoids the
dimension-divisibility obstruction documented in
`docs/paper-gaps/qpbt_ld-dimension-divisibility.tex`. -/
structure ExtendedLinesWitness {P : AdmissibleParams} {ε δQ : ℝ}
    (S : ProjectiveSetting P ε) (points : CombinedPointsWitness S δQ)
    (δ : ℝ) where
  /-- The complete extended-line measurement on each player side. -/
  Qline : (side : PlayerSide) -> DirectLineDesc P.extendedDirectLd ->
    Measurement (DirectDegPoly P.extendedDirectLd (P.m * P.d + 1))
      (S.ExpandedLocalSpace side)
  /-- Axis-line outcomes outside degree `d` have zero effect. -/
  axis_degree : ∀ side line f, line.kind = .axis ->
    Not (∀ i, P.d < i.val -> f i = 0) ->
      (Qline side line).effect f = 0
  /-- Alice's evaluated line measurement is consistent with Bob's completed
  combined point measurement. -/
  consistent_alice : consistencyDefect
    (directLinePointDist P.extendedDirectLd)
    (fun sample answer => S.place .AA'
      (((Qline .alice sample.1).postprocess
        (fun f => (directEvalOpt sample.1 sample.2 f).map
          (extendedDirectScalarEquiv P))).effect answer))
    (fun sample answer => S.place .BA''
      (((points.Q .bob
        (projX (directPointToPauli P sample.2))
        (projZ (directPointToPauli P sample.2))).postprocess fun ab =>
          some (directPointToPauli P sample.2 (alphaVar P.m) * ab.1 +
            directPointToPauli P sample.2 (betaVar P.m) * ab.2)).effect answer))
    S.psiHat <= δ
  /-- Bob's evaluated line measurement is consistent with Alice's completed
  combined point measurement. -/
  consistent_bob : consistencyDefect
    (directLinePointDist P.extendedDirectLd)
    (fun sample answer => S.place .BB'
      (((Qline .bob sample.1).postprocess
        (fun f => (directEvalOpt sample.1 sample.2 f).map
          (extendedDirectScalarEquiv P))).effect answer))
    (fun sample answer => S.place .AB''
      (((points.Q .alice
        (projX (directPointToPauli P sample.2))
        (projZ (directPointToPauli P sample.2))).postprocess fun ab =>
          some (directPointToPauli P sample.2 (alphaVar P.m) * ab.1 +
            directPointToPauli P sample.2 (betaVar P.m) * ab.2)).effect answer))
    S.psiHat <= δ

/-- The side-indexed global polynomial-pair measurements handed to Chapter 16.
This is the exact conclusion of `lem:qld-4-7`, paper lines 1267--1274, with
the two heterogeneous point-consistency displays stated separately. -/
structure GlobalPairWitness {P : AdmissibleParams} {ε : ℝ}
    (S : ProjectiveSetting P ε) (δ : ℝ) where
  /-- The complete global polynomial-pair measurement on each player side. -/
  Smeas : (side : PlayerSide) ->
    Measurement (PolyPair P) (S.ExpandedLocalSpace side)
  /-- Both global polynomial-pair measurements are projective. -/
  projective : ∀ side, Measurement.IsProjective (Smeas side)
  /-- Alice's global evaluations are consistent with Bob's source point
  measurements, for each Pauli basis. -/
  point_consistent_alice : ∀ W : PauliKind,
    consistencyDefect (uniformDistribution (Fin P.m -> PauliScalar P))
      (fun u a => S.place .AA'
        (((Smeas .alice).postprocess (evalAt W u)).effect a))
      (fun u a => S.place .BA''
        ((S.pointMeasExp .bob W u).effect a))
      S.psiHat <= δ
  /-- Bob's global evaluations are consistent with Alice's source point
  measurements, for each Pauli basis. -/
  point_consistent_bob : ∀ W : PauliKind,
    consistencyDefect (uniformDistribution (Fin P.m -> PauliScalar P))
      (fun u a => S.place .BB'
        (((Smeas .bob).postprocess (evalAt W u)).effect a))
      (fun u a => S.place .AB''
        ((S.pointMeasExp .alice W u).effect a))
      S.psiHat <= δ

end

end MIPStarRE.QPBT
