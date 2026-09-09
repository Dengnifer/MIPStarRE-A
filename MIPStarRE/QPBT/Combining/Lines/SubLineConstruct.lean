import MIPStarRE.QPBT.Combining.Lines.SubLineBranch
import MIPStarRE.QPBT.Combining.Lines.SubLineProduct
import MIPStarRE.QPBT.Combining.Lines.SubLineSeed

/-!
# The sampling procedure of the sub-line lemma

This module carries out the directly indexed auxiliary construction for `lem:qld-sublines`.
A line kind is drawn from the two kinds, an extended coordinate and an extended point
and direction are drawn uniformly, and two scalar seeds are drawn
independently in the coordinate-index fibers of the two coordinates that the
two source lines must carry.  The sampled triple consists of the axis or
diagonal line of the extended sample together with the two source lines
decoded from the two coordinate blocks of the extended point and direction and
from the two seeds.

The module records the elementary evaluations of that triple, the description
of the support of the resulting law, the three pointwise properties of a
sampled triple -- incidence of the two source blocks, compatibility of the
affine data, and closure of the axis branch -- and the identification of its
extended-line marginal.

## References

The construction supports blueprint `lem:qld-sublines` on the directly indexed
extended carrier; its source is
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1063-1116`.
The restricted laws are the auxiliary blueprint `def:ith-restricted-line-refined`,
supporting paper `def:ith-restricted-line` at lines 1038--1048.
-/

open scoped BigOperators

namespace MIPStarRE.QPBT

open MIPStarRE.LDT

noncomputable section

/-! ## The auxiliary randomness of one branch -/

/-- An extended point together with an extended direction.  Blueprint
`lem:qld-sublines`, paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1063-1116`. -/
abbrev SubLinePointDir (P : AdmissibleParams) :=
  (Fin P.extendedDirectLd.m → DirectScalarQ P.extendedDirectLd) ×
    (Fin P.extendedDirectLd.m → DirectScalarQ P.extendedDirectLd)

/-- The auxiliary randomness of one branch of the sampling procedure: an
extended point, an extended direction, and the two scalar seeds of the two
source lines.  Blueprint `lem:qld-sublines`, paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1063-1116`. -/
abbrev SubLineRaw (P : AdmissibleParams) :=
  SubLinePointDir P × (ScalarQ P.toLdParams × ScalarQ P.toLdParams)

/-- The law of the scalar seed carried by a source line at a given coordinate
index: uniform on the coordinate-index fiber of that index.  Blueprint
`def:ith-restricted-line-refined`, paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1038-1048`. -/
noncomputable def subLineSeedDist (P : AdmissibleParams) (i : Fin P.m) :
    Distribution (ScalarQ P.toLdParams) :=
  Distribution.restrict (uniformDistribution (ScalarQ P.toLdParams))
    (ldSeedIndexEvent P.toLdParams i) (ldSeedIndexEvent_positive P.toLdParams i)

/-- Every seed law of a source line has total mass one. -/
theorem subLineSeedDist_isProbability (P : AdmissibleParams) (i : Fin P.m) :
    (subLineSeedDist P i).IsProbability := by
  rw [subLineSeedDist]
  exact Distribution.restrict_isProbability _ _
    (ldSeedIndexEvent_positive P.toLdParams i)

/-- The auxiliary randomness law of the sampling procedure: the extended
coordinate is uniform, the extended point and direction are uniform and
independent of it, and the two seeds are independent and uniform on the
coordinate-index fibers of the two coordinates carried by the two source
lines.  Blueprint `lem:qld-sublines`, paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1063-1116`. -/
noncomputable def subLineRawDist (P : AdmissibleParams) :
    Distribution (Fin (2 * P.m + 2) × SubLineRaw P) :=
  Distribution.bind (uniformDistribution (Fin (2 * P.m + 2))) fun k =>
    (Distribution.prod (uniformDistribution (SubLinePointDir P))
        (Distribution.prod (subLineSeedDist P (subLineXIndex P k))
          (subLineSeedDist P (subLineZIndex P k)))).map fun w => (k, w)

/-- The auxiliary randomness law has total mass one. -/
theorem subLineRawDist_isProbability (P : AdmissibleParams) :
    (subLineRawDist P).IsProbability := by
  refine Distribution.bind_isProbability _ _
    (uniformDistribution_isProbability _) fun k _ => ?_
  exact Distribution.IsProbability.map
    (Distribution.prod_isProbability _ _ (uniformDistribution_isProbability _)
      (Distribution.prod_isProbability _ _ (subLineSeedDist_isProbability P _)
        (subLineSeedDist_isProbability P _))) _

/-! ## The sampled triple -/

/-- The extended line of a branch: the canonical axis or diagonal line of an
extended sample.  Blueprint `lem:qld-sublines`, paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1063-1116`. -/
noncomputable def subLineExtLineOfSample (P : AdmissibleParams)
    (kind : LineKind) (s : DirectLdSpace P.extendedDirectLd) :
    DirectLineDesc P.extendedDirectLd :=
  match kind with
  | .axis => directALineDescOf P.extendedDirectLd s
  | .diagonal => directDLineDescOf P.extendedDirectLd s

/-- The extended line of a branch, read off the auxiliary randomness.
Blueprint `lem:qld-sublines`, paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1063-1116`. -/
noncomputable def subLineExtLine (P : AdmissibleParams) (kind : LineKind)
    (k : Fin (2 * P.m + 2)) (w : SubLineRaw P) :
    DirectLineDesc P.extendedDirectLd :=
  subLineExtLineOfSample P kind ⟨w.1.1, k, w.1.2⟩

/-- A source line of a branch: the canonical axis or diagonal line decoded
from a point block, a scalar seed and a direction block.  Blueprint
`lem:qld-sublines`, paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1063-1116`. -/
noncomputable def subLineSourceLine (P : AdmissibleParams) (kind : LineKind)
    (b : Fin P.m → PauliScalar P) (s : ScalarQ P.toLdParams)
    (d : Fin P.m → PauliScalar P) : LineDesc P.toLdParams :=
  match kind with
  | .axis => aLineDescOfBlock P.toLdParams (b, (s, d))
  | .diagonal => dLineDescOfBlock P.toLdParams (b, (s, d))

/-- The triple sampled by one branch of the procedure: the extended line
together with the two source lines decoded from its two coordinate blocks and
from the two scalar seeds.  Blueprint `lem:qld-sublines`,
paper `references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1063-1116`.
-/
noncomputable def subLineTripleOf (P : AdmissibleParams) (kind : LineKind)
    (k : Fin (2 * P.m + 2)) (w : SubLineRaw P) : SubLineTriple P :=
  (subLineExtLine P kind k w,
    (subLineSourceLine P kind (projX (directPointToPauli P w.1.1)) w.2.1
        (projX (directPointToPauli P w.1.2)),
      subLineSourceLine P kind (projZ (directPointToPauli P w.1.1)) w.2.2
        (projZ (directPointToPauli P w.1.2))))

/-- The law of the triples sampled by one branch.  Blueprint
`lem:qld-sublines`, paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1063-1116`. -/
noncomputable def subLineBranchDist (P : AdmissibleParams) (kind : LineKind) :
    Distribution (SubLineTriple P) :=
  (subLineRawDist P).map fun w => subLineTripleOf P kind w.1 w.2

/-- The sub-line law of `lem:qld-sublines`: the equal mixture of the two
branches of the sampling procedure.  Blueprint
`lem:qld-sublines`, paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1063-1116`. -/
noncomputable def subLineDist (P : AdmissibleParams) :
    Distribution (SubLineTriple P) :=
  Distribution.bind (uniformDistribution (Fin 2))
    ![subLineBranchDist P .axis, subLineBranchDist P .diagonal]

/-! ## Elementary evaluations of the sampled triple -/

/-- The extended line of a branch has the kind of that branch. -/
theorem subLineExtLine_kind (P : AdmissibleParams) (kind : LineKind)
    (k : Fin (2 * P.m + 2)) (w : SubLineRaw P) :
    (subLineExtLine P kind k w).kind = kind := by
  cases kind <;> rfl

/-- The direction of the extended line of a branch is the branch direction. -/
theorem subLineExtLine_direction (P : AdmissibleParams) (kind : LineKind)
    (k : Fin (2 * P.m + 2)) (w : SubLineRaw P) :
    (subLineExtLine P kind k w).direction =
      subLineExtDirection P kind k w.1.2 := by
  cases kind <;> rfl

/-- The base of the extended line of a branch is the canonical representative
of the drawn point in the branch direction. -/
theorem subLineExtLine_base (P : AdmissibleParams) (kind : LineKind)
    (k : Fin (2 * P.m + 2)) (w : SubLineRaw P) :
    (subLineExtLine P kind k w).base =
      lineRepMap (subLineExtDirection P kind k w.1.2) w.1.1 := by
  cases kind <;> rfl

/-- A source line of a branch has the kind of that branch. -/
theorem subLineSourceLine_kind (P : AdmissibleParams) (kind : LineKind)
    (b : Fin P.m → PauliScalar P) (s : ScalarQ P.toLdParams)
    (d : Fin P.m → PauliScalar P) :
    (subLineSourceLine P kind b s d).kind = kind := by
  cases kind <;> rfl

/-- The direction of a source line of a branch is the branch source direction
at the coordinate index named by its seed. -/
theorem subLineSourceLine_direction (P : AdmissibleParams) (kind : LineKind)
    (b : Fin P.m → PauliScalar P) (s : ScalarQ P.toLdParams)
    (d : Fin P.m → PauliScalar P) :
    (subLineSourceLine P kind b s d).direction =
      subLineSourceDirection P kind (chiIndex P.toLdParams s) d := by
  cases kind <;> rfl

/-- The base of a source line of a branch is the canonical representative of
its point block in its own direction. -/
theorem subLineSourceLine_base (P : AdmissibleParams) (kind : LineKind)
    (b : Fin P.m → PauliScalar P) (s : ScalarQ P.toLdParams)
    (d : Fin P.m → PauliScalar P) :
    (subLineSourceLine P kind b s d).base =
      lineRepMap (subLineSourceDirection P kind (chiIndex P.toLdParams s) d)
        b := by
  cases kind <;> rfl

/-! ## The support of the sub-line law -/

/-- Every triple in the support of the sub-line law is sampled by one branch
from auxiliary randomness whose two seeds lie in the coordinate-index fibers
of the two coordinates carried by the two source lines.  Blueprint
`lem:qld-sublines`, paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1063-1116`. -/
theorem exists_raw_of_mem_subLineDist_support (P : AdmissibleParams)
    {sample : SubLineTriple P} (hsample : sample ∈ (subLineDist P).support) :
    ∃ (kind : LineKind) (k : Fin (2 * P.m + 2)) (w : SubLineRaw P),
      chiIndex P.toLdParams w.2.1 = subLineXIndex P k ∧
        chiIndex P.toLdParams w.2.2 = subLineZIndex P k ∧
        sample = subLineTripleOf P kind k w := by
  classical
  have hbind : sample ∈ (uniformDistribution (Fin 2)).support.biUnion
      (fun c => (![subLineBranchDist P .axis,
        subLineBranchDist P .diagonal] c).support) := hsample
  obtain ⟨c, -, hc⟩ := Finset.mem_biUnion.mp hbind
  obtain ⟨kind, hkind⟩ : ∃ kind : LineKind,
      sample ∈ (subLineBranchDist P kind).support := by
    fin_cases c
    · exact ⟨.axis, by simpa using hc⟩
    · exact ⟨.diagonal, by simpa using hc⟩
  obtain ⟨kw, hkw, hkw'⟩ := Finset.mem_image.mp hkind
  obtain ⟨k, -, hk⟩ := Finset.mem_biUnion.mp
    (show kw ∈ (uniformDistribution (Fin (2 * P.m + 2))).support.biUnion
      (fun k => ((Distribution.prod (uniformDistribution (SubLinePointDir P))
        (Distribution.prod (subLineSeedDist P (subLineXIndex P k))
          (subLineSeedDist P (subLineZIndex P k)))).map
        (fun w => (k, w))).support) from hkw)
  obtain ⟨w, hw, hw'⟩ := Finset.mem_image.mp hk
  obtain ⟨-, hseeds⟩ := Finset.mem_product.mp hw
  obtain ⟨hsx, hsz⟩ := Finset.mem_product.mp hseeds
  have hx : chiIndex P.toLdParams w.2.1 = subLineXIndex P k :=
    (Finset.mem_filter.mp hsx).2
  have hz : chiIndex P.toLdParams w.2.2 = subLineZIndex P k :=
    (Finset.mem_filter.mp hsz).2
  refine ⟨kind, k, w, hx, hz, ?_⟩
  rw [← hkw', ← hw']

/-! ## Pointwise properties of a sampled triple -/

/-- The direction of the source `X` line of a sampled triple is the branch
source direction at the coordinate carried by that line. -/
theorem subLineTripleOf_xDirection (P : AdmissibleParams) (kind : LineKind)
    (k : Fin (2 * P.m + 2)) (w : SubLineRaw P)
    (hx : chiIndex P.toLdParams w.2.1 = subLineXIndex P k) :
    (subLineTripleOf P kind k w).2.1.direction =
      subLineSourceDirection P kind (subLineXIndex P k)
        (projX (directPointToPauli P w.1.2)) := by
  have h : (subLineTripleOf P kind k w).2.1.direction =
      subLineSourceDirection P kind (chiIndex P.toLdParams w.2.1)
        (projX (directPointToPauli P w.1.2)) :=
    subLineSourceLine_direction P kind _ w.2.1 _
  rw [h, hx]

/-- The direction of the source `Z` line of a sampled triple is the branch
source direction at the coordinate carried by that line. -/
theorem subLineTripleOf_zDirection (P : AdmissibleParams) (kind : LineKind)
    (k : Fin (2 * P.m + 2)) (w : SubLineRaw P)
    (hz : chiIndex P.toLdParams w.2.2 = subLineZIndex P k) :
    (subLineTripleOf P kind k w).2.2.direction =
      subLineSourceDirection P kind (subLineZIndex P k)
        (projZ (directPointToPauli P w.1.2)) := by
  have h : (subLineTripleOf P kind k w).2.2.direction =
      subLineSourceDirection P kind (chiIndex P.toLdParams w.2.2)
        (projZ (directPointToPauli P w.1.2)) :=
    subLineSourceLine_direction P kind _ w.2.2 _
  rw [h, hz]

/-- The `X` block of the direction of the extended line of a sampled triple
lies in the line spanned by the direction of its source `X` line. -/
theorem subLineTripleOf_xSpan (P : AdmissibleParams) (kind : LineKind)
    (k : Fin (2 * P.m + 2)) (w : SubLineRaw P)
    (hx : chiIndex P.toLdParams w.2.1 = subLineXIndex P k) :
    projX (directPointToPauli P (subLineTripleOf P kind k w).1.direction) ∈
      Submodule.span (PauliScalar P)
        ({(subLineTripleOf P kind k w).2.1.direction} :
          Set (Fin P.m → PauliScalar P)) := by
  have hext : (subLineTripleOf P kind k w).1.direction =
      subLineExtDirection P kind k w.1.2 := subLineExtLine_direction P kind k w
  rw [subLineTripleOf_xDirection P kind k w hx, hext]
  exact projX_subLineExtDirection_mem_span P kind k w.1.2

/-- The `Z` block of the direction of the extended line of a sampled triple
lies in the line spanned by the direction of its source `Z` line. -/
theorem subLineTripleOf_zSpan (P : AdmissibleParams) (kind : LineKind)
    (k : Fin (2 * P.m + 2)) (w : SubLineRaw P)
    (hz : chiIndex P.toLdParams w.2.2 = subLineZIndex P k) :
    projZ (directPointToPauli P (subLineTripleOf P kind k w).1.direction) ∈
      Submodule.span (PauliScalar P)
        ({(subLineTripleOf P kind k w).2.2.direction} :
          Set (Fin P.m → PauliScalar P)) := by
  have hext : (subLineTripleOf P kind k w).1.direction =
      subLineExtDirection P kind k w.1.2 := subLineExtLine_direction P kind k w
  rw [subLineTripleOf_zDirection P kind k w hz, hext]
  exact projZ_subLineExtDirection_mem_span P kind k w.1.2

/-- The base of the source `X` line of a sampled triple is the canonical
representative, in its own direction, of the `X` block of the base of the
extended line.  Blueprint `lem:qld-sublines`, paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1063-1116`. -/
theorem subLineTripleOf_xBase (P : AdmissibleParams) (kind : LineKind)
    (k : Fin (2 * P.m + 2)) (w : SubLineRaw P)
    (hx : chiIndex P.toLdParams w.2.1 = subLineXIndex P k) :
    (subLineTripleOf P kind k w).2.1.base =
      lineRepMap (subLineTripleOf P kind k w).2.1.direction
        (projX (directPointToPauli P (subLineTripleOf P kind k w).1.base)) := by
  have hbridge := lineRepMap_projX_directPointToPauli_lineRepMap P
    (subLineExtDirection P kind k w.1.2) w.1.1
    (subLineSourceDirection P kind (subLineXIndex P k)
      (projX (directPointToPauli P w.1.2)))
    (projX_subLineExtDirection_mem_span P kind k w.1.2)
  have hbase : (subLineTripleOf P kind k w).2.1.base =
      lineRepMap (subLineSourceDirection P kind (subLineXIndex P k)
        (projX (directPointToPauli P w.1.2)))
        (projX (directPointToPauli P w.1.1)) := by
    have h : (subLineTripleOf P kind k w).2.1.base =
        lineRepMap (subLineSourceDirection P kind
          (chiIndex P.toLdParams w.2.1) (projX (directPointToPauli P w.1.2)))
          (projX (directPointToPauli P w.1.1)) :=
      subLineSourceLine_base P kind _ w.2.1 _
    rw [h, hx]
  have hextbase : (subLineTripleOf P kind k w).1.base =
      lineRepMap (subLineExtDirection P kind k w.1.2) w.1.1 :=
    subLineExtLine_base P kind k w
  rw [hbase, subLineTripleOf_xDirection P kind k w hx, hextbase]
  exact hbridge.symm

/-- The base of the source `Z` line of a sampled triple is the canonical
representative, in its own direction, of the `Z` block of the base of the
extended line.  Blueprint `lem:qld-sublines`, paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1063-1116`. -/
theorem subLineTripleOf_zBase (P : AdmissibleParams) (kind : LineKind)
    (k : Fin (2 * P.m + 2)) (w : SubLineRaw P)
    (hz : chiIndex P.toLdParams w.2.2 = subLineZIndex P k) :
    (subLineTripleOf P kind k w).2.2.base =
      lineRepMap (subLineTripleOf P kind k w).2.2.direction
        (projZ (directPointToPauli P (subLineTripleOf P kind k w).1.base)) := by
  have hbridge := lineRepMap_projZ_directPointToPauli_lineRepMap P
    (subLineExtDirection P kind k w.1.2) w.1.1
    (subLineSourceDirection P kind (subLineZIndex P k)
      (projZ (directPointToPauli P w.1.2)))
    (projZ_subLineExtDirection_mem_span P kind k w.1.2)
  have hbase : (subLineTripleOf P kind k w).2.2.base =
      lineRepMap (subLineSourceDirection P kind (subLineZIndex P k)
        (projZ (directPointToPauli P w.1.2)))
        (projZ (directPointToPauli P w.1.1)) := by
    have h : (subLineTripleOf P kind k w).2.2.base =
        lineRepMap (subLineSourceDirection P kind
          (chiIndex P.toLdParams w.2.2) (projZ (directPointToPauli P w.1.2)))
          (projZ (directPointToPauli P w.1.1)) :=
      subLineSourceLine_base P kind _ w.2.2 _
    rw [h, hz]
  have hextbase : (subLineTripleOf P kind k w).1.base =
      lineRepMap (subLineExtDirection P kind k w.1.2) w.1.1 :=
    subLineExtLine_base P kind k w
  rw [hbase, subLineTripleOf_zDirection P kind k w hz, hextbase]
  exact hbridge.symm

/-- Every point of the extended line of a sampled triple projects onto both of
its source lines.  Blueprint `lem:qld-sublines`, paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1063-1116`. -/
theorem subLineTripleOf_incidence (P : AdmissibleParams) (kind : LineKind)
    (k : Fin (2 * P.m + 2)) (w : SubLineRaw P)
    (hx : chiIndex P.toLdParams w.2.1 = subLineXIndex P k)
    (hz : chiIndex P.toLdParams w.2.2 = subLineZIndex P k)
    {u : Fin P.extendedDirectLd.m → DirectScalarQ P.extendedDirectLd}
    (hu : u ∈ (subLineTripleOf P kind k w).1.pointSet) :
    projX (directPointToPauli P u) ∈
        (subLineTripleOf P kind k w).2.1.pointSet ∧
      projZ (directPointToPauli P u) ∈
        (subLineTripleOf P kind k w).2.2.pointSet :=
  ⟨projX_mem_pointSet P _ _ _ (subLineTripleOf_xBase P kind k w hx)
      (subLineTripleOf_xSpan P kind k w hx) hu,
    projZ_mem_pointSet P _ _ _ (subLineTripleOf_zBase P kind k w hz)
      (subLineTripleOf_zSpan P kind k w hz) hu⟩

/-- Every sampled triple carries affine data sufficient for
`combineLinePoly_spec`.  Blueprint `lem:qld-sublines`, paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1063-1116`. -/
theorem subLineTripleOf_compatibility (P : AdmissibleParams) (kind : LineKind)
    (k : Fin (2 * P.m + 2)) (w : SubLineRaw P)
    (hx : chiIndex P.toLdParams w.2.1 = subLineXIndex P k)
    (hz : chiIndex P.toLdParams w.2.2 = subLineZIndex P k) :
    ∃ aX bX aZ bZ uAlpha vAlpha uBeta vBeta : PauliScalar P,
      IsCombineLineCompatible
        (directPointToPauli P (subLineTripleOf P kind k w).1.base)
        (directPointToPauli P (subLineTripleOf P kind k w).1.direction)
        (subLineTripleOf P kind k w).2.1.base
        (subLineTripleOf P kind k w).2.1.direction
        (subLineTripleOf P kind k w).2.2.base
        (subLineTripleOf P kind k w).2.2.direction
        aX bX aZ bZ uAlpha vAlpha uBeta vBeta := by
  obtain ⟨aX, haX⟩ := Submodule.mem_span_singleton.mp
    (sub_lineRepMap_mem_span (subLineTripleOf P kind k w).2.1.direction
      (projX (directPointToPauli P (subLineTripleOf P kind k w).1.base)))
  obtain ⟨aZ, haZ⟩ := Submodule.mem_span_singleton.mp
    (sub_lineRepMap_mem_span (subLineTripleOf P kind k w).2.2.direction
      (projZ (directPointToPauli P (subLineTripleOf P kind k w).1.base)))
  obtain ⟨bX, hbX⟩ := Submodule.mem_span_singleton.mp
    (subLineTripleOf_xSpan P kind k w hx)
  obtain ⟨bZ, hbZ⟩ := Submodule.mem_span_singleton.mp
    (subLineTripleOf_zSpan P kind k w hz)
  have hXblock :
      projX (directPointToPauli P (subLineTripleOf P kind k w).1.base) =
        (subLineTripleOf P kind k w).2.1.base +
          aX • (subLineTripleOf P kind k w).2.1.direction := by
    rw [subLineTripleOf_xBase P kind k w hx, haX]
    abel
  have hZblock :
      projZ (directPointToPauli P (subLineTripleOf P kind k w).1.base) =
        (subLineTripleOf P kind k w).2.2.base +
          aZ • (subLineTripleOf P kind k w).2.2.direction := by
    rw [subLineTripleOf_zBase P kind k w hz, haZ]
    abel
  have hcompat := isCombineLineCompatible_of_blocks
    (directPointToPauli P (subLineTripleOf P kind k w).1.base)
    (directPointToPauli P (subLineTripleOf P kind k w).1.direction)
    (subLineTripleOf P kind k w).2.1.base
    (subLineTripleOf P kind k w).2.1.direction
    (subLineTripleOf P kind k w).2.2.base
    (subLineTripleOf P kind k w).2.2.direction
    aX bX aZ bZ hXblock hbX.symm hZblock hbZ.symm
  exact ⟨aX, bX, aZ, bZ, _, _, _, _, hcompat⟩

/-- An extended axis line of a sampled triple has axis-parallel source lines.
Blueprint `lem:qld-sublines`, paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1063-1116`. -/
theorem subLineTripleOf_axis_closure (P : AdmissibleParams) (kind : LineKind)
    (k : Fin (2 * P.m + 2)) (w : SubLineRaw P)
    (haxis : (subLineTripleOf P kind k w).1.kind = .axis) :
    (subLineTripleOf P kind k w).2.1.kind = .axis ∧
      (subLineTripleOf P kind k w).2.2.kind = .axis := by
  have hkind : kind = .axis := by
    have h : (subLineTripleOf P kind k w).1.kind = kind :=
      subLineExtLine_kind P kind k w
    rw [← h]
    exact haxis
  subst hkind
  exact ⟨subLineSourceLine_kind P .axis _ _ _,
    subLineSourceLine_kind P .axis _ _ _⟩

/-! ## Total mass and extended marginal -/

/-- The sub-line law has total mass one. -/
theorem subLineDist_isProbability (P : AdmissibleParams) :
    (subLineDist P).IsProbability := by
  refine Distribution.bind_isProbability _ _
    (uniformDistribution_isProbability _) fun c _ => ?_
  fin_cases c
  · exact Distribution.IsProbability.map (subLineRawDist_isProbability P) _
  · exact Distribution.IsProbability.map (subLineRawDist_isProbability P) _

/-- The index-first decomposition of an extended direct sample, read at the
bare extended dimension.  This is the decomposition
`directLdSpaceIndexEquiv` of `def:ld-question-distribution` with its stored
coordinate typed by the bare dimension `2 m + 2`. -/
private def subLineSampleEquiv (P : AdmissibleParams) :
    DirectLdSpace P.extendedDirectLd ≃
      Fin (2 * P.m + 2) × SubLinePointDir P where
  toFun s := (s.index, s.point, s.direction)
  invFun w := ⟨w.2.1, w.1, w.2.2⟩
  left_inv s := by cases s; rfl
  right_inv w := by cases w; rfl

/-- The extended-line marginal of one branch of the sub-line law is the law of
the canonical line of the corresponding kind through a uniformly sampled
extended direct sample.  Blueprint `lem:qld-sublines`, paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1063-1116`. -/
theorem subLineBranchDist_map_fst (P : AdmissibleParams) (kind : LineKind) :
    (subLineBranchDist P kind).map Prod.fst =
      (uniformDistribution (DirectLdSpace P.extendedDirectLd)).map
        (subLineExtLineOfSample P kind) := by
  classical
  have hstep1 : (subLineBranchDist P kind).map Prod.fst =
      Distribution.bind (uniformDistribution (Fin (2 * P.m + 2))) fun k =>
        (Distribution.prod (uniformDistribution (SubLinePointDir P))
            (Distribution.prod (subLineSeedDist P (subLineXIndex P k))
              (subLineSeedDist P (subLineZIndex P k)))).map
          fun w => subLineExtLineOfSample P kind ⟨w.1.1, k, w.1.2⟩ := by
    rw [subLineBranchDist, Distribution.map_map, subLineRawDist,
      Distribution.bind_map]
    refine Distribution.bind_congr_support _ _ _ fun k _ => ?_
    rw [Distribution.map_map]
    rfl
  have hstep2 : ∀ k : Fin (2 * P.m + 2),
      (Distribution.prod (uniformDistribution (SubLinePointDir P))
          (Distribution.prod (subLineSeedDist P (subLineXIndex P k))
            (subLineSeedDist P (subLineZIndex P k)))).map
        (fun w => subLineExtLineOfSample P kind ⟨w.1.1, k, w.1.2⟩) =
      (uniformDistribution (SubLinePointDir P)).map
        (fun pd => subLineExtLineOfSample P kind ⟨pd.1, k, pd.2⟩) := by
    intro k
    exact Distribution.prod_map_of_fst
      (uniformDistribution (SubLinePointDir P))
      (Distribution.prod (subLineSeedDist P (subLineXIndex P k))
        (subLineSeedDist P (subLineZIndex P k)))
      (Distribution.prod_isProbability
        (subLineSeedDist P (subLineXIndex P k))
        (subLineSeedDist P (subLineZIndex P k))
        (subLineSeedDist_isProbability P (subLineXIndex P k))
        (subLineSeedDist_isProbability P (subLineZIndex P k)))
      (fun pd => subLineExtLineOfSample P kind ⟨pd.1, k, pd.2⟩)
  have hstep3 :
      Distribution.bind (uniformDistribution (Fin (2 * P.m + 2))) (fun k =>
        (uniformDistribution (SubLinePointDir P)).map
          (fun pd => subLineExtLineOfSample P kind ⟨pd.1, k, pd.2⟩)) =
      (uniformDistribution (Fin (2 * P.m + 2) × SubLinePointDir P)).map
        (fun w => subLineExtLineOfSample P kind ⟨w.2.1, w.1, w.2.2⟩) := by
    rw [uniformDistribution_prod (Fin (2 * P.m + 2)) (SubLinePointDir P)]
    exact (Distribution.prod_map_eq_bind
      (uniformDistribution (Fin (2 * P.m + 2)))
      (uniformDistribution (SubLinePointDir P))
      (fun w => subLineExtLineOfSample P kind ⟨w.2.1, w.1, w.2.2⟩)).symm
  have hstep4 :
      (uniformDistribution (Fin (2 * P.m + 2) × SubLinePointDir P)).map
        (fun w => subLineExtLineOfSample P kind ⟨w.2.1, w.1, w.2.2⟩) =
      (uniformDistribution (DirectLdSpace P.extendedDirectLd)).map
        (subLineExtLineOfSample P kind) := by
    rw [← uniformDistribution_map_equiv (subLineSampleEquiv P),
      Distribution.map_map]
    rfl
  rw [hstep1, Distribution.bind_congr_support _ _ _ (fun k _ => hstep2 k),
    hstep3, hstep4]

/-- The extended-line marginal of the sub-line law is the extended-line
marginal of the directly indexed line-point law.  Blueprint
`lem:qld-sublines`, paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1063-1116`. -/
theorem subLineDist_map_fst (P : AdmissibleParams) :
    (subLineDist P).map Prod.fst =
      (directLinePointDist P.extendedDirectLd).map Prod.fst := by
  classical
  have haxis : (subLineBranchDist P .axis).map Prod.fst =
      (directALinePointDist P.extendedDirectLd).map Prod.fst := by
    rw [subLineBranchDist_map_fst, directALinePointDist, Distribution.map_map]
    rfl
  have hdiag : (subLineBranchDist P .diagonal).map Prod.fst =
      (directDLinePointDist P.extendedDirectLd).map Prod.fst := by
    rw [subLineBranchDist_map_fst, directDLinePointDist, Distribution.map_map]
    rfl
  rw [subLineDist, Distribution.bind_map, directLinePointDist,
    ← Distribution.bind_uniform_fin_two, Distribution.bind_map]
  refine Distribution.bind_congr_support _ _ _ fun c _ => ?_
  fin_cases c
  · exact haxis
  · exact hdiag

end

end MIPStarRE.QPBT
