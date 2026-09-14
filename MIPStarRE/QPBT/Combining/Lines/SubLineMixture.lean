import MIPStarRE.QPBT.Combining.Lines.SubLineSource

/-!
# The projected mixtures of the sub-line law

This module assembles the two projected point marginals of the sub-line law of
`lem:qld-sublines` into mixtures of the restricted product laws.  Drawing a
uniform point of the extended line of a mixture of line laws is the same
mixture of the corresponding uniform-point laws, so the two projected
marginals of the sub-line law are the mixtures, over the drawn kind and the
drawn extended coordinate, of the projected marginals of one branch at one
extended coordinate.  Each of those is the component law of the pair of
indices carried by that branch, so the mixing law is the law of the kind
together with the pair of indices assigned to a uniform extended coordinate.

## References

The assembly is the last step of the proof of `lem:qld-sublines` in
blueprint `lem:qld-sublines`, whose source is
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1063-1116`.
The restricted laws are `def:ith-restricted-line`, blueprint lines
1209--1228, paper lines 1038--1048.
-/

open scoped BigOperators

namespace MIPStarRE.QPBT

open MIPStarRE.LDT

noncomputable section

/-! ## The uniform point of a mixture of line laws -/

/-- Drawing a uniform point of the extended line of a mixture of line-triple
laws is the corresponding mixture of the uniform-point laws.  Blueprint
`lem:qld-sublines`, paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1063-1116`. -/
theorem subLinePointDist_bind (P : AdmissibleParams) {α : Type*}
    (μ : Distribution α) (ν : α → Distribution (SubLineTriple P)) :
    subLinePointDist P (Distribution.bind μ ν) =
      Distribution.bind μ (fun a => subLinePointDist P (ν a)) := by
  classical
  unfold subLinePointDist
  rw [Distribution.prod_bind_left, Distribution.bind_map]

/-! ## The projected marginals of one branch at one extended coordinate -/

/-- One branch of the sampling procedure, read at a fixed extended coordinate,
is the law of the triple decoded from the auxiliary randomness of that
coordinate.  Blueprint `lem:qld-sublines`, paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1063-1116`. -/
theorem subLineBranchDist_eq_bind (P : AdmissibleParams) (kind : LineKind) :
    subLineBranchDist P kind =
      Distribution.bind (uniformDistribution (Fin (2 * P.m + 2))) fun k =>
        (Distribution.prod (uniformDistribution (SubLinePointDir P))
            (Distribution.prod (subLineSeedDist P (subLineXIndex P k))
              (subLineSeedDist P (subLineZIndex P k)))).map
          fun w => subLineTripleOf P kind k w := by
  classical
  rw [subLineBranchDist, subLineRawDist, Distribution.bind_map]
  refine Distribution.bind_congr_support _ _ _ fun k _ => ?_
  rw [Distribution.map_map]

/-- The `X` marginal of a uniform point of the extended line of one branch at
one extended coordinate is the `X` component law of the pair of indices of
that branch.  Blueprint `lem:qld-sublines`, paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1063-1116`. -/
theorem subLineBranchDist_map_subLineXProjection_at (P : AdmissibleParams)
    (kind : LineKind) (k : Fin (2 * P.m + 2)) :
    (subLinePointDist P
        ((Distribution.prod (uniformDistribution (SubLinePointDir P))
            (Distribution.prod (subLineSeedDist P (subLineXIndex P k))
              (subLineSeedDist P (subLineZIndex P k)))).map
          fun w => subLineTripleOf P kind k w)).map subLineXProjection =
      subLineXComponentDist P
        (kind, (subLineXIndex P k, subLineZIndex P k)) := by
  classical
  unfold subLinePointDist
  rw [Distribution.prod_map_left, Distribution.map_map, Distribution.map_map]
  exact subLineBranchRaw_map_projX P kind k

/-- The `Z` marginal of a uniform point of the extended line of one branch at
one extended coordinate is the `Z` component law of the pair of indices of
that branch.  Blueprint `lem:qld-sublines`, paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1063-1116`. -/
theorem subLineBranchDist_map_subLineZProjection_at (P : AdmissibleParams)
    (kind : LineKind) (k : Fin (2 * P.m + 2)) :
    (subLinePointDist P
        ((Distribution.prod (uniformDistribution (SubLinePointDir P))
            (Distribution.prod (subLineSeedDist P (subLineXIndex P k))
              (subLineSeedDist P (subLineZIndex P k)))).map
          fun w => subLineTripleOf P kind k w)).map subLineZProjection =
      subLineZComponentDist P
        (kind, (subLineXIndex P k, subLineZIndex P k)) := by
  classical
  unfold subLinePointDist
  rw [Distribution.prod_map_left, Distribution.map_map, Distribution.map_map]
  exact subLineBranchRaw_map_projZ P kind k

/-! ## The mixing law of the two indices -/

/-- The law of the kind and the pair of source indices assigned to a uniform
extended coordinate of one branch.  Blueprint
`lem:qld-sublines`, paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1063-1116`. -/
noncomputable def subLineComponentBranch (P : AdmissibleParams)
    (kind : LineKind) : Distribution (SubLineComponent P) :=
  (uniformDistribution (Fin (2 * P.m + 2))).map fun k =>
    (kind, (subLineXIndex P k, subLineZIndex P k))

/-- The mixing law of the sub-line lemma: the equal mixture over the two kinds
of the law of the pair of source indices of a uniform extended coordinate.
Blueprint `lem:qld-sublines`, paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1063-1116`. -/
noncomputable def subLineComponentDist (P : AdmissibleParams) :
    Distribution (SubLineComponent P) :=
  Distribution.bind (uniformDistribution (Fin 2))
    ![subLineComponentBranch P .axis, subLineComponentBranch P .diagonal]

/-- The mixing law has total mass one. -/
theorem subLineComponentDist_isProbability (P : AdmissibleParams) :
    (subLineComponentDist P).IsProbability := by
  refine Distribution.bind_isProbability _ _
    (uniformDistribution_isProbability _) fun c _ => ?_
  fin_cases c
  · exact Distribution.IsProbability.map
      (uniformDistribution_isProbability _) _
  · exact Distribution.IsProbability.map
      (uniformDistribution_isProbability _) _

/-! ## The two projected marginals of one branch -/

/-- The `X` marginal of a uniform point of the extended line of one branch is
the mixture, along the pair of source indices of a uniform extended
coordinate, of the `X` component laws.  Blueprint
`lem:qld-sublines`, paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1063-1116`. -/
theorem subLineBranchDist_map_subLineXProjection (P : AdmissibleParams)
    (kind : LineKind) :
    (subLinePointDist P (subLineBranchDist P kind)).map subLineXProjection =
      Distribution.bind (subLineComponentBranch P kind)
        (subLineXComponentDist P) := by
  classical
  rw [subLineBranchDist_eq_bind, subLinePointDist_bind, Distribution.bind_map,
    subLineComponentBranch, Distribution.bind_map_left]
  refine Distribution.bind_congr_support _ _ _ fun k _ => ?_
  exact subLineBranchDist_map_subLineXProjection_at P kind k

/-- The `Z` marginal of a uniform point of the extended line of one branch is
the mixture, along the pair of source indices of a uniform extended
coordinate, of the `Z` component laws.  Blueprint
`lem:qld-sublines`, paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1063-1116`. -/
theorem subLineBranchDist_map_subLineZProjection (P : AdmissibleParams)
    (kind : LineKind) :
    (subLinePointDist P (subLineBranchDist P kind)).map subLineZProjection =
      Distribution.bind (subLineComponentBranch P kind)
        (subLineZComponentDist P) := by
  classical
  rw [subLineBranchDist_eq_bind, subLinePointDist_bind, Distribution.bind_map,
    subLineComponentBranch, Distribution.bind_map_left]
  refine Distribution.bind_congr_support _ _ _ fun k _ => ?_
  exact subLineBranchDist_map_subLineZProjection_at P kind k

/-! ## The two projected marginals of the sub-line law -/

/-- The `X` point marginal of the sub-line law is the mixture of the `X`
component laws along the mixing law.  Blueprint
`lem:qld-sublines`, paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1063-1116`. -/
theorem subLineDist_map_subLineXProjection (P : AdmissibleParams) :
    (subLinePointDist P (subLineDist P)).map subLineXProjection =
      Distribution.bind (subLineComponentDist P) (subLineXComponentDist P) := by
  classical
  rw [subLineDist, subLinePointDist_bind, Distribution.bind_map,
    subLineComponentDist, Distribution.bind_bind]
  refine Distribution.bind_congr_support _ _ _ fun c _ => ?_
  fin_cases c
  · exact subLineBranchDist_map_subLineXProjection P .axis
  · exact subLineBranchDist_map_subLineXProjection P .diagonal

/-- The `Z` point marginal of the sub-line law is the mixture of the `Z`
component laws along the mixing law.  Blueprint
`lem:qld-sublines`, paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1063-1116`. -/
theorem subLineDist_map_subLineZProjection (P : AdmissibleParams) :
    (subLinePointDist P (subLineDist P)).map subLineZProjection =
      Distribution.bind (subLineComponentDist P) (subLineZComponentDist P) := by
  classical
  rw [subLineDist, subLinePointDist_bind, Distribution.bind_map,
    subLineComponentDist, Distribution.bind_bind]
  refine Distribution.bind_congr_support _ _ _ fun c _ => ?_
  fin_cases c
  · exact subLineBranchDist_map_subLineZProjection P .axis
  · exact subLineBranchDist_map_subLineZProjection P .diagonal

/-- The two one-point projected marginals of the sub-line law are mixtures of
the restricted product laws along one common mixing law.  Blueprint
`lem:qld-sublines`, paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1063-1116`. -/
theorem subLineDist_source_mixture (P : AdmissibleParams) :
    ∃ components : Distribution (SubLineComponent P),
      components.IsProbability ∧
        (subLinePointDist P (subLineDist P)).map subLineXProjection =
          Distribution.bind components (subLineXComponentDist P) ∧
        (subLinePointDist P (subLineDist P)).map subLineZProjection =
          Distribution.bind components (subLineZComponentDist P) :=
  ⟨subLineComponentDist P, subLineComponentDist_isProbability P,
    subLineDist_map_subLineXProjection P,
    subLineDist_map_subLineZProjection P⟩

end

end MIPStarRE.QPBT
