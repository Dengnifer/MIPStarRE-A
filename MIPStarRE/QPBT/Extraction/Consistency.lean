import MIPStarRE.QPBT.Extraction.Observables

/-!
# Consistency of the pulled-apart Pauli measurements

This module records the two estimates by which the polynomial marginals absorb
the expanded point measurements, with both heterogeneous player placements
written explicitly. It also states the consistency of the pulled-apart
measurements with the original point measurements and the self-consistency of
the corresponding observables.

## References

The marginal estimates formalize `lem:qld-constructing-the-paulis-helper` in
`blueprint/src/chapter/ch16_qpbt_extraction.tex:176-203`, from
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1609-1664`.
The remaining declarations formalize `lem:qld-construct-the-paulis` in
blueprint lines 105-168, from paper lines 1458-1608.
-/

open scoped BigOperators Matrix

namespace MIPStarRE.QPBT

open MIPStarRE.LDT MIPStarRE.Quantum

noncomputable section

/-! ## Absorption of expanded point measurements -/

/-- The polynomial marginal and the opposite player's expanded point
measurement resolve the identity on average. The two conjuncts are the
`AA'`--`BA''` and `BB'`--`AB''` instances of the source's symmetric-equivalents
clause.

This is Equation `eq:qld-sg-cons` of
`lem:qld-constructing-the-paulis-helper`, blueprint
`ch16_qpbt_extraction.tex:176-186`, paper
`14_analysis_of_the_pauli_basis_test.tex:1609-1635`.

The source absorbs constant factors and the game error into `deltaS`. Here
`deltaG` is the raw global-witness error, and `deltaConstructPaulis` records
that enlargement explicitly.

**Proof obligation:** issue #47 tracks the agreement calculation converting
`GlobalPairWitness.point_consistent_alice` and its Bob-side counterpart into
these two identity estimates. -/
theorem sum_marginalPoly_pointMeas_approx_id :
    ∃ C : ℝ, 1 ≤ C ∧
      ∀ (P : AdmissibleParams) (epsilon deltaG : ℝ),
        0 ≤ epsilon → epsilon ≤ 1 → 0 ≤ deltaG →
          ∀ (S : ProjectiveSetting P epsilon)
            (w : GlobalPairWitness S deltaG) (W : PauliKind),
            opDistSq (uniformDistribution (Fin P.m → PauliScalar P))
              (fun u => ∑ g : Poly P,
                S.place .AA' ((w.marginalPoly .alice W).effect g) *
                  S.place .BA'' ((S.pointMeasExp .bob W u).effect
                    (MvPolynomial.eval u g.1)))
              (fun _ => 1) S.psiHat ≤
                deltaConstructPaulis C epsilon deltaG P.m P.d P.q ∧
            opDistSq (uniformDistribution (Fin P.m → PauliScalar P))
              (fun u => ∑ g : Poly P,
                S.place .BB' ((w.marginalPoly .bob W).effect g) *
                  S.place .AB'' ((S.pointMeasExp .alice W u).effect
                    (MvPolynomial.eval u g.1)))
              (fun _ => 1) S.psiHat ≤
                deltaConstructPaulis C epsilon deltaG P.m P.d P.q := by
  sorry

/-- Each polynomial marginal annihilates the complement of the corresponding
same-side expanded point effect on average. The answer summation is over the
polynomial outcome, and both `AA'` and `BB'` placements are stated explicitly.

This is Equation `eq:qld-sg-cons2` of
`lem:qld-constructing-the-paulis-helper`, blueprint
`ch16_qpbt_extraction.tex:176-203`, paper
`14_analysis_of_the_pauli_basis_test.tex:1617-1662`.

The explicit `deltaConstructPaulis` bound retains the point-measurement error
which the source absorbs into its adjusted `deltaS`.

**Proof obligation:** issue #47 tracks the projection-contraction and expanded
point self-consistency calculation at paper lines 1637-1662. -/
theorem marginalPoly_sub_pointMeas_approx_zero :
    ∃ C : ℝ, 1 ≤ C ∧
      ∀ (P : AdmissibleParams) (epsilon deltaG : ℝ),
        0 ≤ epsilon → epsilon ≤ 1 → 0 ≤ deltaG →
          ∀ (S : ProjectiveSetting P epsilon)
            (w : GlobalPairWitness S deltaG) (W : PauliKind),
            opFamilyDistSq (uniformDistribution (Fin P.m → PauliScalar P))
              (fun u g =>
                S.place .AA' ((w.marginalPoly .alice W).effect g) *
                  (1 - S.place .AA' ((S.pointMeasExp .alice W u).effect
                    (MvPolynomial.eval u g.1))))
              (fun _ _ => 0) S.psiHat ≤
                deltaConstructPaulis C epsilon deltaG P.m P.d P.q ∧
            opFamilyDistSq (uniformDistribution (Fin P.m → PauliScalar P))
              (fun u g =>
                S.place .BB' ((w.marginalPoly .bob W).effect g) *
                  (1 - S.place .BB' ((S.pointMeasExp .bob W u).effect
                    (MvPolynomial.eval u g.1))))
              (fun _ _ => 0) S.psiHat ≤
                deltaConstructPaulis C epsilon deltaG P.m P.d P.q := by
  sorry

/-! ## Non-encoding support -/

/-- The state-dependent mass assigned by a side's polynomial marginal to
outcomes outside the low-degree encoding image.  The finite support filter is
written explicitly so the restricted decoder identity is never applied to an
arbitrary polynomial representative.

This is the left-hand side of `eq:qld-nonencoding-mass` in
`blueprint/src/chapter/ch16_qpbt_extraction.tex:155-159`, from
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1458-1602`.
The bound remains a proposition-valued proof obligation, as required by
`docs/paper-gaps/qpbt_decoding-identity.tex:87-123`. -/
noncomputable def nonencodingMarginalMass {P : AdmissibleParams}
    {epsilon deltaS : ℝ} {S : ProjectiveSetting P epsilon}
    (w : GlobalPairWitness S deltaS) (side : PlayerSide) (W : PauliKind) : ℝ := by
  classical
  exact ∑ g ∈ Finset.univ.filter (fun g : Poly P => ¬ IsEncoding g),
    (inner ℂ S.psiHat
      (applyOperatorToState
        (S.placeSide side
          (heteroKron ((w.marginalPoly side W).effect g)
            (1 : Op (PauliRegister P))))
        S.psiHat)).re

/-- The non-encoding support estimate required by the Chapter 16 extraction
argument. For either player side and either Pauli basis, the marginal mass on
polynomial representatives outside the encoding image is bounded by the
common construction error.

This is the named obligation for `eq:qld-nonencoding-mass`, blueprint
`blueprint/src/chapter/ch16_qpbt_extraction.tex:155-159`, paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1458-1602`.
The estimate is intentionally not folded into a decoder identity; its proof
must use the point-consistency hypotheses and Schwartz--Zippel. See
`docs/paper-gaps/qpbt_decoding-identity.tex:87-123`.

**Proof obligation:** issue #47 tracks this support estimate. -/
theorem nonencodingMarginalMass_le :
    ∃ C : ℝ, 1 ≤ C ∧
      ∀ (P : AdmissibleParams) (epsilon deltaG : ℝ),
        0 ≤ epsilon → epsilon ≤ 1 → 0 ≤ deltaG →
          ∀ (S : ProjectiveSetting P epsilon)
            (w : GlobalPairWitness S deltaG)
            (side : PlayerSide) (W : PauliKind),
            nonencodingMarginalMass w side W ≤
              deltaConstructPaulis C epsilon deltaG P.m P.d P.q := by
  sorry

/-! ## Consistency of the pulled-apart measurements -/

/-- Alice's original point measurement is consistent with Bob's pulled-apart
measurement on average over uniformly random points. This is the first display
of Item 1 in `lem:qld-construct-the-paulis`, blueprint
`ch16_qpbt_extraction.tex:105-122`, paper
`14_analysis_of_the_pauli_basis_test.tex:1463-1492`.

The source reuses `deltaS` after absorbing the non-encoding and game-error
terms. The Lean conclusion keeps the raw witness error `deltaG` separate in
`deltaConstructPaulis`.

**Proof obligation:** issue #47 tracks the non-encoding-mass estimate required
by the restricted decoder identity; see
`docs/paper-gaps/qpbt_decoding-identity.tex`. -/
theorem tildeM_consistent_pointMeas :
    ∃ C : ℝ, 1 ≤ C ∧
      ∀ (P : AdmissibleParams) (epsilon deltaG : ℝ),
        0 ≤ epsilon → epsilon ≤ 1 → 0 ≤ deltaG →
          ∀ (S : ProjectiveSetting P epsilon)
            (w : GlobalPairWitness S deltaG) (W : PauliKind),
            consistencyDefect
              (uniformDistribution (Fin P.m → PauliScalar P))
              (fun u a =>
                S.placePlayer .alice ((S.pointMeas .alice W u).effect a))
              (fun u a => S.placeSide .bob
                (tildeM w .bob W (indicatorVec u) a))
              S.psiHat ≤
                deltaConstructPaulis C epsilon deltaG P.m P.d P.q := by
  sorry

/-- Alice's pulled-apart measurement is consistent with Bob's original point
measurement on average over uniformly random points. This is the
register-interchanged display of Item 1 in `lem:qld-construct-the-paulis`,
blueprint `ch16_qpbt_extraction.tex:105-122`, paper
`14_analysis_of_the_pauli_basis_test.tex:1463-1492`.

The conclusion uses the same explicit construction scale as the first player
ordering.

**Proof obligation:** issue #47 tracks the player-interchanged
non-encoding-mass argument. -/
theorem tildeM_consistent_pointMeas' :
    ∃ C : ℝ, 1 ≤ C ∧
      ∀ (P : AdmissibleParams) (epsilon deltaG : ℝ),
        0 ≤ epsilon → epsilon ≤ 1 → 0 ≤ deltaG →
          ∀ (S : ProjectiveSetting P epsilon)
            (w : GlobalPairWitness S deltaG) (W : PauliKind),
            consistencyDefect
              (uniformDistribution (Fin P.m → PauliScalar P))
              (fun u a => S.placeSide .alice
                (tildeM w .alice W (indicatorVec u) a))
              (fun u a =>
                S.placePlayer .bob ((S.pointMeas .bob W u).effect a))
              S.psiHat ≤
                deltaConstructPaulis C epsilon deltaG P.m P.d P.q := by
  sorry

/-- The pulled-apart observables on Alice's and Bob's extraction blocks are
self-consistent on average over the uniformly random Pauli register. This is
Item 2 of `lem:qld-construct-the-paulis`, blueprint
`ch16_qpbt_extraction.tex:123-167`, paper
`14_analysis_of_the_pauli_basis_test.tex:1476-1605`.

The construction scale exposes the square-root game error and
Schwartz--Zippel loss that the source absorbs into `deltaS`.

**Proof obligation:** issue #47 tracks the pulling-consistency calculation and
the final trace postprocessing from measurements to observables. -/
theorem tildeObs_selfConsistent :
    ∃ C : ℝ, 1 ≤ C ∧
      ∀ (P : AdmissibleParams) (epsilon deltaG : ℝ),
        0 ≤ epsilon → epsilon ≤ 1 → 0 ≤ deltaG →
          ∀ (S : ProjectiveSetting P epsilon)
            (w : GlobalPairWitness S deltaG) (W : PauliKind)
            (j : Fin P.model.basisDim),
            opDistSq (uniformDistribution (PauliRegister P))
              (fun u => S.placeSide .alice (tildeObs w .alice W u j))
              (fun u => S.placeSide .bob (tildeObs w .bob W u j))
              S.psiHat ≤
                deltaConstructPaulis C epsilon deltaG P.m P.d P.q := by
  sorry

end

end MIPStarRE.QPBT
