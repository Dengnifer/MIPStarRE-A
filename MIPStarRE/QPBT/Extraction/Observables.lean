import MIPStarRE.QPBT.Algebra.Decoding
import MIPStarRE.QPBT.Combining.Witnesses
import MIPStarRE.QPBT.Extraction.Defs

/-!
# Pulled-apart Pauli observables

This module constructs the measurements and observables used to pull the two
Pauli bases onto separate registers. The construction retains the distinct
local spaces of the two players and uses the binary basis fixed in the
canonical field model.

## References

The product form and observable relations formalize `lem:tildew-product-form`
in `blueprint/src/chapter/ch16_qpbt_extraction.tex:75-88`, from
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1415-1456`.
The swap identities formalize
`lem:v-swap-conjugation`, blueprint lines 208-243 and paper lines 1687-1713.
-/

open scoped BigOperators Matrix

namespace MIPStarRE.QPBT

open MIPStarRE.LDT MIPStarRE.LDT.Preliminaries MIPStarRE.Quantum

noncomputable section

/-! ## Pulled-apart measurements and observables -/

namespace PauliKind

/-- Select the polynomial belonging to a Pauli basis from a joint polynomial
outcome. This is the marginalization used at paper
`14_analysis_of_the_pauli_basis_test.tex:1421-1423` and blueprint
`ch16_qpbt_extraction.tex:35-44`. -/
def selectPoly {P : AdmissibleParams} (W : PauliKind) : PolyPair P -> Poly P
  | pair => match W with
    | .X => pair.1
    | .Z => pair.2

end PauliKind

namespace GlobalPairWitness

/-- The single-basis marginal of the global polynomial-pair measurement.
This is `def:s-w-marginals`, blueprint
`ch16_qpbt_extraction.tex:35-44`, paper
`14_analysis_of_the_pauli_basis_test.tex:1421-1423`. -/
noncomputable def marginalPoly {P : AdmissibleParams} {epsilon delta : ℝ}
    {S : ProjectiveSetting P epsilon} (w : GlobalPairWitness S delta)
    (side : PlayerSide) (W : PauliKind) :
    Measurement (Poly P) (S.ExpandedLocalSpace side) :=
  (w.Smeas side).postprocess W.selectPoly

/-- The single-basis marginal remains a projective measurement. This is the
projectivity assertion implicit in `def:s-w-marginals`, blueprint
`ch16_qpbt_extraction.tex:35-44`, paper
`14_analysis_of_the_pauli_basis_test.tex:1421-1423`.

**Proof obligation:** issue #19 tracks the preservation of projectivity under
the finite postprocessing map `PauliKind.selectPoly`. -/
theorem marginalPoly_isProjective {P : AdmissibleParams} {epsilon delta : ℝ}
    {S : ProjectiveSetting P epsilon} (w : GlobalPairWitness S delta)
    (side : PlayerSide) (W : PauliKind) :
    Measurement.IsProjective (w.marginalPoly side W) := by
  sorry

end GlobalPairWitness

/-- The pulled-apart projective-measurement effect from Equation `eq:tilde_M`.
The polynomial marginal acts on the player's expanded local space and the
dot-product projector acts on the newly adjoined register. Blueprint
`ch16_qpbt_extraction.tex:55-62`; paper
`14_analysis_of_the_pauli_basis_test.tex:1425-1435`. -/
noncomputable def tildeM {P : AdmissibleParams} {epsilon delta : ℝ}
    {S : ProjectiveSetting P epsilon} (w : GlobalPairWitness S delta)
    (side : PlayerSide) (W : PauliKind) (u : PauliRegister P)
    (a : PauliScalar P) : Op (ExtractionBlock P (S.LocalSpace side)) :=
  ∑ g : Poly P,
    heteroKron ((w.marginalPoly side W).effect g)
      (tauDotProj W u (dotProduct (decodeFq g) u - a))

/-- Each pulled-apart effect is a projector, as asserted in
`def:tilde-m-measurement`, blueprint `ch16_qpbt_extraction.tex:55-62`, paper
`14_analysis_of_the_pauli_basis_test.tex:1425-1435`.

**Proof obligation:** issue #19 tracks the orthogonal-sum calculation using
`marginalPoly_isProjective` and `tauDotProj_isProj`. -/
theorem tildeM_isProj {P : AdmissibleParams} {epsilon delta : ℝ}
    {S : ProjectiveSetting P epsilon} (w : GlobalPairWitness S delta)
    (side : PlayerSide) (W : PauliKind) (u : PauliRegister P)
    (a : PauliScalar P) :
    IsProj (tildeM w side W u a) := by
  sorry

/-- The pulled-apart effects are complete for each fixed basis and Pauli
register vector. This is the completeness assertion in
`def:tilde-m-measurement`, blueprint `ch16_qpbt_extraction.tex:55-62`, paper
`14_analysis_of_the_pauli_basis_test.tex:1425-1435`.

**Proof obligation:** issue #19 tracks summing the orthogonal dot-product
projectors and the polynomial marginal effects. -/
theorem sum_tildeM_eq_one {P : AdmissibleParams} {epsilon delta : ℝ}
    {S : ProjectiveSetting P epsilon} (w : GlobalPairWitness S delta)
    (side : PlayerSide) (W : PauliKind) (u : PauliRegister P) :
    ∑ a : PauliScalar P, tildeM w side W u a = 1 := by
  sorry

/-- The binary observable obtained from the trace coarse-graining of `tildeM`.
This is Equation `eq:def-tildewj` in `def:tilde-w-observables`, blueprint
`ch16_qpbt_extraction.tex:64-71`, paper
`14_analysis_of_the_pauli_basis_test.tex:1437-1442`. -/
noncomputable def tildeObs {P : AdmissibleParams} {epsilon delta : ℝ}
    {S : ProjectiveSetting P epsilon} (w : GlobalPairWitness S delta)
    (side : PlayerSide) (W : PauliKind) (u : PauliRegister P)
    (j : Fin P.model.basisDim) : Op (ExtractionBlock P (S.LocalSpace side)) :=
  ∑ a : PauliScalar P,
    phaseSign (fixedBinTrace P.model (P.model.basis j * a)) •
      tildeM w side W u a

/-- Product form of the pulled-apart observable, Equation
`eq:tildewj-product-form` of `lem:tildew-product-form`. Blueprint
`ch16_qpbt_extraction.tex:75-88`; paper
`14_analysis_of_the_pauli_basis_test.tex:1442-1450`.

**Proof obligation:** issue #19 tracks the finite Fourier regrouping needed to
derive this equality from `tauObservable_eq_sum_pauliProj`. Discharge: expand
the two finite sums and reindex the Pauli outcomes by their dot product. -/
theorem tildeObs_eq_heteroKron {P : AdmissibleParams} {epsilon delta : ℝ}
    {S : ProjectiveSetting P epsilon} (w : GlobalPairWitness S delta)
    (side : PlayerSide) (W : PauliKind) (u : PauliRegister P)
    (j : Fin P.model.basisDim) :
    tildeObs w side W u j =
      heteroKron
        (∑ pair : PolyPair P,
          phaseSign (fixedBinTrace P.model
            (P.model.basis j * dotProduct (decodeFq (W.selectPoly pair)) u)) •
            (w.Smeas side).effect pair)
        (tauObservable W (P.model.basis j • u)) := by
  sorry

/-- Every pulled-apart observable is Hermitian, as asserted in
`lem:tildew-product-form`, blueprint `ch16_qpbt_extraction.tex:75-88`, paper
`14_analysis_of_the_pauli_basis_test.tex:1450`.

**Proof obligation:** issue #19 tracks this consequence of the product form.
Discharge: use projectivity of `w.Smeas side` and Hermiticity of the generalized
Pauli observable. -/
theorem tildeObs_isHermitian {P : AdmissibleParams} {epsilon delta : ℝ}
    {S : ProjectiveSetting P epsilon} (w : GlobalPairWitness S delta)
    (side : PlayerSide) (W : PauliKind) (u : PauliRegister P)
    (j : Fin P.model.basisDim) :
    (tildeObs w side W u j).IsHermitian := by
  sorry

/-- Every pulled-apart observable squares to the identity, as asserted in
`lem:tildew-product-form`, blueprint `ch16_qpbt_extraction.tex:75-88`, paper
`14_analysis_of_the_pauli_basis_test.tex:1450`.

**Proof obligation:** issue #19 tracks this consequence of the product form.
Discharge: eliminate cross terms using the orthogonality of `w.Smeas side` and
use that `tauObservable` is self-inverse. -/
theorem tildeObs_mul_self {P : AdmissibleParams} {epsilon delta : ℝ}
    {S : ProjectiveSetting P epsilon} (w : GlobalPairWitness S delta)
    (side : PlayerSide) (W : PauliKind) (u : PauliRegister P)
    (j : Fin P.model.basisDim) :
    tildeObs w side W u j * tildeObs w side W u j = 1 := by
  sorry

/-- The corrected twisted commutation relation for pulled-apart observables.
This is Equation `eq:tildew-twisted-commutation` in blueprint
`ch16_qpbt_extraction.tex:82-87`, correcting paper
`14_analysis_of_the_pauli_basis_test.tex:1451-1456`.

**Local fix:** the paper drops this phase when `j != j'`, which is false for
general register vectors; see `docs/paper-gaps/qpbt_cross-basis-phase.tex`.
Issue #19 tracks the proof. Discharge: combine both product forms with
`tauObservable_X_mul_Z`. -/
theorem tildeObs_twisted_commutation {P : AdmissibleParams}
    {epsilon delta : ℝ} {S : ProjectiveSetting P epsilon}
    (w : GlobalPairWitness S delta) (side : PlayerSide)
    (u v : PauliRegister P) (j j' : Fin P.model.basisDim) :
    tildeObs w side .X u j * tildeObs w side .Z v j' =
      phaseSign (fixedBinTrace P.model
        (P.model.basis j * P.model.basis j' * dotProduct u v)) •
        (tildeObs w side .Z v j' * tildeObs w side .X u j) := by
  sorry

/-! ## Swap conjugation -/

/-- The swap map built from the global polynomial-pair measurement, with the
crossed decoded arguments required by `def:v-swap-unitary`. Blueprint
`ch16_qpbt_extraction.tex:208-215`; paper
`14_analysis_of_the_pauli_basis_test.tex:1687-1700`. -/
noncomputable def swapUnitary {P : AdmissibleParams} {epsilon delta : ℝ}
    {S : ProjectiveSetting P epsilon} (w : GlobalPairWitness S delta)
    (side : PlayerSide) : Op (ExtractionBlock P (S.LocalSpace side)) :=
  ∑ pair : PolyPair P,
    heteroKron ((w.Smeas side).effect pair)
      (tauObservable .X (decodeFq pair.2) *
        tauObservable .Z (decodeFq pair.1))

/-- The swap map is a right unitary. This is the first exact unitarity
calculation of `lem:v-swap-conjugation`, blueprint
`ch16_qpbt_extraction.tex:219-226`, paper
`14_analysis_of_the_pauli_basis_test.tex:1687-1699`.

**Proof obligation:** issue #19 tracks the finite projector calculation.
Discharge: use projectivity and completeness of `w.Smeas side` together with
self-inverseness of both generalized Pauli observables. -/
theorem swapUnitary_mul_conjTranspose {P : AdmissibleParams}
    {epsilon delta : ℝ} {S : ProjectiveSetting P epsilon}
    (w : GlobalPairWitness S delta) (side : PlayerSide) :
    swapUnitary w side * (swapUnitary w side)ᴴ = 1 := by
  sorry

/-- The swap map is a left unitary. This is the reverse exact unitarity
calculation implicit in `lem:v-swap-conjugation`, blueprint
`ch16_qpbt_extraction.tex:219-226`, paper
`14_analysis_of_the_pauli_basis_test.tex:1687-1699`.

**Proof obligation:** issue #19 tracks the reverse projector calculation.
Discharge: use the same orthogonality and Pauli involution identities as in
`swapUnitary_mul_conjTranspose`. -/
theorem conjTranspose_mul_swapUnitary {P : AdmissibleParams}
    {epsilon delta : ℝ} {S : ProjectiveSetting P epsilon}
    (w : GlobalPairWitness S delta) (side : PlayerSide) :
    (swapUnitary w side)ᴴ * swapUnitary w side = 1 := by
  sorry

/-- Exact conjugation of a pulled-apart observable by the swap map. This is
Equation `eq:v-swap-obs-conjugation` in `lem:v-swap-conjugation`, blueprint
`ch16_qpbt_extraction.tex:219-226`, paper
`14_analysis_of_the_pauli_basis_test.tex:1701-1713`.

**Proof obligation:** issue #19 tracks the diagonal projector reduction.
Discharge: substitute `tildeObs_eq_heteroKron`, eliminate off-diagonal outcomes,
and cancel the phase using `tauObservable_X_mul_Z`. -/
theorem swapUnitary_conj_tildeObs {P : AdmissibleParams}
    {epsilon delta : ℝ} {S : ProjectiveSetting P epsilon}
    (w : GlobalPairWitness S delta) (side : PlayerSide) (W : PauliKind)
    (u : PauliRegister P) (j : Fin P.model.basisDim) :
    conjBy (swapUnitary w side) (tildeObs w side W u j) =
      heteroKron (1 : Op (S.ExpandedLocalSpace side))
        (tauObservable W (P.model.basis j • u)) := by
  sorry

/-- Exact conjugation of a pulled-apart point effect by the swap map. This is
Equation `eq:qld-unitary-6` in `lem:v-swap-conjugation`, blueprint
`ch16_qpbt_extraction.tex:227-233`; its calculation occurs at paper
`14_analysis_of_the_pauli_basis_test.tex:1805-1822`.

**Proof obligation:** issue #19 tracks the exact relabeling calculation.
Discharge: expand `tildeM`, conjugate each Pauli projector, and translate the
dot-product constraint with `lowDegreeEnc_eq_dotProduct`; no unrestricted
decoder interpolation identity is used. -/
theorem swapUnitary_conj_tildeM {P : AdmissibleParams}
    {epsilon delta : ℝ} {S : ProjectiveSetting P epsilon}
    (w : GlobalPairWitness S delta) (side : PlayerSide) (W : PauliKind)
    (u : Fin P.m -> PauliScalar P) (a : PauliScalar P) :
    conjBy (swapUnitary w side) (tildeM w side W (indicatorVec u) a) =
      heteroKron (1 : Op (S.ExpandedLocalSpace side))
        (bracketOp (pauliProj W) (fun h => lowDegreeEnc h u) a) := by
  sorry

end

end MIPStarRE.QPBT
