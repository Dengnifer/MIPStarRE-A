import MIPStarRE.QPBT.Algebra.Decoding
import MIPStarRE.QPBT.Combining.Witnesses
import MIPStarRE.QPBT.Extraction.Defs
import MIPStarRE.QPBT.Test.MagicSquareTheorems.Rigidity.Reflections

/-!
# Pulled-apart Pauli observables

This module constructs the measurements and observables used to pull the two
Pauli bases onto separate registers. The construction retains the distinct
local spaces of the two players and uses the binary basis fixed in the
canonical field model.

## References

The product form and observable relations formalize blueprint
`lem:tildew-product-form`, from
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1415-1456`.
The swap identities formalize blueprint `lem:v-swap-conjugation`, from paper
lines 1687-1713.
-/

open scoped BigOperators Matrix

namespace MIPStarRE.QPBT

open MIPStarRE.LDT hiding Measurement
open MIPStarRE.LDT.Preliminaries MIPStarRE.Quantum

noncomputable section

/-! ## Pulled-apart measurements and observables -/

namespace PauliKind

/-- Select the polynomial belonging to a Pauli basis from a joint polynomial
outcome. This is the marginalization used at paper
`14_analysis_of_the_pauli_basis_test.tex:1421-1423` and blueprint
`def:s-w-marginals`. -/
def selectPoly {P : AdmissibleParams} (W : PauliKind) : PolyPair P -> Poly P
  | pair => match W with
    | .X => pair.1
    | .Z => pair.2

end PauliKind

namespace GlobalPairWitness

/-- The single-basis marginal of the global polynomial-pair measurement.
This is blueprint
`def:s-w-marginals`, paper
`14_analysis_of_the_pauli_basis_test.tex:1421-1423`. -/
noncomputable def marginalPoly {P : AdmissibleParams} {epsilon delta : ℝ}
    {S : ProjectiveSetting P epsilon} (w : GlobalPairWitness S delta)
    (side : PlayerSide) (W : PauliKind) :
    Measurement (Poly P) (S.ExpandedLocalSpace side) :=
  (w.Smeas side).postprocess W.selectPoly

/-- The single-basis marginal remains a projective measurement. This is the
projectivity assertion implicit in blueprint
`def:s-w-marginals`, paper
`14_analysis_of_the_pauli_basis_test.tex:1421-1423`. Finite postprocessing
preserves projectivity, independently of the construction of the joint
measurement. -/
theorem marginalPoly_isProjective {P : AdmissibleParams} {epsilon delta : ℝ}
    {S : ProjectiveSetting P epsilon} (w : GlobalPairWitness S delta)
    (side : PlayerSide) (W : PauliKind) :
    Measurement.IsProjective (w.marginalPoly side W) := by
  exact SandwichProduct.postprocess_isProjective
    (w.Smeas side) (w.projective side) W.selectPoly

end GlobalPairWitness

/-- The pulled-apart projective-measurement effect from Equation `eq:tilde_M`.
The polynomial marginal acts on the player's expanded local space and the
dot-product projector acts on the newly adjoined register. Blueprint
`eq:tilde_M`; paper
`14_analysis_of_the_pauli_basis_test.tex:1425-1435`. -/
noncomputable def tildeM {P : AdmissibleParams} {epsilon delta : ℝ}
    {S : ProjectiveSetting P epsilon} (w : GlobalPairWitness S delta)
    (side : PlayerSide) (W : PauliKind) (u : PauliRegister P)
    (a : PauliScalar P) : Op (ExtractionBlock P (S.LocalSpace side)) :=
  ∑ g : Poly P,
    heteroKron ((w.marginalPoly side W).effect g)
      (tauDotProj W u (dotProduct (decodeFq g) u - a))

/-- Each pulled-apart effect is a projector, as asserted in
blueprint `def:tilde-m-measurement`, paper
`14_analysis_of_the_pauli_basis_test.tex:1425-1435`.

**Proof obligation:** issue #47 tracks the orthogonal-sum calculation using
`marginalPoly_isProjective` and `tauDotProj_isProj`. -/
theorem tildeM_isProj {P : AdmissibleParams} {epsilon delta : ℝ}
    {S : ProjectiveSetting P epsilon} (w : GlobalPairWitness S delta)
    (side : PlayerSide) (W : PauliKind) (u : PauliRegister P)
    (a : PauliScalar P) :
    IsProj (tildeM w side W u a) := by
  sorry

/-- The pulled-apart effects are complete for each fixed basis and Pauli
register vector. This is the completeness assertion in
blueprint `def:tilde-m-measurement`, paper
`14_analysis_of_the_pauli_basis_test.tex:1425-1435`.

**Proof obligation:** issue #47 tracks summing the orthogonal dot-product
projectors and the polynomial marginal effects. -/
theorem sum_tildeM_eq_one {P : AdmissibleParams} {epsilon delta : ℝ}
    {S : ProjectiveSetting P epsilon} (w : GlobalPairWitness S delta)
    (side : PlayerSide) (W : PauliKind) (u : PauliRegister P) :
    ∑ a : PauliScalar P, tildeM w side W u a = 1 := by
  sorry

/-- The binary observable obtained from the trace coarse-graining of `tildeM`.
This is Equation `eq:def-tildewj` in blueprint
`def:tilde-w-observables`, paper
`14_analysis_of_the_pauli_basis_test.tex:1437-1442`. -/
noncomputable def tildeObs {P : AdmissibleParams} {epsilon delta : ℝ}
    {S : ProjectiveSetting P epsilon} (w : GlobalPairWitness S delta)
    (side : PlayerSide) (W : PauliKind) (u : PauliRegister P)
    (j : Fin P.model.basisDim) : Op (ExtractionBlock P (S.LocalSpace side)) :=
  ∑ a : PauliScalar P,
    phaseSign (fixedBinTrace P.model (P.model.basis j * a)) •
      tildeM w side W u a

/-- Fourier regrouping of the dot-product effects after translating their
outcomes. This is the change of variables in the product calculation at paper
`14_analysis_of_the_pauli_basis_test.tex:1442-1450`, supporting blueprint
`lem:tildew-product-form`. It uses only the definition of the coarse-graining,
not its projectivity. -/
private theorem sum_phaseSign_tauDotProj_sub {params : AdmissibleParams}
    (kind : PauliKind) (vector : PauliRegister params)
    (coefficient offset : PauliScalar params) :
    (∑ value : PauliScalar params,
      phaseSign (fixedBinTrace params.model (coefficient * value)) •
        tauDotProj kind vector (offset - value)) =
      phaseSign (fixedBinTrace params.model (coefficient * offset)) •
        tauObservable kind (coefficient • vector) := by
  classical
  calc
    _ = ∑ value : PauliScalar params,
        phaseSign (fixedBinTrace params.model (coefficient * (offset - value))) •
          tauDotProj kind vector value := by
      symm
      simpa using (Equiv.subLeft offset).sum_comp
        (fun value => phaseSign (fixedBinTrace params.model (coefficient * value)) •
          tauDotProj kind vector (offset - value))
    _ = ∑ label : PauliRegister params,
        phaseSign (fixedBinTrace params.model
          (coefficient * (offset - dotProduct label vector))) • pauliProj kind label := by
      simp only [tauDotProj, bracketOp, Finset.smul_sum]
      rw [← Finset.sum_fiberwise Finset.univ (fun label => dotProduct label vector)
        (fun label => phaseSign (fixedBinTrace params.model
          (coefficient * (offset - dotProduct label vector))) • pauliProj kind label)]
      apply Finset.sum_congr rfl
      intro value _
      apply Finset.sum_congr rfl
      intro label hlabel
      rw [(Finset.mem_filter.mp hlabel).2]
    _ = _ := by
      rw [tauObservable_eq_sum_pauliProj, Finset.smul_sum]
      apply Finset.sum_congr rfl
      intro label _
      rw [smul_smul, smul_dotProduct, smul_eq_mul, dotProduct_comm vector label]
      congr 1
      rw [mul_sub, fixedBinTrace, map_sub, sub_eq_add_neg,
        ZMod.neg_eq_self_mod_two, phaseSign_add]

/-- Product form of the pulled-apart observable, Equation
`eq:tildewj-product-form` of `lem:tildew-product-form`. Blueprint
`lem:tildew-product-form`; paper
`14_analysis_of_the_pauli_basis_test.tex:1442-1450`. The finite Fourier
regrouping uses `tauObservable_eq_sum_pauliProj` and the definitions of both
marginalizations, independently of dot-product projectivity or consistency
estimates. -/
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
  classical
  simp only [tildeObs, tildeM, Finset.smul_sum]
  rw [Finset.sum_comm]
  calc
    _ = ∑ polynomial : Poly P,
        heteroKron ((w.marginalPoly side W).effect polynomial)
          (∑ value : PauliScalar P,
            phaseSign (fixedBinTrace P.model (P.model.basis j * value)) •
              tauDotProj W u (dotProduct (decodeFq polynomial) u - value)) := by
      apply Finset.sum_congr rfl
      intro polynomial _
      rw [DistanceCalculus.heteroKron_finset_sum_right]
      apply Finset.sum_congr rfl
      intro value _
      exact (Matrix.kronecker_smul _ _ _).symm
    _ = heteroKron
        (∑ polynomial : Poly P,
          phaseSign (fixedBinTrace P.model
            (P.model.basis j * dotProduct (decodeFq polynomial) u)) •
              (w.marginalPoly side W).effect polynomial)
        (tauObservable W (P.model.basis j • u)) := by
      simp_rw [sum_phaseSign_tauDotProj_sub]
      rw [DistanceCalculus.heteroKron_finset_sum_left]
      apply Finset.sum_congr rfl
      intro polynomial _
      simp only [heteroKron, Matrix.kronecker, Matrix.kronecker_smul,
        Matrix.smul_kronecker]
    _ = _ := by
      congr 1
      simp only [GlobalPairWitness.marginalPoly, Measurement.postprocess_effect,
        Finset.smul_sum]
      rw [← Finset.sum_fiberwise Finset.univ W.selectPoly
        (fun pair => phaseSign (fixedBinTrace P.model
          (P.model.basis j * dotProduct (decodeFq (W.selectPoly pair)) u)) •
            (w.Smeas side).effect pair)]
      apply Finset.sum_congr rfl
      intro polynomial _
      apply Finset.sum_congr rfl
      intro pair hpair
      rw [(Finset.mem_filter.mp hpair).2]

/-- The complex binary character agrees with the real sign used in spectral sums.
This formalization-only identity permits its use
in the involution and commutation assertions of `lem:tildew-product-form`. -/
private theorem phaseSign_eq_complex_bitSign (value : ZMod 2) :
    phaseSign value = (MagicSquareRigidity.bitSign value : ℂ) := by
  rcases zmod_two_eq_zero_or_one value with hvalue | hvalue <;>
    subst value <;> norm_num [phaseSign, MagicSquareRigidity.bitSign, ZMod.val_one]

/-- Every pulled-apart observable is Hermitian, as asserted in
blueprint `lem:tildew-product-form`, paper
`14_analysis_of_the_pauli_basis_test.tex:1450`. Both factors in the product
form are real linear combinations of Hermitian measurement effects. -/
theorem tildeObs_isHermitian {P : AdmissibleParams} {epsilon delta : ℝ}
    {S : ProjectiveSetting P epsilon} (w : GlobalPairWitness S delta)
    (side : PlayerSide) (W : PauliKind) (u : PauliRegister P)
    (j : Fin P.model.basisDim) :
    (tildeObs w side W u j).IsHermitian := by
  classical
  rw [tildeObs_eq_heteroKron]
  change (heteroKron _ _)ᴴ = _
  rw [MagicSquareRigidity.heteroKron_conjTranspose]
  congr 1
  · rw [Matrix.conjTranspose_sum]
    apply Finset.sum_congr rfl
    intro pair _
    rw [Matrix.conjTranspose_smul, star_phaseSign]
    congr 1
    exact (w.projective side pair).isSelfAdjoint
  · rw [tauObservable_eq_sum_pauliProj, Matrix.conjTranspose_sum]
    apply Finset.sum_congr rfl
    intro label _
    rw [Matrix.conjTranspose_smul, star_phaseSign]
    congr 1
    simp [pauliProj, Pi.star_def]

/-- Every pulled-apart observable squares to the identity, as asserted in
blueprint `lem:tildew-product-form`, paper
`14_analysis_of_the_pauli_basis_test.tex:1450`. Orthogonality and completeness
of the joint measurement make its sign-weighted sum an involution, as is the
generalized Pauli factor. -/
theorem tildeObs_mul_self {P : AdmissibleParams} {epsilon delta : ℝ}
    {S : ProjectiveSetting P epsilon} (w : GlobalPairWitness S delta)
    (side : PlayerSide) (W : PauliKind) (u : PauliRegister P)
    (j : Fin P.model.basisDim) :
    tildeObs w side W u j * tildeObs w side W u j = 1 := by
  classical
  have hsquare := MagicSquareRigidity.signObs_mul_self
    (w.Smeas side) (w.projective side)
    (fun pair => fixedBinTrace P.model
      (P.model.basis j * dotProduct (decodeFq (W.selectPoly pair)) u))
  simp only [MagicSquareRigidity.signObs, ← phaseSign_eq_complex_bitSign] at hsquare
  rw [tildeObs_eq_heteroKron, heteroKron_mul, hsquare, tauObservable_sq,
    heteroKron_one_one]

/-- The corrected twisted commutation relation for pulled-apart observables.
This is Equation `eq:tildew-twisted-commutation` in blueprint
`eq:tildew-twisted-commutation`, correcting paper
`14_analysis_of_the_pauli_basis_test.tex:1451-1456`.

**Local fix:** the paper drops this phase when `j != j'`, which is false for
general register vectors; see `docs/paper-gaps/qpbt_cross-basis-phase.tex`.
The sign-weighted sums of the joint projectors commute, leaving exactly the
phase of `tauObservable_X_mul_Z`. -/
theorem tildeObs_twisted_commutation {P : AdmissibleParams}
    {epsilon delta : ℝ} {S : ProjectiveSetting P epsilon}
    (w : GlobalPairWitness S delta) (side : PlayerSide)
    (u v : PauliRegister P) (j j' : Fin P.model.basisDim) :
    tildeObs w side .X u j * tildeObs w side .Z v j' =
      phaseSign (fixedBinTrace P.model
        (P.model.basis j * P.model.basis j' * dotProduct u v)) •
        (tildeObs w side .Z v j' * tildeObs w side .X u j) := by
  classical
  have hcomm := MagicSquareRigidity.signObs_comm
    (w.Smeas side) (w.projective side)
    (fun pair => fixedBinTrace P.model
      (P.model.basis j * dotProduct (decodeFq (PauliKind.X.selectPoly pair)) u))
    (fun pair => fixedBinTrace P.model
      (P.model.basis j' * dotProduct (decodeFq (PauliKind.Z.selectPoly pair)) v))
  simp only [MagicSquareRigidity.signObs, ← phaseSign_eq_complex_bitSign] at hcomm
  rw [tildeObs_eq_heteroKron, tildeObs_eq_heteroKron,
    heteroKron_mul, heteroKron_mul, tauObservable_X_mul_Z,
    MagicSquareRigidity.heteroKron_smul_right, hcomm]
  congr 2
  simp only [fixedBinTrace, smul_dotProduct, dotProduct_smul, smul_eq_mul,
    mul_assoc, mul_left_comm]

/-! ## Swap conjugation -/

/-- The swap map built from the global polynomial-pair measurement, with the
crossed decoded arguments required by `def:v-swap-unitary`. Blueprint
`def:v-swap-unitary`; paper
`14_analysis_of_the_pauli_basis_test.tex:1687-1700`. -/
noncomputable def swapUnitary {P : AdmissibleParams} {epsilon delta : ℝ}
    {S : ProjectiveSetting P epsilon} (w : GlobalPairWitness S delta)
    (side : PlayerSide) : Op (ExtractionBlock P (S.LocalSpace side)) :=
  ∑ pair : PolyPair P,
    heteroKron ((w.Smeas side).effect pair)
      (tauObservable .X (decodeFq pair.2) *
        tauObservable .Z (decodeFq pair.1))

/-- The swap map is a right unitary. This is the first exact unitarity
calculation of blueprint
`lem:v-swap-conjugation`, paper
`14_analysis_of_the_pauli_basis_test.tex:1687-1699`.

**Proof obligation:** issue #47 tracks the finite projector calculation.
Discharge: use projectivity and completeness of `w.Smeas side` together with
self-inverseness of both generalized Pauli observables. -/
theorem swapUnitary_mul_conjTranspose {P : AdmissibleParams}
    {epsilon delta : ℝ} {S : ProjectiveSetting P epsilon}
    (w : GlobalPairWitness S delta) (side : PlayerSide) :
    swapUnitary w side * (swapUnitary w side)ᴴ = 1 := by
  sorry

/-- The swap map is a left unitary. This is the reverse exact unitarity
calculation implicit in blueprint
`lem:v-swap-conjugation`, paper
`14_analysis_of_the_pauli_basis_test.tex:1687-1699`.

**Proof obligation:** issue #47 tracks the reverse projector calculation.
Discharge: use the same orthogonality and Pauli involution identities as in
`swapUnitary_mul_conjTranspose`. -/
theorem conjTranspose_mul_swapUnitary {P : AdmissibleParams}
    {epsilon delta : ℝ} {S : ProjectiveSetting P epsilon}
    (w : GlobalPairWitness S delta) (side : PlayerSide) :
    (swapUnitary w side)ᴴ * swapUnitary w side = 1 := by
  sorry

/-- Exact conjugation of a pulled-apart observable by the swap map. This is
Equation `eq:v-swap-obs-conjugation` in `lem:v-swap-conjugation`, blueprint
`eq:v-swap-obs-conjugation`, paper
`14_analysis_of_the_pauli_basis_test.tex:1701-1713`.

**Proof obligation:** issue #47 tracks the diagonal projector reduction.
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
`eq:qld-unitary-6`; its calculation occurs at paper
`14_analysis_of_the_pauli_basis_test.tex:1805-1822`.

**Proof obligation:** issue #47 tracks the exact relabeling calculation.
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
