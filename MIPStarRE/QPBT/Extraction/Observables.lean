import MIPStarRE.QPBT.Algebra.Decoding
import MIPStarRE.QPBT.Combining.Witnesses
import MIPStarRE.QPBT.Extraction.Defs
import MIPStarRE.QPBT.Test.MagicSquareTheorems.Rigidity.Reflections
import MIPStarRE.Quantum.ControlledUnitary

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
blueprint `lem:tilde-m-projective`, paper
`14_analysis_of_the_pauli_basis_test.tex:1425-1435`.

Each tensor summand is projective. Distinct polynomial marginals are
orthogonal, so their tensor summands are orthogonal as well. -/
theorem tildeM_isProj {P : AdmissibleParams} {epsilon delta : ℝ}
    {S : ProjectiveSetting P epsilon} (w : GlobalPairWitness S delta)
    (side : PlayerSide) (W : PauliKind) (u : PauliRegister P)
    (a : PauliScalar P) :
    IsProj (tildeM w side W u a) := by
  classical
  have hproj (g : Poly P) : IsProj
      (heteroKron ((w.marginalPoly side W).effect g)
        (tauDotProj W u (dotProduct (decodeFq g) u - a))) :=
    MakingMeasurementsProjective.isProj_kronecker
      (w.marginalPoly_isProjective side W g) (tauDotProj_isProj W u _)
  unfold tildeM
  constructor
  · change (∑ g : Poly P, _) * (∑ g : Poly P, _) = _
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun g _ => ?_
    rw [Matrix.mul_sum, Finset.sum_eq_single g]
    · exact (hproj g).isIdempotentElem
    · intro g' _ hg'
      rw [heteroKron_mul, MagicSquareRigidity.mul_eq_zero_of_isProj_family
        (w.marginalPoly_isProjective side W) (w.marginalPoly side W).sum_le_one
        hg'.symm]
      simp [heteroKron]
    · intro hg
      exact (hg (Finset.mem_univ g)).elim
  · change (∑ g : Poly P, _)ᴴ = _
    rw [Matrix.conjTranspose_sum]
    exact Finset.sum_congr rfl fun g _ => (hproj g).isSelfAdjoint

/-- The pulled-apart effects are complete for each fixed basis and Pauli
register vector. This is the completeness assertion in
blueprint `lem:tilde-m-projective`, paper
`14_analysis_of_the_pauli_basis_test.tex:1425-1435`.

For each polynomial, subtracting the scalar outcome from its decoded dot
product permutes the field. Completeness then follows by summing the
dot-product projectors and the polynomial marginal effects. -/
theorem sum_tildeM_eq_one {P : AdmissibleParams} {epsilon delta : ℝ}
    {S : ProjectiveSetting P epsilon} (w : GlobalPairWitness S delta)
    (side : PlayerSide) (W : PauliKind) (u : PauliRegister P) :
    ∑ a : PauliScalar P, tildeM w side W u a = 1 := by
  classical
  simp only [tildeM]
  rw [Finset.sum_comm]
  calc
    _ = ∑ g : Poly P, heteroKron ((w.marginalPoly side W).effect g)
        (∑ a : PauliScalar P, tauDotProj W u (dotProduct (decodeFq g) u - a)) := by
      exact Finset.sum_congr rfl fun g _ =>
        (DistanceCalculus.heteroKron_finset_sum_right _ _ _).symm
    _ = ∑ g : Poly P, heteroKron ((w.marginalPoly side W).effect g) 1 := by
      refine Finset.sum_congr rfl fun g _ => ?_
      congr 1
      calc
        _ = ∑ a : PauliScalar P, tauDotProj W u a :=
          (Equiv.subLeft (dotProduct (decodeFq g) u)).sum_comp (tauDotProj W u)
        _ = 1 := sum_tauDotProj_eq_one W u
    _ = heteroKron (∑ g : Poly P, (w.marginalPoly side W).effect g) 1 :=
      (DistanceCalculus.heteroKron_finset_sum_left _ _ _).symm
    _ = 1 := by rw [(w.marginalPoly side W).sum_eq_one, heteroKron_one_one]

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

/-- The characteristic-two Pauli observable is Hermitian. This finite spectral
calculation supplies the adjoints used in the swap identity at paper
`14_analysis_of_the_pauli_basis_test.tex:1687-1699`. -/
private theorem tauObservable_conjTranspose {P : AdmissibleParams}
    (W : PauliKind) (u : PauliRegister P) :
    (tauObservable W u)ᴴ = tauObservable W u := by
  rw [tauObservable_eq_sum_pauliProj, Matrix.conjTranspose_sum]
  apply Finset.sum_congr rfl
  intro label _
  rw [Matrix.conjTranspose_smul, star_phaseSign]
  congr 1
  simp [pauliProj, Pi.star_def]

/-- Each crossed Pauli product is unitary, by the two involution identities
used at paper `14_analysis_of_the_pauli_basis_test.tex:1687-1699`. -/
private theorem swapPauli_mul_conjTranspose {P : AdmissibleParams}
    (pair : PolyPair P) :
    (tauObservable .X (decodeFq pair.2) * tauObservable .Z (decodeFq pair.1)) *
        (tauObservable .X (decodeFq pair.2) * tauObservable .Z (decodeFq pair.1))ᴴ = 1 := by
  rw [Matrix.conjTranspose_mul, tauObservable_conjTranspose,
    tauObservable_conjTranspose, ← Matrix.mul_assoc,
    Matrix.mul_assoc (tauObservable .X (decodeFq pair.2)), tauObservable_sq,
    Matrix.mul_one, tauObservable_sq]

/-- The crossed Pauli factors acquire the phase determined by the selected
polynomial. This is the commutation identity used at paper
`14_analysis_of_the_pauli_basis_test.tex:1701-1713`. -/
private theorem swapPauli_mul_tauObservable {P : AdmissibleParams}
    (pair : PolyPair P) (W : PauliKind) (u : PauliRegister P) :
    (tauObservable .X (decodeFq pair.2) * tauObservable .Z (decodeFq pair.1)) *
        tauObservable W u =
      phaseSign (fixedBinTrace P.model
        (dotProduct (decodeFq (W.selectPoly pair)) u)) •
        (tauObservable W u *
          (tauObservable .X (decodeFq pair.2) * tauObservable .Z (decodeFq pair.1))) := by
  cases W with
  | X =>
      have hcomm : tauObservable .X (decodeFq pair.2) * tauObservable .X u =
          tauObservable .X u * tauObservable .X (decodeFq pair.2) := by
        rw [tauObservable_mul, tauObservable_mul, add_comm]
      have hcross := congrArg
        (fun A : Op (PauliRegister P) =>
          phaseSign (binTrace (PauliScalar P) (dotProduct u (decodeFq pair.1))) • A)
        (tauObservable_X_mul_Z u (decodeFq pair.1))
      simp only [smul_smul, phaseSign_mul_self, one_smul] at hcross
      simp only [PauliKind.selectPoly, fixedBinTrace]
      rw [dotProduct_comm (decodeFq pair.1) u]
      calc
        _ = tauObservable .X (decodeFq pair.2) *
            (tauObservable .Z (decodeFq pair.1) * tauObservable .X u) :=
          Matrix.mul_assoc _ _ _
        _ = _ := by
          rw [← hcross, Matrix.mul_smul, ← Matrix.mul_assoc, hcomm, Matrix.mul_assoc]
  | Z =>
      have hcomm : tauObservable .Z (decodeFq pair.1) * tauObservable .Z u =
          tauObservable .Z u * tauObservable .Z (decodeFq pair.1) := by
        rw [tauObservable_mul, tauObservable_mul, add_comm]
      simp only [PauliKind.selectPoly, fixedBinTrace]
      calc
        _ = tauObservable .X (decodeFq pair.2) *
            (tauObservable .Z (decodeFq pair.1) * tauObservable .Z u) :=
          Matrix.mul_assoc _ _ _
        _ = _ := by
          rw [hcomm, ← Matrix.mul_assoc, tauObservable_X_mul_Z,
            Matrix.smul_mul, Matrix.mul_assoc]

/-- Conjugating a Pauli observable by the crossed Pauli factors multiplies it
by the selected binary phase, as in paper
`14_analysis_of_the_pauli_basis_test.tex:1701-1713`. -/
private theorem swapPauli_conj_tauObservable {P : AdmissibleParams}
    (pair : PolyPair P) (W : PauliKind) (u : PauliRegister P) :
    conjBy (tauObservable .X (decodeFq pair.2) * tauObservable .Z (decodeFq pair.1))
        (tauObservable W u) =
      phaseSign (fixedBinTrace P.model
        (dotProduct (decodeFq (W.selectPoly pair)) u)) • tauObservable W u := by
  rw [conjBy, swapPauli_mul_tauObservable, Matrix.smul_mul, Matrix.mul_assoc,
    swapPauli_mul_conjTranspose, Matrix.mul_one]

/-- Fourier inversion turns the Pauli conjugation phase into a translation of
the projector label. This is the projector identity used at paper
`14_analysis_of_the_pauli_basis_test.tex:1805-1822`. -/
private theorem swapPauli_conj_pauliProj {P : AdmissibleParams}
    (pair : PolyPair P) (W : PauliKind) (h : PauliRegister P) :
    conjBy (tauObservable .X (decodeFq pair.2) * tauObservable .Z (decodeFq pair.1))
        (pauliProj W h) =
      pauliProj W (h + decodeFq (W.selectPoly pair)) := by
  classical
  rw [pauliProj_eq_avg_tauObservable, conjBy, Matrix.mul_smul, Matrix.smul_mul,
    Matrix.mul_sum, Finset.sum_mul, pauliProj_eq_avg_tauObservable]
  congr 1
  apply Finset.sum_congr rfl
  intro u _
  rw [Matrix.mul_smul, Matrix.smul_mul]
  change _ • conjBy _ _ = _
  rw [swapPauli_conj_tauObservable, smul_smul]
  congr 1
  rw [fixedBinTrace, ← phaseSign_add, ← map_add,
    dotProduct_comm (decodeFq (W.selectPoly pair)) u, dotProduct_add]

/-- Translation of the Pauli label translates its dot-product outcome. This
is the finite reindexing in paper
`14_analysis_of_the_pauli_basis_test.tex:1805-1822`; it does not require a
polynomial to be in the image of the low-degree encoding. -/
private theorem swapPauli_conj_tauDotProj {P : AdmissibleParams}
    (pair : PolyPair P) (W : PauliKind) (u : PauliRegister P) (a : PauliScalar P) :
    conjBy (tauObservable .X (decodeFq pair.2) * tauObservable .Z (decodeFq pair.1))
        (tauDotProj W u a) =
      tauDotProj W u (a + dotProduct (decodeFq (W.selectPoly pair)) u) := by
  classical
  simp only [tauDotProj, bracketOp, conjBy, Matrix.mul_sum, Finset.sum_mul]
  change (∑ h ∈ Finset.univ.filter (fun h => dotProduct h u = a),
    conjBy (tauObservable .X (decodeFq pair.2) * tauObservable .Z (decodeFq pair.1))
      (pauliProj W h)) = _
  simp_rw [swapPauli_conj_pauliProj]
  apply Finset.sum_equiv (Equiv.addRight (decodeFq (W.selectPoly pair)))
  · intro h
    simp [add_dotProduct]
  · intro h _
    rfl

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

Projectivity and completeness of `w.Smeas side` reduce the product to its
diagonal outcomes. The two Pauli involutions then cancel in reverse order. -/
theorem swapUnitary_mul_conjTranspose {P : AdmissibleParams}
    {epsilon delta : ℝ} {S : ProjectiveSetting P epsilon}
    (w : GlobalPairWitness S delta) (side : PlayerSide) :
    swapUnitary w side * (swapUnitary w side)ᴴ = 1 := by
  classical
  apply sum_heteroKron_mul_conjTranspose (w.Smeas side) (w.projective side)
  exact swapPauli_mul_conjTranspose

/-- The swap map is a left unitary. This is the reverse exact unitarity
calculation implicit in blueprint
`lem:v-swap-conjugation`, paper
`14_analysis_of_the_pauli_basis_test.tex:1687-1699`.

For finite square matrices, the right inverse identity also gives the left
inverse identity. -/
theorem conjTranspose_mul_swapUnitary {P : AdmissibleParams}
    {epsilon delta : ℝ} {S : ProjectiveSetting P epsilon}
    (w : GlobalPairWitness S delta) (side : PlayerSide) :
    (swapUnitary w side)ᴴ * swapUnitary w side = 1 := by
  exact mul_eq_one_comm.mp (swapUnitary_mul_conjTranspose w side)

/-- Conjugation by the swap map acts separately on each joint outcome. This
is the diagonal-projector reduction at paper
`14_analysis_of_the_pauli_basis_test.tex:1701-1713,1805-1822`. -/
private theorem swapUnitary_conj_controlled {P : AdmissibleParams}
    {epsilon delta : ℝ} {S : ProjectiveSetting P epsilon}
    (w : GlobalPairWitness S delta) (side : PlayerSide)
    (R : PolyPair P → Op (PauliRegister P)) :
    conjBy (swapUnitary w side)
        (∑ pair, heteroKron ((w.Smeas side).effect pair) (R pair)) =
      ∑ pair, heteroKron ((w.Smeas side).effect pair)
        (conjBy (tauObservable .X (decodeFq pair.2) *
          tauObservable .Z (decodeFq pair.1)) (R pair)) := by
  have hself (pair : PolyPair P) :
      ((w.Smeas side).effect pair)ᴴ = (w.Smeas side).effect pair :=
    (w.projective side pair).isSelfAdjoint
  simp only [conjBy, swapUnitary, Matrix.conjTranspose_sum,
    MagicSquareRigidity.heteroKron_conjTranspose, hself]
  rw [sum_heteroKron_mul_sum_heteroKron (w.Smeas side) (w.projective side),
    sum_heteroKron_mul_sum_heteroKron (w.Smeas side) (w.projective side)]

/-- Exact conjugation of a pulled-apart observable by the swap map. This is
Equation `eq:v-swap-obs-conjugation` in `lem:v-swap-conjugation`, blueprint
`eq:v-swap-obs-conjugation`, paper
`14_analysis_of_the_pauli_basis_test.tex:1701-1713`.

The product form and diagonal projector reduction leave two copies of the
same binary phase, whose product is one. -/
theorem swapUnitary_conj_tildeObs {P : AdmissibleParams}
    {epsilon delta : ℝ} {S : ProjectiveSetting P epsilon}
    (w : GlobalPairWitness S delta) (side : PlayerSide) (W : PauliKind)
    (u : PauliRegister P) (j : Fin P.model.basisDim) :
    conjBy (swapUnitary w side) (tildeObs w side W u j) =
      heteroKron (1 : Op (S.ExpandedLocalSpace side))
        (tauObservable W (P.model.basis j • u)) := by
  classical
  rw [tildeObs_eq_heteroKron, DistanceCalculus.heteroKron_finset_sum_left]
  simp_rw [MagicSquareRigidity.heteroKron_smul_left,
    ← MagicSquareRigidity.heteroKron_smul_right]
  rw [swapUnitary_conj_controlled]
  have hcancel (pair : PolyPair P) :
      conjBy (tauObservable .X (decodeFq pair.2) * tauObservable .Z (decodeFq pair.1))
        (phaseSign (fixedBinTrace P.model
          (P.model.basis j * dotProduct (decodeFq (W.selectPoly pair)) u)) •
            tauObservable W (P.model.basis j • u)) =
        tauObservable W (P.model.basis j • u) := by
    rw [conjBy, Matrix.mul_smul, Matrix.smul_mul]
    change _ • conjBy _ _ = _
    rw [swapPauli_conj_tauObservable, smul_smul]
    have hdot : dotProduct (decodeFq (W.selectPoly pair)) (P.model.basis j • u) =
        P.model.basis j * dotProduct (decodeFq (W.selectPoly pair)) u := by
      rw [dotProduct_smul, smul_eq_mul]
    rw [hdot, phaseSign_mul_self, one_smul]
  simp_rw [hcancel]
  rw [← DistanceCalculus.heteroKron_finset_sum_left, (w.Smeas side).sum_eq_one]

/-- Exact conjugation of a pulled-apart point effect by the swap map. This is
Equation `eq:qld-unitary-6` in `lem:v-swap-conjugation`, blueprint
`eq:qld-unitary-6`; its calculation occurs at paper
`14_analysis_of_the_pauli_basis_test.tex:1805-1822`.

Conjugation translates each Pauli projector and its dot-product constraint.
The two copies of the decoded label cancel in characteristic two. The final
identification uses `lowDegreeEnc_eq_dotProduct`, not an unrestricted decoder
interpolation identity. -/
theorem swapUnitary_conj_tildeM {P : AdmissibleParams}
    {epsilon delta : ℝ} {S : ProjectiveSetting P epsilon}
    (w : GlobalPairWitness S delta) (side : PlayerSide) (W : PauliKind)
    (u : Fin P.m -> PauliScalar P) (a : PauliScalar P) :
    conjBy (swapUnitary w side) (tildeM w side W (indicatorVec u) a) =
      heteroKron (1 : Op (S.ExpandedLocalSpace side))
        (bracketOp (pauliProj W) (fun h => lowDegreeEnc h u) a) := by
  classical
  have hM : tildeM w side W (indicatorVec u) a =
      ∑ pair : PolyPair P, heteroKron ((w.Smeas side).effect pair)
        (tauDotProj W (indicatorVec u)
          (dotProduct (decodeFq (W.selectPoly pair)) (indicatorVec u) - a)) := by
    simp only [tildeM, GlobalPairWitness.marginalPoly, Measurement.postprocess_effect]
    simp_rw [DistanceCalculus.heteroKron_finset_sum_left]
    rw [← Finset.sum_fiberwise Finset.univ W.selectPoly
      (fun pair => heteroKron ((w.Smeas side).effect pair)
        (tauDotProj W (indicatorVec u)
          (dotProduct (decodeFq (W.selectPoly pair)) (indicatorVec u) - a)))]
    apply Finset.sum_congr rfl
    intro g _
    apply Finset.sum_congr rfl
    intro pair hpair
    rw [(Finset.mem_filter.mp hpair).2]
  rw [hM, swapUnitary_conj_controlled]
  simp_rw [swapPauli_conj_tauDotProj]
  have hcancel (b : PauliScalar P) : b - a + b = a := by
    letI : CharP (PauliScalar P) 2 :=
      (Algebra.charP_iff (ZMod 2) (PauliScalar P) 2).mp (ZMod.charP 2)
    rw [sub_eq_add_neg, CharTwo.neg_eq, add_right_comm, CharTwo.add_self_eq_zero, zero_add]
  simp_rw [hcancel]
  rw [← DistanceCalculus.heteroKron_finset_sum_left, (w.Smeas side).sum_eq_one]
  congr 1
  simp only [tauDotProj, bracketOp, lowDegreeEnc_eq_dotProduct]

end

end MIPStarRE.QPBT
