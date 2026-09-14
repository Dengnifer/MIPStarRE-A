import MIPStarRE.QPBT.Extraction.PointConsistencyPrime
import MIPStarRE.QPBT.Extraction.PullingMeasurement

/-!
# Point overlaps for the difference-polynomial measurement

Evaluation of the difference polynomial gives `g(u) - g_h(u)`. Unlike
evaluation after decoding, this formula holds for every polynomial outcome.
The resulting point overlaps are the ones supplied by the global witness.

## References

- Blueprint `lem:qld-construct-the-paulis`, Item 2.
- `references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1495-1545`,
  especially `eq:qld-pulling-2b` and `eq:qld-pulling-12`.
- The placement and convolution lemmas in the imported `PointConsistency`
  modules are preserved from PR #539, head
  `ca866da402947c9ee7e1dd5e935a2782fe0d1602`.
- Issue #520. These identities do not construct the global witness.
-/

open scoped BigOperators Matrix MatrixOrder ComplexOrder Classical

namespace MIPStarRE.QPBT

open MIPStarRE.LDT hiding Measurement
open MIPStarRE.Quantum DistanceCalculus

noncomputable section

/-- Evaluation of the difference measurement is a convolution with the ideal
Pauli point projectors. No encoding hypothesis on `g` is needed. -/
theorem pullingMeas_eval_effect {P : AdmissibleParams} {epsilon deltaG : ℝ}
    {S : ProjectiveSetting P epsilon} (w : GlobalPairWitness S deltaG)
    (side : PlayerSide) (W : PauliKind) (u : Fin P.m → PauliScalar P)
    (a : PauliScalar P) :
    ((pullingMeas w side W).postprocess (fun g => evalPoly g u)).effect a =
      ∑ g : Poly P, heteroKron ((w.marginalPoly side W).effect g)
        (tauDotProj W (indicatorVec u) (evalPoly g u - a)) := by
  rw [pullingMeas, Measurement.postprocess_comp]
  have heval (outcome : Poly P × PauliRegister P) :
      evalPoly (pullingPoly outcome) u =
        evalPoly outcome.1 u - dotProduct outcome.2 (indicatorVec u) := by
    change MvPolynomial.eval u (outcome.1.1 - lowDegreeEncoding outcome.2) = _
    rw [MvPolynomial.eval_sub]
    exact congrArg (evalPoly outcome.1 u - ·) (lowDegreeEnc_eq_dotProduct outcome.2 u)
  simp only [Measurement.postprocess_effect, Finset.sum_filter, heval,
    tensorMeasurement, Measurement.ofSumEqOne, pauliRegisterMeas]
  rw [Fintype.sum_prod_type]
  unfold tauDotProj bracketOp
  simp_rw [heteroKron_finset_sum_right, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro g _
  apply Finset.sum_congr rfl
  intro h _
  have hlabel : evalPoly g u - dotProduct h (indicatorVec u) = a ↔
      dotProduct h (indicatorVec u) = evalPoly g u - a := by
    constructor <;> intro heq <;> linear_combination -heq
  simp only [hlabel]

/-- Alice's evaluated difference measurement has precisely the overlap with
Bob's point measurement that appears in the witness's Alice consistency field. -/
theorem sum_pullingMeas_eval_mul_pointMeas {P : AdmissibleParams} {epsilon deltaG : ℝ}
    {S : ProjectiveSetting P epsilon} (w : GlobalPairWitness S deltaG)
    (W : PauliKind) (u : Fin P.m → PauliScalar P) :
    (∑ a : PauliScalar P, S.placeSide .alice
      (((pullingMeas w .alice W).postprocess (fun g => evalPoly g u)).effect a) *
        S.placePlayer .bob ((S.pointMeas .bob W u).effect a)) =
      ∑ g : Poly P, S.place .AA' ((w.marginalPoly .alice W).effect g) *
        S.place .BA'' ((S.pointMeasExp .bob W u).effect (evalPoly g u)) := by
  simp only [pullingMeas_eval_effect, S.placeSide_alice_finset_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro g _
  simp only [S.placeSide_alice_tensor_mul_placePlayer_bob]
  rw [← Finset.mul_sum, ← S.place_finset_sum, S.pointMeasExp_effect_eq_sum_sub .bob W u]
  rfl

/-- The reverse-player overlap uses the witness's Bob consistency field, with
the original `BB'` and `AB''` placements retained. -/
theorem sum_pointMeas_mul_pullingMeas_eval {P : AdmissibleParams} {epsilon deltaG : ℝ}
    {S : ProjectiveSetting P epsilon} (w : GlobalPairWitness S deltaG)
    (W : PauliKind) (u : Fin P.m → PauliScalar P) :
    (∑ a : PauliScalar P, S.placePlayer .alice ((S.pointMeas .alice W u).effect a) *
      S.placeSide .bob
        (((pullingMeas w .bob W).postprocess (fun g => evalPoly g u)).effect a)) =
      ∑ g : Poly P, S.place .BB' ((w.marginalPoly .bob W).effect g) *
        S.place .AB'' ((S.pointMeasExp .alice W u).effect (evalPoly g u)) := by
  simp only [pullingMeas_eval_effect, S.placeSide_bob_finset_sum, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro g _
  simp only [S.placePlayer_alice_mul_placeSide_bob_tensor]
  rw [← Finset.mul_sum, ← S.place_finset_sum, S.pointMeasExp_effect_eq_sum_sub .alice W u]
  rfl

end

end MIPStarRE.QPBT
