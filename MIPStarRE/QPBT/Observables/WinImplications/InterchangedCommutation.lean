import MIPStarRE.QPBT.Observables.WinImplications.FactorTransport
import MIPStarRE.QPBT.Observables.WinImplications.TwistedCommutation

/-!
# The factor-interchanged phase-signed commutation relation

This module runs the second pass of `lem:qld-win-implications-obs`.  The first
pass places Alice's point observables on the left tensor factor of
`S.toStrategy.psi`; here the same generic machinery is instantiated with Bob's
point observables on the left factor of the interchanged state
`ProjectiveSetting.swappedState`, fed by the factor-interchanged consistency
implications of `lem:qld-win-implications` and by Alice's Magic Square
anticommutation, and the conclusion is transported back to
`S.toStrategy.psi`.  No symmetry principle between the two players is used.

## References

The declarations formalize the trailing clause of
`lem:qld-win-implications-obs` in
`blueprint/src/chapter/ch14_qpbt_observables.tex:683-733`, whose paper source
is `references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:309-362`.
-/

open scoped BigOperators Matrix ComplexOrder

namespace MIPStarRE.QPBT

open MIPStarRE.LDT hiding Measurement
open MIPStarRE.Quantum

noncomputable section

namespace WinImplications

local instance pauliEdgeNonemptyInterchanged : Nonempty PauliEdge :=
  pauliEdge_nonempty

/-! ## The interchanged consistency inputs on the interchanged state -/

/-- Commuting point/Pair-W consistency with Bob on the left factor. This is the
factor-interchanged form of item 5 of `lem:qld-win-implications`, transported
to the interchanged state; paper
`14_analysis_of_the_pauli_basis_test.tex:227,232-239`, blueprint
`ch14_qpbt_observables.tex:699-701`. -/
theorem win_comm_cons_swapped_proof :
    ∃ C : ℝ, 1 ≤ C ∧
      ∀ (P : AdmissibleParams) (ε : ℝ) (S : ProjectiveSetting P ε),
      0 ≤ ε → ∀ W : PauliKind,
      consistencyDefect (commTupleDist P)
        (fun ω a => heteroKron
          ((S.pointTraceMeas .bob W (selectedTuplePoint W ω)
            (selectedTupleScalar W ω)).effect a) 1)
        (fun ω a => heteroKron 1
          ((S.pairWMeas .alice W ω.1 ω.2.1 ω.2.2.1 ω.2.2.2).effect a))
        S.swappedState ≤ C * ε := by
  obtain ⟨C, hC, h⟩ := win_comm_cons_interchanged_proof
  refine ⟨C, hC, ?_⟩
  intro P ε S hε W
  refine le_trans (le_of_eq ?_) (h P ε S hε W)
  exact consistencyDefect_swappedState (commTupleDist P)
    (fun ω a => (S.pairWMeas .alice W ω.1 ω.2.1 ω.2.2.1 ω.2.2.2).effect a)
    (fun ω a => (S.pointTraceMeas .bob W (selectedTuplePoint W ω)
      (selectedTupleScalar W ω)).effect a) S.toStrategy.ψ

/-- Pair-W self-consistency with Bob on the left factor, transported to the
interchanged state. Paper
`14_analysis_of_the_pauli_basis_test.tex:315-320`, blueprint
`ch14_qpbt_observables.tex:683-733`. -/
theorem pairW_self_consistency_comm_swapped {P : AdmissibleParams} {ε : ℝ}
    (S : ProjectiveSetting P ε) (W : PauliKind) :
    consistencyDefect (commTupleDist P)
        (fun ω a => heteroKron
          ((S.pairWMeas .bob W ω.1 ω.2.1 ω.2.2.1 ω.2.2.2).effect a) 1)
        (fun ω a => heteroKron 1
          ((S.pairWMeas .alice W ω.1 ω.2.1 ω.2.2.1 ω.2.2.2).effect a))
        S.swappedState ≤ 2 * (Fintype.card PauliEdge : ℝ) * ε := by
  refine le_trans (le_of_eq ?_) (pairW_self_consistency_comm_le S W)
  exact consistencyDefect_swappedState (commTupleDist P)
    (fun ω a => (S.pairWMeas .alice W ω.1 ω.2.1 ω.2.2.1 ω.2.2.2).effect a)
    (fun ω a => (S.pairWMeas .bob W ω.1 ω.2.1 ω.2.2.1 ω.2.2.2).effect a)
    S.toStrategy.ψ

/-- The commuting Pair check with Bob on the left factor, transported to the
interchanged state. Paper
`14_analysis_of_the_pauli_basis_test.tex:210-231`, blueprint
`ch14_qpbt_observables.tex:699-701`. -/
theorem win_comm_swapped_proof :
    ∃ C : ℝ, 1 ≤ C ∧
      ∀ (P : AdmissibleParams) (ε : ℝ) (S : ProjectiveSetting P ε),
      0 ≤ ε → ∀ W : PauliKind,
      consistencyDefect (commTupleDist P)
        (fun ω a => heteroKron
          ((S.pairWMeas .bob W ω.1 ω.2.1 ω.2.2.1 ω.2.2.2).effect a) 1)
        (fun ω a => heteroKron 1
          ((S.pairComponentMeas .alice W ω).effect a))
        S.swappedState ≤ C * ε := by
  obtain ⟨C, hC, h⟩ := win_comm_interchanged_proof
  refine ⟨C, hC, ?_⟩
  intro P ε S hε W
  refine le_trans (le_of_eq ?_) (h P ε S hε W)
  exact consistencyDefect_swappedState (commTupleDist P)
    (fun ω a => (S.pairComponentMeas .alice W ω).effect a)
    (fun ω a => (S.pairWMeas .bob W ω.1 ω.2.1 ω.2.2.1 ω.2.2.2).effect a)
    S.toStrategy.ψ

/-- Magic Square variable consistency with Bob on the left factor, transported
to the interchanged state. Paper
`14_analysis_of_the_pauli_basis_test.tex:250-263`, blueprint
`ch14_qpbt_observables.tex:699-701`. -/
theorem win_ms_cons_swapped_proof :
    ∃ C : ℝ, 1 ≤ C ∧
      ∀ (P : AdmissibleParams) (ε : ℝ) (S : ProjectiveSetting P ε),
      0 ≤ ε → ∀ W : PauliKind,
      consistencyDefect (anticommTupleDist P)
        (fun ω a => heteroKron
          ((S.pointTraceMeas .bob W (selectedTuplePoint W ω)
            (selectedTupleScalar W ω)).effect a) 1)
        (fun ω a => heteroKron 1
          ((S.msVarBitMeas .alice (selectedMsVar W) ω).effect a))
        S.swappedState ≤ C * ε := by
  obtain ⟨C, hC, h⟩ := win_ms_cons_interchanged_proof
  refine ⟨C, hC, ?_⟩
  intro P ε S hε W
  refine le_trans (le_of_eq ?_) (h P ε S hε W)
  exact consistencyDefect_swappedState (anticommTupleDist P)
    (fun ω a => (S.msVarBitMeas .alice (selectedMsVar W) ω).effect a)
    (fun ω a => (S.pointTraceMeas .bob W (selectedTuplePoint W ω)
      (selectedTupleScalar W ω)).effect a) S.toStrategy.ψ

/-! ## The two halves on Bob's factor -/

/-- The point observables of Bob approximately commute on commuting tuples,
read on the interchanged state. Paper
`14_analysis_of_the_pauli_basis_test.tex:311-341`, blueprint
`ch14_qpbt_observables.tex:683-733`. -/
theorem exists_pointObs_commutator_comm_le_bob :
    ∃ C : ℝ, 1 ≤ C ∧
      ∀ (P : AdmissibleParams) (ε : ℝ) (S : ProjectiveSetting P ε), 0 ≤ ε →
      avgOver (commTupleDist P) (fun ω =>
        ‖applyOperatorToState
          (heteroKron (S.pointObs .bob .X ω.2.2.1 ω.1 *
              S.pointObs .bob .Z ω.2.2.2 ω.2.1) (1 : Op S.toStrategy.ιA) -
            heteroKron (S.pointObs .bob .Z ω.2.2.2 ω.2.1 *
              S.pointObs .bob .X ω.2.2.1 ω.1) (1 : Op S.toStrategy.ιA))
          S.swappedState‖ ^ 2) ≤ C * (ε + Real.sqrt ε) := by
  classical
  obtain ⟨C₁, hC₁, hgen⟩ := exists_pointObs_commutator_comm_le
  obtain ⟨Cc, hCc, hcc⟩ := win_comm_cons_swapped_proof
  obtain ⟨Cm, hCm, hcm⟩ := win_comm_swapped_proof
  have hcard : (1 : ℝ) ≤ (Fintype.card PauliEdge : ℝ) := by
    exact_mod_cast (Fintype.card_pos : 0 < Fintype.card PauliEdge)
  set K : ℝ := 2 * (Fintype.card PauliEdge : ℝ) + Cm with hKdef
  have hK : (0 : ℝ) ≤ K := by rw [hKdef]; linarith
  refine ⟨C₁ * Cc + C₁ * Real.sqrt K, by nlinarith [Real.sqrt_nonneg K], ?_⟩
  intro P ε S hε
  have hsq : (0 : ℝ) ≤ Real.sqrt ε := Real.sqrt_nonneg ε
  have hC₁0 : (0 : ℝ) ≤ C₁ := by linarith
  have hCc0 : (0 : ℝ) ≤ Cc := by linarith
  have hmain := hgen (ιL := S.toStrategy.ιB) (ιR := S.toStrategy.ιA)
    (fun ω => S.pointTraceMeas .bob .X ω.1 ω.2.2.1)
    (fun ω => S.pointTraceMeas .bob .Z ω.2.1 ω.2.2.2)
    (fun ω => S.pairWMeas .bob .X ω.1 ω.2.1 ω.2.2.1 ω.2.2.2)
    (fun ω => S.pairWMeas .bob .Z ω.1 ω.2.1 ω.2.2.1 ω.2.2.2)
    (fun ω => S.pairWMeas .alice .X ω.1 ω.2.1 ω.2.2.1 ω.2.2.2)
    (fun ω => S.pairWMeas .alice .Z ω.1 ω.2.1 ω.2.2.1 ω.2.2.2)
    (fun ω => S.pairMeas .alice ω.1 ω.2.1 ω.2.2.1 ω.2.2.2)
    (fun ω => S.pointObs .bob .X ω.2.2.1 ω.1)
    (fun ω => S.pointObs .bob .Z ω.2.2.2 ω.2.1)
    S.swappedState (norm_swappedState S) (by positivity)
    (fun ω => postprocess_isProjective _ (S.isProjective.1 _) _)
    (fun ω => pointObs_eq_one_sub_two_smul S .bob .X ω.2.2.1 ω.1)
    (fun ω => pointObs_eq_one_sub_two_smul S .bob .Z ω.2.2.2 ω.2.1)
    (hcc P ε S hε .X) (hcc P ε S hε .Z)
    (pairW_self_consistency_comm_swapped S .X)
    (pairW_self_consistency_comm_swapped S .Z)
    (hcm P ε S hε .X) (hcm P ε S hε .Z)
  refine le_trans hmain ?_
  have hKsplit : Real.sqrt (2 * (Fintype.card PauliEdge : ℝ) * ε + Cm * ε) =
      Real.sqrt K * Real.sqrt ε := by
    rw [show 2 * (Fintype.card PauliEdge : ℝ) * ε + Cm * ε = K * ε by
      rw [hKdef]; ring]
    exact Real.sqrt_mul hK ε
  rw [hKsplit]
  nlinarith [mul_nonneg hC₁0 hCc0,
    mul_nonneg hC₁0 (Real.sqrt_nonneg K), hε, hsq]

/-- Alice's Magic Square variable anticommutator read on the interchanged
state.  Paper `14_analysis_of_the_pauli_basis_test.tex:349-356`, blueprint
`ch14_qpbt_observables.tex:683-733`. -/
theorem msVarBitObsA_anticommutator_swapped_le {P : AdmissibleParams} {ε : ℝ}
    (S : ProjectiveSetting P ε) (ω : PauliTuple P) :
    ‖applyOperatorToState
        (heteroKron (ιA := S.toStrategy.ιB) (ιB := S.toStrategy.ιA) 1
          (obsOf (S.msVarBitMeas .alice 0 ω) *
              obsOf (S.msVarBitMeas .alice 4 ω) +
            obsOf (S.msVarBitMeas .alice 4 ω) *
              obsOf (S.msVarBitMeas .alice 0 ω)))
        S.swappedState‖ ^ 2 ≤ 1183680 * (1 - S.msValueAt ω) := by
  have htrans := norm_applyOperatorToState_reindexState
    (Equiv.prodComm S.toStrategy.ιA S.toStrategy.ιB)
    (heteroKron (ιA := S.toStrategy.ιB) (ιB := S.toStrategy.ιA) 1
      (obsOf (S.msVarBitMeas .alice 0 ω) *
          obsOf (S.msVarBitMeas .alice 4 ω) +
        obsOf (S.msVarBitMeas .alice 4 ω) *
          obsOf (S.msVarBitMeas .alice 0 ω)))
    S.toStrategy.ψ
  rw [reindexOp_prodComm_heteroKron] at htrans
  exact le_of_eq_of_le (congrArg (fun t : ℝ => t ^ 2) htrans)
    (msVarBitObsA_anticommutator_le S ω)

/-- The point observables of Bob approximately anticommute on anticommuting
tuples, read on the interchanged state. Paper
`14_analysis_of_the_pauli_basis_test.tex:342-362`, blueprint
`ch14_qpbt_observables.tex:683-733`. -/
theorem exists_pointObs_anticommutator_anticomm_le_bob :
    ∃ C : ℝ, 1 ≤ C ∧
      ∀ (P : AdmissibleParams) (ε : ℝ) (S : ProjectiveSetting P ε), 0 ≤ ε →
      avgOver (anticommTupleDist P) (fun ω =>
        ‖applyOperatorToState
          (heteroKron (S.pointObs .bob .X ω.2.2.1 ω.1 *
              S.pointObs .bob .Z ω.2.2.2 ω.2.1) (1 : Op S.toStrategy.ιA) +
            heteroKron (S.pointObs .bob .Z ω.2.2.2 ω.2.1 *
              S.pointObs .bob .X ω.2.2.1 ω.1) (1 : Op S.toStrategy.ιA))
          S.swappedState‖ ^ 2) ≤ C * ε := by
  classical
  obtain ⟨Cms, hCms, hms⟩ := win_ms_cons_swapped_proof
  obtain ⟨Cv, hCv, hv⟩ := win_magic_square_proof
  refine ⟨96 * Cms + 3551040 * Cv, by nlinarith, ?_⟩
  intro P ε S hε
  simp only [pointObs_eq_obsOf]
  have hdist : ∀ W : PauliKind,
      avgOver (anticommTupleDist P) (fun ω => ‖applyOperatorToState
        (heteroKron (ιA := S.toStrategy.ιB) (ιB := S.toStrategy.ιA)
            (obsOf (S.pointTraceMeas .bob W (selectedTuplePoint W ω)
              (selectedTupleScalar W ω))) 1 -
          heteroKron (ιA := S.toStrategy.ιB) (ιB := S.toStrategy.ιA) 1
            (obsOf (S.msVarBitMeas .alice (selectedMsVar W) ω)))
        S.swappedState‖ ^ 2) ≤ 4 * (Cms * ε) := by
    intro W
    have h := obsDist_le_of_consistencyDefect
      (ιL := S.toStrategy.ιB) (ιR := S.toStrategy.ιA) (anticommTupleDist P)
      (fun ω => S.pointTraceMeas .bob W (selectedTuplePoint W ω)
        (selectedTupleScalar W ω))
      (fun ω => S.msVarBitMeas .alice (selectedMsVar W) ω) S.swappedState
      (hms P ε S hε W)
    rw [opDistSq_eq_avgOver] at h
    exact h
  have hdefect : avgOver (anticommTupleDist P)
      (fun ω => 1 - S.msValueAt ω) ≤ Cv * ε := by
    have hprob := anticommTupleDist_isProbability P
    have hsplit : avgOver (anticommTupleDist P)
        (fun ω => 1 - S.msValueAt ω) =
        1 - avgOver (anticommTupleDist P) S.msValueAt := by
      rw [avgOver_sub, avgOver_const_of_isProbability _ hprob]
    rw [hsplit]
    exact le_of_abs_le (hv P ε S hε)
  have hmsavg : avgOver (anticommTupleDist P) (fun ω =>
      ‖applyOperatorToState
        (heteroKron (ιA := S.toStrategy.ιB) (ιB := S.toStrategy.ιA) 1
          (obsOf (S.msVarBitMeas .alice 0 ω) *
              obsOf (S.msVarBitMeas .alice 4 ω) +
            obsOf (S.msVarBitMeas .alice 4 ω) *
              obsOf (S.msVarBitMeas .alice 0 ω)))
        S.swappedState‖ ^ 2) ≤ 1183680 * (Cv * ε) := by
    calc
      _ ≤ avgOver (anticommTupleDist P)
          (fun ω => 1183680 * (1 - S.msValueAt ω)) :=
        avgOver_mono _ _ _
          (fun ω => msVarBitObsA_anticommutator_swapped_le S ω)
      _ = 1183680 * avgOver (anticommTupleDist P)
          (fun ω => 1 - S.msValueAt ω) := avgOver_const_mul _ _ _
      _ ≤ 1183680 * (Cv * ε) :=
        mul_le_mul_of_nonneg_left hdefect (by norm_num)
  have hmain := obs_anticommutator_avg_le (ιL := S.toStrategy.ιB)
    (ιR := S.toStrategy.ιA)
    (fun ω => obsOf (S.pointTraceMeas .bob .X ω.1 ω.2.2.1))
    (fun ω => obsOf (S.pointTraceMeas .bob .Z ω.2.1 ω.2.2.2))
    (fun ω => obsOf (S.msVarBitMeas .alice 0 ω))
    (fun ω => obsOf (S.msVarBitMeas .alice 4 ω)) S.swappedState
    (fun ω => pointTraceObs_conjTranspose_mul_self S .bob .X ω.1 ω.2.2.1)
    (fun ω => pointTraceObs_conjTranspose_mul_self S .bob .Z ω.2.1 ω.2.2.2)
    (fun ω => msVarBitObs_conjTranspose_mul_self S .alice 0 ω)
    (fun ω => msVarBitObs_conjTranspose_mul_self S .alice 4 ω)
    (hdist .X) (hdist .Z) hmsavg
  exact le_trans hmain (le_of_eq (by ring))

/-! ## The interchanged twisted commutation relation -/

/-- The factor-interchanged phase-signed commutation relation on Bob's factor.
This is the trailing clause of `lem:qld-win-implications-obs`, paper
`14_analysis_of_the_pauli_basis_test.tex:309-354`, blueprint
`ch14_qpbt_observables.tex:683-733`. -/
theorem pointObs_twisted_commutation_interchanged_proof :
    ∃ C : ℝ, 1 ≤ C ∧
      ∀ (P : AdmissibleParams) (ε : ℝ) (S : ProjectiveSetting P ε),
      0 ≤ ε →
      opDistSq (uniformDistribution (PauliTuple P))
        (fun ω => heteroKron 1
          (S.pointObs .bob .X ω.2.2.1 ω.1 *
            S.pointObs .bob .Z ω.2.2.2 ω.2.1))
        (fun ω => phaseSign (gammaValue P ω.1 ω.2.1 ω.2.2.1 ω.2.2.2) •
          heteroKron 1
            (S.pointObs .bob .Z ω.2.2.2 ω.2.1 *
              S.pointObs .bob .X ω.2.2.1 ω.1))
        S.toStrategy.ψ ≤ C * Real.sqrt ε := by
  classical
  obtain ⟨Cc, hCc, hcomm⟩ := exists_pointObs_commutator_comm_le_bob
  obtain ⟨Ca, hCa, hanti⟩ := exists_pointObs_anticommutator_anticomm_le_bob
  refine ⟨2 * Cc + Ca + 4, by linarith, ?_⟩
  intro P ε S hε
  have hswapped := twisted_commutation_of_halves
    (fun ω => S.pointObs .bob .X ω.2.2.1 ω.1)
    (fun ω => S.pointObs .bob .Z ω.2.2.2 ω.2.1)
    S.swappedState (norm_swappedState S)
    (fun ω => pointObs_conjTranspose_mul_self S .bob .X ω.2.2.1 ω.1)
    (fun ω => pointObs_conjTranspose_mul_self S .bob .Z ω.2.2.2 ω.2.1)
    hε (by linarith) (by linarith) (hcomm P ε S hε) (hanti P ε S hε)
  have htransport := opDistSq_smul_swappedState
    (ιA := S.toStrategy.ιA) (ιB := S.toStrategy.ιB)
    (uniformDistribution (PauliTuple P))
    (fun ω => phaseSign (gammaValue P ω.1 ω.2.1 ω.2.2.1 ω.2.2.2))
    (fun ω => S.pointObs .bob .X ω.2.2.1 ω.1 *
      S.pointObs .bob .Z ω.2.2.2 ω.2.1)
    (fun ω => S.pointObs .bob .Z ω.2.2.2 ω.2.1 *
      S.pointObs .bob .X ω.2.2.1 ω.1) S.toStrategy.ψ
  exact le_of_eq_of_le htransport.symm hswapped

end WinImplications

end

end MIPStarRE.QPBT
