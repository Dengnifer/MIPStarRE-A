import MIPStarRE.QPBT.Observables.WinImplications.PointObs

/-!
# Approximate commutation of the point observables on commuting tuples

This module carries out the commuting half of the proof of Equation
`eq:pts-obs-commutation` in `lem:qld-win-implications-obs`: the chain of
consistency relations `eq:lc-11`, the commutation analysis
`lem:commutation-analysis`, and the expansion `eq:lc-12` of the observables in
terms of the trace-coarse-grained point projections.

## References

The declarations support `lem:qld-win-implications-obs` in
`blueprint/src/chapter/ch14_qpbt_observables.tex:683-733`, whose paper source
is `references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:309-341`.
-/

open scoped BigOperators Matrix ComplexOrder

namespace MIPStarRE.QPBT

open MIPStarRE.LDT hiding Measurement
open MIPStarRE.Quantum

noncomputable section

namespace WinImplications

local instance pauliEdgeNonemptyCommObs : Nonempty PauliEdge :=
  pauliEdge_nonempty

/-! ## Algebraic preliminaries -/

/-- The left tensor placement is additive in its left factor. Formalization-only
support for `eq:lc-12`, paper
`14_analysis_of_the_pauli_basis_test.tex:330-341`. -/
theorem heteroKron_sub_left {ιA ιB : Type*} (M N : Op ιA) (B : Op ιB) :
    heteroKron M B - heteroKron N B = heteroKron (M - N) B := by
  ext i j
  simp [heteroKron, Matrix.kronecker, sub_mul]

/-- The left tensor placement is homogeneous in its left factor.
Formalization-only support for `eq:lc-12`, paper
`14_analysis_of_the_pauli_basis_test.tex:330-341`. -/
theorem heteroKron_smul_left {ιA ιB : Type*} (c : ℂ) (M : Op ιA) (B : Op ιB) :
    heteroKron (c • M) B = c • heteroKron M B := by
  ext i j
  simp [heteroKron, Matrix.kronecker, mul_assoc]

/-- A sum over the two-element binary alphabet. Formalization-only support for
`def:strategy-observables`, blueprint `ch14_qpbt_observables.tex:480-503`. -/
theorem sum_over_zmodTwo {M : Type*} [AddCommMonoid M] (f : ZMod 2 → M) :
    ∑ b : ZMod 2, f b = f 0 + f 1 := by
  rw [show (Finset.univ : Finset (ZMod 2)) = {0, 1} from by decide]
  rw [Finset.sum_insert (by decide), Finset.sum_singleton]

/-- The commutator of two reflections written as `1 - 2P` is four times the
commutator of the projections. This is the algebra of Equation `eq:lc-12`,
paper `14_analysis_of_the_pauli_basis_test.tex:330-341`, blueprint
`ch14_qpbt_observables.tex:683-733`. -/
theorem reflection_commutator_eq {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A B : Op ι) :
    (1 - (2 : ℂ) • A) * (1 - (2 : ℂ) • B) -
        (1 - (2 : ℂ) • B) * (1 - (2 : ℂ) • A) =
      (4 : ℂ) • (A * B - B * A) := by
  have h2 : ∀ M : Op ι, (2 : ℂ) • M = M + M := fun M => two_smul ℂ M
  have h4 : ∀ M : Op ι, (4 : ℂ) • M = M + M + (M + M) := by
    intro M
    rw [show (4 : ℂ) = 2 + 2 by norm_num, add_smul, h2]
  rw [h2, h2, h4]
  noncomm_ring

/-- Regrouping the outcomes of a projective POVM preserves projectivity. A
private copy of this statement belongs to `Observables/Defs.lean`; this public
form is the one used by `lem:commutation-analysis` below. -/
theorem postprocess_isProjective {α β ι : Type*}
    [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    [Fintype ι] [DecidableEq ι]
    (M : MIPStarRE.Quantum.Measurement α ι)
    (hM : MIPStarRE.QPBT.Measurement.IsProjective M) (f : α → β) :
    MIPStarRE.QPBT.Measurement.IsProjective (M.postprocess f) := by
  classical
  intro b
  refine ⟨?_, ?_⟩
  · change (M.postprocess f).effect b * (M.postprocess f).effect b =
      (M.postprocess f).effect b
    let fiber : Finset α := Finset.univ.filter fun a => f a = b
    calc
      (M.postprocess f).effect b * (M.postprocess f).effect b =
          (∑ a ∈ fiber, M.effect a) * (∑ a' ∈ fiber, M.effect a') := by
            rw [MIPStarRE.Quantum.Measurement.postprocess_effect]
      _ = ∑ a ∈ fiber, ∑ a' ∈ fiber, M.effect a * M.effect a' := by
            rw [Finset.sum_mul]
            simp_rw [Finset.mul_sum]
      _ = ∑ a ∈ fiber, ∑ a' ∈ fiber, if a' = a then M.effect a else 0 := by
            refine Finset.sum_congr rfl ?_
            intro a _
            refine Finset.sum_congr rfl ?_
            intro a' _
            by_cases haa' : a' = a
            · subst a'
              simp [(hM a).isIdempotentElem.eq]
            · have hne : a ≠ a' := fun h => haa' h.symm
              simp [DistanceCalculus.projective_effect_mul_effect_eq_zero M hM hne,
                haa']
      _ = ∑ a ∈ fiber, M.effect a := by
            refine Finset.sum_congr rfl ?_
            intro a ha
            simp [fiber, ha]
      _ = (M.postprocess f).effect b := by
            rw [MIPStarRE.Quantum.Measurement.postprocess_effect]
  · change star ((M.postprocess f).effect b) = (M.postprocess f).effect b
    change ((M.postprocess f).effect b)ᴴ = (M.postprocess f).effect b
    exact (Matrix.nonneg_iff_posSemidef.mp
      ((M.postprocess f).pos b)).isHermitian.eq

/-- The strategy point observable is the reflection about the trace-coarse
grained point projection at label one. This is the first display of
Equation `eq:lc-12`, paper
`14_analysis_of_the_pauli_basis_test.tex:330-336`, blueprint
`ch14_qpbt_observables.tex:683-733`. -/
theorem pointObs_eq_one_sub_two_smul {P : AdmissibleParams} {ε : ℝ}
    (S : ProjectiveSetting P ε) (side : PlayerSide) (W : PauliKind)
    (r : PauliScalar P) (u : Fin P.m → PauliScalar P) :
    S.pointObs side W r u =
      1 - (2 : ℂ) • (S.pointTraceMeas side W u r).effect 1 := by
  classical
  rw [pointObs_eq_traceMeas_obs, sum_over_zmodTwo]
  have hsum : (S.pointTraceMeas side W u r).effect 0 +
      (S.pointTraceMeas side W u r).effect 1 = 1 := by
    have := (S.pointTraceMeas side W u r).sum_eq_one
    rwa [sum_over_zmodTwo] at this
  have hzero : phaseSign (0 : ZMod 2) = 1 := by simp [phaseSign]
  have hone : phaseSign (1 : ZMod 2) = -1 := by
    have : (1 : ZMod 2) ≠ 0 := by decide
    simp [phaseSign, this]
  rw [hzero, hone, one_smul, neg_one_smul]
  have heff0 : (S.pointTraceMeas side W u r).effect 0 =
      1 - (S.pointTraceMeas side W u r).effect 1 := by
    rw [← hsum]; abel
  rw [heff0, two_smul]
  abel

/-! ## Pair/W self-consistency on commuting tuples -/

/-- Pair/W self-consistency is the Pair/W self-loop label mismatch. This is
item 1 of `lem:qld-win-implications` read on the Pair/W questions, paper
`14_analysis_of_the_pauli_basis_test.tex:197-199,315-320`, blueprint
`ch14_qpbt_observables.tex:515-522`. -/
theorem pairWConsistency_eq_mismatch {P : AdmissibleParams} {ε : ℝ}
    (S : ProjectiveSetting P ε) (W : PauliKind) :
    consistencyDefect (commTupleDist P)
        (fun ω a => heteroKron
          ((S.pairWMeas .alice W ω.1 ω.2.1 ω.2.2.1 ω.2.2.2).effect a) 1)
        (fun ω a => heteroKron 1
          ((S.pairWMeas .bob W ω.1 ω.2.1 ω.2.2.1 ω.2.2.2).effect a))
        S.toStrategy.ψ =
      avgOver (commTupleDist P) (fun ω =>
        outcomeEventWeight S.toStrategy
          (ProjectiveSetting.pairWQuestion P W ω.1 ω.2.1 ω.2.2.1 ω.2.2.2)
          (ProjectiveSetting.pairWQuestion P W ω.1 ω.2.1 ω.2.2.1 ω.2.2.2)
          (fun A B => ProjectiveSetting.pairWAnswerOrZero A ≠
            ProjectiveSetting.pairWAnswerOrZero B)) := by
  classical
  let qA : PauliTuple P → PauliQuestion P := fun ω =>
    ProjectiveSetting.pairWQuestion P W ω.1 ω.2.1 ω.2.2.1 ω.2.2.2
  let fA : PauliTuple P → PauliAnswer P → ZMod 2 := fun _ =>
    ProjectiveSetting.pairWAnswerOrZero
  have h := consistencyDefect_postprocess_eq_mismatch
    (commTupleDist P) S.toStrategy qA qA fA fA
  have hA : ∀ ω c,
      heteroKron
          ((S.pairWMeas .alice W ω.1 ω.2.1 ω.2.2.1 ω.2.2.2).effect c)
          (1 : Op S.toStrategy.ιB) =
        heteroKron (((S.toStrategy.A (qA ω)).postprocess (fA ω)).effect c)
          (1 : Op S.toStrategy.ιB) := by
    intro ω c
    rfl
  have hB : ∀ ω c,
      heteroKron (1 : Op S.toStrategy.ιA)
          ((S.pairWMeas .bob W ω.1 ω.2.1 ω.2.2.1 ω.2.2.2).effect c) =
        heteroKron (1 : Op S.toStrategy.ιA)
          (((S.toStrategy.B (qA ω)).postprocess (fA ω)).effect c) := by
    intro ω c
    rfl
  calc
    _ = consistencyDefect (commTupleDist P)
        (fun ω c => heteroKron
          (((S.toStrategy.A (qA ω)).postprocess (fA ω)).effect c) 1)
        (fun ω c => heteroKron 1
          (((S.toStrategy.B (qA ω)).postprocess (fA ω)).effect c))
        S.toStrategy.ψ := consistencyDefect_congr _ _ _ _ _ _ hA hB
    _ = avgOver (commTupleDist P) (fun ω =>
        outcomeEventWeight S.toStrategy (qA ω) (qA ω)
          (fun A B => fA ω A ≠ fA ω B)) := h
    _ = _ := by rfl

/-- The Pair/W measurements are self-consistent on commuting tuples. This is
item 1 of `lem:qld-win-implications` on the Pair/W questions, used in the
chain leading to Equation `eq:lc-11`, paper
`14_analysis_of_the_pauli_basis_test.tex:315-320`, blueprint
`ch14_qpbt_observables.tex:683-733`. -/
theorem pairW_self_consistency_comm_le {P : AdmissibleParams} {ε : ℝ}
    (S : ProjectiveSetting P ε) (W : PauliKind) :
    consistencyDefect (commTupleDist P)
        (fun ω a => heteroKron
          ((S.pairWMeas .alice W ω.1 ω.2.1 ω.2.2.1 ω.2.2.2).effect a) 1)
        (fun ω a => heteroKron 1
          ((S.pairWMeas .bob W ω.1 ω.2.1 ω.2.2.1 ω.2.2.2).effect a))
        S.toStrategy.ψ ≤ 2 * (Fintype.card PauliEdge : ℝ) * ε := by
  classical
  rw [pairWConsistency_eq_mismatch]
  calc
    _ ≤ 2 * avgOver (uniformDistribution (PauliTuple P)) (fun ω =>
        if IsCommuting ω then
          outcomeEventWeight S.toStrategy
            (ProjectiveSetting.pairWQuestion P W ω.1 ω.2.1 ω.2.2.1 ω.2.2.2)
            (ProjectiveSetting.pairWQuestion P W ω.1 ω.2.1 ω.2.2.1 ω.2.2.2)
            (fun A B => ProjectiveSetting.pairWAnswerOrZero A ≠
              ProjectiveSetting.pairWAnswerOrZero B)
        else 0) := by
      apply avgOver_comm_le_two_mul_gated
      intro ω
      exact outcome_event_weight_nonneg S.toStrategy _ _ _
    _ ≤ 2 * avgOver (uniformDistribution (PauliSpace P))
        (pauliRejectionAt S.toStrategy (pauliLoopEdge (.pairW W))) := by
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      rw [← avgOver_pauliTuple_uniform]
      apply avgOver_mono
      intro z
      have hs : outcomeEventWeight S.toStrategy
          ((.pairW W), pauliCL P (.pairW W) z)
          ((.pairW W), pauliCL P (.pairW W) z)
          (fun A B => ProjectiveSetting.pairWAnswerOrZero A ≠
            ProjectiveSetting.pairWAnswerOrZero B) ≤
          pauliRejectionAt S.toStrategy (pauliLoopEdge (.pairW W)) z := by
        refine le_trans ?_ (loopMismatch_le_rejection S (.pairW W) z)
        apply outcome_event_weight_mono
        intro A B hne hAB
        exact hne (by rw [hAB])
      rw [pauliCL_shared_eq P (.pairW W) rfl] at hs
      by_cases hcomm : IsCommuting (pauliSharedSplit P z).1
      · simp only [if_pos hcomm]
        simpa [pauliSharedSplit, ProjectiveSetting.pairWQuestion] using hs
      · simp only [if_neg hcomm]
        exact pauliRejectionAt_nonneg S.toStrategy _ z
    _ ≤ 2 * (Fintype.card PauliEdge : ℝ) * ε := by
      rw [mul_assoc]
      exact mul_le_mul_of_nonneg_left (fixedEdgeRejection_le_error S _)
        (by norm_num)

/-! ## The chained relation of Equation `eq:lc-11` -/

/-- Chaining the commuting-case consistency relations gives the point/Pair
relation `eq:lc-11`. The statement is generic in the two tensor factors and in
the state, so that both orientations of `eq:pts-obs-commutation` use it. Paper
`14_analysis_of_the_pauli_basis_test.tex:311-322`, blueprint
`ch14_qpbt_observables.tex:683-733`. -/
theorem pointTrace_pairComponent_dist_le {P : AdmissibleParams}
    {ιL ιR : Type} [Fintype ιL] [DecidableEq ιL] [Fintype ιR] [DecidableEq ιR]
    (MP QL : PauliTuple P → MIPStarRE.Quantum.Measurement (ZMod 2) ιL)
    (QR RR : PauliTuple P → MIPStarRE.Quantum.Measurement (ZMod 2) ιR)
    (χ : EuclideanSpace ℂ (ιL × ιR)) (hχ : ‖χ‖ = 1) {c₁ c₂ c₃ : ℝ}
    (h1 : consistencyDefect (commTupleDist P)
      (fun ω a => heteroKron ((MP ω).effect a) 1)
      (fun ω a => heteroKron 1 ((QR ω).effect a)) χ ≤ c₁)
    (h2 : consistencyDefect (commTupleDist P)
      (fun ω a => heteroKron ((QL ω).effect a) 1)
      (fun ω a => heteroKron 1 ((QR ω).effect a)) χ ≤ c₂)
    (h3 : consistencyDefect (commTupleDist P)
      (fun ω a => heteroKron ((QL ω).effect a) 1)
      (fun ω a => heteroKron 1 ((RR ω).effect a)) χ ≤ c₃) :
    opFamilyDistSq (commTupleDist P)
      (fun ω a => heteroKron ((MP ω).effect a) 1)
      (fun ω a => heteroKron 1 ((RR ω).effect a)) χ ≤
        2 * (c₁ + 2 * Real.sqrt (c₂ + c₃)) := by
  classical
  have hchain := consistencyDefect_trans_le (commTupleDist P)
    (fun ω => DistanceCalculus.leftPlacedMeasurement (ιB := ιR) (MP ω))
    (fun ω => DistanceCalculus.rightPlacedMeasurement (ιA := ιL) (QR ω))
    (fun ω => DistanceCalculus.leftPlacedMeasurement (ιB := ιR) (QL ω))
    (fun ω => DistanceCalculus.rightPlacedMeasurement (ιA := ιL) (RR ω))
    χ c₁ c₂ c₃ (commTupleDist_isProbability P) hχ h1 h2 h3
  exact opFamilyDistSq_placed_le_of_consistencyDefect_le (commTupleDist P)
    MP RR χ hchain

/-! ## The commutation analysis on commuting tuples -/

/-- Padding an answer alphabet by a unit factor does not change the operator
distance. Formalization-only support for `lem:commutation-analysis`, blueprint
`ch12_qpbt_games.tex:403-416`. -/
theorem opFamilyDistSq_unit_prod {X β ι : Type*} [Fintype β]
    [Fintype ι] [DecidableEq ι]
    (μ : Distribution X) (M N : X → β → Op ι) (ψ : EuclideanSpace ℂ ι) :
    opFamilyDistSq μ (fun x (ub : Unit × β) => M x ub.2)
        (fun x (ub : Unit × β) => N x ub.2) ψ = opFamilyDistSq μ M N ψ := by
  unfold opFamilyDistSq
  congr 1
  funext x
  rw [Fintype.sum_prod_type]
  simp

/-- The one-point relabeling of a binary measurement has the same effects. -/
theorem unitProd_postprocess_effect {β ι : Type*} [Fintype β] [DecidableEq β]
    [Fintype ι] [DecidableEq ι] (M : MIPStarRE.Quantum.Measurement β ι)
    (b : β) :
    (M.postprocess (fun b' : β => ((), b'))).effect ((), b) = M.effect b := by
  classical
  rw [MIPStarRE.Quantum.Measurement.postprocess_effect]
  rw [show (Finset.univ.filter
      (fun b' : β => ((), b') = ((), b))) = {b} from by
    ext b'
    simp [Prod.ext_iff, Finset.mem_filter]]
  exact Finset.sum_singleton _ _

/-- The commutator of the two trace-coarse-grained point projections is small
on commuting tuples. This is Equation `eq:qld-obs-comm`, obtained from
`lem:commutation-analysis`; the statement is generic in the two tensor factors
and in the state. Paper `14_analysis_of_the_pauli_basis_test.tex:322-329`,
blueprint `ch14_qpbt_observables.tex:683-733`. -/
theorem exists_pointTrace_commutator_comm_le :
    ∃ C₀ : ℝ, 1 ≤ C₀ ∧
      ∀ {P : AdmissibleParams} {ιL ιR : Type} [Fintype ιL] [DecidableEq ιL]
        [Fintype ιR] [DecidableEq ιR]
        (MX MZ : PauliTuple P → MIPStarRE.Quantum.Measurement (ZMod 2) ιL)
        (N : PauliTuple P →
          MIPStarRE.Quantum.Measurement (ZMod 2 × ZMod 2) ιR)
        (χ : EuclideanSpace ℂ (ιL × ιR)) {δ : ℝ},
      (∀ ω, MIPStarRE.QPBT.Measurement.IsProjective (N ω)) →
      opFamilyDistSq (commTupleDist P)
          (fun ω b => heteroKron ((MX ω).effect b) 1)
          (fun ω b => heteroKron 1
            (((N ω).postprocess (fun bits => bits.1)).effect b)) χ ≤ δ →
      opFamilyDistSq (commTupleDist P)
          (fun ω b => heteroKron ((MZ ω).effect b) 1)
          (fun ω b => heteroKron 1
            (((N ω).postprocess (fun bits => bits.2)).effect b)) χ ≤ δ →
      avgOver (commTupleDist P) (fun ω =>
        ‖applyOperatorToState (heteroKron
          ((MX ω).effect 1 * (MZ ω).effect 1 -
            (MZ ω).effect 1 * (MX ω).effect 1) 1) χ‖ ^ 2) ≤ C₀ * δ := by
  classical
  obtain ⟨C₀, hC₀, hcomm⟩ := opDistSq_commutator_le
  refine ⟨C₀, hC₀, ?_⟩
  intro P ιL ιR _ _ _ _ MX MZ N χ δ hN hX hZ
  set A : PauliTuple P →
      MIPStarRE.Quantum.Measurement (Unit × ZMod 2) ιL := fun ω =>
    (MX ω).postprocess (fun b => ((), b)) with hAdef
  set D : PauliTuple P →
      MIPStarRE.Quantum.Measurement (Unit × ZMod 2) ιL := fun ω =>
    (MZ ω).postprocess (fun c => ((), c)) with hDdef
  set B : PauliTuple P →
      MIPStarRE.Quantum.Measurement ((Unit × ZMod 2) × ZMod 2) ιR := fun ω =>
    (N ω).postprocess (fun bits => (((), bits.1), bits.2)) with hBdef
  have hBproj : ∀ ω, MIPStarRE.QPBT.Measurement.IsProjective (B ω) := by
    intro ω
    exact postprocess_isProjective _ (hN ω) _
  have hAB : opFamilyDistSq (commTupleDist P)
      (fun ω ab => heteroKron ((A ω).effect ab) 1)
      (fun ω ab => heteroKron 1
        (((B ω).postprocess (fun abc => abc.1)).effect ab)) χ ≤ δ := by
    have hrw : opFamilyDistSq (commTupleDist P)
        (fun ω ab => heteroKron ((A ω).effect ab) 1)
        (fun ω ab => heteroKron 1
          (((B ω).postprocess (fun abc => abc.1)).effect ab)) χ =
      opFamilyDistSq (commTupleDist P)
        (fun ω (ub : Unit × ZMod 2) => heteroKron
          ((MX ω).effect ub.2) (1 : Op ιR))
        (fun ω (ub : Unit × ZMod 2) => heteroKron (1 : Op ιL)
          (((N ω).postprocess (fun bits => bits.1)).effect ub.2)) χ := by
      congr 1 <;> funext ω ab
      · rw [hAdef]
        obtain ⟨⟨⟩, b⟩ := ab
        rw [unitProd_postprocess_effect]
      · obtain ⟨⟨⟩, b⟩ := ab
        congr 1
        rw [hBdef, measurement_postprocess_comp_effect]
        rw [MIPStarRE.Quantum.Measurement.postprocess_effect,
          MIPStarRE.Quantum.Measurement.postprocess_effect]
        refine Finset.sum_congr ?_ (fun _ _ => rfl)
        ext bits
        simp [Prod.ext_iff, Finset.mem_filter]
    refine le_of_eq_of_le hrw ?_
    refine le_of_eq_of_le (opFamilyDistSq_unit_prod (commTupleDist P)
      (fun ω b => heteroKron ((MX ω).effect b) (1 : Op ιR))
      (fun ω b => heteroKron (1 : Op ιL)
        (((N ω).postprocess (fun bits => bits.1)).effect b)) χ) hX
  have hDB : opFamilyDistSq (commTupleDist P)
      (fun ω ac => heteroKron ((D ω).effect ac) 1)
      (fun ω ac => heteroKron 1
        (((B ω).postprocess (fun abc => (abc.1.1, abc.2))).effect ac))
      χ ≤ δ := by
    have hrw : opFamilyDistSq (commTupleDist P)
        (fun ω ac => heteroKron ((D ω).effect ac) 1)
        (fun ω ac => heteroKron 1
          (((B ω).postprocess (fun abc => (abc.1.1, abc.2))).effect ac))
        χ =
      opFamilyDistSq (commTupleDist P)
        (fun ω (ub : Unit × ZMod 2) => heteroKron
          ((MZ ω).effect ub.2) (1 : Op ιR))
        (fun ω (ub : Unit × ZMod 2) => heteroKron (1 : Op ιL)
          (((N ω).postprocess (fun bits => bits.2)).effect ub.2)) χ := by
      congr 1 <;> funext ω ac
      · rw [hDdef]
        obtain ⟨⟨⟩, c⟩ := ac
        rw [unitProd_postprocess_effect]
      · obtain ⟨⟨⟩, c⟩ := ac
        congr 1
        rw [hBdef, measurement_postprocess_comp_effect]
        rw [MIPStarRE.Quantum.Measurement.postprocess_effect,
          MIPStarRE.Quantum.Measurement.postprocess_effect]
        refine Finset.sum_congr ?_ (fun _ _ => rfl)
        ext bits
        simp [Prod.ext_iff, Finset.mem_filter]
    refine le_of_eq_of_le hrw ?_
    refine le_of_eq_of_le (opFamilyDistSq_unit_prod (commTupleDist P)
      (fun ω b => heteroKron ((MZ ω).effect b) (1 : Op ιR))
      (fun ω b => heteroKron (1 : Op ιL)
        (((N ω).postprocess (fun bits => bits.2)).effect b)) χ) hZ
  have hout := hcomm (commTupleDist P) A B D χ δ hBproj hAB hDB
  refine le_trans ?_ hout
  unfold opFamilyDistSq
  apply avgOver_mono
  intro ω
  simp only [sub_zero]
  refine le_trans (le_of_eq ?_) (Finset.single_le_sum
    (f := fun abc : (Unit × ZMod 2) × ZMod 2 =>
      ‖applyOperatorToState (heteroKron
        ((A ω).effect (abc.1.1, abc.1.2) * (D ω).effect (abc.1.1, abc.2) -
          (D ω).effect (abc.1.1, abc.2) * (A ω).effect (abc.1.1, abc.1.2)) 1)
        χ‖ ^ 2)
    (fun _ _ => by positivity) (Finset.mem_univ (((), 1), 1)))
  rw [hAdef, hDdef]
  simp only [unitProd_postprocess_effect]

/-! ## From projections to observables -/

/-- Applying a scaled operator scales the resulting state. Formalization-only
support for `eq:lc-12`, paper
`14_analysis_of_the_pauli_basis_test.tex:330-341`. -/
theorem applyOperatorToState_smul_op {ι : Type*} [Fintype ι] [DecidableEq ι]
    (c : ℂ) (M : Op ι) (v : EuclideanSpace ℂ ι) :
    applyOperatorToState (c • M) v = c • applyOperatorToState M v := by
  unfold applyOperatorToState
  rw [map_smul, LinearMap.smul_apply]

/-- The observable commutator is sixteen times the squared projection
commutator, on every state and both tensor factors. This is the passage from
Equation `eq:qld-obs-comm` to the observables in Equation `eq:lc-12`, paper
`14_analysis_of_the_pauli_basis_test.tex:330-341`, blueprint
`ch14_qpbt_observables.tex:683-733`. -/
theorem norm_pointObs_commutator_sq {ιL ιR : Type*} [Fintype ιL]
    [DecidableEq ιL] [Fintype ιR] [DecidableEq ιR] (PX PZ OX OZ : Op ιL)
    (hX : OX = 1 - (2 : ℂ) • PX) (hZ : OZ = 1 - (2 : ℂ) • PZ)
    (χ : EuclideanSpace ℂ (ιL × ιR)) :
    ‖applyOperatorToState
        (heteroKron (OX * OZ) (1 : Op ιR) -
          heteroKron (OZ * OX) (1 : Op ιR)) χ‖ ^ 2 =
      16 * ‖applyOperatorToState
        (heteroKron (PX * PZ - PZ * PX) (1 : Op ιR)) χ‖ ^ 2 := by
  rw [heteroKron_sub_left, hX, hZ, reflection_commutator_eq,
    heteroKron_smul_left, applyOperatorToState_smul_op, norm_smul]
  have h4 : ‖(4 : ℂ)‖ = 4 := by norm_num
  rw [h4]
  ring

/-- The point observables approximately commute on commuting tuples. This is
the commuting half of Equation `eq:pts-obs-commutation`, stated generically in
the two tensor factors and the state. Paper
`14_analysis_of_the_pauli_basis_test.tex:311-341`, blueprint
`ch14_qpbt_observables.tex:683-733`. -/
theorem exists_pointObs_commutator_comm_le :
    ∃ C : ℝ, 1 ≤ C ∧
      ∀ {P : AdmissibleParams} {ιL ιR : Type} [Fintype ιL] [DecidableEq ιL]
        [Fintype ιR] [DecidableEq ιR]
        (MX MZ QX QZ : PauliTuple P →
          MIPStarRE.Quantum.Measurement (ZMod 2) ιL)
        (VX VZ : PauliTuple P → MIPStarRE.Quantum.Measurement (ZMod 2) ιR)
        (N : PauliTuple P →
          MIPStarRE.Quantum.Measurement (ZMod 2 × ZMod 2) ιR)
        (OX OZ : PauliTuple P → Op ιL)
        (χ : EuclideanSpace ℂ (ιL × ιR)) {c₁ c₂ c₃ : ℝ},
      ‖χ‖ = 1 → 0 ≤ c₁ →
      (∀ ω, MIPStarRE.QPBT.Measurement.IsProjective (N ω)) →
      (∀ ω, OX ω = 1 - (2 : ℂ) • (MX ω).effect 1) →
      (∀ ω, OZ ω = 1 - (2 : ℂ) • (MZ ω).effect 1) →
      consistencyDefect (commTupleDist P)
        (fun ω a => heteroKron ((MX ω).effect a) 1)
        (fun ω a => heteroKron 1 ((VX ω).effect a)) χ ≤ c₁ →
      consistencyDefect (commTupleDist P)
        (fun ω a => heteroKron ((MZ ω).effect a) 1)
        (fun ω a => heteroKron 1 ((VZ ω).effect a)) χ ≤ c₁ →
      consistencyDefect (commTupleDist P)
        (fun ω a => heteroKron ((QX ω).effect a) 1)
        (fun ω a => heteroKron 1 ((VX ω).effect a)) χ ≤ c₂ →
      consistencyDefect (commTupleDist P)
        (fun ω a => heteroKron ((QZ ω).effect a) 1)
        (fun ω a => heteroKron 1 ((VZ ω).effect a)) χ ≤ c₂ →
      consistencyDefect (commTupleDist P)
        (fun ω a => heteroKron ((QX ω).effect a) 1)
        (fun ω a => heteroKron 1
          (((N ω).postprocess (fun bits => bits.1)).effect a)) χ ≤ c₃ →
      consistencyDefect (commTupleDist P)
        (fun ω a => heteroKron ((QZ ω).effect a) 1)
        (fun ω a => heteroKron 1
          (((N ω).postprocess (fun bits => bits.2)).effect a)) χ ≤ c₃ →
      avgOver (commTupleDist P) (fun ω =>
        ‖applyOperatorToState
          (heteroKron (OX ω * OZ ω) (1 : Op ιR) -
            heteroKron (OZ ω * OX ω) (1 : Op ιR)) χ‖ ^ 2) ≤
        C * (c₁ + Real.sqrt (c₂ + c₃)) := by
  classical
  obtain ⟨C₀, hC₀, hcommutator⟩ := exists_pointTrace_commutator_comm_le
  refine ⟨64 * C₀, by linarith, ?_⟩
  intro P ιL ιR _ _ _ _ MX MZ QX QZ VX VZ N OX OZ χ c₁ c₂ c₃ hn hc hp hx hz a1 a2 b1 b2 d1 d2
  set δ : ℝ := 2 * (c₁ + 2 * Real.sqrt (c₂ + c₃)) with hδdef
  have hchainX := pointTrace_pairComponent_dist_le MX QX VX
    (fun ω => (N ω).postprocess (fun bits => bits.1)) χ hn a1 b1 d1
  have hchainZ := pointTrace_pairComponent_dist_le MZ QZ VZ
    (fun ω => (N ω).postprocess (fun bits => bits.2)) χ hn a2 b2 d2
  have hproj := hcommutator MX MZ N χ hp hchainX hchainZ
  have hcongr : avgOver (commTupleDist P) (fun ω =>
      ‖applyOperatorToState
        (heteroKron (OX ω * OZ ω) (1 : Op ιR) -
          heteroKron (OZ ω * OX ω) (1 : Op ιR)) χ‖ ^ 2) =
    16 * avgOver (commTupleDist P) (fun ω =>
      ‖applyOperatorToState (heteroKron
        ((MX ω).effect 1 * (MZ ω).effect 1 -
          (MZ ω).effect 1 * (MX ω).effect 1) (1 : Op ιR)) χ‖ ^ 2) := by
    rw [← avgOver_const_mul]
    refine avgOver_congr _ _ _ (fun ω => ?_)
    exact norm_pointObs_commutator_sq ((MX ω).effect 1) ((MZ ω).effect 1)
      (OX ω) (OZ ω) (hx ω) (hz ω) χ
  rw [hcongr]
  have hC00 : (0 : ℝ) ≤ C₀ := by linarith
  have hs : (0 : ℝ) ≤ Real.sqrt (c₂ + c₃) := Real.sqrt_nonneg _
  have hfinal : 16 * (C₀ * δ) ≤ 64 * C₀ * (c₁ + Real.sqrt (c₂ + c₃)) := by
    rw [hδdef]
    nlinarith [mul_nonneg hC00 hc, mul_nonneg hC00 hs]
  exact le_trans (mul_le_mul_of_nonneg_left hproj (by norm_num)) hfinal

end WinImplications

end

end MIPStarRE.QPBT
