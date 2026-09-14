import MIPStarRE.QPBT.Games.StrategyClasses
import MIPStarRE.QPBT.Games.TypedCondLinear
import MIPStarRE.QPBT.Test.Completeness.Commutation
import MIPStarRE.QPBT.Test.Completeness.HonestStrategy
import MIPStarRE.QPBT.Test.Completeness.HonestStrategy.Assembly
import MIPStarRE.QPBT.Test.Completeness.Rejection
import MIPStarRE.QPBT.Test.LowDegreeGameTheorems
import MIPStarRE.QPBT.Test.MagicSquareTheorems
import MIPStarRE.QPBT.Test.PauliBasisTest

/-!
# Completeness of the Pauli basis test

The Pauli basis test admits a symmetric presentation and a value-one SPCC
strategy.

## References

The source statement is blueprint
`lem:pauli-completeness`, from
`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:1229-1421`.
-/

open scoped BigOperators

namespace MIPStarRE.QPBT

open MIPStarRE.LDT

noncomputable section

/-! ### Auxiliary facts about the Pauli question sampler

The two lemmas of this section are formalization-only.  They record that the
uniform law on the Pauli edge type, and the typed bind seeded by it, do not
depend on the finiteness and decidability data used to form them.  The general
identities about finite weighted distributions that this file uses are stated
in `MIPStarRE/QPBT/Games/DistributionAux.lean`.
-/

/-- Formalization-only auxiliary: the push-forward of a uniform distribution
does not depend on the finiteness and decidability data used to form it. -/
private theorem map_uniformDistribution_congr {α γ : Type*}
    (i₁ i₂ : Fintype α) (j₁ j₂ : DecidableEq α) (k₁ k₂ : Nonempty α)
    (d₁ d₂ : DecidableEq γ) (e : α → γ) :
    @Distribution.map α γ d₁ (@uniformDistribution α i₁ j₁ k₁) e =
      @Distribution.map α γ d₂ (@uniformDistribution α i₂ j₂ k₂) e := by
  have hi : i₁ = i₂ := Subsingleton.elim _ _
  have hj : j₁ = j₂ := funext fun _ => funext fun _ => Subsingleton.elim _ _
  have hd : d₁ = d₂ := funext fun _ => funext fun _ => Subsingleton.elim _ _
  subst hi
  subst hj
  subst hd
  rfl

/-- Formalization-only auxiliary: a uniformly seeded typed bind does not depend
on the finiteness and decidability data used to form it. -/
private theorem bind_map_uniformDistribution_congr {α β γ : Type*}
    (i₁ i₂ : Fintype β) (j₁ j₂ : DecidableEq β) (k₁ k₂ : Nonempty β)
    (d₁ d₂ : DecidableEq γ) (μ : Distribution α) (g : α → β → γ) :
    @Distribution.bind α γ d₁ μ
        (fun a => @Distribution.map β γ d₁ (@uniformDistribution β i₁ j₁ k₁) (g a)) =
      @Distribution.bind α γ d₂ μ
        (fun a => @Distribution.map β γ d₂ (@uniformDistribution β i₂ j₂ k₂) (g a)) := by
  have hi : i₁ = i₂ := Subsingleton.elim _ _
  have hj : j₁ = j₂ := funext fun _ => funext fun _ => Subsingleton.elim _ _
  have hd : d₁ = d₂ := funext fun _ => funext fun _ => Subsingleton.elim _ _
  subst hi
  subst hj
  subst hd
  rfl

/-! ### The Pauli question sampler as a typed conditionally linear distribution -/

/-- `lem:pauli-question-typed-equality`: the Pauli question sampler equals the
distribution that `def:typed-cl-distributions` (`ch12_qpbt_games.tex`) produces
from the family `pauliCL` on the Pauli type graph. Both laws draw an ordered
pair of types whose unordered pair is an edge of the Pauli type graph, draw one
uniform seed in the Pauli seed space, and return the two types together with the
images of that common seed under the two selected maps. The common-level family
assertion is stated separately as `isTypedCondLinearFamily_pauliCL`. Blueprint
`ch13_qpbt_test.tex`, paper
`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:1115-1120`
and `references/qpbt-paper/07_types.tex:84-93`. -/
theorem pauliQuestionDistribution_eq_typedCL (P : AdmissibleParams) :
    pauliQuestionDistribution P =
      typedCLDistribution pauliEdges (by
        refine ⟨Sym2.mk (.point .X) (.point .X), ?_⟩
        simp [pauliEdges]) (pauliCL P) (pauliCL P) := by
  classical
  letI : Nonempty PauliEdge := pauliEdge_nonempty
  have himage : (Finset.univ : Finset PauliEdge).image
      (Subtype.val : PauliEdge → PauliType × PauliType) =
      (Finset.univ : Finset (PauliType × PauliType)).filter
        (fun ab => Sym2.mk ab.1 ab.2 ∈ pauliEdges) := by
    ext ab
    constructor
    · intro hab
      obtain ⟨e, -, rfl⟩ := Finset.mem_image.mp hab
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, e.2⟩
    · intro hab
      exact Finset.mem_image.mpr
        ⟨⟨ab, (Finset.mem_filter.mp hab).2⟩, Finset.mem_univ _, rfl⟩
  have hmine : Distribution.bind
      (Distribution.uniformOnFinset ((Finset.univ : Finset (PauliType × PauliType)).filter
        (fun ab => Sym2.mk ab.1 ab.2 ∈ pauliEdges)))
      (fun uv => (uniformDistribution (PauliSpace P)).map fun z =>
        ((uv.1, pauliCL P uv.1 z), (uv.2, pauliCL P uv.2 z))) =
      pauliQuestionDistribution P := by
    rw [bind_uniformOnFinset_map _ (Subtype.val : PauliEdge → PauliType × PauliType)
      Subtype.val_injective himage
      (fun uv z => ((uv.1, pauliCL P uv.1 z), (uv.2, pauliCL P uv.2 z)))]
    unfold pauliQuestionDistribution
    exact map_uniformDistribution_congr _ _ _ _ _ _ _ _ _
  rw [← hmine]
  simp only [typedCLDistribution, graphDistribution, clDistribution,
    Distribution.map_map]
  exact bind_map_uniformDistribution_congr _ _ _ _ _ _ _ _ _ _

/-- `lem:pauli-question-typed-cl`: the Pauli maps form a common-level typed
conditionally linear family, and their typed distribution is exactly the
question distribution of the Pauli basis test. Blueprint
`ch13_qpbt_test.tex`, paper
`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:964-966,1084-1120`.
-/
theorem pauliQuestionDistribution_isTypedCL (P : AdmissibleParams) :
    IsTypedCondLinearFamily (PauliScalar P) PauliType 3 (pauliCL P) ∧
      pauliQuestionDistribution P =
        typedCLDistribution pauliEdges (by
          refine ⟨Sym2.mk (.point .X) (.point .X), ?_⟩
          simp [pauliEdges]) (pauliCL P) (pauliCL P) := by
  exact ⟨isTypedCondLinearFamily_pauliCL P,
    pauliQuestionDistribution_eq_typedCL P⟩

/-! ### Symmetry of the Pauli basis test -/

/-- Symmetry of the Pauli question distribution in the symmetric game appearing
in `lem:pauli-completeness`. It follows from the identification of the sampler
with the typed conditionally linear distribution of a single family, whose edge
law is a law on unordered pairs and is therefore symmetric. -/
theorem pauliQuestionDistribution_symm (P : AdmissibleParams)
    (x y : PauliQuestion P) :
    (pauliQuestionDistribution P).weight (x, y) =
      (pauliQuestionDistribution P).weight (y, x) := by
  rw [pauliQuestionDistribution_eq_typedCL P]
  exact typedCLDistribution_symm _ _ _ (x, y)

/-- Symmetry of the Pauli decision predicate in the symmetric game appearing in
`lem:pauli-completeness`. -/
theorem pauliWinPredicate_symm (P : AdmissibleParams)
    (x y : PauliQuestion P) (a b : PauliAnswer P) :
    pauliWinPredicate P x y a b = pauliWinPredicate P y x b a := by
  obtain ⟨tA, xA⟩ := x
  obtain ⟨tB, xB⟩ := y
  by_cases hT : tA = tB
  · subst hT
    simp only [pauliWinPredicate]
    rw [Bool.and_comm (validPauliAnswer tA b) (validPauliAnswer tA a)]
    by_cases hab : a = b
    · simp [hab]
    · simp [hab, Ne.symm hab]
  · cases hvA : validPauliAnswer tA a
    · simp [pauliWinPredicate, hvA]
    · cases hvB : validPauliAnswer tB b
      · simp [pauliWinPredicate, hvB]
      · simp only [pauliWinPredicate, hvA, hvB, Bool.and_self,
          if_neg hT, if_neg (Ne.symm hT)]
        rcases tA with (_|_)|(_|_)|(_|_)|(_|_)|(_|_)|_|(iA|jA) <;>
          rcases a with uA|fA|gA|bitsA|bitA|trA|hhA <;>
          (try exact Bool.noConfusion hvA) <;>
          rcases tB with (_|_)|(_|_)|(_|_)|(_|_)|(_|_)|_|(iB|jB) <;>
          rcases b with uB|fB|gB|bitsB|bitB|trB|hhB <;>
          (try exact Bool.noConfusion hvB) <;>
          rfl

/-- The symmetric presentation of the Pauli basis test. The field and basis
are those fixed by `P.model`; no additional model is quantified. -/
noncomputable def pauliBasisTestSymm (P : AdmissibleParams) : SymmetricGame where
  Question := PauliQuestion P
  Answer := PauliAnswer P
  μ := pauliQuestionDistribution P
  μ_prob := (pauliBasisTest P).μ_prob
  μ_symm := pauliQuestionDistribution_symm P
  decide := pauliWinPredicate P
  decide_symm := pauliWinPredicate_symm P

/-- The symmetric presentation has the Pauli basis test as its
underlying game. -/
theorem pauliBasisTestSymm_toGame (P : AdmissibleParams) :
    (pauliBasisTestSymm P).toGame = pauliBasisTest P := by
  rfl

/-- The honest strategy of `lem:pauli-completeness`: the total honest
measurement family of `MIPStarRE.QPBT.Test.Completeness.HonestStrategy.Assembly`
on the maximally entangled state of the Pauli register tensored with the Magic
Square qubit.  Blueprint `lem:pauli-completeness`, paper
`08_classical_and_quantum_low_degree_tests.tex:1290-1360`. -/
noncomputable def honestStrategy (P : AdmissibleParams) :
    SymmetricStrategy (pauliBasisTestSymm P) where
  ι := HonestIndex P
  ψ := eprState (HonestIndex P)
  ψ_norm := eprState_norm (HonestIndex P)
  ψ_swap := reindexState_prodComm_eprState (HonestIndex P)
  M := fun q => honestMeasurement P q.1 q.2

/-- Every measurement of the honest strategy is projective. -/
theorem honestStrategy_projective (P : AdmissibleParams) (x : PauliQuestion P) :
    MIPStarRE.QPBT.Measurement.IsProjective ((honestStrategy P).M x) :=
  honestMeasurement_projective P x.1 x.2

/-- The honest strategy is consistent on its maximally entangled state. -/
theorem honestStrategy_isConsistent (P : AdmissibleParams) :
    (honestStrategy P).IsConsistent :=
  fun x => honestMeasurement_isConsistentOn P x.1 x.2

/-- The honest strategy is a symmetric projective consistent commuting
strategy: every measurement is projective, the family is consistent on the
maximally entangled state, and the effects commute on every question pair of
positive weight. -/
theorem honestStrategy_isSPCC (P : AdmissibleParams) :
    (honestStrategy P).IsSPCC :=
  ⟨honestStrategy_projective P, honestStrategy_isConsistent P,
    honestMeasurement_commuting P⟩

/-- On every question pair of positive weight for the Pauli question sampler the
honest measurement family assigns the zero operator product to every rejected
answer pair.  This is the operator form of perfect acceptance in
`lem:pauli-completeness`, paper
`08_classical_and_quantum_low_degree_tests.tex:1383-1421`. -/
theorem honestMeasurement_rejected_mul (P : AdmissibleParams)
    (x y : PauliQuestion P) (hxy : 0 < (pauliQuestionDistribution P).weight (x, y))
    (a b : PauliAnswer P) (hrej : pauliWinPredicate P x y a b = false) :
    (honestMeasurement P x.1 x.2).effect a *
      (honestMeasurement P y.1 y.2).effect b = 0 := by
  classical
  obtain ⟨z, hedge, hx, hy⟩ := pauliQuestionDistribution_pos_incidence P x y hxy
  obtain ⟨t₁, x₁⟩ := x
  obtain ⟨t₂, x₂⟩ := y
  dsimp only at hx hy hedge ⊢
  subst hx
  subst hy
  rcases pauliEdges_cases hedge with heq | ⟨s₁, s₂, hs₁, hs₂, hms⟩ | hor | hor
  · rw [heq] at hrej ⊢
    rcases (Bool.eq_false_or_eq_true
      (validPauliAnswer (P := P) t₂ a)).symm with hva | hva
    · rw [honestMeasurement_effect_eq_zero_of_invalid P _ _ hva, zero_mul]
    have hab : a ≠ b := by
      rintro rfl
      rw [show pauliWinPredicate P (t₂, pauliCL P t₂ z) (t₂, pauliCL P t₂ z) a a
          = true from by simp [pauliWinPredicate, hva]] at hrej
      exact Bool.noConfusion hrej
    exact DistanceCalculus.projective_effect_mul_effect_eq_zero _
      (honestMeasurement_projective P t₂ _) hab
  · subst hs₁
    subst hs₂
    exact honest_ms_rejected_mul P z hms a b hrej
  · exact honest_oriented_rejected_mul P hor z a b hrej
  · rw [← (honestMeasurement_commute_of_oriented P hor z b a).eq]
    refine honest_oriented_rejected_mul P hor z b a ?_
    rw [pauliWinPredicate_symm]
    exact hrej

/-- `lem:pauli-completeness`: every admissible Pauli basis test has a
value-one SPCC strategy. Blueprint `lem:pauli-completeness`, paper
`08_classical_and_quantum_low_degree_tests.tex:1229-1421`. -/
theorem exists_spcc_value_one (P : AdmissibleParams) :
    ∃ S : SymmetricStrategy (pauliBasisTestSymm P),
      S.IsSPCC ∧ S.toStrategy.value = 1 := by
  classical
  refine ⟨honestStrategy P, honestStrategy_isSPCC P, ?_⟩
  have hborn : ∀ x y : PauliQuestion P,
      0 < (pauliQuestionDistribution P).weight (x, y) →
      ∀ a b : PauliAnswer P, pauliWinPredicate P x y a b = false →
        outcomeWeight (honestStrategy P).toStrategy x y a b = 0 := by
    intro x y hxy a b hrej
    have hmul := honestMeasurement_rejected_mul P x y hxy a b hrej
    have hzero := heteroKron_mulVec_epr_eq_zero_of_mul_eq_zero
      ((honestMeasurement P x.1 x.2).effect a)
      ((honestMeasurement P y.1 y.2).effect b)
      (honestMeasurement_effect_transpose P y.1 y.2 b) hmul
    have hacted : applyOperatorToState
        (heteroKron ((honestMeasurement P x.1 x.2).effect a)
          ((honestMeasurement P y.1 y.2).effect b))
        (eprState (HonestIndex P)) = 0 := by
      rw [applyOperatorToState, Matrix.toLpLin_apply, hzero]
      rfl
    change (inner ℂ (eprState (HonestIndex P))
      (applyOperatorToState
        (heteroKron ((honestMeasurement P x.1 x.2).effect a)
          ((honestMeasurement P y.1 y.2).effect b))
        (eprState (HonestIndex P)))).re = 0
    rw [hacted]
    simp
  have hone : ∀ x y : PauliQuestion P,
      0 < (pauliQuestionDistribution P).weight (x, y) →
      (∑ a : PauliAnswer P, ∑ b : PauliAnswer P,
        if pauliWinPredicate P x y a b then
          outcomeWeight (honestStrategy P).toStrategy x y a b else 0) = 1 := by
    intro x y hxy
    have hcong : (∑ a : PauliAnswer P, ∑ b : PauliAnswer P,
        if pauliWinPredicate P x y a b then
          outcomeWeight (honestStrategy P).toStrategy x y a b else 0) =
        ∑ a : PauliAnswer P, ∑ b : PauliAnswer P,
          outcomeWeight (honestStrategy P).toStrategy x y a b := by
      refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
      by_cases hab : pauliWinPredicate P x y a b = true
      · simp [hab]
      · have hab' := Bool.eq_false_of_not_eq_true hab
        rw [hborn x y hxy a b hab']
        simp [hab']
    rw [hcong]
    exact outcomeWeight_sum_eq_one (honestStrategy P).toStrategy x y
  change avgOver (pauliQuestionDistribution P) (fun xy =>
    ∑ a : PauliAnswer P, ∑ b : PauliAnswer P,
      if pauliWinPredicate P xy.1 xy.2 a b then
        outcomeWeight (honestStrategy P).toStrategy xy.1 xy.2 a b else 0) = 1
  have hcongr : avgOver (pauliQuestionDistribution P) (fun xy =>
      ∑ a : PauliAnswer P, ∑ b : PauliAnswer P,
        if pauliWinPredicate P xy.1 xy.2 a b then
          outcomeWeight (honestStrategy P).toStrategy xy.1 xy.2 a b else 0) =
      avgOver (pauliQuestionDistribution P) (fun _ => 1) := by
    simp only [avgOver]
    refine Finset.sum_congr rfl fun xy _ => ?_
    rcases lt_or_eq_of_le ((pauliQuestionDistribution P).nonnegative xy) with hpos | hzero
    · rw [hone xy.1 xy.2 hpos]
    · rw [← hzero, zero_mul, zero_mul]
  rw [hcongr]
  exact avgOver_const_of_isProbability _ (pauliBasisTestSymm P).μ_prob 1

end

end MIPStarRE.QPBT
