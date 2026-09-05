import MIPStarRE.QPBT.Games.StrategyClasses
import MIPStarRE.QPBT.Games.TypedCondLinear
import MIPStarRE.QPBT.Test.LowDegreeGameTheorems
import MIPStarRE.QPBT.Test.MagicSquareTheorems
import MIPStarRE.QPBT.Test.PauliBasisTest

/-!
# Completeness of the Pauli basis test

The Pauli basis test admits a symmetric presentation and a value-one SPCC
strategy.

## References

The source statement is `lem:pauli-completeness` in
`blueprint/src/chapter/ch13_qpbt_test.tex`, from
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

/-- `lem:pauli-completeness`: every admissible Pauli basis test has a
value-one SPCC strategy. Blueprint `ch13_qpbt_test.tex`, paper
`08_classical_and_quantum_low_degree_tests.tex:1229-1421`. -/
theorem exists_spcc_value_one (P : AdmissibleParams) :
    ∃ S : SymmetricStrategy (pauliBasisTestSymm P),
      S.IsSPCC ∧ S.toStrategy.value = 1 := by
  sorry

end

end MIPStarRE.QPBT
