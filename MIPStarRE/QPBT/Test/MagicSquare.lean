import MIPStarRE.QPBT.Games.CondLinear
import MIPStarRE.QPBT.Games.Defs

/-!
# The Magic Square game

The Magic Square component is represented by finite constraint and variable
question types, the incidence graph, and the two corresponding answer forms.
Its rigidity theorem is outside the stage-4.1 statement closure; only the game
carrier is needed here.

## References

This file formalizes `def:ms-game` in
`blueprint/src/chapter/ch13_qpbt_test.tex:188-203`, from
`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:512-610`.
-/

namespace MIPStarRE.QPBT

open MIPStarRE.LDT

/-- A Magic Square question is either a row/column constraint or a cell
variable.  This is `def:ms-game`, blueprint lines 188-203, paper origin
`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:512-610`.
-/
inductive MsType where
  | constraint (i : Fin 6)
  | var (j : Fin 9)
  deriving DecidableEq, Repr, Inhabited, Fintype

/-- The cell incident to a constraint and one of its three positions in
`def:ms-game`, blueprint `ch13_qpbt_test.tex:188-203`, paper origin
`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:512-610`.
-/
def msConstraintVars (i : Fin 6) (j : Fin 3) : Fin 9 :=
  ⟨if i.val < 3 then i.val * 3 + j.val else i.val - 3 + j.val * 3, by
    by_cases h : i.val < 3 <;> simp [h] <;> omega⟩

/-- The exceptional Magic Square parity, equal to one only on the final
constraint.  Blueprint `blueprint/src/chapter/ch13_qpbt_test.tex:188-203`; paper
origin `references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:512-610`.
-/
def msParity (i : Fin 6) : ZMod 2 :=
  if i.val = 5 then 1 else 0

/-- The 18 constraint-variable incidence edges of the Magic Square graph in
`def:ms-game`, blueprint `ch13_qpbt_test.tex:188-203`, paper origin
`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:512-610`.
-/
def msEdges : Finset (Sym2 MsType) :=
  (Finset.univ : Finset (Fin 6 × Fin 3)).image (fun ij =>
    Sym2.mk (.constraint ij.1) (.var (msConstraintVars ij.1 ij.2)))

/-- The Magic Square incidence graph has an edge, as required by the
nonempty-support API of `graphDistribution`.  This is the finite carrier fact
used to instantiate `def:ms-game`, blueprint `ch13_qpbt_test.tex:188-203`,
paper origin `references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:512-610`.
-/
theorem msEdges_nonempty : msEdges.Nonempty := by
  refine ⟨Sym2.mk (.constraint 0) (.var (msConstraintVars 0 0)), ?_⟩
  exact Finset.mem_image.mpr ⟨(0, 0), Finset.mem_univ _, rfl⟩

/-- A Magic Square answer is a parity triple or a single cell bit, as prescribed
by `def:ms-game`, blueprint `blueprint/src/chapter/ch13_qpbt_test.tex:188-203`,
paper origin `references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:512-610`.
-/
inductive MsAnswer where
  | triple (β : Fin 3 → ZMod 2)
  | bit (γ : ZMod 2)
  deriving DecidableEq

/-- A formalization-only total relabeling from the global Magic Square answer
alphabet to a bit. It folds wrong-form answers into zero so that a variable
question yields a complete binary measurement. -/
def msBitOrZero : MsAnswer → ZMod 2
  | .bit b => b
  | .triple _ => 0

/-- A finite code for the two Magic Square answer constructors.  This is
Lean-only carrier infrastructure for `def:ms-game`, blueprint
`ch13_qpbt_test.tex:188-203`, paper origin
`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:512-610`.
-/
abbrev MsAnswerCode := (Fin 3 → ZMod 2) ⊕ ZMod 2

/-- The constructor-preserving code equivalence for `MsAnswer`; Lean-only
finite-carrier infrastructure for `def:ms-game`, blueprint
`ch13_qpbt_test.tex:188-203`, paper origin
`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:512-610`.
-/
noncomputable def msAnswerEquiv : MsAnswer ≃ MsAnswerCode where
  toFun
    | .triple β => .inl β
    | .bit γ => .inr γ
  invFun
    | .inl β => .triple β
    | .inr γ => .bit γ
  left_inv := by intro x; cases x <;> rfl
  right_inv := by
    intro x
    cases x <;> rfl

noncomputable instance : Fintype MsAnswer :=
  Fintype.ofEquiv MsAnswerCode msAnswerEquiv.symm

instance : Inhabited MsAnswer := ⟨.bit 0⟩

/-- The Magic Square consistency predicate.  Constructor mismatches are
rejected, as required by `def:ms-game` (blueprint lines 188-203; paper
`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:512-610`).
-/
def msWinPredicate :
    MsType → MsType → MsAnswer → MsAnswer → Bool
  | .constraint i, .constraint j, .triple β, .triple β' =>
      decide (i = j ∧ β = β')
  | .var i, .var j, .bit γ, .bit γ' =>
      decide (i = j ∧ γ = γ')
  | .constraint i, .var j, .triple β, .bit γ =>
      decide
        ((∑ k : Fin 3, β k) = msParity i ∧
          ∃ k : Fin 3, msConstraintVars i k = j ∧ β k = γ)
  | .var j, .constraint i, .bit γ, .triple β =>
      decide
        ((∑ k : Fin 3, β k) = msParity i ∧
          ∃ k : Fin 3, msConstraintVars i k = j ∧ β k = γ)
  | _, _, _, _ => false

/-- The Magic Square game as a finite `Game`.  This is `def:ms-game` in
`blueprint/src/chapter/ch13_qpbt_test.tex:188-203`, paper origin
`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:512-610`.
-/
noncomputable def msGame : Game where
  QuestionA := MsType
  QuestionB := MsType
  AnswerA := MsAnswer
  AnswerB := MsAnswer
  μ := graphDistribution msEdges msEdges_nonempty
  μ_prob := by sorry
  decide := msWinPredicate

end MIPStarRE.QPBT
