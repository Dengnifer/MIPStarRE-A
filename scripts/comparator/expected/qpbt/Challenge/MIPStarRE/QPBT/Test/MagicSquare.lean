import Mathlib
import Challenge.MIPStarRE.QPBT.Games.CondLinear
import Challenge.MIPStarRE.QPBT.Games.Defs

/-! Challenge mirror of `MIPStarRE/QPBT/Test/MagicSquare.lean`.

One challenge module per contributing library module, importing the
mirrors of the library modules this one imports.  The partition is
what makes Lean generate the same auxiliary declarations, under the
same names, as the library does. -/

open scoped BigOperators MatrixOrder Matrix ComplexOrder
namespace MIPStarRE.QPBT

-- elaboration context of MIPStarRE/QPBT/Test/MagicSquare.lean
section
open MIPStarRE.LDT

-- source: MIPStarRE/QPBT/Test/MagicSquare.lean:23-30  (MIPStarRE.QPBT.MsType)
/-- A Magic Square question is either a row/column constraint or a cell
variable.  This is blueprint `def:ms-game`, paper origin
`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:512-610`.
-/
inductive MsType where
  | constraint (i : Fin 6)
  | var (j : Fin 9)
  deriving DecidableEq, Repr, Inhabited, Fintype

-- source: MIPStarRE/QPBT/Test/MagicSquare.lean:32-38  (MIPStarRE.QPBT.msConstraintVars)
/-- The cell incident to a constraint and one of its three positions in
blueprint `def:ms-game`, paper origin
`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:512-610`.
-/
def msConstraintVars (i : Fin 6) (j : Fin 3) : Fin 9 :=
  ⟨if i.val < 3 then i.val * 3 + j.val else i.val - 3 + j.val * 3, by
    by_cases h : i.val < 3 <;> simp [h] <;> omega⟩

-- source: MIPStarRE/QPBT/Test/MagicSquare.lean:40-45  (MIPStarRE.QPBT.msParity)
/-- The exceptional Magic Square parity, equal to one only on the final
constraint.  Blueprint `def:ms-game`; paper
origin `references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:512-610`.
-/
def msParity (i : Fin 6) : ZMod 2 :=
  if i.val = 5 then 1 else 0

-- source: MIPStarRE/QPBT/Test/MagicSquare.lean:47-53  (MIPStarRE.QPBT.msEdges)
/-- The 18 constraint-variable incidence edges of the Magic Square graph in
blueprint `def:ms-game`, paper origin
`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:512-610`.
-/
def msEdges : Finset (Sym2 MsType) :=
  (Finset.univ : Finset (Fin 6 × Fin 3)).image (fun ij =>
    Sym2.mk (.constraint ij.1) (.var (msConstraintVars ij.1 ij.2)))

-- source: MIPStarRE/QPBT/Test/MagicSquare.lean:64-71  (MIPStarRE.QPBT.MsAnswer)
/-- A Magic Square answer is a parity triple or a single cell bit, as prescribed
by blueprint `def:ms-game`,
paper origin `references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:512-610`.
-/
inductive MsAnswer where
  | triple (β : Fin 3 → ZMod 2)
  | bit (γ : ZMod 2)
  deriving DecidableEq

-- source: MIPStarRE/QPBT/Test/MagicSquare.lean:109-127  (MIPStarRE.QPBT.msWinPredicate)
/-- The Magic Square consistency predicate.  Constructor mismatches are
rejected, as required by blueprint `def:ms-game`; paper
`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:512-610`.
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
end  -- module scope
end MIPStarRE.QPBT
