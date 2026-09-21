import Mathlib

/-! Challenge mirror of `MIPStarRE/QPBT/Algebra/Coefficients.lean`.

One challenge module per contributing library module, importing the
mirrors of the library modules this one imports.  The partition is
what makes Lean generate the same auxiliary declarations, under the
same names, as the library does. -/

open scoped BigOperators MatrixOrder Matrix ComplexOrder
namespace MIPStarRE.QPBT

-- source: MIPStarRE/QPBT/Algebra/Coefficients.lean:26-33  (MIPStarRE.QPBT.evalCoefficient)
/-- Evaluation of a coefficient tuple at a field element. This is the
representative convention used by the line answers in blueprint
`def:ld-win-predicate`, paper origin
`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:31-391`.
-/
def evalCoefficient {K : Type*} [Semiring K] {n : ℕ}
    (c : Fin n → K) (t : K) : K :=
  ∑ i : Fin n, c i * t ^ i.val
end MIPStarRE.QPBT
