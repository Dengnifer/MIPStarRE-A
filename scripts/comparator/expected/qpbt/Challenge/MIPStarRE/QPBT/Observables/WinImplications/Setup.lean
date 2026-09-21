import Mathlib
import Challenge.MIPStarRE.QPBT.Algebra.SelfDualBasisTheorems
import Challenge.MIPStarRE.QPBT.Games.StrategyClasses
import Challenge.MIPStarRE.QPBT.Test.PauliBasisTest

/-! Challenge mirror of `MIPStarRE/QPBT/Observables/WinImplications/Setup.lean`.

One challenge module per contributing library module, importing the
mirrors of the library modules this one imports.  The partition is
what makes Lean generate the same auxiliary declarations, under the
same names, as the library does. -/

open scoped BigOperators MatrixOrder Matrix ComplexOrder
namespace MIPStarRE.QPBT

-- elaboration context of MIPStarRE/QPBT/Observables/WinImplications/Setup.lean:26-114
noncomputable section
open scoped Matrix ComplexOrder
open MIPStarRE.LDT
open MIPStarRE.Quantum

-- source: MIPStarRE/QPBT/Observables/WinImplications/Setup.lean:52-57  (MIPStarRE.QPBT.pauliQuestionPairDecidableEq)
/-- Equality of Pauli question pairs is decidable. This is used in the
consistency defect from item 1 of blueprint
`lem:qld-win-implications`. -/
noncomputable instance pauliQuestionPairDecidableEq (P : AdmissibleParams) :
    DecidableEq (PauliQuestion P × PauliQuestion P) :=
  Classical.decEq _
end  -- module scope
end MIPStarRE.QPBT
