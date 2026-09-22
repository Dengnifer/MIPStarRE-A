import Mathlib
import Challenge.MIPStarRE.QPBT.Algebra.Pauli
import Challenge.MIPStarRE.QPBT.Algebra.SelfDualBasisTheorems
import Challenge.MIPStarRE.QPBT.Algebra.Subspaces
import Challenge.MIPStarRE.QPBT.State

/-! Challenge mirror of `MIPStarRE/QPBT/Algebra/PauliTheorems.lean`.

One challenge module per contributing library module, importing the
mirrors of the library modules this one imports.  The partition is
what makes Lean generate the same auxiliary declarations, under the
same names, as the library does. -/

open scoped BigOperators MatrixOrder Matrix ComplexOrder
namespace MIPStarRE.QPBT

-- elaboration context of MIPStarRE/QPBT/Algebra/PauliTheorems.lean
section
open MIPStarRE.LDT MIPStarRE.Quantum

-- source: MIPStarRE/QPBT/Algebra/PauliTheorems.lean:697-703  (MIPStarRE.QPBT.qubitPauliProj)
/-- The tensor product of binary Pauli projectors, obtained by specializing
`pauliProj` to `ZMod 2`. This is the binary target in blueprint
`lem:pauli-binary`, paper
`references/qpbt-paper/04_preliminaries.tex:1163-1208`. -/
noncomputable abbrev qubitPauliProj {ι : Type*} [Fintype ι] [DecidableEq ι]
    (W : PauliKind) (b : ι → ZMod 2) : Op (ι → ZMod 2) :=
  pauliProj W b
end  -- module scope
end MIPStarRE.QPBT
