import Mathlib
import Challenge.MIPStarRE.LDT.Basic.Distribution

/-! Challenge mirror of `MIPStarRE/QPBT/Games/CondLinear.lean`.

One challenge module per contributing library module, importing the
mirrors of the library modules this one imports.  The partition is
what makes Lean generate the same auxiliary declarations, under the
same names, as the library does. -/

open scoped BigOperators MatrixOrder Matrix ComplexOrder
namespace MIPStarRE.QPBT

-- elaboration context of MIPStarRE/QPBT/Games/CondLinear.lean
section
open MIPStarRE.LDT
variable {K ι : Type*} [Field K] [Fintype ι] [DecidableEq ι]

-- source: MIPStarRE/QPBT/Games/CondLinear.lean:297-306  (MIPStarRE.QPBT.clDistribution)
/--
The distribution obtained by applying two conditionally linear maps to a common
uniform seed.  This is blueprint
`def:cl-dist`, paper origin
`references/qpbt-paper/05_conditionally_linear_functions.tex:132-138`.
-/
noncomputable def clDistribution [Fintype K] [DecidableEq K]
    (L R : (ι → K) → (ι → K)) :
    Distribution ((ι → K) × (ι → K)) :=
  (uniformDistribution (ι → K)).map (fun z => (L z, R z))

-- source: MIPStarRE/QPBT/Games/CondLinear.lean:372-383  (MIPStarRE.QPBT.graphDistribution)
/--
The graph distribution is uniform on ordered pairs `(a, b)` whose unordered
pair belongs to `E`, including self-loops.  This is blueprint
`def:graph-distribution`;
paper origin `references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:984-1009`.
The underlying graph-distribution definition is
`references/qpbt-paper/07_types.tex:65-82`.
-/
noncomputable def graphDistribution {T : Type*} [Fintype T] [DecidableEq T]
    (E : Finset (Sym2 T)) (_hE : E.Nonempty) : Distribution (T × T) :=
  Distribution.uniformOnFinset
    (Finset.univ.filter fun ab : T × T => Sym2.mk ab.1 ab.2 ∈ E)

-- source: MIPStarRE/QPBT/Games/CondLinear.lean:398-408  (MIPStarRE.QPBT.graphDistribution_symm)
/-- The graph distribution is symmetric in its two arguments: it is uniform on
the ordered pairs whose unordered pair is an edge, and that condition does not
depend on the order of the pair.  This is not a named statement of the source
article; it is `lem:graph-distribution-symm` in
`blueprint/src/chapter/ch12_qpbt_games.tex`. -/
theorem graphDistribution_symm {T : Type*} [Fintype T] [DecidableEq T]
    (E : Finset (Sym2 T)) (hE : E.Nonempty) (a b : T) :
    (graphDistribution E hE).weight (a, b) =
      (graphDistribution E hE).weight (b, a) := by
  classical
  simp [graphDistribution, Distribution.uniformOnFinset_weight, Sym2.eq_swap]
end  -- module scope
end MIPStarRE.QPBT
