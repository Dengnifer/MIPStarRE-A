import Mathlib
import Challenge.MIPStarRE.QPBT.Algebra.Coefficients
import Challenge.MIPStarRE.QPBT.Algebra.FieldBasis
import Challenge.MIPStarRE.QPBT.Algebra.Lines
import Challenge.MIPStarRE.QPBT.Games.Defs

/-! Challenge mirror of `MIPStarRE/QPBT/Test/LowDegreeGame.lean`.

One challenge module per contributing library module, importing the
mirrors of the library modules this one imports.  The partition is
what makes Lean generate the same auxiliary declarations, under the
same names, as the library does. -/

open scoped BigOperators MatrixOrder Matrix ComplexOrder
namespace MIPStarRE.QPBT

-- elaboration context of MIPStarRE/QPBT/Test/LowDegreeGame.lean:31-768
noncomputable section
open MIPStarRE.LDT

-- source: MIPStarRE/QPBT/Test/LowDegreeGame.lean:33-49  (MIPStarRE.QPBT.LdParams)
/-- Numerical parameters for the low-degree game.  The ambient coefficient
space uses the once-and-for-all model `fixedFieldModel P.q P.hq`, rather than a
model supplied by each parameter record.  This is the Lean carrier for
blueprint
`def:ld-game`, with paper origin
`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:31-391`.
-/
structure LdParams where
  q : ℕ
  m : ℕ
  d : ℕ
  k : ℕ
  hm : 1 ≤ m
  hd : 1 ≤ d
  hk : 1 ≤ k
  hq : IsAdmissibleSize q
  hdvd : m ∣ q

-- source: MIPStarRE/QPBT/Test/LowDegreeGame.lean:56-62  (MIPStarRE.QPBT.LdParams.model)
/-- The fixed scalar model of a low-degree parameter tuple.  It is a
compatibility view of the global `fixedFieldModel` selector, not an
independently quantified field representation.  Blueprint `def:ld-game`; paper origin
`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:31-391`.
-/
noncomputable def LdParams.model (P : LdParams) : FixedFieldModel P.q :=
  fixedFieldModel P.q P.hq

-- source: MIPStarRE/QPBT/Test/LowDegreeGame.lean:64-69  (MIPStarRE.QPBT.ScalarQ)
/-- The scalar carrier selected by an `LdParams` record; this is the fixed
field carrier in `def:ld-game`, selected globally by `LdParams.model`.
Blueprint `def:ld-game`, paper origin
`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:31-391`.
-/
abbrev ScalarQ (P : LdParams) := (P.model).K

-- source: MIPStarRE/QPBT/Test/LowDegreeGame.lean:81-85  (MIPStarRE.QPBT.LdIndex)
/-- The register index used by the low-degree game (blueprint
`def:ld-game`; paper origin
`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:31-391`).
-/
abbrev LdIndex (P : LdParams) := (Fin P.m ⊕ Unit) ⊕ Fin P.m

-- source: MIPStarRE/QPBT/Test/LowDegreeGame.lean:87-91  (MIPStarRE.QPBT.LdSpace)
/-- The full ambient low-degree coefficient space (blueprint
`def:ld-game`; paper origin
`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:31-391`).
-/
abbrev LdSpace (P : LdParams) := LdIndex P → ScalarQ P

-- source: MIPStarRE/QPBT/Test/LowDegreeGame.lean:93-97  (MIPStarRE.QPBT.LdSpace.point)
/-- The point coordinates of an ambient low-degree vector in
`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:31-391`.
-/
def LdSpace.point {P : LdParams} (z : LdSpace P) : Fin P.m → ScalarQ P :=
  fun i => z (.inl (.inl i))

-- source: MIPStarRE/QPBT/Test/LowDegreeGame.lean:99-103  (MIPStarRE.QPBT.LdSpace.seed)
/-- The shared scalar coordinate of an ambient low-degree vector in
`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:31-391`.
-/
def LdSpace.seed {P : LdParams} (z : LdSpace P) : ScalarQ P :=
  z (.inl (.inr ()) )

-- source: MIPStarRE/QPBT/Test/LowDegreeGame.lean:105-109  (MIPStarRE.QPBT.LdSpace.direction)
/-- The direction coordinates of an ambient low-degree vector in
`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:31-391`.
-/
def LdSpace.direction {P : LdParams} (z : LdSpace P) : Fin P.m → ScalarQ P :=
  fun i => z (.inr i)

-- source: MIPStarRE/QPBT/Test/LowDegreeGame.lean:111-119  (MIPStarRE.QPBT.chiIndex)
/-- The zero-based coordinate index corresponding to the paper's map `χ`:
`chiIndex P s` represents `χ(s) - 1` in the fixed field representation.  This
is `eq:chi-func` in blueprint `def:ld-question-distribution`, paper origin
`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:31-391`.
-/
noncomputable def chiIndex (P : LdParams) (s : ScalarQ P) : Fin P.m := by
  letI : NeZero P.m := ⟨by
    exact Nat.ne_of_gt (lt_of_lt_of_le Nat.zero_lt_one P.hm)⟩
  exact Fin.ofNat P.m ((binaryRepresentation P.model s).val / (P.q / P.m))

-- source: MIPStarRE/QPBT/Test/LowDegreeGame.lean:198-206  (MIPStarRE.QPBT.prefixProjection)
/-- The projection used in the diagonal-line map zeroes coordinates before the
chosen index and retains the suffix of the direction vector.  This is the
prefix restriction in blueprint
`def:ld-question-distribution`, paper origin
`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:31-391`.
-/
def prefixProjection {P : LdParams} (i : Fin P.m) (v : Fin P.m → ScalarQ P) :
    Fin P.m → ScalarQ P :=
  fun j => if j.val < i.val then 0 else v j

-- source: MIPStarRE/QPBT/Test/LowDegreeGame.lean:220-229  (MIPStarRE.QPBT.ldPointCL)
/-- The point CL map, retaining the point block and clearing the auxiliary
blocks.  It is the map `L_point` of blueprint
`def:ld-question-distribution`, paper origin
`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:31-391`.
-/
def ldPointCL (P : LdParams) (z : LdSpace P) : LdSpace P :=
  fun i => match i with
  | .inl (.inl j) => z (.inl (.inl j))
  | .inl (.inr _) => 0
  | .inr _ => 0

-- source: MIPStarRE/QPBT/Test/LowDegreeGame.lean:231-242  (MIPStarRE.QPBT.ldALineCL)
/-- The affine-line CL map.  The direction block is put through the canonical
line representative map from `def:line-representative`, while the point block
is retained (blueprint `def:ld-question-distribution`; paper
origin `references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:31-391`).
-/
noncomputable def ldALineCL (P : LdParams) (z : LdSpace P) : LdSpace P :=
  let i := chiIndex P (z.seed)
  let rep := lineRepMap (coordinateDirection i)
  fun i => match i with
  | .inl (.inl j) => (rep (z.point)) j
  | .inl (.inr _) => z (.inl (.inr ()))
  | .inr _ => 0

-- source: MIPStarRE/QPBT/Test/LowDegreeGame.lean:244-258  (MIPStarRE.QPBT.ldDLineCL)
/-- The diagonal-line CL map applies the canonical line representative map to
the point block and stores the prefix-projected direction in the direction
block.  This is the `L_DLine` clause of
`def:ld-question-distribution` (blueprint
`def:ld-question-distribution`; paper origin
`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:31-391`).
-/
noncomputable def ldDLineCL (P : LdParams) (z : LdSpace P) : LdSpace P :=
  let i := chiIndex P (z.seed)
  let direction := prefixProjection i (z.direction)
  let rep := lineRepMap direction
  fun i => match i with
  | .inl (.inl j) => (rep (z.point)) j
  | .inl (.inr _) => z (.inl (.inr ()))
  | .inr j => direction j
end  -- module scope
end MIPStarRE.QPBT
