import MIPStarRE.QPBT.Test.MagicSquareTheorems.Rigidity.Anticommutation
import MIPStarRE.QPBT.Test.MagicSquareTheorems.Rigidity.Consistency

/-!
# The second logical Pauli pair of the Magic Square

The ideal Magic Square strategy assigns to the nine cells the two-qubit Pauli
observables

    X ⊗ I     I ⊗ X     X ⊗ X
    I ⊗ Z     Z ⊗ I     Z ⊗ Z
    X ⊗ Z     Z ⊗ X     Y ⊗ Y

read in the zero-based cell order `0, …, 8`.  The rigidity argument extracts
two EPR pairs, one for each tensor factor of this assignment, and therefore
needs two anticommuting pairs of reflections per player.  The chain of issues
#101--#104 supplies the *first* pair, at the cells `0` and `4` (the paper's
`Variable_1` and `Variable_5`), whose ideal images `X ⊗ I` and `Z ⊗ I` act on
the first qubit: `msVarObsA_anticommute` and `msVarObsB_anticommute` in
`Rigidity/Anticommutation.lean`.

This file supplies the *second* pair, at the cells `1` and `3` (the paper's
`Variable_2` and `Variable_4`), whose ideal images `I ⊗ X` and `I ⊗ Z` act on
the second qubit.  Two points distinguish it from the first pair.

* The corrected `thm:ms-rigidity` assumes cross-player consistency only at the
  cells `0` and `4` (`msVariableConsistencyDefect`, `Rigidity/Consistency.lean`),
  so the two players' *variable* reflections at the cells `1` and `3` cannot be
  compared.  The second pair is therefore carried by Alice's *constraint-read*
  reflections `msCellObsA S 0 1` (cell `1`, read from the first row) and
  `msCellObsA S 1 0` (cell `3`, read from the second row) against Bob's variable
  reflections `msVarObsB S 1` and `msVarObsB S 3`.  The game tests exactly this
  orientation, through `msCellObsA_close_msVarObsB`, so no further hypothesis is
  needed.
* Their approximate anticommutation is the solution-group computation of
  `Rigidity/Anticommutation.lean` carried out along a second closed path through
  the grid, namely
  `(1, 3) → (2, 6) → (5, 7) → (3, 1)`,
  which traverses the exceptional third column once and therefore returns the
  reversed product with the opposite sign.

The file also records the approximate commutation between the two pairs, which
the two-qubit swap-isometry extraction needs in order to treat the two extracted
qubits as independent registers.  On Alice's side that relation passes once
through the consistency hypothesis; on Bob's side it passes through Alice's
reflections at a shared constraint and needs no consistency.

## References

`thm:ms-rigidity`, blueprint `blueprint/src/chapter/ch13_qpbt_test.tex:224-253`,
paper `references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:612-652`;
the Magic Square grid is `08_classical_and_quantum_low_degree_tests.tex:512-610`.
The cited robust self-test is Coladangelo--Stark, arXiv:1709.09267v2,
Theorem 6.9, `references/cs-paper/self-testing.tex:660-730`.  The correction to
the strategy class is `docs/paper-gaps/qpbt_ms-rigidity-symmetric-strategies.tex`.
The variable and constraint indices are zero-based.
-/

open scoped BigOperators Matrix MatrixOrder ComplexOrder

namespace MIPStarRE.QPBT.MagicSquareRigidity

open MIPStarRE.LDT MIPStarRE.Quantum

noncomputable section

/-! ## Orders of the three positions of a constraint -/

/-- The three positions of a constraint, in the order `0, 1, 2`, report the
three bits whose sum `constraintBitSum` is constrained. -/
private theorem constraintBitOrZero_sum_012 (a : MsAnswer) :
    constraintBitOrZero 0 a + constraintBitOrZero 1 a + constraintBitOrZero 2 a =
      constraintBitSum a := rfl

/-- The three positions of a constraint, in the order `2, 0, 1`. -/
private theorem constraintBitOrZero_sum_201 (a : MsAnswer) :
    constraintBitOrZero 2 a + constraintBitOrZero 0 a + constraintBitOrZero 1 a =
      constraintBitSum a := by
  simp only [constraintBitSum]
  ring

/-- The three positions of a constraint, in the order `1, 2, 0`. -/
private theorem constraintBitOrZero_sum_120 (a : MsAnswer) :
    constraintBitOrZero 1 a + constraintBitOrZero 2 a + constraintBitOrZero 0 a =
      constraintBitSum a := by
  simp only [constraintBitSum]
  ring

/-- The sign prescribed by a constraint other than the third column is `+1`. -/
private theorem bitSign_msParity_eq_one (i : Fin 6) (hi : i ≠ 5) :
    ((bitSign (msParity i) : ℝ) : ℂ) = 1 := by
  have hp : msParity i = 0 := by
    unfold msParity
    rw [if_neg]
    intro hv
    exact hi (Fin.ext hv)
  rw [hp]
  norm_num [bitSign]

/-- The sign prescribed by the third column is `-1`. -/
private theorem bitSign_msParity_five_eq_neg_one :
    ((bitSign (msParity 5) : ℝ) : ℂ) = -1 := by
  have hp : msParity 5 = 1 := by norm_num [msParity]
  rw [hp]
  norm_num [bitSign, ZMod.val_one]

/-! ## The second closed path of the solution-group computation -/

/-- The solution-group computation for the second logical pair, in the form in
which the closed path of constraints leaves it.  The path visits the four
constraint pairs sharing the cells `0`, `8`, `4`, in the order

    (row 0, column 0) → (column 2, row 2) → (row 1, column 1),

so that the pair of cells `(1, 3)` is carried to `(2, 6)`, then to `(5, 7)`, and
finally to `(3, 1)`.  The single traversal of the exceptional third column
reverses the sign.  Blueprint `ch13_qpbt_test.tex:224-253`; the first-pair
analogue is the body of `msVarObsA_anticommute`. -/
private theorem msCellObsA_second_pair_path (S : Strategy msGame) (ε : ℝ)
    (hwin : 1 - ε ≤ S.value) :
    NormCloseOn (msDilatedStrategy S).ψ (504 * Real.sqrt ε)
      (msCellObsA S 0 1 * msCellObsA S 3 1)
      (-(msCellObsA S 1 0 * msCellObsA S 4 0)) := by
  have step1 := msCellObsA_step S ε hwin 0 3 0 1 2 0 1 2
    constraintBitOrZero_sum_012 constraintBitOrZero_sum_012 (by decide)
  rw [bitSign_msParity_eq_one 0 (by decide), bitSign_msParity_eq_one 3 (by decide),
    one_mul, one_smul] at step1
  have link1 := msCellObsA_mul_close_of_same_cells S ε hwin 0 3 5 2 2 2 0 0
    (by decide) (by decide)
  have step2 := msCellObsA_step S ε hwin 5 2 2 0 1 2 0 1
    constraintBitOrZero_sum_201 constraintBitOrZero_sum_201 (by decide)
  rw [bitSign_msParity_five_eq_neg_one, bitSign_msParity_eq_one 2 (by decide),
    mul_one, neg_one_smul] at step2
  have link2 := msCellObsA_mul_close_of_same_cells S ε hwin 5 2 1 4 1 1 2 2
    (by decide) (by decide)
  have step3 := msCellObsA_step S ε hwin 1 4 1 2 0 1 2 0
    constraintBitOrZero_sum_120 constraintBitOrZero_sum_120 (by decide)
  rw [bitSign_msParity_eq_one 1 (by decide), bitSign_msParity_eq_one 4 (by decide),
    one_mul, one_smul] at step3
  exact ((((step1.trans link1).trans step2).trans link2.neg).trans step3.neg).mono
    (by linarith)

/-! ## Approximate anticommutation of the second pair -/

/-- The two reflections that Alice reads at the cells of the paper's second and
fourth variables, from the first and the second row, approximately anticommute
on the dilated state.  These are the operators whose ideal images are
`I ⊗ σ^X` and `I ⊗ σ^Z`, and they are the second player-local anticommuting
pair required by the two-qubit swap-isometry extraction of `thm:ms-rigidity`.

The closed path of `msCellObsA_second_pair_path` gives the scale
`504 * sqrt ε`, and the two endpoint substitutions add `24 * sqrt ε` each, so
the argument closes at `552 * sqrt ε`; the bound is stated at the scale
`624 * sqrt ε` of the first-pair estimate `msVarObsA_anticommute`, so that the
assembly may use one scale for both pairs.  Blueprint `ch13_qpbt_test.tex:224-253`, paper
`08_classical_and_quantum_low_degree_tests.tex:612-652`. -/
theorem msCellObsA_second_pair_anticommute (S : Strategy msGame) (ε : ℝ)
    (hwin : 1 - ε ≤ S.value) :
    NormCloseOn (msDilatedStrategy S).ψ (624 * Real.sqrt ε)
      (msCellObsA S 0 1 * msCellObsA S 1 0)
      (-(msCellObsA S 1 0 * msCellObsA S 0 1)) := by
  have hsqrt : (0 : ℝ) ≤ Real.sqrt ε := Real.sqrt_nonneg ε
  have hleft : NormCloseOn (msDilatedStrategy S).ψ (12 * Real.sqrt ε + 12 * Real.sqrt ε)
      (msCellObsA S 0 1 * msCellObsA S 1 0) (msCellObsA S 0 1 * msCellObsA S 3 1) :=
    NormCloseOn.isometry_mul (isBinaryObservable_msCellObsA S 0 1).isometry
      (msCellObsA_close_of_same_cell S ε hwin 1 3 0 1 (by decide))
  have hright : NormCloseOn (msDilatedStrategy S).ψ (12 * Real.sqrt ε + 12 * Real.sqrt ε)
      (msCellObsA S 1 0 * msCellObsA S 4 0) (msCellObsA S 1 0 * msCellObsA S 0 1) :=
    NormCloseOn.isometry_mul (isBinaryObservable_msCellObsA S 1 0).isometry
      (msCellObsA_close_of_same_cell S ε hwin 4 0 0 1 (by decide))
  exact ((hleft.trans (msCellObsA_second_pair_path S ε hwin)).trans hright.neg).mono
    (by linarith)

/-- The two reflections that Bob reads at the cells of the paper's second and
fourth variables approximately anticommute on the dilated state.  These are
Bob's counterparts of `msCellObsA_second_pair_anticommute`, obtained from the
same closed path by replacing each of its two endpoints with the pair of Bob
variable reflections that the game compares to it.  The path gives the scale
`504 * sqrt ε` and each of the two endpoint replacements `24 * sqrt ε`, so the
argument closes at `552 * sqrt ε`; the bound is stated at the first-pair scale
`624 * sqrt ε`.
Blueprint `ch13_qpbt_test.tex:224-253`. -/
theorem msVarObsB_second_pair_anticommute (S : Strategy msGame) (ε : ℝ)
    (hwin : 1 - ε ≤ S.value) :
    NormCloseOn (msDilatedStrategy S).ψ (624 * Real.sqrt ε)
      (msVarObsB S 1 * msVarObsB S 3) (-(msVarObsB S 3 * msVarObsB S 1)) := by
  have hsqrt : (0 : ℝ) ≤ Real.sqrt ε := Real.sqrt_nonneg ε
  have hstart := (msCellObsA_mul_close S ε hwin 0 3 1 1).symm
  rw [show msConstraintVars 3 1 = 3 from by decide,
    show msConstraintVars 0 1 = 1 from by decide] at hstart
  have hend := msCellObsA_mul_close S ε hwin 1 4 0 0
  rw [show msConstraintVars 4 0 = 1 from by decide,
    show msConstraintVars 1 0 = 3 from by decide] at hend
  refine normCloseOn_neg_swap
    (((hstart.trans (msCellObsA_second_pair_path S ε hwin)).trans hend.neg).mono ?_)
  linarith

/-! ## Cross-player agreement for the second pair -/

/-- Alice's reflection at the cell of the paper's second variable, read from the
first row, agrees on the dilated state with Bob's variable reflection at that
cell.  This is the cross-player agreement that replaces, for the second pair,
the consistency hypothesis used at the cells `0` and `4`; the game tests it
directly. -/
theorem msCellObsA_close_msVarObsB_second_x (S : Strategy msGame) (ε : ℝ)
    (hwin : 1 - ε ≤ S.value) :
    NormCloseOn (msDilatedStrategy S).ψ (12 * Real.sqrt ε)
      (msCellObsA S 0 1) (msVarObsB S 1) := by
  have h := msCellObsA_close_msVarObsB S ε hwin 0 1
  rwa [show msConstraintVars 0 1 = 1 from by decide] at h

/-- Alice's reflection at the cell of the paper's fourth variable, read from the
second row, agrees on the dilated state with Bob's variable reflection at that
cell. -/
theorem msCellObsA_close_msVarObsB_second_z (S : Strategy msGame) (ε : ℝ)
    (hwin : 1 - ε ≤ S.value) :
    NormCloseOn (msDilatedStrategy S).ψ (12 * Real.sqrt ε)
      (msCellObsA S 1 0) (msVarObsB S 3) := by
  have h := msCellObsA_close_msVarObsB S ε hwin 1 0
  rwa [show msConstraintVars 1 0 = 3 from by decide] at h

/-! ## Commutation between the two logical pairs -/

/-- Formalization-only substitution scheme for an approximate commutation.  Two
reflections `X` and `Y` commute approximately on `ψ` once each is close to a
reflection `Xc`, respectively `Yc`, of an exactly commuting pair, provided each
of `X` and `Y` is also close to a reflection `Xb`, respectively `Yb`, of the
other player, which commutes with everything the substitution moves past.  The
two applications of `NormCloseOn.mul_left_subst` are the two places where the
substituted operator sits on the left of a product.  Formalization-only support
for `thm:ms-rigidity`, blueprint `ch13_qpbt_test.tex:224-253`. -/
private theorem normCloseOn_comm_subst {ι : Type} [Fintype ι] [DecidableEq ι]
    {ψ : EuclideanSpace ℂ ι} {a b c d : ℝ} {X Xc Xb Y Yc Yb : Op ι}
    (hX : IsBinaryObservable X) (hXc : IsBinaryObservable Xc)
    (hXb : IsBinaryObservable Xb) (hY : IsBinaryObservable Y)
    (hYc : IsBinaryObservable Yc) (hYb : IsBinaryObservable Yb)
    (hXXc : NormCloseOn ψ a X Xc) (hYYc : NormCloseOn ψ b Y Yc)
    (hXXb : NormCloseOn ψ c X Xb) (hYYb : NormCloseOn ψ d Y Yb)
    (hcomm : Xc * Yc = Yc * Xc)
    (hXYb : X * Yb = Yb * X) (hXcYb : Xc * Yb = Yb * Xc)
    (hYXb : Y * Xb = Xb * Y) (hYcXb : Yc * Xb = Xb * Yc) :
    NormCloseOn ψ (2 * a + 2 * b + 2 * c + 2 * d) (X * Y) (Y * X) := by
  have h1 : NormCloseOn ψ (d + a + d) (X * Y) (Xc * Y) :=
    NormCloseOn.mul_left_subst hXXc hYYb hX.isometry hXc.isometry hYb.isometry hXYb hXcYb
  have h2 : NormCloseOn ψ b (Xc * Y) (Xc * Yc) :=
    NormCloseOn.isometry_mul hXc.isometry hYYc
  have h3 : NormCloseOn ψ a (Yc * Xc) (Yc * X) :=
    NormCloseOn.isometry_mul hYc.isometry hXXc.symm
  have h4 : NormCloseOn ψ (c + b + c) (Yc * X) (Y * X) :=
    NormCloseOn.mul_left_subst hYYc.symm hXXb hYc.isometry hY.isometry hXb.isometry
      hYcXb hYXb
  have h5 : NormCloseOn ψ a (Xc * Yc) (Yc * X) := by
    rw [hcomm]
    exact h3
  exact (((h1.trans h2).trans h5).trans h4).mono (by linarith)

/-- Bob's variable reflections at two cells of one constraint approximately
commute on the dilated state.  Bob's two logical pairs are compared through
Alice's reflections at that constraint, which commute exactly, so this estimate
uses only the value of the strategy.  Applied to the four pairs of cells
`(0, 1)`, `(0, 3)`, `(4, 1)` and `(4, 3)`, taken respectively in the first row,
the first column, the second column and the second row, it is the inter-pair
commutation that the two-qubit swap-isometry extraction needs on Bob's side.
Blueprint `ch13_qpbt_test.tex:224-253`. -/
theorem msVarObsB_comm_of_shared_constraint (S : Strategy msGame) (ε : ℝ)
    (hwin : 1 - ε ≤ S.value) (i : Fin 6) (k l : Fin 3) :
    NormCloseOn (msDilatedStrategy S).ψ (96 * Real.sqrt ε)
      (msVarObsB S (msConstraintVars i k) * msVarObsB S (msConstraintVars i l))
      (msVarObsB S (msConstraintVars i l) * msVarObsB S (msConstraintVars i k)) := by
  have hXXc : NormCloseOn (msDilatedStrategy S).ψ (12 * Real.sqrt ε)
      (msVarObsB S (msConstraintVars i k)) (msCellObsA S i k) :=
    (msCellObsA_close_msVarObsB S ε hwin i k).symm
  have hYYc : NormCloseOn (msDilatedStrategy S).ψ (12 * Real.sqrt ε)
      (msVarObsB S (msConstraintVars i l)) (msCellObsA S i l) :=
    (msCellObsA_close_msVarObsB S ε hwin i l).symm
  refine (normCloseOn_comm_subst (isBinaryObservable_msVarObsB S (msConstraintVars i k))
    (isBinaryObservable_msCellObsA S i k) (isBinaryObservable_msCellObsA S i k)
    (isBinaryObservable_msVarObsB S (msConstraintVars i l))
    (isBinaryObservable_msCellObsA S i l) (isBinaryObservable_msCellObsA S i l)
    hXXc hYYc hXXc hYYc (msCellObsA_comm S i k l)
    (msCellObsA_comm_msVarObsB S i l (msConstraintVars i k)).symm
    (msCellObsA_comm S i k l)
    (msCellObsA_comm_msVarObsB S i k (msConstraintVars i l)).symm
    (msCellObsA_comm S i l k)).mono ?_
  linarith

/-- Alice's variable reflection at a cell of the first logical pair
approximately commutes on the dilated state with her constraint-read reflection
at a cell of the second logical pair, provided some constraint contains both
cells.  The hypothesis `hik` names the position of the variable cell `j` in that
constraint, and `hcell` says that the constraint-read reflection is attached to
the same cell as the position `l` of that constraint.

This is the inter-pair commutation on Alice's side.  Unlike Bob's, it passes
once through the consistency hypothesis of the corrected `thm:ms-rigidity`,
because the game does not compare Alice's variable reflection with her own
constraint-read reflection at the same cell.  Applied with `j = 0, 4` and the
second-pair reflections `msCellObsA S 0 1` and `msCellObsA S 1 0`, it gives the
four estimates the two-qubit extraction needs.  Blueprint
`ch13_qpbt_test.tex:224-253`; the consistency defect is
`msVariableConsistencyDefect`, `Rigidity/Consistency.lean`. -/
theorem msVarObsA_comm_msCellObsA_of_shared_constraint (S : Strategy msGame)
    (ε δ : ℝ) (hwin : 1 - ε ≤ S.value) (j : Fin 9)
    (hδ : msVariableConsistencyDefect S j ≤ δ) (i : Fin 6) (k l : Fin 3)
    (hik : msConstraintVars i k = j) (i' : Fin 6) (l' : Fin 3)
    (hcell : msConstraintVars i l = msConstraintVars i' l') :
    NormCloseOn (msDilatedStrategy S).ψ
      (4 * Real.sqrt (864 * ε + 6 * δ) + 96 * Real.sqrt ε)
      (msVarObsA S j * msCellObsA S i' l')
      (msCellObsA S i' l' * msVarObsA S j) := by
  have hsqrt : (0 : ℝ) ≤ Real.sqrt ε := Real.sqrt_nonneg ε
  have hXXb : NormCloseOn (msDilatedStrategy S).ψ (Real.sqrt (864 * ε + 6 * δ))
      (msVarObsA S j) (msVarObsB S j) := msVarObsA_close_msVarObsB S ε δ hwin j hδ
  have hik' : NormCloseOn (msDilatedStrategy S).ψ (12 * Real.sqrt ε)
      (msCellObsA S i k) (msVarObsB S j) := by
    have h := msCellObsA_close_msVarObsB S ε hwin i k
    rwa [hik] at h
  have hXXc : NormCloseOn (msDilatedStrategy S).ψ
      (Real.sqrt (864 * ε + 6 * δ) + 12 * Real.sqrt ε)
      (msVarObsA S j) (msCellObsA S i k) := hXXb.trans hik'.symm
  have hYYc : NormCloseOn (msDilatedStrategy S).ψ (12 * Real.sqrt ε + 12 * Real.sqrt ε)
      (msCellObsA S i' l') (msCellObsA S i l) :=
    msCellObsA_close_of_same_cell S ε hwin i' i l' l hcell.symm
  have hYYb : NormCloseOn (msDilatedStrategy S).ψ (12 * Real.sqrt ε)
      (msCellObsA S i' l') (msVarObsB S (msConstraintVars i' l')) :=
    msCellObsA_close_msVarObsB S ε hwin i' l'
  refine (normCloseOn_comm_subst (isBinaryObservable_msVarObsA S j)
    (isBinaryObservable_msCellObsA S i k) (isBinaryObservable_msVarObsB S j)
    (isBinaryObservable_msCellObsA S i' l') (isBinaryObservable_msCellObsA S i l)
    (isBinaryObservable_msVarObsB S (msConstraintVars i' l'))
    hXXc hYYc hXXb hYYb (msCellObsA_comm S i k l)
    (msVarObsA_comm_msVarObsB S j (msConstraintVars i' l'))
    (msCellObsA_comm_msVarObsB S i k (msConstraintVars i' l'))
    (msCellObsA_comm_msVarObsB S i' l' j)
    (msCellObsA_comm_msVarObsB S i l j)).mono ?_
  linarith

end

end MIPStarRE.QPBT.MagicSquareRigidity
