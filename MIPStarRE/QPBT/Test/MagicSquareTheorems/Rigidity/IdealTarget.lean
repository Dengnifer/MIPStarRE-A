import MIPStarRE.QPBT.Algebra.Pauli
import MIPStarRE.QPBT.Test.MagicSquareTheorems.Rigidity.GroundSlice

/-!
# The ideal target of the Magic Square rigidity theorem

The conclusion of `thm:ms-rigidity` compares the two players' bit measurements
with the Pauli basis projectors on a two-qubit register and their shared state
with two EPR pairs tensored with an auxiliary bipartite state.  This file
records the two elementary properties of that target which the estimates of the
rigidity assembly use: the Pauli basis projectors of one kind form a complete
projective measurement, so that any marginal of them is a positive contraction,
and the ideal state is a unit vector whenever the auxiliary state is.

The completeness of the Pauli basis follows from the Fourier expansion
`tauObservable_eq_sum_pauliProj` evaluated at the zero label, where the
generalized Pauli observable is the identity.  Positivity is the rank-one
factorization `pauliProj W e = v vᴴ` for the normalized Pauli eigenvector `v`.

## References

`def:generalized-pauli` and `lem:pauli-observable-expansion`, blueprint
`blueprint/src/chapter/ch11_qpbt_algebra.tex:494-688`, paper
`references/qpbt-paper/04_preliminaries.tex:908-1161`; the target of the
rigidity theorem is `thm:ms-rigidity`, blueprint
`blueprint/src/chapter/ch13_qpbt_test.tex:224-253`, paper
`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:612-652`.
-/

open scoped BigOperators Matrix MatrixOrder ComplexOrder

namespace MIPStarRE.QPBT

open MIPStarRE.Quantum

noncomputable section

variable {K : Type*} [Field K] [Fintype K] [DecidableEq K] [Algebra (ZMod 2) K]

/-! ## The Pauli basis is a complete projective measurement -/

/-! ## Marginals of the Pauli basis -/

/-- A marginal of the Pauli basis projectors, over any set of labels, is
positive semidefinite. -/
theorem posSemidef_sum_ite_pauliProj {ι : Type*} [Fintype ι] [DecidableEq ι]
    (W : PauliKind) (p : (ι → K) → Prop) [DecidablePred p] :
    (∑ e : ι → K, if p e then pauliProj W e else 0).PosSemidef := by
  classical
  refine Finset.sum_induction _ Matrix.PosSemidef (fun _ _ h₁ h₂ => h₁.add h₂)
    (Matrix.PosSemidef.zero) ?_
  intro e _
  by_cases hp : p e
  · rw [if_pos hp]
    exact posSemidef_pauliProj W e
  · rw [if_neg hp]
    exact Matrix.PosSemidef.zero

/-- A marginal of the Pauli basis projectors is a positive operator in the
Loewner order. -/
theorem sum_ite_pauliProj_nonneg {ι : Type*} [Fintype ι] [DecidableEq ι]
    (W : PauliKind) (p : (ι → K) → Prop) [DecidablePred p] :
    0 ≤ ∑ e : ι → K, if p e then pauliProj W e else 0 := by
  refine Matrix.le_iff.mpr ?_
  simpa using posSemidef_sum_ite_pauliProj W p

/-- The two marginals of the Pauli basis attached to a binary function of the
labels sum to the identity. -/
theorem sum_binary_marginal_pauliProj {ι : Type*} [Fintype ι] [DecidableEq ι]
    (W : PauliKind) (f : (ι → K) → ZMod 2) :
    (∑ b : ZMod 2, ∑ e : ι → K, if f e = b then pauliProj W e else 0) = 1 := by
  classical
  rw [Finset.sum_comm]
  rw [← sum_pauliProj_eq_one (K := K) (ι := ι) W]
  refine Finset.sum_congr rfl fun e _ => ?_
  rw [Finset.sum_ite_eq (Finset.univ : Finset (ZMod 2)) (f e) (fun _ => pauliProj W e)]
  simp

/-- The binary measurement on the Pauli basis attached to a binary function of
the labels: its effects are the two marginals of the Pauli basis projectors.
This is the ideal target family of `thm:ms-rigidity`, blueprint
`ch13_qpbt_test.tex:224-253`. -/
noncomputable def pauliMarginalMeasurement {ι : Type*} [Fintype ι] [DecidableEq ι]
    (W : PauliKind) (f : (ι → K) → ZMod 2) :
    MIPStarRE.Quantum.Measurement (ZMod 2) (ι → K) :=
  MIPStarRE.Quantum.Measurement.ofSumEqOne
    (fun b => ∑ e : ι → K, if f e = b then pauliProj W e else 0)
    (fun b => sum_ite_pauliProj_nonneg W (fun e => f e = b))
    (sum_binary_marginal_pauliProj W f)

/-- The effects of the Pauli marginal measurement are the marginals
themselves. -/
@[simp]
theorem pauliMarginalMeasurement_effect {ι : Type*} [Fintype ι] [DecidableEq ι]
    (W : PauliKind) (f : (ι → K) → ZMod 2) (b : ZMod 2) :
    (pauliMarginalMeasurement W f).effect b =
      ∑ e : ι → K, if f e = b then pauliProj W e else 0 := rfl

/-- A marginal of the Pauli basis projectors is a contraction, in the form used
by the estimates of the rigidity assembly. -/
theorem conjTranspose_mul_le_one_sum_ite_pauliProj {ι : Type*} [Fintype ι]
    [DecidableEq ι] (W : PauliKind) (f : (ι → K) → ZMod 2) (b : ZMod 2) :
    (∑ e : ι → K, if f e = b then pauliProj W e else 0)ᴴ *
        (∑ e : ι → K, if f e = b then pauliProj W e else 0) ≤ 1 :=
  MagicSquareRigidity.conjTranspose_mul_le_one_of_effect
    (pauliMarginalMeasurement W f) b

/-! ## The ideal state is normalized -/

/-- The ideal state of `thm:ms-rigidity`, a maximally entangled state on the
extracted registers tensored with an auxiliary bipartite state and shuffled into
local player order, has the norm of the auxiliary state.  In particular it is a
unit vector whenever the auxiliary state is.  The norm identities for the
coordinate operations are `reindexState_norm_eq` and `vecTensor_norm_eq` in
`MIPStarRE/QPBT/State.lean`.  Blueprint `ch13_qpbt_test.tex:224-253`. -/
theorem norm_reindexState_prodShuffle_vecTensor_eprState {V ιA'' ιB'' : Type*}
    [Fintype V] [DecidableEq V] [Nonempty V] [Fintype ιA''] [DecidableEq ιA'']
    [Fintype ιB''] [DecidableEq ιB''] (aux : EuclideanSpace ℂ (ιA'' × ιB'')) :
    ‖reindexState prodShuffle (vecTensor (eprState V) aux)‖ = ‖aux‖ := by
  rw [reindexState_norm_eq, vecTensor_norm_eq, eprState_norm, one_mul]

end

end MIPStarRE.QPBT
