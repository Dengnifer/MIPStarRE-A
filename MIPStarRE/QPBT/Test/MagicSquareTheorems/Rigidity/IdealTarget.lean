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

omit [Field K] [Fintype K] [Algebra (ZMod 2) K] in
/-- Formalization-only: a product of coordinate indicators is the indicator of
equality of the two tuples. -/
private theorem prod_indicator_eq_one_apply {ι : Type*} [Fintype ι]
    (x y : ι → K) :
    (∏ _i : ι, (if x _i = y _i then (1 : ℂ) else 0)) = if x = y then 1 else 0 := by
  by_cases h : x = y
  · subst h
    simp
  · rw [if_neg h]
    obtain ⟨i, hi⟩ := Function.ne_iff.mp h
    exact Finset.prod_eq_zero (Finset.mem_univ i) (if_neg hi)

omit [Fintype K] in
/-- The generalized Pauli observable at the zero label is the identity, for
either Pauli kind.  `def:generalized-pauli`, blueprint
`ch11_qpbt_algebra.tex:529-571`. -/
theorem tauObservable_zero {ι : Type*} [Fintype ι] [DecidableEq ι] (W : PauliKind) :
    tauObservable (K := K) W (0 : ι → K) = 1 := by
  ext x y
  rw [Matrix.one_apply, ← prod_indicator_eq_one_apply (K := K) x y]
  simp only [tauObservable]
  cases W <;>
    exact Finset.prod_congr rfl fun i _ => by
      simp [tauShift, tauPhase, phaseSign]

/-- The Pauli basis projectors of one kind sum to the identity: they are the
effects of a complete measurement.  This is the Fourier expansion
`tauObservable_eq_sum_pauliProj` of `lem:pauli-observable-expansion` at the zero
label, blueprint `ch11_qpbt_algebra.tex:674-688`, paper
`references/qpbt-paper/04_preliminaries.tex:1151-1161`. -/
theorem sum_pauliProj_eq_one {ι : Type*} [Fintype ι] [DecidableEq ι] (W : PauliKind) :
    (∑ e : ι → K, pauliProj W e) = 1 := by
  have h := tauObservable_eq_sum_pauliProj (K := K) W (0 : ι → K)
  rw [tauObservable_zero] at h
  rw [h]
  refine Finset.sum_congr rfl fun e _ => ?_
  have hzero : dotProduct (0 : ι → K) e = 0 := by
    simp [dotProduct]
  rw [hzero]
  simp [phaseSign]

/-- Each Pauli basis projector is positive semidefinite: it is the rank-one
outer product of the normalized Pauli eigenvector with itself. -/
theorem posSemidef_pauliProj {ι : Type*} [Fintype ι] [DecidableEq ι]
    (W : PauliKind) (e : ι → K) : (pauliProj W e).PosSemidef := by
  set A : Matrix Unit (ι → K) ℂ :=
    Matrix.of (fun (_ : Unit) (x : ι → K) => star (pauliVec W e x)) with hA
  have h : pauliProj W e = Aᴴ * A := by
    ext x y
    rw [Matrix.mul_apply]
    simp [hA, pauliProj, Matrix.vecMulVec_apply, Matrix.conjTranspose_apply]
  rw [h]
  exact Matrix.posSemidef_conjTranspose_mul_self A

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

/-- Formalization-only: reindexing Euclidean coordinates along an equivalence
preserves the norm.  The same identity is proved for the seed-fiber lift as
`reindexState_norm_eq` in
`MIPStarRE/QPBT/Combining/DirectLowDegree/Transport/SeedFiber.lean`; it belongs
with `reindexState` in `MIPStarRE/QPBT/State.lean`, and hoisting it there is
left to a follow-up so that the Magic Square rigidity chain does not acquire a
dependency on the low-degree transport modules. -/
private theorem norm_reindexState {ι κ : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype κ] [DecidableEq κ] (e : ι ≃ κ) (ψ : EuclideanSpace ℂ ι) :
    ‖reindexState e ψ‖ = ‖ψ‖ := by
  rw [← sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)]
  rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq]
  change (∑ j : κ, ‖ψ (e.symm j)‖ ^ 2) = ∑ i : ι, ‖ψ i‖ ^ 2
  exact e.symm.sum_comp (fun i => ‖ψ i‖ ^ 2)

/-- Formalization-only: the coordinate tensor of two Euclidean vectors has the
product norm.  See the note on `norm_reindexState` for the relation to
`vecTensor_norm_eq` in the low-degree transport modules. -/
private theorem norm_vecTensor {ι κ : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype κ] [DecidableEq κ] (u : EuclideanSpace ℂ ι) (v : EuclideanSpace ℂ κ) :
    ‖vecTensor u v‖ = ‖u‖ * ‖v‖ := by
  rw [← sq_eq_sq₀ (norm_nonneg _) (mul_nonneg (norm_nonneg _) (norm_nonneg _))]
  rw [EuclideanSpace.norm_sq_eq, mul_pow, EuclideanSpace.norm_sq_eq,
    EuclideanSpace.norm_sq_eq]
  change (∑ p : ι × κ, ‖u p.1 * v p.2‖ ^ 2) =
    (∑ i : ι, ‖u i‖ ^ 2) * ∑ j : κ, ‖v j‖ ^ 2
  simp only [norm_mul, mul_pow]
  rw [← Finset.univ_product_univ, Finset.sum_product, Finset.sum_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.mul_sum]

/-- The ideal state of `thm:ms-rigidity`, a maximally entangled state on the
extracted registers tensored with an auxiliary bipartite state and shuffled into
local player order, has the norm of the auxiliary state.  In particular it is a
unit vector whenever the auxiliary state is.  Blueprint
`ch13_qpbt_test.tex:224-253`. -/
theorem norm_reindexState_prodShuffle_vecTensor_eprState {V ιA'' ιB'' : Type*}
    [Fintype V] [DecidableEq V] [Nonempty V] [Fintype ιA''] [DecidableEq ιA'']
    [Fintype ιB''] [DecidableEq ιB''] (aux : EuclideanSpace ℂ (ιA'' × ιB'')) :
    ‖reindexState prodShuffle (vecTensor (eprState V) aux)‖ = ‖aux‖ := by
  rw [norm_reindexState, norm_vecTensor, eprState_norm, one_mul]

end

end MIPStarRE.QPBT
