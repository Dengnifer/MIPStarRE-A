import Mathlib

/-!
# Subspaces for the Pauli basis test

This module supplies the register subspaces, dot-product orthogonals, and the
canonical coordinate complement used by the conditionally linear maps.  The
canonical complement is presented through the intrinsic pivot-rank test; the
equivalence with a particular row-reduced-echelon implementation is a later
construction theorem.

## References

The statement-level definitions are `def:register-subspace`,
`def:dot-product-orthogonal`, `def:canonical-complement`, and
`def:cl-canonical` in `blueprint/src/chapter/ch11_qpbt_algebra.tex`;
the paper origin is `references/qpbt-paper/04_preliminaries.tex:231-384`.
-/

open scoped BigOperators

namespace MIPStarRE.QPBT

variable {K ι : Type*} [Field K] [Fintype ι] [DecidableEq ι]

/--
`registerSubmodule K S` is the span of the standard coordinate vectors indexed
by `S`.  It is the Lean encoding of `def:register-subspace` from
`blueprint/src/chapter/ch11_qpbt_algebra.tex:24-29`, whose paper origin is
`references/qpbt-paper/04_preliminaries.tex:231-239`.
-/
def registerSubmodule (K : Type*) [Field K] (S : Finset ι) : Submodule K (ι → K) :=
  Submodule.span K {v | ∃ i, i ∈ S ∧ v = Pi.single i 1}

/--
`dotOrthogonal W` consists of vectors whose coordinate dot product with every
member of `W` vanishes.  This is `def:dot-product-orthogonal` in
`blueprint/src/chapter/ch11_qpbt_algebra.tex:31-42`, with paper origin
`references/qpbt-paper/04_preliminaries.tex:241-255`.
-/
def dotOrthogonal (W : Submodule K (ι → K)) : Submodule K (ι → K) where
  carrier := {u | ∀ v, v ∈ W → dotProduct u v = 0}
  zero_mem' := by
    intro v hv
    simp [dotProduct]
  add_mem' := by
    intro u v hu hv w hw
    calc
      dotProduct (u + v) w =
          (dotProduct u w) + (dotProduct v w) := by
            change (∑ i, (u i + v i) * w i) =
              (∑ i, u i * w i) + (∑ i, v i * w i)
            simp_rw [add_mul]
            rw [Finset.sum_add_distrib]
      _ = 0 := by rw [hu w hw, hv w hw, add_zero]
  smul_mem' := by
    intro c u hu v hv
    calc
      dotProduct (c • u) v = c * dotProduct u v := by
        simp [dotProduct, smul_eq_mul, mul_assoc, Finset.mul_sum]
      _ = 0 := by rw [hu v hv, mul_zero]

/-- Restrict a coordinate vector to the first `k` coordinates.  Lean-only rank
infrastructure for `def:canonical-complement`, blueprint
`ch11_qpbt_algebra.tex:84-110`, paper `references/qpbt-paper/04_preliminaries.tex:231-384`.
-/
private def prefixMap (k n : ℕ) (hk : k ≤ n) :
    (Fin n → K) →ₗ[K] (Fin k → K) :=
  { toFun := fun x i => x ⟨i.1, lt_of_lt_of_le i.2 hk⟩
    map_add' := by
      intro x y
      rfl
    map_smul' := by
      intro c x
      rfl }

/-- The rank of a prefix restriction used by the pivot characterization. -/
private noncomputable def prefixRank {n : ℕ} (W : Submodule K (Fin n → K))
    (k : ℕ) (hk : k ≤ n) : ℕ :=
  Module.finrank K (W.map (prefixMap k n hk))

/--
The non-pivot coordinate set of `W`, defined by the rank-increase
characterization of pivots.  This is the basis-free encoding approved for
`def:canonical-complement` in `blueprint/src/chapter/ch11_qpbt_algebra.tex:84-110`;
the paper's Gaussian-elimination presentation is
`references/qpbt-paper/04_preliminaries.tex:303-320`.
-/
noncomputable def canonicalComplement {n : ℕ}
    (W : Submodule K (Fin n → K)) : Finset (Fin n) :=
  Finset.univ.filter fun j =>
    prefixRank W (j.1 + 1) (Nat.succ_le_of_lt j.2) =
      prefixRank W j.1 j.2.le

/--
The canonical coordinate complement spans a complement of `W`.  This is the
proposition `lem:canonical-complement` in
`blueprint/src/chapter/ch11_qpbt_algebra.tex:112-120`, with paper origin
`references/qpbt-paper/04_preliminaries.tex:342-373`.
The proof is intentionally deferred in the stage-4.1 skeleton.
-/
theorem isCompl_registerSubmodule_canonicalComplement {n : ℕ}
    (W : Submodule K (Fin n → K)) :
    IsCompl W (registerSubmodule K (canonicalComplement W)) := by
  sorry

/--
The projector onto the canonical coordinate complement along `W`.  This is
`def:cl-canonical` in `blueprint/src/chapter/ch11_qpbt_algebra.tex:133-145`,
originating at `references/qpbt-paper/04_preliminaries.tex:375-384`.
-/
noncomputable def canonicalProjOfKernel {n : ℕ}
    (W : Submodule K (Fin n → K)) : (Fin n → K) →ₗ[K] (Fin n → K) := by
  let T := registerSubmodule K (canonicalComplement W)
  let p : (Fin n → K) →ₗ[K] T :=
    Submodule.projectionOnto T W
      (isCompl_registerSubmodule_canonicalComplement W).symm
  exact T.subtype.comp p

end MIPStarRE.QPBT
