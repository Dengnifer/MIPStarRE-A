import MIPStarRE.QPBT.Algebra.Pauli
import MIPStarRE.QPBT.Algebra.Subspaces
import MIPStarRE.LDT.Preliminaries.FiniteFields

/-! # Pauli commutation and cancellation obligations

The source nodes are `lem:twisted-commutation` and `lem:cancellation` in
`blueprint/src/chapter/ch11_qpbt_algebra.tex:638-652`, from
`references/qpbt-paper/04_preliminaries.tex:1123-1140`.  The general-prime
statements use the canonical character `ffChar`; binary declarations below are
separately named QPBT specializations.
-/

open scoped BigOperators Matrix

namespace MIPStarRE.QPBT

open MIPStarRE.LDT MIPStarRE.LDT.Preliminaries MIPStarRE.Quantum

/-- A prime-field shift observable. -/
noncomputable def primeTauShift {p : ℕ} {K : Type*} [Field K] [Fintype K]
    [DecidableEq K] [Fact p.Prime] [Algebra (ZMod p) K]
    (a : K) : Op K := fun i j => if i = j + a then 1 else 0

/-- A prime-field phase observable. -/
noncomputable def primeTauPhase {p : ℕ} {K : Type*} [Field K] [Fintype K]
    [DecidableEq K] [Fact p.Prime] [Algebra (ZMod p) K]
    (b : K) : Op K := fun i j =>
  if i = j then ffChar (p := p) (F := K) (b * j) else 0

/-- Prime-field generalized Pauli observable, with `false` denoting phase. -/
noncomputable def primeTauObservable {p : ℕ} {K ι : Type*} [Field K] [Fintype K]
    [DecidableEq K] [Fact p.Prime] [Algebra (ZMod p) K]
    [Fintype ι] [DecidableEq ι] (W : Bool) (a : ι → K) : Op (ι → K) :=
  fun x y => ∏ i : ι, if W then primeTauShift (p := p) (a i) (x i) (y i)
    else primeTauPhase (p := p) (a i) (x i) (y i)

theorem primeTauObservable_mul {p : ℕ} {K ι : Type*} [Field K] [Fintype K]
    [DecidableEq K] [Fact p.Prime] [Algebra (ZMod p) K] [Fintype ι]
    [DecidableEq ι] (W : Bool) (a a' : ι → K) :
    primeTauObservable (p := p) W a * primeTauObservable (p := p) W a' =
      primeTauObservable (p := p) W (a + a') := by
  sorry

theorem primeTauObservable_pow {p : ℕ} {K ι : Type*} [Field K] [Fintype K]
    [DecidableEq K] [Fact p.Prime] [Algebra (ZMod p) K] [Fintype ι]
    [DecidableEq ι] (W : Bool) (a : ι → K) :
    (primeTauObservable (p := p) W a) ^ p = 1 := by
  sorry

theorem primeTauObservable_pow_char {p : ℕ} {K ι : Type*} [Field K] [Fintype K]
    [DecidableEq K] [Fact p.Prime] [Algebra (ZMod p) K] [Fintype ι]
    [DecidableEq ι] (W : Bool) (a : ι → K) :
    (primeTauObservable (p := p) W a) ^ p = 1 := by
  sorry

theorem primeTauObservable_X_mul_Z {p : ℕ} {K ι : Type*} [Field K] [Fintype K]
    [DecidableEq K] [Fact p.Prime] [Algebra (ZMod p) K] [Fintype ι]
    [DecidableEq ι] (a b : ι → K) :
    primeTauObservable (p := p) true a * primeTauObservable (p := p) false b =
      (ffChar (p := p) (F := K) (dotProduct a b)) •
        (primeTauObservable (p := p) false b * primeTauObservable (p := p) true a) := by
  sorry

/-- Binary Pauli product specialization used by QPBT consumers. -/
theorem tauObservable_mul {K ι : Type*} [Field K] [Fintype K] [DecidableEq K]
    [Algebra (ZMod 2) K] [Fintype ι] [DecidableEq ι]
    (W : PauliKind) (a a' : ι → K) :
    tauObservable W a * tauObservable W a' = tauObservable W (a + a') := by
  sorry

/-- Binary characteristic-two power specialization. -/
theorem tauObservable_sq {K ι : Type*} [Field K] [Fintype K] [DecidableEq K]
    [Algebra (ZMod 2) K] [Fintype ι] [DecidableEq ι] (W : PauliKind) (a : ι → K) :
    tauObservable W a * tauObservable W a = 1 := by
  sorry

/-- Binary twisted commutation specialization. -/
theorem tauObservable_X_mul_Z {K ι : Type*} [Field K] [Fintype K] [DecidableEq K]
    [Algebra (ZMod 2) K] [Fintype ι] [DecidableEq ι] (a b : ι → K) :
    tauObservable .X a * tauObservable .Z b =
      (phaseSign (binTrace K (dotProduct a b))) •
        (tauObservable .Z b * tauObservable .X a) := by
  sorry

theorem avg_neg_one_pow_binTrace_eq_zero {K : Type*} [Field K] [Fintype K]
    {k : Type*}
    [DecidableEq K] [Algebra (ZMod 2) K] [Fintype k] [DecidableEq k]
    (V : Submodule K (k → K)) [Fintype V] (v : k → K)
    (hv : v ∉ dotOrthogonal V) :
    𝔼 u : V, phaseSign (binTrace K (dotProduct (u : k → K) v)) = 0 := by
  sorry

end MIPStarRE.QPBT
