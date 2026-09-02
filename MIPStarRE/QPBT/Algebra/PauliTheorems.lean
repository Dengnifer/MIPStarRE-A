import MIPStarRE.QPBT.Algebra.Pauli
import MIPStarRE.QPBT.Algebra.SelfDualBasisTheorems
import MIPStarRE.QPBT.Algebra.Subspaces
import MIPStarRE.QPBT.State
import MIPStarRE.LDT.Preliminaries.FiniteFields

/-! # Pauli commutation and cancellation obligations

The source nodes are `lem:twisted-commutation` and `lem:cancellation` in
`blueprint/src/chapter/ch11_qpbt_algebra.tex:573-625`, from
`references/qpbt-paper/04_preliminaries.tex:1056-1095,1124-1132`. The general-prime
statements use the canonical character `ffChar`; binary declarations below are
separately named QPBT specializations.
-/

open scoped BigOperators Matrix

namespace MIPStarRE.QPBT

open MIPStarRE.LDT MIPStarRE.LDT.Preliminaries MIPStarRE.Quantum

/-- The shift observable in `lem:twisted-commutation`, blueprint
`ch11_qpbt_algebra.tex:573-600`, paper `04_preliminaries.tex:1056-1089`. -/
noncomputable def primeTauShift {p : ℕ} {K : Type*} [Field K] [Fintype K]
    [DecidableEq K] [Fact p.Prime] [Algebra (ZMod p) K]
    (a : K) : Op K := fun i j => if i = j + a then 1 else 0

/-- The phase observable in `lem:twisted-commutation`, blueprint
`ch11_qpbt_algebra.tex:573-600`, paper `04_preliminaries.tex:1056-1089`. -/
noncomputable def primeTauPhase {p : ℕ} {K : Type*} [Field K] [Fintype K]
    [DecidableEq K] [Fact p.Prime] [Algebra (ZMod p) K]
    (b : K) : Op K := fun i j =>
  if i = j then ffChar (p := p) (F := K) (b * j) else 0

/-- The multi-qudit observable in `lem:twisted-commutation`, with `false`
denoting phase; blueprint `ch11_qpbt_algebra.tex:565-600`, paper
`04_preliminaries.tex:1073-1095,1141-1151`. -/
noncomputable def primeTauObservable {p : ℕ} {K ι : Type*} [Field K] [Fintype K]
    [DecidableEq K] [Fact p.Prime] [Algebra (ZMod p) K]
    [Fintype ι] [DecidableEq ι] (W : Bool) (a : ι → K) : Op (ι → K) :=
  fun x y => ∏ i : ι, if W then primeTauShift (p := p) (a i) (x i) (y i)
    else primeTauPhase (p := p) (a i) (x i) (y i)

/-- The product identity `eq:pauli-product-power`, blueprint
`ch11_qpbt_algebra.tex:577-585`, paper `04_preliminaries.tex:1082-1089`. -/
theorem primeTauObservable_mul {p : ℕ} {K ι : Type*} [Field K] [Fintype K]
    [DecidableEq K] [Fact p.Prime] [Algebra (ZMod p) K] [Fintype ι]
    [DecidableEq ι] (W : Bool) (a a' : ι → K) :
    primeTauObservable (p := p) W a * primeTauObservable (p := p) W a' =
      primeTauObservable (p := p) W (a + a') := by
  sorry

/-- The prime-field exponent identity in `eq:pauli-product-power`, blueprint
`ch11_qpbt_algebra.tex:577-585`, paper `04_preliminaries.tex:1082-1089`. -/
theorem primeTauObservable_pow {p : ℕ} {K ι : Type*} [Field K] [Fintype K]
    [DecidableEq K] [Fact p.Prime] [Algebra (ZMod p) K] [Fintype ι]
    [DecidableEq ι] (W : Bool) (a : ι → K) (b : ZMod p) :
    (primeTauObservable (p := p) W a) ^ b.val =
      primeTauObservable (p := p) W (fun i => a i * algebraMap (ZMod p) K b) := by
  sorry

/-- The characteristic-`p` consequence of `primeTauObservable_pow`, blueprint
`ch11_qpbt_algebra.tex:583-585`, paper `04_preliminaries.tex:1088-1089`. -/
theorem primeTauObservable_pow_char {p : ℕ} {K ι : Type*} [Field K] [Fintype K]
    [DecidableEq K] [Fact p.Prime] [Algebra (ZMod p) K] [Fintype ι]
    [DecidableEq ι] (W : Bool) (a : ι → K) :
    (primeTauObservable (p := p) W a) ^ p = 1 := by
  sorry

/-- The source multi-qudit twisted relation `eq:twisted-fq`, blueprint
`ch11_qpbt_algebra.tex:586-597`, paper `04_preliminaries.tex:1090-1095,1141-1151`. -/
theorem primeTauObservable_X_mul_Z {p : ℕ} {K ι : Type*} [Field K] [Fintype K]
    [DecidableEq K] [Fact p.Prime] [Algebra (ZMod p) K] [Fintype ι]
    [DecidableEq ι] [Nonempty ι] (a b : ι → K) :
    primeTauObservable (p := p) true a * primeTauObservable (p := p) false b =
      (ffChar (p := p) (F := K) (-dotProduct a b)) •
        (primeTauObservable (p := p) false b * primeTauObservable (p := p) true a) := by
  sorry

/-- Binary specialization of `eq:pauli-product-power`, blueprint
`ch11_qpbt_algebra.tex:577-585`, paper `04_preliminaries.tex:1082-1089`.

**Scope restriction:** This characteristic-two consumer theorem is separated
from the general-prime source node as documented in
`docs/paper-gaps/qpbt_characteristic-two-pauli-scope.tex`. -/
theorem tauObservable_mul {K ι : Type*} [Field K] [Fintype K] [DecidableEq K]
    [Algebra (ZMod 2) K] [Fintype ι] [DecidableEq ι]
    (W : PauliKind) (a a' : ι → K) :
    tauObservable W a * tauObservable W a' = tauObservable W (a + a') := by
  sorry

/-- Binary characteristic-two specialization of `eq:pauli-product-power`,
blueprint `ch11_qpbt_algebra.tex:583-585`, paper `04_preliminaries.tex:1088-1089`.

**Scope restriction:** This characteristic-two consumer theorem is separated
from the general-prime source node as documented in
`docs/paper-gaps/qpbt_characteristic-two-pauli-scope.tex`. -/
theorem tauObservable_sq {K ι : Type*} [Field K] [Fintype K] [DecidableEq K]
    [Algebra (ZMod 2) K] [Fintype ι] [DecidableEq ι] (W : PauliKind) (a : ι → K) :
    tauObservable W a * tauObservable W a = 1 := by
  sorry

/-- Binary specialization of `eq:twisted-fq`, blueprint
`ch11_qpbt_algebra.tex:586-597`, paper `04_preliminaries.tex:1090-1095`.

**Scope restriction:** This characteristic-two consumer theorem is separated
from the general-prime source node as documented in
`docs/paper-gaps/qpbt_characteristic-two-pauli-scope.tex`. -/
theorem tauObservable_X_mul_Z {K ι : Type*} [Field K] [Fintype K] [DecidableEq K]
    [Algebra (ZMod 2) K] [Fintype ι] [DecidableEq ι] (a b : ι → K) :
    tauObservable .X a * tauObservable .Z b =
      (phaseSign (binTrace K (dotProduct a b))) •
        (tauObservable .Z b * tauObservable .X a) := by
  sorry

/-- Uniform complex expectation over a finite submodule, as used by
`lem:cancellation`; blueprint `ch11_qpbt_algebra.tex:616-625`, paper
`04_preliminaries.tex:1124-1132`. -/
noncomputable def submoduleExpect {K ι : Type*} [Field K] [Fintype K]
    [DecidableEq K] [Fintype ι] [DecidableEq ι]
    (V : Submodule K (ι → K)) (f : V → ℂ) : ℂ := by
  letI : Fintype V := Fintype.ofFinite V
  exact 𝔼 u : V, f u

/-- Fourier cancellation `lem:cancellation` over an arbitrary field submodule;
blueprint `ch11_qpbt_algebra.tex:616-625`, paper
`04_preliminaries.tex:1124-1132`. -/
theorem ffChar_dotProduct_submodule_expect_eq_zero {p : ℕ} {K ι : Type*}
    [Field K] [Fintype K] [DecidableEq K] [Fact p.Prime] [Algebra (ZMod p) K]
    [Fintype ι] [DecidableEq ι] (V : Submodule K (ι → K)) (v : ι → K)
    (hv : v ∉ dotOrthogonal V) :
    submoduleExpect V
      (fun u => ffChar (p := p) (F := K) (dotProduct (u : ι → K) v)) = 0 := by
  sorry

/-- Binary specialization of `lem:cancellation`, blueprint
`ch11_qpbt_algebra.tex:616-625`, paper `04_preliminaries.tex:1124-1132`.

**Scope restriction:** This characteristic-two consumer theorem is separated
from the general-prime source node as documented in
`docs/paper-gaps/qpbt_characteristic-two-pauli-scope.tex`. -/
theorem avg_neg_one_pow_binTrace_eq_zero {K : Type*} [Field K] [Fintype K]
    {k : Type*}
    [DecidableEq K] [Algebra (ZMod 2) K] [Fintype k] [DecidableEq k]
    (V : Submodule K (k → K)) [Fintype V] (v : k → K)
    (hv : v ∉ dotOrthogonal V) :
    𝔼 u : V, phaseSign (binTrace K (dotProduct (u : k → K) v)) = 0 := by
  sorry

/-- The tensor product of binary Pauli projectors, obtained by specializing
`pauliProj` to `ZMod 2`. This is the binary target in `lem:pauli-binary`,
blueprint `ch11_qpbt_algebra.tex:675-708`, paper
`references/qpbt-paper/04_preliminaries.tex:1163-1208`. -/
noncomputable abbrev qubitPauliProj {ι : Type*} [Fintype ι] [DecidableEq ι]
    (W : PauliKind) (b : ι → ZMod 2) : Op (ι → ZMod 2) :=
  pauliProj W b

/-- `lem:pauli-binary`: the fixed binary coordinates induce an isometry that
maps EPR states and generalized Pauli projectors to their qubit forms.
Blueprint `ch11_qpbt_algebra.tex:675-708`, paper
`references/qpbt-paper/04_preliminaries.tex:1163-1208`.

**Local fix:** The source's final factor index is printed as
`j ∈ {1, ..., q}`; the basis expansion at paper lines 1191--1194 shows that
the intended range has `basisDim = log₂ q` entries. -/
theorem exists_qubitIsometry (q : ℕ) (F : FixedFieldModel q) (L : ℕ) :
    ∃ φ : EuclideanSpace ℂ (Fin L → F.K) ≃ₗᵢ[ℂ]
        EuclideanSpace ℂ (Fin L × Fin F.basisDim → ZMod 2),
      isometryTensor φ.toLinearIsometry φ.toLinearIsometry
          (eprState (Fin L → F.K)) =
          eprState (Fin L × Fin F.basisDim → ZMod 2) ∧
        ∀ (W : PauliKind) (u : Fin L → F.K),
          pauliProj W u =
            conjIsometry φ.symm.toLinearIsometry
              (qubitPauliProj W (kappaVec F u)) := by
  sorry

end MIPStarRE.QPBT
