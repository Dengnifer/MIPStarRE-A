import MIPStarRE.QPBT.Combining.Linearity.NaimarkRounding

/-!
# Boolean representation stability

This file completes the proof of the quantum linearity theorem of Natarajan
and Vidick in the specialized form used by the linearity route.  A family of
binary observables `O^u`, indexed by the Boolean cube `F_2^t` and weighted by a
positive semidefinite trace-one operator `ρ`, whose products `O^u O^v` are on
average close to `O^{u+v}` in the state-dependent distance, is on average close,
in the same distance and weighted by the extended state `ρ ⊗ |anc⟩⟨anc|`, to
an exactly linear family of binary observables on an ancillary extension.

The extension, the ancillary vector, and the exactly linear family are those
of the Naimark rounding of the Fourier-square POVM.  The main computation is
an identity, not an inequality: the average raw distance between the rounded
family and the ampliated original family, weighted by `ρ ⊗ |anc⟩⟨anc|`, equals
the average multiplicative defect of the original family weighted by `ρ`.  Both
sides equal `2 - 2 * (two-query correlation)`.  The left side reduces to the
correlation by compressing the rounded observables along the ancillary vector
and applying the cubic Fourier identity; the right side is the operator BLR
computation, including the reindexing of the uniform pair.  No commutation
among the observables is assumed, and the weight `ρ` is never replaced by the
normalized trace.

## Main results

* `heteroKron_ancProj_posSemidef` and `trace_heteroKron_ancProj`: the extended
  weight `ρ ⊗ |anc⟩⟨anc|` is again positive semidefinite with trace one.
* `re_trace_roundedObservable_mul_heteroKron`: the compression of the
  correlation between a rounded observable and the ampliated original
  observable to the original space.
* `stateDepDistSq_roundedObservable`: the pointwise distance between a rounded
  observable and the ampliated original observable, in terms of the overlap
  with the character sum of the Fourier-square POVM.
* `avg_stateDepDistSq_roundedObservable_eq_avg_multiplicativeDefect`: the
  distance/defect identity
  `E_u d_{ρ'}(L^u, O^u ⊗ 1)^2 = E_{u,v} d_ρ(O^u O^v, O^{u+v})^2`.
* `exists_exact_boolean_representation`: the Boolean representation stability
  theorem, obtained by weakening the identity to the incoming bound.

## References

Natarajan--Vidick, arXiv:1610.03574, Theorem 10 and its Fourier/Naimark
proof, `references/nv-paper/fullpaper.tex:1074-1113`; the closing step, which
converts the overlap certificate into the distance bound, is at lines
1104--1112, and the state-dependent distance is defined at lines 866--900.
The QPBT paper quotes the theorem at
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:711-725`.  The
blueprint statement is `thm:linearity` in
`blueprint/src/chapter/ch15_qpbt_combining.tex:98-147`, and the target public
theorem is `exists_exactly_linear_observables` in
`MIPStarRE/QPBT/Combining/Linearity.lean`.  The normalization convention, under
which the incoming average multiplicative defect and the outgoing average raw
distance carry the same constant, is recorded in
`docs/paper-gaps/qpbt_linearity-distance-normalization.tex`.
-/

open scoped BigOperators Matrix MatrixOrder ComplexOrder

namespace MIPStarRE.QPBT

open MIPStarRE.LDT
open MIPStarRE.Quantum

noncomputable section

/-! ## The extended weight -/

/-- Formalization-only auxiliary lemma for the extended state
`ρ' = ρ ⊗ |anc⟩⟨anc|` of `references/nv-paper/fullpaper.tex:1081-1082`: the
rank-one density of any vector is positive semidefinite. -/
theorem ancProj_posSemidef {ι : Type} [Fintype ι] (v : EuclideanSpace ℂ ι) :
    (ancProj v).PosSemidef :=
  Matrix.posSemidef_vecMulVec_self_star _

/-- Formalization-only auxiliary lemma for the extended state
`ρ' = ρ ⊗ |anc⟩⟨anc|` of `references/nv-paper/fullpaper.tex:1081-1082`: the
trace of the rank-one density of a vector is the square of its norm. -/
theorem trace_ancProj {ι : Type} [Fintype ι] (v : EuclideanSpace ℂ ι) :
    Matrix.trace (ancProj v) = (‖v‖ : ℂ) ^ 2 := by
  have h := inner_self_eq_norm_sq_to_K (𝕜 := ℂ) v
  rw [EuclideanSpace.inner_eq_star_dotProduct] at h
  exact (Matrix.trace_vecMulVec _ _).trans h

/-- The extended weight `ρ ⊗ |anc⟩⟨anc|` of a positive semidefinite operator
`ρ` and an ancillary vector is positive semidefinite.  Together with
`trace_heteroKron_ancProj` this is the assertion that `ρ'` is a density
operator on the extended space at `references/nv-paper/fullpaper.tex:1081-1082`. -/
theorem heteroKron_ancProj_posSemidef {ι ι' : Type} [Fintype ι] [Fintype ι']
    {ρ : Op ι} (hρ : ρ.PosSemidef) (anc : EuclideanSpace ℂ ι') :
    (heteroKron ρ (ancProj anc)).PosSemidef :=
  hρ.kronecker (ancProj_posSemidef anc)

/-- The extended weight `ρ ⊗ |anc⟩⟨anc|` of a trace-one operator `ρ` and a unit
vector `anc` has trace one.  Together with `heteroKron_ancProj_posSemidef` this
is the assertion that `ρ'` is a density operator on the extended space at
`references/nv-paper/fullpaper.tex:1081-1082`. -/
theorem trace_heteroKron_ancProj {ι ι' : Type} [Fintype ι] [Fintype ι']
    (ρ : Op ι) (htrace : ρ.trace = 1)
    (anc : EuclideanSpace ℂ ι') (hanc : ‖anc‖ = 1) :
    (heteroKron ρ (ancProj anc)).trace = 1 := by
  unfold heteroKron
  simp only [Matrix.kronecker]
  rw [Matrix.trace_kronecker, htrace, trace_ancProj, hanc]
  simp

/-- The ampliation `O ⊗ 1` of a binary observable by the identity of an
ancillary space is a binary observable.  This is the sense in which the
original observables `A(a)` act on the extended space in display (8) of
`references/nv-paper/fullpaper.tex:1083-1086`. -/
theorem isBinaryObservable_heteroKron_one {ι ι' : Type} [Fintype ι] [DecidableEq ι]
    [Fintype ι'] [DecidableEq ι'] {O : Op ι} (hO : IsBinaryObservable O) :
    IsBinaryObservable (heteroKron O (1 : Op ι')) := by
  unfold heteroKron
  simp only [Matrix.kronecker]
  refine ⟨?_, ?_⟩
  · rw [Matrix.IsHermitian, Matrix.conjTranspose_kronecker, hO.1.eq, Matrix.conjTranspose_one]
  · rw [← Matrix.mul_kronecker_mul, hO.2, Matrix.one_mul, Matrix.one_kronecker_one]

/-! ## The distance/defect identity -/

/-- The correlation between a rounded observable `L^u` and the ampliated
original observable `O^u ⊗ 1`, evaluated in the extended state
`ρ ⊗ |anc⟩⟨anc|`, has the same real part as the overlap between `O^u` and the
character sum `∑_v (-1)^{v·u} B^v` of the Fourier-square POVM evaluated in
`ρ`.  Taking the adjoint of the triple product reverses the order of the three
Hermitian factors, after which the ampliated observable is absorbed into the
weight and the rounded observable is compressed along the ancillary vector.
This is the passage from `Tr_{ρ'}(A(a) 𝒜(a))` to
`Tr_ρ(A(a) ∑_u (-1)^{u·a} (hat A^u)^2)` at
`references/nv-paper/fullpaper.tex:1105-1110`, with the operator order of the
Lean distance preserved. -/
theorem re_trace_roundedObservable_mul_heteroKron {t : ℕ} {ι : Type}
    [Fintype ι] [DecidableEq ι]
    (O : (Fin t → ZMod 2) → Op ι) (hO : ∀ a, IsBinaryObservable (O a))
    (ρ : Op ι) (hρ : ρ.PosSemidef) (u : Fin t → ZMod 2) :
    (Matrix.trace (roundedObservable O hO u *
        heteroKron (O u) (1 : Op (Option (Fin t → ZMod 2))) *
        heteroKron ρ (ancProj (naimarkAncilla t)))).re =
      (Matrix.trace (O u * (∑ v : Fin t → ZMod 2, booleanCharacter v u •
        (operatorFourier O v * operatorFourier O v)) * ρ)).re := by
  have hL := roundedObservable_isHermitian O hO u
  have hT := (isBinaryObservable_heteroKron_one (ι' := Option (Fin t → ZMod 2)) (hO u)).1
  have hρ' : (heteroKron ρ (ancProj (naimarkAncilla t))).IsHermitian :=
    (heteroKron_ancProj_posSemidef hρ _).isHermitian
  have hprod : heteroKron ρ (ancProj (naimarkAncilla t)) *
      heteroKron (O u) (1 : Op (Option (Fin t → ZMod 2))) =
        heteroKron (ρ * O u) (ancProj (naimarkAncilla t)) := by
    unfold heteroKron
    simp only [Matrix.kronecker]
    rw [← Matrix.mul_kronecker_mul, Matrix.mul_one]
  have hstar :
      star (Matrix.trace (roundedObservable O hO u *
          heteroKron (O u) (1 : Op (Option (Fin t → ZMod 2))) *
          heteroKron ρ (ancProj (naimarkAncilla t)))) =
        Matrix.trace (O u * (∑ v : Fin t → ZMod 2, booleanCharacter v u •
          (operatorFourier O v * operatorFourier O v)) * ρ) := by
    calc
      star (Matrix.trace (roundedObservable O hO u *
          heteroKron (O u) (1 : Op (Option (Fin t → ZMod 2))) *
          heteroKron ρ (ancProj (naimarkAncilla t)))) =
          Matrix.trace ((roundedObservable O hO u *
            heteroKron (O u) (1 : Op (Option (Fin t → ZMod 2))) *
            heteroKron ρ (ancProj (naimarkAncilla t)))ᴴ) := by
        rw [Matrix.trace_conjTranspose]
      _ = Matrix.trace (heteroKron ρ (ancProj (naimarkAncilla t)) *
            (heteroKron (O u) (1 : Op (Option (Fin t → ZMod 2))) *
              roundedObservable O hO u)) := by
        simp only [Matrix.conjTranspose_mul, hL.eq, hT.eq, hρ'.eq, Matrix.mul_assoc]
      _ = Matrix.trace (heteroKron (ρ * O u) (ancProj (naimarkAncilla t)) *
            roundedObservable O hO u) := by
        rw [← Matrix.mul_assoc, hprod]
      _ = Matrix.trace (ρ * O u * ∑ v : Fin t → ZMod 2, booleanCharacter v u •
            (operatorFourier O v * operatorFourier O v)) :=
        trace_heteroKron_mul_roundedObservable O hO (ρ * O u) u
      _ = Matrix.trace (O u * (∑ v : Fin t → ZMod 2, booleanCharacter v u •
            (operatorFourier O v * operatorFourier O v)) * ρ) :=
        (Matrix.trace_mul_cycle (O u) _ ρ).symm
  have := congrArg Complex.re hstar
  simpa [Complex.star_def, Complex.conj_re] using this

/-- The squared state-dependent distance between a rounded observable `L^u` and
the ampliated original observable `O^u ⊗ 1`, weighted by the extended state
`ρ ⊗ |anc⟩⟨anc|`, equals `2 - 2 Re Tr(O^u (∑_v (-1)^{v·u} B^v) ρ)`.  This
combines the raw-correlation identity for binary observables with the
compression of the rounded observable; it is the pointwise form of the closing
computation at `references/nv-paper/fullpaper.tex:1104-1112`, in the raw
normalization of `docs/paper-gaps/qpbt_linearity-distance-normalization.tex`. -/
theorem stateDepDistSq_roundedObservable {t : ℕ} {ι : Type}
    [Fintype ι] [DecidableEq ι]
    (O : (Fin t → ZMod 2) → Op ι) (hO : ∀ a, IsBinaryObservable (O a))
    (ρ : Op ι) (hρ : ρ.PosSemidef) (htrace : ρ.trace = 1) (u : Fin t → ZMod 2) :
    stateDepDistSq (roundedObservable O hO u)
        (heteroKron (O u) (1 : Op (Option (Fin t → ZMod 2))))
        (heteroKron ρ (ancProj (naimarkAncilla t))) =
      2 - 2 * (Matrix.trace (O u * (∑ v : Fin t → ZMod 2, booleanCharacter v u •
        (operatorFourier O v * operatorFourier O v)) * ρ)).re := by
  rw [stateDepDistSq_eq_two_sub_two_mul_correlation _ _ _
      (roundedObservable_isBinaryObservable O hO u) (isBinaryObservable_heteroKron_one (hO u))
      (heteroKron_ancProj_posSemidef hρ _)
      (trace_heteroKron_ancProj ρ htrace _ (norm_naimarkAncilla t)),
    re_trace_roundedObservable_mul_heteroKron O hO ρ hρ u]

/-- The distance/defect identity: the average, over a uniformly random `u`, of
the squared state-dependent distance between the rounded observable `L^u` and
the ampliated original observable `O^u ⊗ 1`, weighted by `ρ ⊗ |anc⟩⟨anc|`,
equals the average, over a uniformly random pair `(u, v)`, of the squared
state-dependent defect of `O^u O^v` from `O^{u+v}`, weighted by `ρ`.  Both
sides equal `2 - 2 * (two-query correlation)`: the left side through the
pointwise compression and the cubic Fourier identity, the right side through
the operator BLR computation and its reindexing of the uniform pair.  This is
the closing step of the proof of Theorem 10 at
`references/nv-paper/fullpaper.tex:1104-1112`, sharpened from the inequality
of display (8) to an equality; no commutation among the observables is used. -/
theorem avg_stateDepDistSq_roundedObservable_eq_avg_multiplicativeDefect {t : ℕ}
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (O : (Fin t → ZMod 2) → Op ι) (hO : ∀ a, IsBinaryObservable (O a))
    (ρ : Op ι) (hρ : ρ.PosSemidef) (htrace : ρ.trace = 1) :
    avgOver (uniformDistribution (Fin t → ZMod 2))
        (fun u => stateDepDistSq (roundedObservable O hO u)
          (heteroKron (O u) (1 : Op (Option (Fin t → ZMod 2))))
          (heteroKron ρ (ancProj (naimarkAncilla t)))) =
      avgOver (uniformDistribution ((Fin t → ZMod 2) × (Fin t → ZMod 2)))
        (fun pair => multiplicativeDefect O ρ pair.1 pair.2) := by
  rw [avgOver_congr _ _ _ (stateDepDistSq_roundedObservable O hO ρ hρ htrace),
    avgOver_sub, avgOver_const_mul, avgOver_uniform_const,
    avg_overlap_fourierSquare_eq_sum_cube, operatorFourier_cube_trace_eq_correlation,
    avg_multiplicativeDefect_eq_two_sub_two_mul_correlation O hO ρ hρ htrace]

/-! ## Boolean representation stability -/

/-- Boolean representation stability.  Let `t` be positive, `η ≥ 0`, `ρ` a
positive semidefinite trace-one operator on a finite carrier, and `O^u`, for
`u ∈ F_2^t`, binary observables whose products satisfy
`E_{u,v} d_ρ(O^u O^v, O^{u+v})^2 ≤ η`.  Then there are a finite ancillary
carrier, a unit vector `anc` in it, and binary observables `L^u` on the
product carrier with `L^u L^v = L^{u+v}` for all `u, v` and
`E_u d_{ρ'}(L^u, O^u ⊗ 1)^2 ≤ η`, where `ρ' = ρ ⊗ |anc⟩⟨anc|`.

The ancillary carrier is `Option (F_2^t)`, the vector is the canonical
ancillary vector of the Naimark dilation, and the family is the rounded
observables of the Fourier-square POVM; the bound is the distance/defect
identity `avg_stateDepDistSq_roundedObservable_eq_avg_multiplicativeDefect`
weakened by the hypothesis.  This is Theorem 10 of Natarajan--Vidick,
`references/nv-paper/fullpaper.tex:1074-1088`, in the state-weighted
`Z_2^t` form quoted at
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:711-725` and
stated as `thm:linearity` in
`blueprint/src/chapter/ch15_qpbt_combining.tex:98-147`, with the incoming
hypothesis expressed as the average multiplicative defect in the raw
normalization of `docs/paper-gaps/qpbt_linearity-distance-normalization.tex`.
The positivity of `t` and the nonnegativity of `η` are part of the quoted
statement and are not needed by the proof. -/
theorem exists_exact_boolean_representation {ι : Type}
    [Fintype ι] [DecidableEq ι]
    (t : ℕ) (_ht : 0 < t) (η : ℝ) (_hη : 0 ≤ η)
    (ρ : Op ι) (hρ : ρ.PosSemidef) (htrace : ρ.trace = 1)
    (O : (Fin t → ZMod 2) → Op ι)
    (hO : ∀ u, IsBinaryObservable (O u))
    (hdefect :
      avgOver (uniformDistribution ((Fin t → ZMod 2) × (Fin t → ZMod 2)))
        (fun pair => stateDepDistSq (O pair.1 * O pair.2) (O (pair.1 + pair.2)) ρ) ≤ η) :
    ∃ (ι' : Type) (_ : Fintype ι') (_ : DecidableEq ι')
        (anc : EuclideanSpace ℂ ι'),
      ‖anc‖ = 1 ∧
        ∃ L : (Fin t → ZMod 2) → Op (ι × ι'),
          (∀ u, IsBinaryObservable (L u)) ∧
          (∀ u v, L u * L v = L (u + v)) ∧
          avgOver (uniformDistribution (Fin t → ZMod 2))
              (fun u => stateDepDistSq (L u)
                (heteroKron (O u) (1 : Op ι'))
                (heteroKron ρ (ancProj anc))) ≤ η := by
  refine ⟨Option (Fin t → ZMod 2), inferInstance, inferInstance, naimarkAncilla t,
    norm_naimarkAncilla t, roundedObservable O hO, roundedObservable_isBinaryObservable O hO,
    roundedObservable_mul O hO, ?_⟩
  rw [avg_stateDepDistSq_roundedObservable_eq_avg_multiplicativeDefect O hO ρ hρ htrace]
  exact hdefect

end

end MIPStarRE.QPBT
