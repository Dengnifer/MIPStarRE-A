import MIPStarRE.QPBT.Games.StrategyClasses

/-! # Ground-coordinate compression of finite measurements

For a distinguished ancilla coordinate `k₀`, `groundCompressMeasurement k₀ M`
has effects `M.effect a (i, k₀) (j, k₀)`. Positivity and completeness descend
to this principal submatrix. Compression commutes with finite outcome
postprocessing and preserves bipartite consistency exactly on `padState`.
The two players' spaces and their ancilla spaces may all be different.

These are Lean-only auxiliaries for the two Naimark steps in the proof of
`lem:qld-4-7`, tracked by issue #277. They allow measurements on the enlarged
spaces to be compared on the original spaces, including after polynomial
evaluation. Compression does not in general preserve projectivity; obtaining
projective measurements on the original spaces requires a separate rounding
argument. No statement of `lem:qld-4-7` is formalized here.

## References

* `references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1278-1288`,
  the two Naimark steps in the proof of `lem:qld-4-7`.
* `references/qpbt-paper/06_nonlocal_games_and_mipstar.tex:232-248`,
  `def:consistency`.
-/

namespace MIPStarRE.QPBT

open scoped BigOperators MatrixOrder ComplexOrder
open MIPStarRE.LDT MIPStarRE.Quantum

noncomputable section

section Measurement

variable {α β I K : Type*} [Fintype α] [Fintype β]
  [Fintype I] [DecidableEq I] [Fintype K] [DecidableEq K]

/-- Compress every effect of a finite POVM to the coordinate `k₀` of its
ancilla. This is the POVM with effects `J† M_a J`, where `J` inserts `k₀`.
Positivity follows from `Matrix.PosSemidef.submatrix`, and completeness from
the injectivity of the coordinate inclusion. -/
def groundCompressMeasurement (k₀ : K) (M : Quantum.Measurement α (I × K)) :
    Quantum.Measurement α I :=
  Quantum.Measurement.ofSumEqOne
    (fun a => (M.effect a).submatrix (fun i => (i, k₀)) (fun i => (i, k₀)))
    (fun a => Matrix.nonneg_iff_posSemidef.mpr
      ((Matrix.nonneg_iff_posSemidef.mp (M.pos a)).submatrix _)) <| by
    ext i j
    simpa [Matrix.sum_apply, Matrix.submatrix_apply, Matrix.one_apply] using
      congrArg (fun T : Op (I × K) => T (i, k₀) (j, k₀)) M.sum_eq_one

/-- The compressed effect is the principal submatrix at `k₀`. -/
@[simp] theorem ground_compress_measurement_effect
    (k₀ : K) (M : Quantum.Measurement α (I × K)) (a : α) (i j : I) :
    (groundCompressMeasurement k₀ M).effect a i j =
      M.effect a (i, k₀) (j, k₀) := rfl

/-- Ground-coordinate compression commutes with arbitrary finite relabeling
of outcomes, since taking a submatrix commutes with each fiber sum. -/
@[simp] theorem ground_compress_measurement_postprocess
    [DecidableEq α] [DecidableEq β]
    (k₀ : K) (M : Quantum.Measurement α (I × K)) (f : α → β) :
    groundCompressMeasurement k₀ (M.postprocess f) =
      (groundCompressMeasurement k₀ M).postprocess f := by
  apply Quantum.Measurement.ext
  intro b
  ext i j
  simp only [ground_compress_measurement_effect, Quantum.Measurement.postprocess_effect,
    Matrix.sum_apply]

end Measurement

section Bipartite

variable {X α β I J K L : Type*}
  [Fintype X] [DecidableEq X] [Fintype α] [Fintype β]
  [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
  [Fintype K] [DecidableEq K] [Fintype L] [DecidableEq L]

/-- Every bipartite outcome correlation on the independently padded state
equals the correlation of the compressed POVMs on the original state.
Neither normalization nor equality of the player spaces is required. -/
theorem vector_qform_ground_compress_measurement
    (k₀ : K) (l₀ : L) (ψ : EuclideanSpace ℂ (I × J))
    (A : Quantum.Measurement α (I × K)) (B : Quantum.Measurement β (J × L))
    (a : α) (b : β) :
    vectorQForm (padState k₀ l₀ ψ) (heteroKron (A.effect a) (B.effect b)) =
      vectorQForm ψ (heteroKron
        ((groundCompressMeasurement k₀ A).effect a)
        ((groundCompressMeasurement l₀ B).effect b)) := by
  exact stateQForm_padState k₀ l₀ ψ _ _ _ _ (fun _ _ => rfl) (fun _ _ => rfl)

/-- The averaged off-diagonal consistency defect is exactly preserved by
ground-coordinate compression on independently padded bipartite states.
This applies to any finite question distribution and any pair of POVM families. -/
theorem consistency_defect_ground_compress_measurement [DecidableEq α]
    (μ : Distribution X) (k₀ : K) (l₀ : L) (ψ : EuclideanSpace ℂ (I × J))
    (A : X → Quantum.Measurement α (I × K))
    (B : X → Quantum.Measurement α (J × L)) :
    consistencyDefect μ
        (fun x a => heteroKron ((A x).effect a) 1)
        (fun x a => heteroKron 1 ((B x).effect a)) (padState k₀ l₀ ψ) =
      consistencyDefect μ
        (fun x a => heteroKron ((groundCompressMeasurement k₀ (A x)).effect a) 1)
        (fun x a => heteroKron 1 ((groundCompressMeasurement l₀ (B x)).effect a)) ψ := by
  unfold consistencyDefect
  apply avgOver_congr
  intro x
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  split_ifs with hab
  · rfl
  · simp only [heteroKron_mul, mul_one, one_mul]
    exact vector_qform_ground_compress_measurement k₀ l₀ ψ (A x) (B x) a b

/-- A consistency bound holds on the independently padded state if and only
if the same bound holds for the compressed measurements on the original state. -/
theorem is_consistent_within_ground_compress_measurement_iff [DecidableEq α]
    (μ : Distribution X) (k₀ : K) (l₀ : L) (ψ : EuclideanSpace ℂ (I × J))
    (A : X → Quantum.Measurement α (I × K))
    (B : X → Quantum.Measurement α (J × L)) (δ : ℝ) :
    IsConsistentWithin μ
        (fun x a => heteroKron ((A x).effect a) 1)
        (fun x a => heteroKron 1 ((B x).effect a)) (padState k₀ l₀ ψ) δ ↔
      IsConsistentWithin μ
        (fun x a => heteroKron ((groundCompressMeasurement k₀ (A x)).effect a) 1)
        (fun x a => heteroKron 1 ((groundCompressMeasurement l₀ (B x)).effect a)) ψ δ := by
  unfold IsConsistentWithin
  rw [consistency_defect_ground_compress_measurement]

/-- Exact consistency preservation also holds after question-dependent
postprocessing. The original outcome types and the two outcome maps may
differ; only the final outcome alphabet is shared. In the application to
`lem:qld-4-7`, these maps include evaluation of the polynomial outcomes. -/
theorem consistency_defect_ground_compress_measurement_postprocess
    {γ : Type*} [Fintype γ] [DecidableEq γ] [DecidableEq α] [DecidableEq β]
    (μ : Distribution X) (k₀ : K) (l₀ : L) (ψ : EuclideanSpace ℂ (I × J))
    (A : X → Quantum.Measurement α (I × K))
    (B : X → Quantum.Measurement β (J × L)) (f : X → α → γ) (g : X → β → γ) :
    consistencyDefect μ
        (fun x c => heteroKron (((A x).postprocess (f x)).effect c) 1)
        (fun x c => heteroKron 1 (((B x).postprocess (g x)).effect c))
        (padState k₀ l₀ ψ) =
      consistencyDefect μ
        (fun x c => heteroKron
          (((groundCompressMeasurement k₀ (A x)).postprocess (f x)).effect c) 1)
        (fun x c => heteroKron 1
          (((groundCompressMeasurement l₀ (B x)).postprocess (g x)).effect c)) ψ := by
  simpa only [ground_compress_measurement_postprocess] using
    consistency_defect_ground_compress_measurement μ k₀ l₀ ψ
      (fun x => (A x).postprocess (f x)) (fun x => (B x).postprocess (g x))

end Bipartite

/-- Compressing the existing completed Naimark dilation at `none` recovers
the original POVM as a measurement, by its established effect identity. -/
@[simp] theorem ground_compress_dilated_measurement
    {α I : Type} [Fintype α] [DecidableEq α] [Fintype I] [DecidableEq I]
    (a₀ : α) (M : Quantum.Measurement α I) :
    groundCompressMeasurement none (dilatedMeasurement a₀ M) = M := by
  apply Quantum.Measurement.ext
  intro a
  ext i j
  exact dilatedMeasurement_compression a₀ a M i j

end

end MIPStarRE.QPBT
