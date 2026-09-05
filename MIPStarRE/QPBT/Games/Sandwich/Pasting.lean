import MIPStarRE.QPBT.Games.Sandwich.Quantitative

/-! # Support lemmas for the pasting estimate

This module collects the quantitative steps of the proof of `lem:pasting`
recorded in `docs/paper-gaps/qpbt_pasting-product-error.tex`.

## References

Blueprint `blueprint/src/chapter/ch12_qpbt_games.tex:960-1050`; paper
`references/qpbt-paper/06_nonlocal_games_and_mipstar.tex:504-525`.
-/

open scoped BigOperators MatrixOrder Matrix ComplexOrder

namespace MIPStarRE.QPBT

open MIPStarRE.LDT hiding Measurement
open MIPStarRE.Quantum
open DistanceCalculus

/-- Cross consistency of the coarse-grained second codeword family. Under the
register exchange `eq:pasting-1-sym` of the second comparison in
`eq:pasting-1`, the self-consistency `eq:pasting-2` of the answer measurement
and that second comparison itself, the coarse second codeword family is
consistent with its own copy on the opposite factor, with the square-root loss
of the triangle estimate `fact:triangle-for-simeq`. This is the step of
`lem:pasting` that uses the symmetric convention; blueprint
`ch12_qpbt_games.tex:960-990`. -/
theorem consistencyDefect_codeword_cross_le
    {X Y₁ Y₂ R₁ R₂ Γ₂ ι : Type*}
    [Fintype X] [DecidableEq X] [Fintype Y₁] [DecidableEq Y₁]
    [Fintype Y₂] [DecidableEq Y₂] [Fintype R₁] [DecidableEq R₁]
    [Fintype R₂] [DecidableEq R₂] [Fintype Γ₂] [DecidableEq Γ₂]
    [Fintype ι] [DecidableEq ι]
    (D : Distribution ((X × Y₁) × Y₂)) (eval₂ : Γ₂ → Y₂ → R₂)
    (G₂ : X → Measurement Γ₂ ι) (A : ((X × Y₁) × Y₂) → Measurement (R₁ × R₂) ι)
    (ψ : EuclideanSpace ℂ (ι × ι)) (δ : ℝ)
    (hD : D.IsProbability) (hψ : ‖ψ‖ = 1)
    (hsym : consistencyDefect D
      (fun q a₂ => heteroKron (((G₂ q.1.1).postprocess
        (fun g => eval₂ g q.2)).effect a₂) 1)
      (fun q a₂ => heteroKron 1 (((A q).postprocess Prod.snd).effect a₂)) ψ ≤ δ)
    (hself : consistencyDefect D (fun q a => heteroKron ((A q).effect a) 1)
      (fun q a => heteroKron 1 ((A q).effect a)) ψ ≤ δ)
    (hfwd : consistencyDefect D
      (fun q a₂ => heteroKron (((A q).postprocess Prod.snd).effect a₂) 1)
      (fun q a₂ => heteroKron 1 (((G₂ q.1.1).postprocess
        (fun g => eval₂ g q.2)).effect a₂)) ψ ≤ δ) :
    consistencyDefect D
      (fun q a₂ => heteroKron (((G₂ q.1.1).postprocess
        (fun g => eval₂ g q.2)).effect a₂) 1)
      (fun q a₂ => heteroKron 1 (((G₂ q.1.1).postprocess
        (fun g => eval₂ g q.2)).effect a₂)) ψ ≤ δ + 2 * Real.sqrt (2 * δ) := by
  classical
  have hmarg : consistencyDefect D
      (fun q a₂ => heteroKron (((A q).postprocess Prod.snd).effect a₂) 1)
      (fun q a₂ => heteroKron 1 (((A q).postprocess Prod.snd).effect a₂)) ψ ≤ δ :=
    le_trans (consistencyDefect_postprocess_le D A A ψ Prod.snd) hself
  have hmain := consistencyDefect_trans_le D
    (fun q => Measurement.leftPlacement (ιB := ι)
      ((G₂ q.1.1).postprocess (fun g => eval₂ g q.2)))
    (fun q => Measurement.rightPlacement (ιA := ι) ((A q).postprocess Prod.snd))
    (fun q => Measurement.leftPlacement (ιB := ι) ((A q).postprocess Prod.snd))
    (fun q => Measurement.rightPlacement (ιA := ι)
      ((G₂ q.1.1).postprocess (fun g => eval₂ g q.2)))
    ψ δ δ δ hD hψ hsym hmarg hfwd
  have hδδ : δ + δ = 2 * δ := by ring
  rw [hδδ] at hmain
  exact hmain

end MIPStarRE.QPBT
