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

/-- The coarse one-sided commutator estimate of `lem:pasting`. The two
comparisons `eq:pasting-1` move the coarse codeword families of the two
generators onto the joint projective answer measurement placed on the opposite
factor, so the two coarse families approximately commute on the state, with one
universal constant. This is step 3 of the proof of the adopted statement in
`docs/paper-gaps/qpbt_pasting-product-error.tex`; blueprint
`ch12_qpbt_games.tex:960-990`. -/
theorem exists_coarse_commutator_bound :
    ∃ C : ℝ, 1 ≤ C ∧
      ∀ {X Y₁ Y₂ R₁ R₂ Γ₁ Γ₂ ι : Type*}
        [Fintype X] [DecidableEq X] [Fintype Y₁] [DecidableEq Y₁]
        [Fintype Y₂] [DecidableEq Y₂] [Fintype R₁] [DecidableEq R₁]
        [Fintype R₂] [DecidableEq R₂] [Fintype Γ₁] [DecidableEq Γ₁]
        [Fintype Γ₂] [DecidableEq Γ₂] [Fintype ι] [DecidableEq ι]
        (D : Distribution ((X × Y₁) × Y₂))
        (eval₁ : Γ₁ → Y₁ → R₁) (eval₂ : Γ₂ → Y₂ → R₂)
        (G₁ : X → Measurement Γ₁ ι) (G₂ : X → Measurement Γ₂ ι)
        (A : ((X × Y₁) × Y₂) → Measurement (R₁ × R₂) ι)
        (ψ : EuclideanSpace ℂ (ι × ι)) (δ : ℝ),
        (∀ q, MIPStarRE.QPBT.Measurement.IsProjective (A q)) →
        consistencyDefect D
          (fun q a₁ => heteroKron (((A q).postprocess Prod.fst).effect a₁) 1)
          (fun q a₁ => heteroKron 1 (((G₁ q.1.1).postprocess
            (fun g => eval₁ g q.1.2)).effect a₁)) ψ ≤ δ →
        consistencyDefect D
          (fun q a₂ => heteroKron (((A q).postprocess Prod.snd).effect a₂) 1)
          (fun q a₂ => heteroKron 1 (((G₂ q.1.1).postprocess
            (fun g => eval₂ g q.2)).effect a₂)) ψ ≤ δ →
        opFamilyDistSq D
          (fun q (a : R₁ × R₂) => heteroKron 1
            (((G₁ q.1.1).postprocess (fun g => eval₁ g q.1.2)).effect a.1 *
                ((G₂ q.1.1).postprocess (fun g => eval₂ g q.2)).effect a.2 -
              ((G₂ q.1.1).postprocess (fun g => eval₂ g q.2)).effect a.2 *
                ((G₁ q.1.1).postprocess (fun g => eval₁ g q.1.2)).effect a.1))
          (fun _ _ => 0) ψ ≤ C * δ := by
  classical
  obtain ⟨C₀, hC₀, hcomm⟩ := opDistSq_commutator_right_le
  refine ⟨2 * C₀, by linarith, ?_⟩
  intro X Y₁ Y₂ R₁ R₂ Γ₁ Γ₂ ι _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    D eval₁ eval₂ G₁ G₂ A ψ δ hA h₁ h₂
  set P : ((X × Y₁) × Y₂) → Measurement R₁ ι :=
    fun q => (G₁ q.1.1).postprocess (fun g => eval₁ g q.1.2) with hPdef
  set Q : ((X × Y₁) × Y₂) → Measurement R₂ ι :=
    fun q => (G₂ q.1.1).postprocess (fun g => eval₂ g q.2) with hQdef
  let f₁ : R₁ ≃ (Unit × R₁) :=
    ⟨fun a => ((), a), fun p => p.2, fun _ => rfl, by rintro ⟨⟨⟩, a⟩; rfl⟩
  let f₂ : R₂ ≃ (Unit × R₂) :=
    ⟨fun a => ((), a), fun p => p.2, fun _ => rfl, by rintro ⟨⟨⟩, a⟩; rfl⟩
  let eB : ((Unit × R₁) × R₂) ≃ (R₁ × R₂) :=
    ⟨fun p => (p.1.2, p.2), fun a => (((), a.1), a.2),
      by rintro ⟨⟨⟨⟩, a⟩, b⟩; rfl, fun _ => rfl⟩
  let AR : ((X × Y₁) × Y₂) → Measurement (Unit × R₁) ι :=
    fun q => Measurement.congrAlphabet f₁.symm (P q)
  let DR : ((X × Y₁) × Y₂) → Measurement (Unit × R₂) ι :=
    fun q => Measurement.congrAlphabet f₂.symm (Q q)
  let BJ : ((X × Y₁) × Y₂) → Measurement ((Unit × R₁) × R₂) ι :=
    fun q => Measurement.congrAlphabet eB (A q)
  have hBJ : ∀ q, MIPStarRE.QPBT.Measurement.IsProjective (BJ q) :=
    fun q => Measurement.isProjective_congrAlphabet eB (A q) (hA q)
  have hd₁ : opFamilyDistSq D
      (fun q a₁ => heteroKron (((A q).postprocess Prod.fst).effect a₁) 1)
      (fun q a₁ => heteroKron 1 ((P q).effect a₁)) ψ ≤ 2 * δ := by
    refine le_trans (opFamilyDistSq_le_two_mul_consistencyDefect D
      (fun q => Measurement.leftPlacement ((A q).postprocess Prod.fst))
      (fun q => Measurement.rightPlacement (P q)) ψ) ?_
    simp only [Measurement.leftPlacement_effect,
      Measurement.rightPlacement_effect]
    linarith [h₁]
  have hd₂ : opFamilyDistSq D
      (fun q a₂ => heteroKron (((A q).postprocess Prod.snd).effect a₂) 1)
      (fun q a₂ => heteroKron 1 ((Q q).effect a₂)) ψ ≤ 2 * δ := by
    refine le_trans (opFamilyDistSq_le_two_mul_consistencyDefect D
      (fun q => Measurement.leftPlacement ((A q).postprocess Prod.snd))
      (fun q => Measurement.rightPlacement (Q q)) ψ) ?_
    simp only [Measurement.leftPlacement_effect,
      Measurement.rightPlacement_effect]
    linarith [h₂]
  have hBA : opFamilyDistSq D
      (fun q ab => heteroKron
        (((BJ q).postprocess (fun abc => abc.1)).effect ab) 1)
      (fun q ab => heteroKron 1 ((AR q).effect ab)) ψ ≤ 2 * δ := by
    refine le_trans (le_of_eq ?_) hd₁
    rw [opFamilyDistSq_reindex D f₁
      (fun q a₁ => heteroKron (((A q).postprocess Prod.fst).effect a₁) 1)
      (fun q a₁ => heteroKron 1 ((P q).effect a₁)) ψ]
    refine opFamilyDistSq_congr D _ _ _ _ ψ (fun q ab => ?_) (fun q ab => rfl)
    congr 1
    rw [Measurement.postprocess_congrAlphabet]
    simp only [Measurement.postprocess_effect]
    refine Finset.sum_congr (Finset.filter_congr fun a _ => ?_) fun _ _ => rfl
    simp [eB, f₁, Prod.ext_iff]
  have hBD : opFamilyDistSq D
      (fun q ac => heteroKron
        (((BJ q).postprocess (fun abc => (abc.1.1, abc.2))).effect ac) 1)
      (fun q ac => heteroKron 1 ((DR q).effect ac)) ψ ≤ 2 * δ := by
    refine le_trans (le_of_eq ?_) hd₂
    rw [opFamilyDistSq_reindex D f₂
      (fun q a₂ => heteroKron (((A q).postprocess Prod.snd).effect a₂) 1)
      (fun q a₂ => heteroKron 1 ((Q q).effect a₂)) ψ]
    refine opFamilyDistSq_congr D _ _ _ _ ψ (fun q ac => ?_) (fun q ac => rfl)
    congr 1
    rw [Measurement.postprocess_congrAlphabet]
    simp only [Measurement.postprocess_effect]
    refine Finset.sum_congr (Finset.filter_congr fun a _ => ?_) fun _ _ => rfl
    simp [eB, f₂, Prod.ext_iff]
  have hconc := hcomm D AR BJ DR ψ (2 * δ) hBJ hBA hBD
  rw [opFamilyDistSq_reindex D eB _ _ ψ] at hconc
  refine le_trans (le_of_eq ?_) (le_trans hconc (le_of_eq (by ring)))
  exact opFamilyDistSq_congr D _ _ _ _ ψ (fun q a => rfl) (fun q a => rfl)

end MIPStarRE.QPBT
