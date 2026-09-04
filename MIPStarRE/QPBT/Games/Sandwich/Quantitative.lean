import MIPStarRE.QPBT.Games.Sandwich.Support

/-! # Quantitative sandwiched-measurement estimate

This module proves the palindromic measurement construction and the linear
quantitative sandwich estimate used by the public facade.

## References

Blueprint `blueprint/src/chapter/ch12_qpbt_games.tex:454-507`; paper
`references/qpbt-paper/06_nonlocal_games_and_mipstar.tex:465-501`.
-/

open scoped BigOperators MatrixOrder Matrix ComplexOrder

namespace MIPStarRE.QPBT

open MIPStarRE.LDT hiding Measurement
open MIPStarRE.Quantum
open DistanceCalculus

namespace SandwichInternal

set_option maxHeartbeats 400000 in
/-- Replacing the two outer copies and the inner marginal in a joint
projective effect costs two outer distances and one inner distance. -/
private theorem sqrt_opFamilyDistSq_joint_sandwich_le
    {X α β ιA ιB : Type*}
    [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB]
    (μ : Distribution X) (J : X → Measurement (α × β) ιA)
    (G : X → Measurement α ιB) (P : X → Measurement β ιB)
    (ψ : EuclideanSpace ℂ (ιA × ιB)) (q d : ℝ)
    (hJ : ∀ x, MIPStarRE.QPBT.Measurement.IsProjective (J x))
    (hG : ∀ x, MIPStarRE.QPBT.Measurement.IsProjective (G x))
    (hq : opFamilyDistSq μ
      (fun x a => heteroKron (((J x).postprocess Prod.fst).effect a) 1)
      (fun x a => heteroKron 1 ((G x).effect a)) ψ ≤ q)
    (hd : opFamilyDistSq μ
      (fun x b => heteroKron (((J x).postprocess Prod.snd).effect b) 1)
      (fun x b => heteroKron 1 ((P x).effect b)) ψ ≤ d) :
    Real.sqrt (opFamilyDistSq μ
      (fun x ab => heteroKron ((J x).effect ab) 1)
      (fun x ab => heteroKron 1
        ((G x).effect ab.1 * (P x).effect ab.2 * (G x).effect ab.1)) ψ) ≤
      2 * Real.sqrt q + Real.sqrt d := by
  classical
  let JA : X → Measurement α ιA := fun x => (J x).postprocess Prod.fst
  let JB : X → Measurement β ιA := fun x => (J x).postprocess Prod.snd
  let JL : X → Measurement (α × β) (ιA × ιB) := fun x =>
    DistanceCalculus.leftPlacedMeasurement (ιB := ιB) (J x)
  let JAL : X → Measurement α (ιA × ιB) := fun x =>
    DistanceCalculus.leftPlacedMeasurement (ιB := ιB) (JA x)
  let JBL : X → Measurement β (ιA × ιB) := fun x =>
    DistanceCalculus.leftPlacedMeasurement (ιB := ιB) (JB x)
  let GR : X → Measurement α (ιA × ιB) := fun x =>
    DistanceCalculus.rightPlacedMeasurement (ιA := ιA) (G x)
  let PR : X → Measurement β (ιA × ιB) := fun x =>
    DistanceCalculus.rightPlacedMeasurement (ιA := ιA) (P x)
  let F₀ : X → (α × β) → Op (ιA × ιB) := fun x ab => (JL x).effect ab
  let F₁ : X → (α × β) → Op (ιA × ιB) := fun x ab =>
    ((GR x).effect ab.1 * (JAL x).effect ab.1) * (JBL x).effect ab.2
  let F₂ : X → (α × β) → Op (ιA × ιB) := fun x ab =>
    ((GR x).effect ab.1 * (JAL x).effect ab.1) * (PR x).effect ab.2
  let F₃ : X → (α × β) → Op (ιA × ιB) := fun x ab =>
    ((GR x).effect ab.1 * (PR x).effect ab.2) * (GR x).effect ab.1
  have hq' : opFamilyDistSq μ (fun x a => (JAL x).effect a)
      (fun x a => (GR x).effect a) ψ ≤ q := by
    simpa [JAL, JA, GR, DistanceCalculus.leftPlacedMeasurement,
      DistanceCalculus.rightPlacedMeasurement,
      MIPStarRE.Quantum.Measurement.ofSumEqOne] using hq
  have hd' : opFamilyDistSq μ (fun x b => (JBL x).effect b)
      (fun x b => (PR x).effect b) ψ ≤ d := by
    simpa [JBL, JB, PR, DistanceCalculus.leftPlacedMeasurement,
      DistanceCalculus.rightPlacedMeasurement,
      MIPStarRE.Quantum.Measurement.ofSumEqOne] using hd
  have hS₀ (x : X) (a : α) :
      (1 - ∑ ab : α × β, if ab.1 = a then
        ((JL x).effect ab)ᴴ * (JL x).effect ab else 0).PosSemidef := by
    apply Matrix.le_iff.mp
    calc
      (∑ ab : α × β, if ab.1 = a then
          ((JL x).effect ab)ᴴ * (JL x).effect ab else 0) =
          ∑ b : β, ((JL x).effect (a, b))ᴴ * (JL x).effect (a, b) := by
        rw [Fintype.sum_prod_type]
        rw [Fintype.sum_eq_single a]
        · simp
        · intro a' ha'
          simp [ha']
      _ ≤ 1 := measurement_pair_fiber_sum_adjoint_mul_le_one (JL x) a
  have hstep₀raw : opFamilyDistSq μ
      (fun x (ab : α × β) => (JL x).effect ab * (JAL x).effect ab.1)
      (fun x (ab : α × β) => (JL x).effect ab * (GR x).effect ab.1) ψ ≤ q :=
    opFamilyDistSq_mul_fiber_le μ JAL GR
      (fun (ab : α × β) (_ : X) => ab.1)
      (fun x (ab : α × β) => (JL x).effect ab) ψ q hS₀ hq'
  have hstep₀ : opFamilyDistSq μ F₀ F₁ ψ ≤ q := by
    calc
      opFamilyDistSq μ F₀ F₁ ψ = opFamilyDistSq μ
          (fun x (ab : α × β) => (JL x).effect ab * (JAL x).effect ab.1)
          (fun x (ab : α × β) => (JL x).effect ab * (GR x).effect ab.1) ψ := by
        apply DistanceCalculus.opFamilyDistSq_congr
        · intro x ab
          symm
          simp only [F₀, JL, JAL, DistanceCalculus.leftPlacedMeasurement,
            MIPStarRE.Quantum.Measurement.ofSumEqOne]
          change heteroKron ((J x).effect ab) 1 *
              heteroKron ((JA x).effect ab.1) 1 =
            heteroKron ((J x).effect ab) 1
          rw [heteroKron_mul, effect_mul_postprocess_effect
            (J x) (hJ x) Prod.fst ab.1 ab, if_pos rfl, mul_one]
        · intro x ab
          simp only [F₁, JL, GR, JAL, JBL,
            DistanceCalculus.leftPlacedMeasurement,
            DistanceCalculus.rightPlacedMeasurement,
            MIPStarRE.Quantum.Measurement.ofSumEqOne]
          change (heteroKron 1 ((G x).effect ab.1) *
                heteroKron ((JA x).effect ab.1) 1) *
              heteroKron ((JB x).effect ab.2) 1 =
            heteroKron ((J x).effect ab) 1 *
              heteroKron 1 ((G x).effect ab.1)
          rw [heteroKron_mul, heteroKron_mul, heteroKron_mul]
          simp only [one_mul, mul_one]
          congr 1
          simpa only [JA, JB] using postprocess_product_eq_effect
            (J x) (hJ x) Prod.fst Prod.snd ab (by
              intro z hz₁ hz₂
              exact Prod.ext hz₁ hz₂)
      _ ≤ q := hstep₀raw
  have hS₁ (x : X) (b : β) :
      (1 - ∑ ab : α × β, if ab.2 = b then
        (((GR x).effect ab.1 * (JAL x).effect ab.1)ᴴ *
          ((GR x).effect ab.1 * (JAL x).effect ab.1)) else 0).PosSemidef := by
    apply Matrix.le_iff.mp
    calc
      (∑ ab : α × β, if ab.2 = b then
          (((GR x).effect ab.1 * (JAL x).effect ab.1)ᴴ *
            ((GR x).effect ab.1 * (JAL x).effect ab.1)) else 0) =
          ∑ a : α, heteroKron ((JA x).effect a) ((G x).effect a) := by
        rw [Fintype.sum_prod_type]
        apply Finset.sum_congr rfl
        intro a _
        rw [Fintype.sum_eq_single b]
        · simp only [if_pos]
          have hp := heteroKron_isProj
            (postprocess_isProjective (J x) (hJ x) Prod.fst a) (hG x a)
          simp only [GR, JAL, DistanceCalculus.rightPlacedMeasurement,
            DistanceCalculus.leftPlacedMeasurement,
            MIPStarRE.Quantum.Measurement.ofSumEqOne]
          simp only [heteroKron_mul, one_mul, mul_one]
          rw [hp.isSelfAdjoint.isHermitian.eq, hp.isIdempotentElem.eq]
        · intro b' hb'
          simp [hb']
      _ ≤ 1 := matched_tensor_sum_le_one (JA x) (G x)
  have hstep₁raw : opFamilyDistSq μ
      (fun x (ab : α × β) =>
        ((GR x).effect ab.1 * (JAL x).effect ab.1) * (JBL x).effect ab.2)
      (fun x (ab : α × β) =>
        ((GR x).effect ab.1 * (JAL x).effect ab.1) * (PR x).effect ab.2)
      ψ ≤ d :=
    opFamilyDistSq_mul_fiber_le μ JBL PR
      (fun (ab : α × β) (_ : X) => ab.2)
      (fun x (ab : α × β) => (GR x).effect ab.1 * (JAL x).effect ab.1)
      ψ d hS₁ hd'
  have hstep₁ : opFamilyDistSq μ F₁ F₂ ψ ≤ d := by
    simpa only [F₁, F₂] using hstep₁raw
  have hS₂ (x : X) (a : α) :
      (1 - ∑ ab : α × β, if ab.1 = a then
        (((GR x).effect ab.1 * (PR x).effect ab.2)ᴴ *
          ((GR x).effect ab.1 * (PR x).effect ab.2)) else 0).PosSemidef := by
    apply Matrix.le_iff.mp
    calc
      (∑ ab : α × β, if ab.1 = a then
          (((GR x).effect ab.1 * (PR x).effect ab.2)ᴴ *
            ((GR x).effect ab.1 * (PR x).effect ab.2)) else 0) =
          rightTensor (ι₁ := ιA)
            (∑ b : β, ((G x).effect a * (P x).effect b)ᴴ *
              ((G x).effect a * (P x).effect b)) := by
        rw [Fintype.sum_prod_type, Fintype.sum_eq_single a]
        · simp only [if_pos]
          rw [← rightTensor_finset_sum]
          apply Finset.sum_congr rfl
          intro b _
          simp only [GR, PR, DistanceCalculus.rightPlacedMeasurement,
            MIPStarRE.Quantum.Measurement.ofSumEqOne]
          simp only [heteroKron_mul, one_mul]
          change (rightTensor (ι₁ := ιA)
              ((G x).effect a * (P x).effect b))ᴴ *
                rightTensor (ι₁ := ιA) ((G x).effect a * (P x).effect b) =
            rightTensor (ι₁ := ιA)
              (((G x).effect a * (P x).effect b)ᴴ *
                ((G x).effect a * (P x).effect b))
          rw [rightTensor_conjTranspose, rightTensor_mul_rightTensor]
        · intro a' ha'
          simp [ha']
      _ ≤ rightTensor (ι₁ := ιA) (1 : Op ιB) :=
        rightTensor_mono
          (projective_mul_measurement_sum_adjoint_mul_le_one
            ((G x).effect a) (hG x a) (P x))
      _ = 1 := rightTensor_one
  have hstep₂raw : opFamilyDistSq μ
      (fun x (ab : α × β) =>
        ((GR x).effect ab.1 * (PR x).effect ab.2) * (JAL x).effect ab.1)
      (fun x (ab : α × β) =>
        ((GR x).effect ab.1 * (PR x).effect ab.2) * (GR x).effect ab.1)
      ψ ≤ q :=
    opFamilyDistSq_mul_fiber_le μ JAL GR
      (fun (ab : α × β) (_ : X) => ab.1)
      (fun x (ab : α × β) => (GR x).effect ab.1 * (PR x).effect ab.2)
      ψ q hS₂ hq'
  have hstep₂ : opFamilyDistSq μ F₂ F₃ ψ ≤ q := by
    calc
      opFamilyDistSq μ F₂ F₃ ψ = opFamilyDistSq μ
          (fun x (ab : α × β) => ((GR x).effect ab.1 * (PR x).effect ab.2) *
            (JAL x).effect ab.1)
          (fun x (ab : α × β) => ((GR x).effect ab.1 * (PR x).effect ab.2) *
            (GR x).effect ab.1) ψ := by
        apply DistanceCalculus.opFamilyDistSq_congr
        · intro x ab
          simp only [F₂, GR, PR, JAL,
            DistanceCalculus.leftPlacedMeasurement,
            DistanceCalculus.rightPlacedMeasurement,
            MIPStarRE.Quantum.Measurement.ofSumEqOne]
          change heteroKron 1 ((G x).effect ab.1) *
              heteroKron ((JA x).effect ab.1) 1 *
                heteroKron 1 ((P x).effect ab.2) =
            (heteroKron 1 ((G x).effect ab.1) *
              heteroKron 1 ((P x).effect ab.2)) *
              heteroKron ((JA x).effect ab.1) 1
          simp only [heteroKron_mul, one_mul, mul_one]
        · intro _ _
          rfl
      _ ≤ q := hstep₂raw
  have htri₀ := sqrt_opFamilyDistSq_triangle μ F₀ F₁ F₃ ψ
  have htri₁ := sqrt_opFamilyDistSq_triangle μ F₁ F₂ F₃ ψ
  have hs₀ := Real.sqrt_le_sqrt hstep₀
  have hs₁ := Real.sqrt_le_sqrt hstep₁
  have hs₂ := Real.sqrt_le_sqrt hstep₂
  calc
    Real.sqrt (opFamilyDistSq μ
        (fun x ab => heteroKron ((J x).effect ab) 1)
        (fun x ab => heteroKron 1
          ((G x).effect ab.1 * (P x).effect ab.2 * (G x).effect ab.1)) ψ) =
        Real.sqrt (opFamilyDistSq μ F₀ F₃ ψ) := by
      apply congrArg Real.sqrt
      apply DistanceCalculus.opFamilyDistSq_congr
      · intro x ab
        rfl
      · intro x ab
        simp only [F₃, GR, PR, DistanceCalculus.rightPlacedMeasurement,
          MIPStarRE.Quantum.Measurement.ofSumEqOne]
        rw [heteroKron_mul, heteroKron_mul]
        simp
    _ ≤
        Real.sqrt (opFamilyDistSq μ F₀ F₁ ψ) +
          Real.sqrt (opFamilyDistSq μ F₁ F₃ ψ) := htri₀
    _ ≤ Real.sqrt (opFamilyDistSq μ F₀ F₁ ψ) +
        (Real.sqrt (opFamilyDistSq μ F₁ F₂ ψ) +
          Real.sqrt (opFamilyDistSq μ F₂ F₃ ψ)) := by gcongr
    _ ≤ 2 * Real.sqrt q + Real.sqrt d := by
      linarith only [hs₀, hs₁, hs₂]

/-- The palindromic effects form a POVM when each constituent measurement is
projective. This is `lem:ld-sandwich-measurement`, the measurement assertion
implicit in `lem:ld-sandwich`; blueprint `ch12_qpbt_games.tex:489-507`, paper
`references/qpbt-paper/06_nonlocal_games_and_mipstar.tex:484-494`. -/
theorem sandwichProduct_isMeasurement {k : ℕ} {X ι : Type*}
    [Fintype ι] [DecidableEq ι] {Γ : Fin k → Type*}
    [∀ i, Fintype (Γ i)] (G : (i : Fin k) → X → Measurement (Γ i) ι)
    (hG : ∀ i x, MIPStarRE.QPBT.Measurement.IsProjective (G i x)) (x : X) :
    (∀ g : (i : Fin k) → Γ i,
      0 ≤ sandwichProduct (fun i x' a => (G i x').effect a) x g) ∧
      (∑ g : (i : Fin k) → Γ i,
        sandwichProduct (fun i x' a => (G i x').effect a) x g) = 1 := by
  classical
  induction k with
  | zero =>
      constructor
      · intro g
        change 0 ≤ (1 : Op ι)
        exact Matrix.PosSemidef.one.nonneg
      · simp [sandwichProduct, sandwichProductCore]
  | succ k ih =>
      cases k with
      | zero =>
          constructor
          · intro g
            change 0 ≤ (G 0 x).effect (g 0)
            exact (G 0 x).pos (g 0)
          · change
              (∑ g : (i : Fin 1) → Γ i,
                (G 0 x).effect (g 0)) = 1
            calc
              (∑ g : (i : Fin 1) → Γ i, (G 0 x).effect (g 0)) =
                  ∑ p : Γ 0 × ((i : Fin 0) → Γ i.castSucc),
                    (G 0 x).effect (((Fin.snocEquiv Γ) p) 0) := by
                exact Fintype.sum_equiv (Fin.snocEquiv Γ).symm _ _
                  (by intro g; rw [Equiv.apply_symm_apply])
              _ = ∑ a : Γ 0, (G 0 x).effect a := by
                rw [Fintype.sum_prod_type]
                apply Finset.sum_congr rfl
                intro a _
                simp only [Fintype.sum_unique]
                congr 1
              _ = 1 := (G 0 x).sum_eq_one
      | succ k =>
          have hprev := ih
            (G := fun i x' => G i.castSucc x')
            (hG := fun i x' => hG i.castSucc x')
          constructor
          · intro g
            change 0 ≤
              (G (Fin.last (k + 1)) x).effect (g (Fin.last (k + 1))) *
                sandwichProductCore (k + 1) (fun i => Γ i.castSucc)
                  (fun i a => (G i.castSucc x).effect a)
                  (fun i => g i.castSucc) *
                (G (Fin.last (k + 1)) x).effect (g (Fin.last (k + 1)))
            have hinner := hprev.1 (fun i => g i.castSucc)
            apply Matrix.nonneg_iff_posSemidef.mpr
            have hpos :
                (((G (Fin.last (k + 1)) x).effect (g (Fin.last (k + 1))))ᴴ *
                  sandwichProductCore (k + 1) (fun i => Γ i.castSucc)
                    (fun i a => (G i.castSucc x).effect a)
                    (fun i => g i.castSucc) *
                  (G (Fin.last (k + 1)) x).effect
                    (g (Fin.last (k + 1)))).PosSemidef :=
              (Matrix.nonneg_iff_posSemidef.mp hinner).conjTranspose_mul_mul_same _
            rw [MIPStarRE.QPBT.DistanceCalculus.measurement_effect_hermitian] at hpos
            exact hpos
          · change
              (∑ g : (i : Fin (k + 2)) → Γ i,
                sandwichProductCore (k + 2) Γ
                  (fun i a => (G i x).effect a) g) = 1
            calc
              (∑ g : (i : Fin (k + 2)) → Γ i,
                  sandwichProductCore (k + 2) Γ
                    (fun i a => (G i x).effect a) g) =
                  ∑ p : Γ (Fin.last (k + 1)) ×
                      ((i : Fin (k + 1)) → Γ i.castSucc),
                    sandwichProductCore (k + 2) Γ
                      (fun i a => (G i x).effect a) ((Fin.snocEquiv Γ) p) := by
                exact Fintype.sum_equiv (Fin.snocEquiv Γ).symm _ _
                  (by intro g; rw [Equiv.apply_symm_apply])
              _ = ∑ a : Γ (Fin.last (k + 1)),
                    ∑ g : (i : Fin (k + 1)) → Γ i.castSucc,
                      (G (Fin.last (k + 1)) x).effect a *
                        sandwichProductCore (k + 1) (fun i => Γ i.castSucc)
                          (fun i b => (G i.castSucc x).effect b) g *
                        (G (Fin.last (k + 1)) x).effect a := by
                rw [Fintype.sum_prod_type]
                apply Finset.sum_congr rfl
                intro a _
                apply Finset.sum_congr rfl
                intro g _
                simp [sandwichProductCore]
              _ = ∑ a : Γ (Fin.last (k + 1)),
                    (G (Fin.last (k + 1)) x).effect a *
                      (∑ g : (i : Fin (k + 1)) → Γ i.castSucc,
                        sandwichProductCore (k + 1) (fun i => Γ i.castSucc)
                          (fun i b => (G i.castSucc x).effect b) g) *
                      (G (Fin.last (k + 1)) x).effect a := by
                apply Finset.sum_congr rfl
                intro a _
                rw [Finset.mul_sum, Finset.sum_mul]
              _ = ∑ a : Γ (Fin.last (k + 1)),
                    (G (Fin.last (k + 1)) x).effect a := by
                have hprevSum := hprev.2
                change
                  (∑ g : (i : Fin (k + 1)) → Γ i.castSucc,
                    sandwichProductCore (k + 1) (fun i => Γ i.castSucc)
                      (fun i b => (G i.castSucc x).effect b) g) = 1 at hprevSum
                apply Finset.sum_congr rfl
                intro a _
                rw [hprevSum, mul_one,
                  (hG (Fin.last (k + 1)) x a).isIdempotentElem.eq]
              _ = 1 := (G (Fin.last (k + 1)) x).sum_eq_one

/-- Splitting the last outcome from a tuple of length at least two exposes the
recursive palindromic product. -/
private theorem sandwichProduct_snoc {k : ℕ} {X ι : Type*}
    [Fintype ι] [DecidableEq ι] {Γ : Fin (k + 2) → Type*}
    [∀ i, Fintype (Γ i)]
    (G : (i : Fin (k + 2)) → X → Measurement (Γ i) ι)
    (x : X) (p : Γ (Fin.last (k + 1)) ×
      ((i : Fin (k + 1)) → Γ i.castSucc)) :
    sandwichProduct (fun i x' a => (G i x').effect a) x
        ((Fin.snocEquiv Γ) p) =
      (G (Fin.last (k + 1)) x).effect p.1 *
        sandwichProduct (fun i x' a => (G i.castSucc x').effect a) x p.2 *
      (G (Fin.last (k + 1)) x).effect p.1 := by
  simp [sandwichProduct, sandwichProductCore]

/-- Iterating the joint replacement estimate gives a linear bound for the
square root of the distance to the palindromic measurement. -/
private theorem sqrt_opFamilyDistSq_sandwichProduct_le
    {k : ℕ} {X ιA ιB : Type*} {Γ : Fin k → Type*}
    [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB]
    [∀ i, Fintype (Γ i)] [∀ i, DecidableEq (Γ i)]
    (μ : Distribution X) (G : (i : Fin k) → X → Measurement (Γ i) ιB)
    (A : X → Measurement ((i : Fin k) → Γ i) ιA)
    (ψ : EuclideanSpace ℂ (ιA × ιB)) (q : ℝ)
    (hG : ∀ i x, MIPStarRE.QPBT.Measurement.IsProjective (G i x))
    (hA : ∀ x, MIPStarRE.QPBT.Measurement.IsProjective (A x))
    (hq : ∀ i, opFamilyDistSq μ
      (fun x a => heteroKron (((A x).postprocess (fun g => g i)).effect a) 1)
      (fun x a => heteroKron 1 ((G i x).effect a)) ψ ≤ q) :
    Real.sqrt (opFamilyDistSq μ
      (fun x g => heteroKron ((A x).effect g) 1)
      (fun x g => heteroKron 1
        (sandwichProduct (fun i x' a => (G i x').effect a) x g)) ψ) ≤
      2 * (k : ℝ) * Real.sqrt q := by
  classical
  induction k using Nat.twoStepInduction with
  | zero =>
      have hAone (x : X) (g : (i : Fin 0) → Γ i) : (A x).effect g = 1 := by
        calc
          (A x).effect g = (A x).effect default := by
            exact congrArg (A x).effect (Subsingleton.elim g default)
          _ = ∑ h : (i : Fin 0) → Γ i, (A x).effect h := by
            rw [Fintype.sum_unique]
          _ = 1 := (A x).sum_eq_one
      have hdistzero : opFamilyDistSq μ
          (fun x g => heteroKron ((A x).effect g) 1)
          (fun x g => heteroKron 1
            (sandwichProduct (fun i x' a => (G i x').effect a) x g)) ψ =
          opFamilyDistSq μ
            (fun (_ : X) (_ : (i : Fin 0) → Γ i) => (1 : Op (ιA × ιB)))
            (fun (_ : X) (_ : (i : Fin 0) → Γ i) => (1 : Op (ιA × ιB))) ψ := by
        apply DistanceCalculus.opFamilyDistSq_congr
        · intro x g
          simp [hAone, heteroKron_one_one]
        · intro x g
          simp [sandwichProduct, sandwichProductCore, heteroKron_one_one]
      rw [hdistzero]
      simp [opFamilyDistSq, applyOperatorToState, MIPStarRE.LDT.avgOver_zero]
  | one =>
      let e : ((i : Fin 1) → Γ i) ≃ Γ default := Equiv.piUnique Γ
      have heval : Function.Injective
          (fun g : (i : Fin 1) → Γ i => g default) := e.injective
      have hdist : opFamilyDistSq μ
          (fun x g => heteroKron ((A x).effect g) 1)
          (fun x g => heteroKron 1
            (sandwichProduct (fun i x' a => (G i x').effect a) x g)) ψ ≤ q := by
        rw [DistanceCalculus.opFamilyDistSq_reindex μ e]
        calc
          opFamilyDistSq μ
              (fun x a => heteroKron ((A x).effect (e.symm a)) 1)
              (fun x a => heteroKron 1
                (sandwichProduct (fun i x' b => (G i x').effect b) x
                  (e.symm a))) ψ =
              opFamilyDistSq μ
                (fun x a => heteroKron
                  (((A x).postprocess (fun g => g default)).effect a) 1)
                (fun x a => heteroKron 1 ((G default x).effect a)) ψ := by
            apply DistanceCalculus.opFamilyDistSq_congr
            · intro x a
              congr 1
              have heffect :=
                postprocess_effect_of_injective (A x) (fun g => g default) heval
                  (e.symm a)
              change ((A x).postprocess (fun g => g default)).effect
                (e (e.symm a)) = (A x).effect (e.symm a) at heffect
              rw [e.apply_symm_apply] at heffect
              exact heffect.symm
            · intro x a
              have hi : (0 : Fin 1) = default := Subsingleton.elim _ _
              cases hi
              change heteroKron 1 ((G default x).effect ((e.symm a) default)) =
                heteroKron 1 ((G default x).effect a)
              rw [show (e.symm a) default = a from e.apply_symm_apply a]
          _ ≤ q := hq default
      have hsqrt := Real.sqrt_le_sqrt hdist
      norm_num
      linarith [Real.sqrt_nonneg q]
  | more k _ ih =>
      let e := (Fin.snocEquiv Γ).symm
      let J : X → Measurement
          (Γ (Fin.last (k + 1)) × ((i : Fin (k + 1)) → Γ i.castSucc)) ιA :=
        fun x => (A x).postprocess e
      let Apre : X → Measurement ((i : Fin (k + 1)) → Γ i.castSucc) ιA :=
        fun x => (A x).postprocess
          (fun (g : (j : Fin (k + 2)) → Γ j) (i : Fin (k + 1)) => g i.castSucc)
      let P : X → Measurement ((i : Fin (k + 1)) → Γ i.castSucc) ιB :=
        fun x => MIPStarRE.Quantum.Measurement.ofSumEqOne
          (fun g => sandwichProduct
            (fun i x' a => (G i.castSucc x').effect a) x g)
          (sandwichProduct_isMeasurement
            (fun i x' => G i.castSucc x')
            (fun i x' => hG i.castSucc x') x).1
          (sandwichProduct_isMeasurement
            (fun i x' => G i.castSucc x')
            (fun i x' => hG i.castSucc x') x).2
      have hJ (x : X) : MIPStarRE.QPBT.Measurement.IsProjective (J x) :=
        postprocess_isProjective (A x) (hA x) e
      have hApre (x : X) : MIPStarRE.QPBT.Measurement.IsProjective (Apre x) :=
        postprocess_isProjective (A x) (hA x)
          (fun (g : (j : Fin (k + 2)) → Γ j) (i : Fin (k + 1)) => g i.castSucc)
      have hJfst (x : X) (a : Γ (Fin.last (k + 1))) :
          ((J x).postprocess Prod.fst).effect a =
            ((A x).postprocess (fun g => g (Fin.last (k + 1)))).effect a := by
        rw [postprocess_postprocess_effect]
        change ((A x).postprocess
          (fun g => ((Fin.snocEquiv Γ).symm g).1)).effect a = _
        rfl
      have hJsnd (x : X) (g : (i : Fin (k + 1)) → Γ i.castSucc) :
          ((J x).postprocess Prod.snd).effect g = (Apre x).effect g := by
        rw [postprocess_postprocess_effect]
        change ((A x).postprocess
          (fun h => ((Fin.snocEquiv Γ).symm h).2)).effect g = _
        rfl
      have hqpre : ∀ i, opFamilyDistSq μ
          (fun x a => heteroKron
            (((Apre x).postprocess (fun g => g i)).effect a) 1)
          (fun x a => heteroKron 1 ((G i.castSucc x).effect a)) ψ ≤ q := by
        intro i
        calc
          opFamilyDistSq μ
              (fun x a => heteroKron
                (((Apre x).postprocess (fun g => g i)).effect a) 1)
              (fun x a => heteroKron 1 ((G i.castSucc x).effect a)) ψ =
              opFamilyDistSq μ
                (fun x a => heteroKron
                  (((A x).postprocess (fun g => g i.castSucc)).effect a) 1)
                (fun x a => heteroKron 1 ((G i.castSucc x).effect a)) ψ := by
            apply DistanceCalculus.opFamilyDistSq_congr
            · intro x a
              congr 1
              rw [postprocess_postprocess_effect]
            · intro _ _
              rfl
          _ ≤ q := hq i.castSucc
      have hprefix := ih
        (G := fun i x => G i.castSucc x) (A := Apre)
        (hG := fun i x => hG i.castSucc x) (hA := hApre) (hq := hqpre)
      have hlast : opFamilyDistSq μ
          (fun x a => heteroKron (((J x).postprocess Prod.fst).effect a) 1)
          (fun x a => heteroKron 1 ((G (Fin.last (k + 1)) x).effect a)) ψ ≤ q := by
        calc
          opFamilyDistSq μ
              (fun x a => heteroKron (((J x).postprocess Prod.fst).effect a) 1)
              (fun x a => heteroKron 1
                ((G (Fin.last (k + 1)) x).effect a)) ψ =
              opFamilyDistSq μ
                (fun x a => heteroKron
                  (((A x).postprocess
                    (fun g => g (Fin.last (k + 1)))).effect a) 1)
                (fun x a => heteroKron 1
                  ((G (Fin.last (k + 1)) x).effect a)) ψ := by
            apply DistanceCalculus.opFamilyDistSq_congr
            · intro x a
              rw [hJfst]
            · intro _ _
              rfl
          _ ≤ q := hq (Fin.last (k + 1))
      have hprefix' : opFamilyDistSq μ
          (fun x g => heteroKron (((J x).postprocess Prod.snd).effect g) 1)
          (fun x g => heteroKron 1 ((P x).effect g)) ψ =
          opFamilyDistSq μ
            (fun x g => heteroKron ((Apre x).effect g) 1)
            (fun x g => heteroKron 1
              (sandwichProduct (fun i x' a => (G i.castSucc x').effect a)
                x g)) ψ := by
        apply DistanceCalculus.opFamilyDistSq_congr
        · intro x g
          rw [hJsnd]
        · intro x g
          rfl
      have hjoint := sqrt_opFamilyDistSq_joint_sandwich_le μ J
        (fun x => G (Fin.last (k + 1)) x) P ψ q
        (opFamilyDistSq μ
          (fun x g => heteroKron (((J x).postprocess Prod.snd).effect g) 1)
          (fun x g => heteroKron 1 ((P x).effect g)) ψ)
        hJ (fun x => hG (Fin.last (k + 1)) x) hlast le_rfl
      rw [hprefix'] at hjoint
      have hdist : opFamilyDistSq μ
          (fun x g => heteroKron ((A x).effect g) 1)
          (fun x g => heteroKron 1
            (sandwichProduct (fun i x' a => (G i x').effect a) x g)) ψ =
          opFamilyDistSq μ
            (fun x p => heteroKron ((J x).effect p) 1)
            (fun x p => heteroKron 1
              ((G (Fin.last (k + 1)) x).effect p.1 *
                (P x).effect p.2 *
                (G (Fin.last (k + 1)) x).effect p.1)) ψ := by
        rw [DistanceCalculus.opFamilyDistSq_reindex μ e]
        apply DistanceCalculus.opFamilyDistSq_congr
        · intro x p
          congr 1
          symm
          simpa only [J, e, Equiv.apply_symm_apply] using
            postprocess_effect_of_injective (A x) e e.injective (e.symm p)
        · intro x p
          congr 1
          simpa only [e, Equiv.symm_symm, Equiv.apply_symm_apply, P,
            MIPStarRE.Quantum.Measurement.ofSumEqOne] using
            sandwichProduct_snoc G x p
      rw [hdist]
      calc
        Real.sqrt (opFamilyDistSq μ
            (fun x p => heteroKron ((J x).effect p) 1)
            (fun x p => heteroKron 1
              ((G (Fin.last (k + 1)) x).effect p.1 *
                (P x).effect p.2 *
                (G (Fin.last (k + 1)) x).effect p.1)) ψ) ≤
            2 * Real.sqrt q + Real.sqrt (opFamilyDistSq μ
              (fun x g => heteroKron ((Apre x).effect g) 1)
              (fun x g => heteroKron 1
                (sandwichProduct (fun i x' a => (G i.castSucc x').effect a)
                  x g)) ψ) := hjoint
        _ ≤ 2 * ((k + 2 : ℕ) : ℝ) * Real.sqrt q := by
          norm_num [Nat.cast_add] at hprefix ⊢
          linarith

/-- The sandwiched simultaneous-measurement estimate of `lem:ld-sandwich`.
One universal asymptotic constant applies independently of the distribution,
measurements, state, and error parameters. Blueprint
`ch12_qpbt_games.tex:454-480`, paper
`references/qpbt-paper/06_nonlocal_games_and_mipstar.tex:465-501`. -/
theorem consistencyDefect_sandwich_le :
    ∃ C₀ : ℝ, 1 ≤ C₀ ∧
      ∀ {k : ℕ} {X Y ιA ιB : Type*} {R Γ : Fin k → Type*}
        [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y] [Nonempty Y]
        [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB]
        [∀ i, Fintype (R i)] [∀ i, DecidableEq (R i)]
        [∀ i, Fintype (Γ i)] [∀ i, DecidableEq (Γ i)]
        (μ : Distribution X)
        (eval : (i : Fin k) → Γ i → Y → R i)
        (G : (i : Fin k) → X → Measurement (Γ i) ιB)
        (A : X → Measurement ((i : Fin k) → Γ i) ιA)
        (ψ : EuclideanSpace ℂ (ιA × ιB)) (ε δ : ℝ),
      μ.IsProbability → ‖ψ‖ = 1 → 0 < ε → 0 ≤ δ →
      (∀ i x, MIPStarRE.QPBT.Measurement.IsProjective (G i x)) →
      (∀ x, MIPStarRE.QPBT.Measurement.IsProjective (A x)) →
      (∀ i (g g' : Γ i), g ≠ g' →
        avgOver (uniformDistribution Y)
          (fun y => if eval i g y = eval i g' y then 1 else 0) ≤ ε) →
      (∀ i, consistencyDefect (Distribution.prod μ (uniformDistribution Y))
        (fun xy a => heteroKron (((A xy.1).postprocess
          (fun g => eval i (g i) xy.2)).effect a) 1)
        (fun xy a => heteroKron 1 (((G i xy.1).postprocess
          (fun g => eval i g xy.2)).effect a)) ψ ≤ δ) →
      consistencyDefect (Distribution.prod μ (uniformDistribution Y))
        (fun xy a => heteroKron (((A xy.1).postprocess
          (evalFunctionTuple eval xy.2)).effect a) 1)
        (fun xy a => heteroKron 1 (∑ g : (i : Fin k) → Γ i,
          if evalFunctionTuple eval xy.2 g = a then
            sandwichProduct (fun i x h => (G i x).effect h) xy.1 g else 0)) ψ ≤
        C₀ * (k : ℝ) * Real.sqrt (δ + ε) := by
  refine ⟨8, by norm_num, ?_⟩
  intro k X Y ιA ιB R Γ
    _ _ _ _ _ _ _ _ _ _ _ _ _ μ eval G A ψ ε δ
    hμ hψ hε hδ hG hA hcollision hevaluated
  classical
  have herr : 0 ≤ δ + ε := add_nonneg hδ (le_of_lt hε)
  have hcodeword (i : Fin k) :
      consistencyDefect μ
          (fun x g => heteroKron
            (((A x).postprocess (fun h => h i)).effect g) 1)
          (fun x g => heteroKron 1 ((G i x).effect g)) ψ ≤ δ + ε := by
    have hcollisionStep := consistencyDefect_codewords_le_evaluated_add
      μ (fun x => (A x).postprocess (fun h => h i)) (fun x => G i x)
      ψ (eval i) ε hμ hψ (le_of_lt hε) (hcollision i)
    have hcollisionStep' :
        consistencyDefect μ
            (fun x g => heteroKron
              (((A x).postprocess (fun h => h i)).effect g) 1)
            (fun x g => heteroKron 1 ((G i x).effect g)) ψ ≤
          consistencyDefect (Distribution.prod μ (uniformDistribution Y))
            (fun xy a => heteroKron (((A xy.1).postprocess
              (fun h => eval i (h i) xy.2)).effect a) 1)
            (fun xy a => heteroKron 1 (((G i xy.1).postprocess
              (fun g => eval i g xy.2)).effect a)) ψ + ε := by
      simpa only [postprocess_postprocess_effect] using hcollisionStep
    calc
      _ ≤ _ := hcollisionStep'
      _ ≤ δ + ε := by linarith [hevaluated i]
  have hcoordinate (i : Fin k) : opFamilyDistSq μ
      (fun x g => heteroKron (((A x).postprocess (fun h => h i)).effect g) 1)
      (fun x g => heteroKron 1 ((G i x).effect g)) ψ ≤
        2 * (δ + ε) := by
    let AL : X → Measurement (Γ i) (ιA × ιB) := fun x =>
      leftPlacedMeasurement ((A x).postprocess (fun h => h i))
    let BR : X → Measurement (Γ i) (ιA × ιB) := fun x =>
      rightPlacedMeasurement (G i x)
    have hdistance := opFamilyDistSq_le_two_mul_consistencyDefect μ AL BR ψ
    have hdistance' : opFamilyDistSq μ
        (fun x g => heteroKron (((A x).postprocess (fun h => h i)).effect g) 1)
        (fun x g => heteroKron 1 ((G i x).effect g)) ψ ≤
          2 * consistencyDefect μ
            (fun x g => heteroKron
              (((A x).postprocess (fun h => h i)).effect g) 1)
            (fun x g => heteroKron 1 ((G i x).effect g)) ψ := by
      simpa only [AL, BR, leftPlacedMeasurement, rightPlacedMeasurement,
        MIPStarRE.Quantum.Measurement.ofSumEqOne] using hdistance
    exact hdistance'.trans
      (mul_le_mul_of_nonneg_left (hcodeword i) (by norm_num))
  let B : X → Measurement ((i : Fin k) → Γ i) ιB := fun x =>
    MIPStarRE.Quantum.Measurement.ofSumEqOne
      (fun g => sandwichProduct (fun i x' a => (G i x').effect a) x g)
      (sandwichProduct_isMeasurement G hG x).1
      (sandwichProduct_isMeasurement G hG x).2
  have hroot := sqrt_opFamilyDistSq_sandwichProduct_le
    μ G A ψ (2 * (δ + ε)) hG hA hcoordinate
  have hroot' : Real.sqrt (opFamilyDistSq μ
      (fun x g => heteroKron ((A x).effect g) 1)
      (fun x g => heteroKron 1 ((B x).effect g)) ψ) ≤
      4 * (k : ℝ) * Real.sqrt (δ + ε) := by
    have hsqrtTwo : Real.sqrt 2 ≤ 2 := by
      nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2), Real.sqrt_nonneg 2]
    have hsqrtError : Real.sqrt (2 * (δ + ε)) ≤
        2 * Real.sqrt (δ + ε) := by
      rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)]
      exact mul_le_mul_of_nonneg_right hsqrtTwo (Real.sqrt_nonneg _)
    have hrootB : Real.sqrt (opFamilyDistSq μ
        (fun x g => heteroKron ((A x).effect g) 1)
        (fun x g => heteroKron 1 ((B x).effect g)) ψ) ≤
        2 * (k : ℝ) * Real.sqrt (2 * (δ + ε)) := by
      simpa only [B, MIPStarRE.Quantum.Measurement.ofSumEqOne] using hroot
    calc
      Real.sqrt (opFamilyDistSq μ
          (fun x g => heteroKron ((A x).effect g) 1)
          (fun x g => heteroKron 1 ((B x).effect g)) ψ) ≤
          2 * (k : ℝ) * Real.sqrt (2 * (δ + ε)) := hrootB
      _ ≤ 2 * (k : ℝ) * (2 * Real.sqrt (δ + ε)) := by
        gcongr
      _ = 4 * (k : ℝ) * Real.sqrt (δ + ε) := by ring
  let AL : X → Measurement ((i : Fin k) → Γ i) (ιA × ιB) :=
    fun x => leftPlacedMeasurement (A x)
  let BR : X → Measurement ((i : Fin k) → Γ i) (ιA × ιB) :=
    fun x => rightPlacedMeasurement (B x)
  have hone : IsProj (1 : Op ιB) := IsStarProjection.one _
  have hAL (x : X) : MIPStarRE.QPBT.Measurement.IsProjective (AL x) := by
    intro g
    exact heteroKron_isProj (hA x g) hone
  have hbaseRaw := consistencyDefect_le_sqrt_of_projective_left
    μ AL BR ψ hμ hψ hAL
  have hbase : consistencyDefect μ
      (fun x g => heteroKron ((A x).effect g) 1)
      (fun x g => heteroKron 1 ((B x).effect g)) ψ ≤
      8 * (k : ℝ) * Real.sqrt (δ + ε) := by
    have hbase' : consistencyDefect μ
        (fun x g => heteroKron ((A x).effect g) 1)
        (fun x g => heteroKron 1 ((B x).effect g)) ψ ≤
        Real.sqrt (2 * opFamilyDistSq μ
          (fun x g => heteroKron ((A x).effect g) 1)
          (fun x g => heteroKron 1 ((B x).effect g)) ψ) := by
      simpa only [AL, BR, leftPlacedMeasurement, rightPlacedMeasurement,
        MIPStarRE.Quantum.Measurement.ofSumEqOne] using hbaseRaw
    have hsqrtTwo : Real.sqrt 2 ≤ 2 := by
      nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2), Real.sqrt_nonneg 2]
    calc
      consistencyDefect μ
          (fun x g => heteroKron ((A x).effect g) 1)
          (fun x g => heteroKron 1 ((B x).effect g)) ψ ≤
          Real.sqrt (2 * opFamilyDistSq μ
            (fun x g => heteroKron ((A x).effect g) 1)
            (fun x g => heteroKron 1 ((B x).effect g)) ψ) := hbase'
      _ = Real.sqrt 2 * Real.sqrt (opFamilyDistSq μ
          (fun x g => heteroKron ((A x).effect g) 1)
          (fun x g => heteroKron 1 ((B x).effect g)) ψ) := by
        rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)]
      _ ≤ 2 * Real.sqrt (opFamilyDistSq μ
          (fun x g => heteroKron ((A x).effect g) 1)
          (fun x g => heteroKron 1 ((B x).effect g)) ψ) := by
        gcongr
      _ ≤ 2 * (4 * (k : ℝ) * Real.sqrt (δ + ε)) := by
        gcongr
      _ = 8 * (k : ℝ) * Real.sqrt (δ + ε) := by ring
  have hprocessed := consistencyDefect_prod_postprocess_le
    μ A B ψ (fun y => evalFunctionTuple eval y)
  have htarget : consistencyDefect (Distribution.prod μ (uniformDistribution Y))
      (fun xy a => heteroKron (((A xy.1).postprocess
        (evalFunctionTuple eval xy.2)).effect a) 1)
      (fun xy a => heteroKron 1 (∑ g : (i : Fin k) → Γ i,
        if evalFunctionTuple eval xy.2 g = a then
          sandwichProduct (fun i x h => (G i x).effect h) xy.1 g else 0)) ψ ≤
      consistencyDefect μ
        (fun x g => heteroKron ((A x).effect g) 1)
        (fun x g => heteroKron 1 ((B x).effect g)) ψ := by
    simpa only [B, MIPStarRE.Quantum.Measurement.ofSumEqOne,
      MIPStarRE.Quantum.Measurement.postprocess_effect, Finset.sum_filter] using hprocessed
  exact htarget.trans hbase

end SandwichInternal

end MIPStarRE.QPBT
