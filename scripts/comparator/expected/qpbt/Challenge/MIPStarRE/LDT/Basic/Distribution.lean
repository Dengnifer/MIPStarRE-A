import Mathlib
import Challenge.MIPStarRE.LDT.Basic.ParametersBase
import Challenge.MIPStarRE.Quantum.FiniteMatrix.NormalizedTrace

/-! Challenge mirror of `MIPStarRE/LDT/Basic/Distribution.lean`.

One challenge module per contributing library module, importing the
mirrors of the library modules this one imports.  The partition is
what makes Lean generate the same auxiliary declarations, under the
same names, as the library does. -/

open scoped BigOperators MatrixOrder Matrix ComplexOrder
namespace MIPStarRE.LDT

-- source: MIPStarRE/LDT/Basic/Distribution.lean:22-27  (MIPStarRE.LDT.Distribution)
/-- A finite-support weighted distribution with nonnegative real-valued weights. -/
structure Distribution (α : Type*) where
  support : Finset α := ∅
  weight : α → Error := fun _ => 0
  nonnegative : ∀ a, 0 ≤ weight a := by intro _; positivity
  outsideSupport : ∀ a, a ∉ support → weight a = 0 := by intro _ _; rfl
namespace Distribution

-- source: MIPStarRE/LDT/Basic/Distribution.lean:31-33  (MIPStarRE.LDT.Distribution.totalWeight)
/-- The total mass carried by the explicit support of a distribution. -/
def totalWeight {α : Type*} (𝒟 : Distribution α) : Error :=
  ∑ a ∈ 𝒟.support, 𝒟.weight a

-- source: MIPStarRE/LDT/Basic/Distribution.lean:35-37  (MIPStarRE.LDT.Distribution.IsProbability)
/-- A `Distribution` is probabilistic when its total mass is exactly `1`. -/
def IsProbability {α : Type*} (𝒟 : Distribution α) : Prop :=
  𝒟.totalWeight = 1

-- source: MIPStarRE/LDT/Basic/Distribution.lean:39-52  (MIPStarRE.LDT.Distribution.map)
/-- Push a finite-support distribution forward along a map.

This is the project `Distribution` analogue of `PMF.map`.  The support is the
image of the original finite support, and each new weight is the sum of the
weights in the corresponding fiber. -/
noncomputable def map {α β : Type*} [DecidableEq β]
    (𝒟 : Distribution α) (e : α → β) : Distribution β where
  support := 𝒟.support.image e
  weight := fun b => ∑ a ∈ 𝒟.support.filter (fun a => e a = b), 𝒟.weight a
  nonnegative := fun _ => Finset.sum_nonneg fun a _ => 𝒟.nonnegative a
  outsideSupport := fun _ hb =>
    Finset.sum_eq_zero fun a ha =>
      (hb (Finset.mem_image.mpr
        ⟨a, (Finset.mem_filter.mp ha).1, (Finset.mem_filter.mp ha).2⟩)).elim

-- source: MIPStarRE/LDT/Basic/Distribution.lean:65-72  (MIPStarRE.LDT.Distribution.map_totalWeight)
/-- Push-forward preserves total mass. -/
theorem map_totalWeight {α β : Type*} [DecidableEq β]
    (𝒟 : Distribution α) (e : α → β) :
    (𝒟.map e).totalWeight = 𝒟.totalWeight := by
  simpa [totalWeight, map] using
    (Finset.sum_fiberwise_of_maps_to
      (s := 𝒟.support) (t := 𝒟.support.image e) (g := e)
      (fun a ha => Finset.mem_image.mpr ⟨a, ha, rfl⟩) 𝒟.weight)
end Distribution
namespace Distribution.IsProbability

-- source: MIPStarRE/LDT/Basic/Distribution.lean:154-158  (MIPStarRE.LDT.Distribution.IsProbability.map)
/-- Push-forward preserves the probability invariant. -/
theorem map {α β : Type*} [DecidableEq β]
    {𝒟 : Distribution α} (h𝒟 : 𝒟.IsProbability) (e : α → β) :
    (𝒟.map e).IsProbability := by
  simpa [Distribution.IsProbability, Distribution.map_totalWeight] using h𝒟
end Distribution.IsProbability

-- source: MIPStarRE/LDT/Basic/Distribution.lean:228-230  (MIPStarRE.LDT.avgOver)
/-- Average a scalar function against the stored finite support of a distribution. -/
def avgOver {α : Type*} (𝒟 : Distribution α) (f : α → Error) : Error :=
  ∑ a ∈ 𝒟.support, 𝒟.weight a * f a
namespace Distribution

-- source: MIPStarRE/LDT/Basic/Distribution.lean:414-427  (MIPStarRE.LDT.Distribution.uniformOnFinset)
/-- The uniform distribution on a specified finite support.

The stored support is `s`, and the weight of a point is the elementary finite
uniform weight `1 / s.card` on `s` and `0` off `s`.  When the support is empty
this gives the zero sub-probability distribution, matching the convention used
for degenerate filtered supports in the LDT development. -/
noncomputable def uniformOnFinset {α : Type*} (s : Finset α) : Distribution α :=
  letI := Classical.decEq α
  { support := s
    weight := fun a => if a ∈ s then 1 / (s.card : Error) else 0
    nonnegative := fun _ => by
      split_ifs <;> positivity
    outsideSupport := fun _ ha => by
      simp [ha] }

-- source: MIPStarRE/LDT/Basic/Distribution.lean:430-432 (simp context)
@[simp]
theorem uniformOnFinset_support {α : Type*} (s : Finset α) :
    (uniformOnFinset s).support = s := rfl

-- source: MIPStarRE/LDT/Basic/Distribution.lean:433-439  (MIPStarRE.LDT.Distribution.uniformOnFinset_weight)
@[simp]
theorem uniformOnFinset_weight {α : Type*} [DecidableEq α] (s : Finset α) (a : α) :
    (uniformOnFinset s).weight a =
      if a ∈ s then 1 / (s.card : Error) else 0 := by
  by_cases ha : a ∈ s
  · simp [uniformOnFinset, ha]
  · simp [uniformOnFinset, ha]

-- source: MIPStarRE/LDT/Basic/Distribution.lean:441-457  (MIPStarRE.LDT.Distribution.uniformOnFinset_isProbability)
/-- A nonempty finite support gives a probability distribution. -/
theorem uniformOnFinset_isProbability {α : Type*} (s : Finset α) (hs : s.Nonempty) :
    (uniformOnFinset s).IsProbability := by
  classical
  dsimp [IsProbability, totalWeight]
  simp_rw [uniformOnFinset_weight]
  have hcard_nat : s.card ≠ 0 := Finset.card_ne_zero.mpr hs
  have hcard : (s.card : Error) ≠ 0 := by
    exact_mod_cast hcard_nat
  have hsum :
      (∑ a ∈ s, if a ∈ s then 1 / (s.card : Error) else 0) =
        ∑ _a ∈ s, 1 / (s.card : Error) := by
    refine Finset.sum_congr rfl ?_
    intro a ha
    simp [ha]
  rw [hsum]
  simp [Finset.sum_const, hcard]
end Distribution

-- source: MIPStarRE/LDT/Basic/Distribution.lean:489-492  (MIPStarRE.LDT.uniformDistribution)
/-- The uniform distribution on a nonempty finite type. -/
noncomputable def uniformDistribution (α : Type*)
    [Fintype α] [DecidableEq α] [Nonempty α] : Distribution α :=
  Distribution.uniformOnFinset Finset.univ

-- source: MIPStarRE/LDT/Basic/Distribution.lean:510-515  (MIPStarRE.LDT.uniformDistribution_isProbability)
/-- The uniform distribution is a genuine probability distribution. -/
theorem uniformDistribution_isProbability (α : Type*)
    [Fintype α] [DecidableEq α] [Nonempty α] :
    (uniformDistribution α).IsProbability := by
  simpa [uniformDistribution] using
    Distribution.uniformOnFinset_isProbability (Finset.univ : Finset α) Finset.univ_nonempty
end MIPStarRE.LDT
