import MIPStarRE.QPBT.Games.Consistency
import MIPStarRE.QPBT.Games.StrategyClasses
import MIPStarRE.QPBT.Games.TypedCondLinear
import MIPStarRE.QPBT.Observables.LineDefs

/-!
# Low-degree polynomial measurements and soundness

This file defines the finite polynomial-measurement index and states the
low-degree soundness theorem used by the QPBT combining argument. Polynomial
outcomes are bounded multivariate polynomials.

## References

The principal definition and theorem are `def:ld-meas` and `lem:ld-soundness` in
`blueprint/src/chapter/ch13_qpbt_test.tex:164-202`. Their paper origin is
`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:243-287,392-480`.
The dimension-divisibility hypothesis is documented in
`docs/paper-gaps/qpbt_ld-dimension-divisibility.tex`.
-/

open scoped BigOperators

namespace MIPStarRE.QPBT

open MIPStarRE.LDT
open MIPStarRE.LDT.Preliminaries
open MIPStarRE.Quantum

noncomputable section

/-!
### Formalization-only auxiliary facts about the ambient low-degree space
-/

/-- Formalization-only auxiliary equivalence splitting an ambient low-degree
vector into its point, seed, and direction blocks. -/
private def ldSpaceSplit (L : LdParams) :
    LdSpace L ≃ ((Fin L.m → ScalarQ L) × ScalarQ L) × (Fin L.m → ScalarQ L) where
  toFun z := ((LdSpace.point z, LdSpace.seed z), LdSpace.direction z)
  invFun p := fun i =>
    match i with
    | .inl (.inl j) => p.1.1 j
    | .inl (.inr _) => p.1.2
    | .inr j => p.2 j
  left_inv z := by
    funext i
    rcases i with (j | u) | j
    · rfl
    · cases u
      rfl
    · rfl
  right_inv p := by
    obtain ⟨⟨a, b⟩, c⟩ := p
    rfl

/-- Formalization-only auxiliary lemma: the point block of a uniformly random
ambient vector is uniform. -/
private theorem map_uniformDistribution_point (L : LdParams) :
    (uniformDistribution (LdSpace L)).map LdSpace.point =
      uniformDistribution (Fin L.m → ScalarQ L) := by
  have hsplit : (uniformDistribution (LdSpace L)).map (ldSpaceSplit L) =
      uniformDistribution (((Fin L.m → ScalarQ L) × ScalarQ L) × (Fin L.m → ScalarQ L)) :=
    uniformDistribution_map_equiv (ldSpaceSplit L)
  calc
    (uniformDistribution (LdSpace L)).map LdSpace.point
        = (((uniformDistribution (LdSpace L)).map (ldSpaceSplit L)).map
            Prod.fst).map Prod.fst := by
          rw [Distribution.map_map, Distribution.map_map]
          rfl
    _ = ((uniformDistribution
          (((Fin L.m → ScalarQ L) × ScalarQ L) × (Fin L.m → ScalarQ L))).map
            Prod.fst).map Prod.fst := by rw [hsplit]
    _ = (uniformDistribution ((Fin L.m → ScalarQ L) × ScalarQ L)).map Prod.fst := by
          rw [uniformDistribution_map_fst]
    _ = uniformDistribution (Fin L.m → ScalarQ L) := uniformDistribution_map_fst

/-- Formalization-only auxiliary lemma: the shared scalar coordinate of a
uniformly random ambient vector is uniform. -/
private theorem map_uniformDistribution_seed (L : LdParams) :
    (uniformDistribution (LdSpace L)).map LdSpace.seed =
      uniformDistribution (ScalarQ L) := by
  have hsplit : (uniformDistribution (LdSpace L)).map (ldSpaceSplit L) =
      uniformDistribution (((Fin L.m → ScalarQ L) × ScalarQ L) × (Fin L.m → ScalarQ L)) :=
    uniformDistribution_map_equiv (ldSpaceSplit L)
  calc
    (uniformDistribution (LdSpace L)).map LdSpace.seed
        = (((uniformDistribution (LdSpace L)).map (ldSpaceSplit L)).map
            Prod.fst).map Prod.snd := by
          rw [Distribution.map_map, Distribution.map_map]
          rfl
    _ = ((uniformDistribution
          (((Fin L.m → ScalarQ L) × ScalarQ L) × (Fin L.m → ScalarQ L))).map
            Prod.fst).map Prod.snd := by rw [hsplit]
    _ = (uniformDistribution ((Fin L.m → ScalarQ L) × ScalarQ L)).map Prod.snd := by
          rw [uniformDistribution_map_fst]
    _ = uniformDistribution (ScalarQ L) := uniformDistribution_map_snd

/-- Formalization-only auxiliary lemma: an admissible field size is positive. -/
private theorem ldParams_q_pos (L : LdParams) : 0 < L.q := by
  obtain ⟨j, -, hj⟩ := L.hq
  rw [hj]
  exact Nat.pow_pos (by norm_num)

/-- Formalization-only auxiliary lemma: the coordinate index of a scalar is
read off from its binary representation. -/
private theorem chiIndex_eq_iff (L : LdParams) (s : ScalarQ L) (i : Fin L.m) :
    chiIndex L s = i ↔
      ((binaryRepresentation L.model s).val / (L.q / L.m)) % L.m = i.val := by
  rw [Fin.ext_iff]
  simp [chiIndex]

/-- Formalization-only auxiliary lemma: every fiber of the coordinate index has
exactly `q / m` elements.  This is the balance property used in
`def:ld-question-distribution`, blueprint `ch13_qpbt_test.tex:34-59`, paper
`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:31-391`. -/
private theorem card_chiIndex_fiber (L : LdParams) (i : Fin L.m) :
    ((Finset.univ : Finset (ScalarQ L)).filter fun s => chiIndex L s = i).card
      = L.q / L.m := by
  have hq : 0 < L.q := ldParams_q_pos L
  have hqk : L.m * (L.q / L.m) = L.q := Nat.mul_div_cancel' L.hdvd
  have hkpos : 0 < L.q / L.m := by
    rcases Nat.eq_zero_or_pos (L.q / L.m) with h | h
    · rw [h, Nat.mul_zero] at hqk
      omega
    · exact h
  have hstep1 :
      ((Finset.univ : Finset (ScalarQ L)).filter fun s => chiIndex L s = i).card
        = ((Finset.univ : Finset (Fin L.q)).filter
            fun n => (n.val / (L.q / L.m)) % L.m = i.val).card := by
    refine Finset.card_equiv (binaryRepresentation L.model) fun s => ?_
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, chiIndex_eq_iff]
  have hstep2 :
      ((Finset.range L.q).filter fun t => (t / (L.q / L.m)) % L.m = i.val)
        = ((Finset.univ : Finset (Fin L.q)).filter
            fun n => (n.val / (L.q / L.m)) % L.m = i.val).image Fin.val := by
    ext t
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_image,
      Finset.mem_univ, true_and]
    constructor
    · rintro ⟨ht, hP⟩
      exact ⟨⟨t, ht⟩, hP, rfl⟩
    · rintro ⟨n, hP, rfl⟩
      exact ⟨n.isLt, hP⟩
  have hstep3 :
      ((Finset.range L.q).filter fun t => (t / (L.q / L.m)) % L.m = i.val)
        = Finset.Ico (i.val * (L.q / L.m)) (i.val * (L.q / L.m) + L.q / L.m) := by
    ext t
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]
    constructor
    · rintro ⟨htq, hP⟩
      have hlt : t / (L.q / L.m) < L.m := by
        rw [Nat.div_lt_iff_lt_mul hkpos]
        omega
      have hdiv : t / (L.q / L.m) = i.val := by
        rwa [Nat.mod_eq_of_lt hlt] at hP
      have hle : t / (L.q / L.m) * (L.q / L.m) ≤ t := Nat.div_mul_le_self t _
      have hupper : t < (i.val + 1) * (L.q / L.m) := by
        rw [← Nat.div_lt_iff_lt_mul hkpos, hdiv]
        omega
      have hexp : (i.val + 1) * (L.q / L.m)
          = i.val * (L.q / L.m) + L.q / L.m := by ring
      rw [hdiv] at hle
      omega
    · rintro ⟨hlo, hhi⟩
      have hexp : (i.val + 1) * (L.q / L.m)
          = i.val * (L.q / L.m) + L.q / L.m := by ring
      have hdiv : t / (L.q / L.m) = i.val := by
        have h1 : i.val ≤ t / (L.q / L.m) := (Nat.le_div_iff_mul_le hkpos).mpr hlo
        have h2 : t / (L.q / L.m) < i.val + 1 := by
          rw [Nat.div_lt_iff_lt_mul hkpos]
          omega
        omega
      refine ⟨?_, ?_⟩
      · have hbound : (i.val + 1) * (L.q / L.m) ≤ L.m * (L.q / L.m) :=
          Nat.mul_le_mul_right _ i.isLt
        omega
      · rw [hdiv, Nat.mod_eq_of_lt i.isLt]
  rw [hstep1, ← Finset.card_image_of_injective
      ((Finset.univ : Finset (Fin L.q)).filter
        fun n => (n.val / (L.q / L.m)) % L.m = i.val) Fin.val_injective,
    ← hstep2, hstep3, Nat.card_Ico]
  omega

/-- Formalization-only auxiliary lemma: the coordinate index of a uniformly
random scalar is uniform.  This is the balance assertion made in
`def:ld-question-distribution`, blueprint `ch13_qpbt_test.tex:34-59`, paper
`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:31-391`. -/
private theorem map_uniformDistribution_chiIndex (L : LdParams) :
    (uniformDistribution (ScalarQ L)).map (chiIndex L) =
      uniformDistribution (Fin L.m) :=
  uniformDistribution_map_of_card_fiber _ (L.q / L.m) (card_chiIndex_fiber L)

/-- Formalization-only auxiliary lemma: zeroing an initial segment of the
coordinates is idempotent. -/
private theorem prefixProjection_prefixProjection (L : LdParams) (i : Fin L.m)
    (v : Fin L.m → ScalarQ L) :
    prefixProjection i (prefixProjection i v) = prefixProjection i v := by
  funext j
  by_cases h : j.val < i.val
  · simp only [prefixProjection, if_pos h]
  · simp only [prefixProjection, if_neg h]

/-- `lem:alnf`: the point and axis-index marginals of the axis line-point
distribution are uniform. Blueprint `ch13_qpbt_test.tex:101-106`, paper
`08_classical_and_quantum_low_degree_tests.tex:243-257`. -/
theorem aLinePointDist_point_marginal_uniform (L : LdParams) :
    (aLinePointDist L).map Prod.snd =
        uniformDistribution (Fin L.m → ScalarQ L) ∧
      (aLinePointDist L).map (fun sample => chiIndex L sample.1.seed) =
        uniformDistribution (Fin L.m) := by
  constructor
  · have hmap : (aLinePointDist L).map Prod.snd
        = (uniformDistribution (LdSpace L)).map LdSpace.point := by
      change ((((uniformDistribution (LdSpace L)).map
          fun z => (ldALineCL L z, ldPointCL L z)).map
          fun s => (aLineDescOf L s.1, LdSpace.point s.2)).map Prod.snd) = _
      rw [Distribution.map_map, Distribution.map_map]
      rfl
    rw [hmap, map_uniformDistribution_point]
  · have hmap : (aLinePointDist L).map (fun sample => chiIndex L sample.1.seed)
        = ((uniformDistribution (LdSpace L)).map LdSpace.seed).map (chiIndex L) := by
      change ((((uniformDistribution (LdSpace L)).map
          fun z => (ldALineCL L z, ldPointCL L z)).map
          fun s => (aLineDescOf L s.1, LdSpace.point s.2)).map
          fun sample => chiIndex L sample.1.seed) = _
      rw [Distribution.map_map, Distribution.map_map, Distribution.map_map]
      rfl
    rw [hmap, map_uniformDistribution_seed, map_uniformDistribution_chiIndex]

/-- The incidence conclusion of `lem:alnf`, blueprint
`ch13_qpbt_test.tex:101-106`, paper
`08_classical_and_quantum_low_degree_tests.tex:243-257`. -/
theorem aLinePointDist_mem_line (L : LdParams) :
    ∀ sample ∈ (aLinePointDist L).support, sample.2 ∈ sample.1.pointSet := by
  intro sample hsample
  have hsupport : (aLinePointDist L).support =
      ((Finset.univ : Finset (LdSpace L)).image
        fun z => (ldALineCL L z, ldPointCL L z)).image
        fun s => (aLineDescOf L s.1, LdSpace.point s.2) := rfl
  rw [hsupport] at hsample
  obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp hsample
  obtain ⟨z, -, rfl⟩ := Finset.mem_image.mp hs
  change LdSpace.point z ∈
    linePoints
      (lineRepMap (coordinateDirection (chiIndex L (LdSpace.seed z)))
        (lineRepMap (coordinateDirection (chiIndex L (LdSpace.seed z)))
          (LdSpace.point z)))
      (coordinateDirection (chiIndex L (LdSpace.seed z)))
  rw [lineRepMap_apply_self]
  exact mem_linePoints_lineRepMap _ _

/-- `lem:dlnf`: the point and prefix-index marginals of the diagonal
line-point distribution are uniform. Blueprint `ch13_qpbt_test.tex:113-118`,
paper `08_classical_and_quantum_low_degree_tests.tex:261-272`. -/
theorem dLinePointDist_point_marginal_uniform (L : LdParams) :
    (dLinePointDist L).map Prod.snd =
        uniformDistribution (Fin L.m → ScalarQ L) ∧
      (dLinePointDist L).map (fun sample => chiIndex L sample.1.seed) =
        uniformDistribution (Fin L.m) := by
  constructor
  · have hmap : (dLinePointDist L).map Prod.snd
        = (uniformDistribution (LdSpace L)).map LdSpace.point := by
      change ((((uniformDistribution (LdSpace L)).map
          fun z => (ldDLineCL L z, ldPointCL L z)).map
          fun s => (dLineDescOf L s.1, LdSpace.point s.2)).map Prod.snd) = _
      rw [Distribution.map_map, Distribution.map_map]
      rfl
    rw [hmap, map_uniformDistribution_point]
  · have hmap : (dLinePointDist L).map (fun sample => chiIndex L sample.1.seed)
        = ((uniformDistribution (LdSpace L)).map LdSpace.seed).map (chiIndex L) := by
      change ((((uniformDistribution (LdSpace L)).map
          fun z => (ldDLineCL L z, ldPointCL L z)).map
          fun s => (dLineDescOf L s.1, LdSpace.point s.2)).map
          fun sample => chiIndex L sample.1.seed) = _
      rw [Distribution.map_map, Distribution.map_map, Distribution.map_map]
      rfl
    rw [hmap, map_uniformDistribution_seed, map_uniformDistribution_chiIndex]

/-- The incidence conclusion of `lem:dlnf`, blueprint
`ch13_qpbt_test.tex:113-118`, paper
`08_classical_and_quantum_low_degree_tests.tex:261-272`. -/
theorem dLinePointDist_mem_line (L : LdParams) :
    ∀ sample ∈ (dLinePointDist L).support, sample.2 ∈ sample.1.pointSet := by
  intro sample hsample
  have hsupport : (dLinePointDist L).support =
      ((Finset.univ : Finset (LdSpace L)).image
        fun z => (ldDLineCL L z, ldPointCL L z)).image
        fun s => (dLineDescOf L s.1, LdSpace.point s.2) := rfl
  rw [hsupport] at hsample
  obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp hsample
  obtain ⟨z, -, rfl⟩ := Finset.mem_image.mp hs
  change LdSpace.point z ∈
    linePoints
      (lineRepMap
        (prefixProjection (chiIndex L (LdSpace.seed z))
          (prefixProjection (chiIndex L (LdSpace.seed z)) (LdSpace.direction z)))
        (lineRepMap
          (prefixProjection (chiIndex L (LdSpace.seed z)) (LdSpace.direction z))
          (LdSpace.point z)))
      (prefixProjection (chiIndex L (LdSpace.seed z))
        (prefixProjection (chiIndex L (LdSpace.seed z)) (LdSpace.direction z)))
  rw [prefixProjection_prefixProjection, lineRepMap_apply_self]
  exact mem_linePoints_lineRepMap _ _

/-- The diagonal direction in every sampled description has the prefix-zero
property of `lem:dlnf`, blueprint `ch13_qpbt_test.tex:113-118`, paper
`08_classical_and_quantum_low_degree_tests.tex:261-272`. -/
theorem dLinePointDist_prefix_zero (L : LdParams) :
    ∀ sample ∈ (dLinePointDist L).support,
      ∀ j : Fin L.m, j.val < (chiIndex L sample.1.seed).val →
        sample.1.direction j = 0 := by
  intro sample hsample
  have hsupport : (dLinePointDist L).support =
      ((Finset.univ : Finset (LdSpace L)).image
        fun z => (ldDLineCL L z, ldPointCL L z)).image
        fun s => (dLineDescOf L s.1, LdSpace.point s.2) := rfl
  rw [hsupport] at hsample
  obtain ⟨s, -, rfl⟩ := Finset.mem_image.mp hsample
  exact LineDesc.diagonal_prefix_zero (dLineDescOf L s.1) rfl

/-- The low-degree question sampler is the typed conditionally linear
distribution on the complete type graph. This is `lem:ld-question-typed-cl`,
blueprint `ch13_qpbt_test.tex:85-95`, which identifies the sampler with
`def:typed-cl-distributions` (`ch12_qpbt_games.tex:1400-1404`); paper
`references/qpbt-paper/07_types.tex:84-94`. -/
theorem ldQuestionDistribution_eq_typedCL (L : LdParams) :
    ldQuestionDistribution L =
      typedCLDistribution (Finset.univ : Finset (Sym2 LdType)) (by simp)
        (ldCL L) (ldCL L) := by
  have hgraph : ∀ hE : (Finset.univ : Finset (Sym2 LdType)).Nonempty,
      graphDistribution (Finset.univ : Finset (Sym2 LdType)) hE =
        uniformDistribution (LdType × LdType) := by
    intro hE
    have hfilter : ((Finset.univ : Finset (LdType × LdType)).filter
        fun ab => Sym2.mk ab.1 ab.2 ∈ (Finset.univ : Finset (Sym2 LdType)))
        = (Finset.univ : Finset (LdType × LdType)) := by
      simp
    change Distribution.uniformOnFinset _ = _
    rw [hfilter]
    rfl
  have hleft : ldQuestionDistribution L =
      Distribution.bind (uniformDistribution (LdType × LdType))
        (fun uv => (uniformDistribution (LdSpace L)).map
          fun z => ((uv.1, ldCL L uv.1 z), (uv.2, ldCL L uv.2 z))) := by
    rw [bind_uniformDistribution_map]
    rfl
  have hright : ∀ hE : (Finset.univ : Finset (Sym2 LdType)).Nonempty,
      typedCLDistribution (Finset.univ : Finset (Sym2 LdType)) hE (ldCL L) (ldCL L) =
        Distribution.bind (uniformDistribution (LdType × LdType))
          (fun uv => (uniformDistribution (LdSpace L)).map
            fun z => ((uv.1, ldCL L uv.1 z), (uv.2, ldCL L uv.2 z))) := by
    intro hE
    have hfamily : (fun uv : LdType × LdType =>
        (clDistribution (ldCL L uv.1) (ldCL L uv.2)).map
          fun xy => ((uv.1, xy.1), (uv.2, xy.2))) =
      fun uv : LdType × LdType => (uniformDistribution (LdSpace L)).map
        fun z => ((uv.1, ldCL L uv.1 z), (uv.2, ldCL L uv.2 z)) := by
      funext uv
      exact Distribution.map_map _ _ _
    change Distribution.bind (graphDistribution _ hE) _ = _
    rw [hgraph hE, hfamily]
  rw [hleft, hright]

/-- Bounded multivariate polynomials form a finite set over a finite coefficient
semiring. This is the finite outcome set required by `def:ld-meas`,
blueprint `ch13_qpbt_test.tex:164-171`, paper
`08_classical_and_quantum_low_degree_tests.tex:394-408`. -/
noncomputable instance polyFuncFintype (m : ℕ) (K : Type*)
    [CommSemiring K] [Fintype K] (d : ℕ) : Fintype ↥(polyFunc m K d) := by
  letI : Finite ↥(polyFunc m K d) := Module.finite_of_finite K
  exact Fintype.ofFinite _

/-- A bounded multivariate polynomial outcome over an arbitrary finite
coefficient semiring. -/
noncomputable abbrev PolyIndex (m : ℕ) (K : Type*) [CommSemiring K]
    [Fintype K] (d : ℕ) := ↥(polyFunc m K d)

/-- A POVM indexed by one bounded multivariate polynomial. -/
noncomputable abbrev PolyMeas (m : ℕ) (K : Type*) [CommSemiring K]
    [Fintype K] [DecidableEq K] (d : ℕ) (ι : Type*)
    [Fintype ι] [DecidableEq ι] :=
  MIPStarRE.Quantum.Measurement (PolyIndex m K d) ι

/-- The dependent family in `def:ld-meas`: component `i` may
have its own coefficient field, number of variables, and degree bound.
Blueprint `ch13_qpbt_test.tex:164-171`, paper
`08_classical_and_quantum_low_degree_tests.tex:394-408`. -/
noncomputable abbrev PolyMeasFamily (k : ℕ) (K : Fin k → Type*)
    [∀ i, CommSemiring (K i)] [∀ i, Fintype (K i)]
    [∀ i, DecidableEq (K i)] (m d : Fin k → ℕ) (ι : Type*)
    [Fintype ι] [DecidableEq ι] :=
  MIPStarRE.Quantum.Measurement ((i : Fin k) → PolyIndex (m i) (K i) (d i)) ι

/-- A simultaneous tuple of `L.k` bounded polynomial representatives. -/
noncomputable abbrev PolyTuple (L : LdParams) :=
  Fin L.k → PolyIndex L.m (ScalarQ L) L.d

/-- The constant-family specialization used by `lem:ld-soundness`. -/
noncomputable abbrev PolyMeasTuple (L : LdParams) (ι : Type*)
    [Fintype ι] [DecidableEq ι] :=
  PolyMeasFamily L.k (fun _ => ScalarQ L) (fun _ => L.m) (fun _ => L.d) ι

/-- Evaluate every component of a polynomial tuple at a point. -/
def evalPolyTupleAt {L : LdParams} (u : Fin L.m → ScalarQ L)
    (g : PolyTuple L) : Fin L.k → ScalarQ L :=
  fun j => MvPolynomial.eval u (g j).1

/-- Embed a geometric point into the ambient coefficient space used by a
point question. -/
def pointSpaceOf (L : LdParams) (u : Fin L.m → ScalarQ L) : LdSpace L :=
  fun i => match i with
  | .inl (.inl j) => u j
  | .inl (.inr _) => 0
  | .inr _ => 0

/-- The typed low-degree point question associated with `u`. -/
def ldPointQuestionOf (L : LdParams) (u : Fin L.m → ScalarQ L) : LdQuestion L :=
  (.point, pointSpaceOf L u)

/-- Read the point component of a low-degree answer, sending answers of the
wrong form to the fixed zero tuple. This total relabeling turns the strategy's
answer measurement into the point POVM used by `lem:ld-soundness`. -/
def ldPointValuesOrZero (L : LdParams) : LdAnswer L → Fin L.k → ScalarQ L
  | .pointVals values => values
  | .alinePolys _ => 0
  | .dlinePolys _ => 0

/-- The quantitative error function in `lem:ld-soundness`.  Its argument order
is `(a, b, ε, q, m, d, k)`. -/
noncomputable def deltaLd (a b ε : ℝ) (q m d k : ℕ) : ℝ :=
  a * Real.rpow (((d * m * k : ℕ) : ℝ)) a *
    (Real.rpow ε b + Real.rpow (q : ℝ) (-b) +
      Real.rpow 2 (-(b * ((m * d : ℕ) : ℝ))))

/-- Quantum soundness of the simultaneous classical low individual degree
test (`lem:ld-soundness`, blueprint lines 135--160; paper theorem and proof
`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:413-458`).

The first two consistency bounds compare the point-answer postprocessing of the
strategy with evaluations of the polynomial measurements. Answers of the wrong
form are folded into the zero tuple so that the point family remains a POVM.

The source reduction still requires proofs of the claimed game correspondence
and of the auxiliary parameter bound. These two open facts are detailed in
`docs/paper-gaps/qpbt_ld-dimension-divisibility.tex` and
`rem:ld-soundness-provider`, and are tracked by issue #16. -/
theorem exists_ld_soundness :
    ∃ a b : ℝ, 1 ≤ a ∧ 0 < b ∧ b ≤ 1 ∧
      ∀ (L : LdParams) (ε : ℝ), 0 < ε →
        ∀ S : Strategy (ldGame L), S.IsProjective → 1 - ε ≤ S.value →
          ∃ GA : PolyMeasTuple L S.ιA, ∃ GB : PolyMeasTuple L S.ιB,
            consistencyDefect (uniformDistribution (Fin L.m → ScalarQ L))
                (fun u outcome =>
                  heteroKron
                    (((S.A (ldPointQuestionOf L u)).postprocess
                      (ldPointValuesOrZero L)).effect outcome) 1)
                (fun u outcome =>
                  heteroKron 1
                    ((GB.postprocess (evalPolyTupleAt u)).effect outcome))
                S.ψ ≤ deltaLd a b ε L.q L.m L.d L.k ∧
            consistencyDefect (uniformDistribution (Fin L.m → ScalarQ L))
                (fun u outcome =>
                  heteroKron
                    ((GA.postprocess (evalPolyTupleAt u)).effect outcome) 1)
                (fun u outcome =>
                  heteroKron 1
                    (((S.B (ldPointQuestionOf L u)).postprocess
                      (ldPointValuesOrZero L)).effect outcome))
                S.ψ ≤ deltaLd a b ε L.q L.m L.d L.k ∧
            consistencyDefect (uniformDistribution Unit)
                (fun _ g => heteroKron (GA.effect g) 1)
                (fun _ g => heteroKron 1 (GB.effect g))
                S.ψ ≤ deltaLd a b ε L.q L.m L.d L.k := by
  sorry

end

end MIPStarRE.QPBT
