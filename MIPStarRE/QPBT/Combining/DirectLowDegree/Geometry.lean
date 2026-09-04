import MIPStarRE.QPBT.Observables.LineDefs
import MIPStarRE.QPBT.Test.PauliBasisTest

/-!
# Geometry for the directly indexed low-degree game

This module defines the parameters, line carrier, and line-point distributions
for the directly indexed low-degree game.

## References

The line-point distributions originate in
`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:243-272`.
The directly indexed repair is documented in
`docs/paper-gaps/qpbt_ld-dimension-divisibility.tex`.
-/

open scoped BigOperators

namespace MIPStarRE.QPBT

open MIPStarRE.LDT
open MIPStarRE.LDT.Preliminaries
open MIPStarRE.Quantum

noncomputable section

/-- Parameters for the directly indexed low-degree game.  Unlike `LdParams`,
this directly indexed line-space construction has no divisibility field: its coordinate index is
sampled from `Fin m` rather than encoded by fibers of `chiIndex`.

This is the direct-index repair described in
`docs/paper-gaps/qpbt_ld-dimension-divisibility.tex`; it is not a second
definition of the source verifier game. -/
structure DirectLdParams where
  q : ℕ
  m : ℕ
  d : ℕ
  k : ℕ
  hm : 1 ≤ m
  hd : 1 ≤ d
  hk : 1 ≤ k
  hq : IsAdmissibleSize q

/-- The canonical scalar model for directly indexed parameters. -/
noncomputable def DirectLdParams.model (D : DirectLdParams) : FixedFieldModel D.q :=
  fixedFieldModel D.q D.hq

/-- The scalar field of a directly indexed low-degree game. -/
abbrev DirectScalarQ (D : DirectLdParams) := D.model.K

/-- The first coordinate, available because directly indexed dimensions are
positive. -/
def DirectLdParams.firstIndex (D : DirectLdParams) : Fin D.m :=
  ⟨0, lt_of_lt_of_le Nat.zero_lt_one D.hm⟩

instance (D : DirectLdParams) : Nonempty (Fin D.m) := ⟨D.firstIndex⟩

/-- The direct game used at the extended dimension of the combining map.  Its
field, degree, and simultaneity parameters are inherited from `P`, while its
dimension is `2 * P.m + 2`; no divisibility assertion is introduced.

The construction has dimension `2 * P.m + 2` without requiring
`2 * P.m + 2 ∣ P.q`; it supplies the directly indexed line and coordinate
spaces used in the dimension-extension argument of
`blueprint/src/chapter/ch15_qpbt_combining.tex:1257-1293`.
-/
def AdmissibleParams.extendedDirectLd (P : AdmissibleParams) : DirectLdParams where
  q := P.q
  m := 2 * P.m + 2
  d := P.d
  k := 1
  hm := by omega
  hd := P.hd
  hk := by decide
  hq := P.hq

/-- A common random sample for the directly indexed question distribution.
The point, coordinate index, and unrestricted direction are mutually uniform. -/
structure DirectLdSpace (D : DirectLdParams) where
  point : Fin D.m → DirectScalarQ D
  index : Fin D.m
  direction : Fin D.m → DirectScalarQ D
  deriving DecidableEq, Fintype

instance (D : DirectLdParams) : Nonempty (DirectLdSpace D) :=
  ⟨⟨0, D.firstIndex, 0⟩⟩

/-- Decompose a direct sample into its point and the remaining independent
coordinates. -/
private def directLdSpacePointEquiv (D : DirectLdParams) :
    DirectLdSpace D ≃
      (Fin D.m → DirectScalarQ D) ×
        (Fin D.m × (Fin D.m → DirectScalarQ D)) where
  toFun sample := (sample.point, sample.index, sample.direction)
  invFun sample := ⟨sample.1, sample.2.1, sample.2.2⟩
  left_inv sample := by cases sample; rfl
  right_inv sample := by cases sample; rfl

/-- Decompose a direct sample into its stored index and the remaining
independent coordinates. -/
private def directLdSpaceIndexEquiv (D : DirectLdParams) :
    DirectLdSpace D ≃
      Fin D.m ×
        ((Fin D.m → DirectScalarQ D) ×
          (Fin D.m → DirectScalarQ D)) where
  toFun sample := (sample.index, sample.point, sample.direction)
  invFun sample := ⟨sample.2.1, sample.1, sample.2.2⟩
  left_inv sample := by cases sample; rfl
  right_inv sample := by cases sample; rfl

/-- Zero the coordinates preceding the directly sampled prefix index. -/
def directPrefixProjection {D : DirectLdParams} (i : Fin D.m)
    (v : Fin D.m → DirectScalarQ D) : Fin D.m → DirectScalarQ D :=
  fun j => if j.val < i.val then 0 else v j

/-- Canonical line descriptions whose coordinate index is stored directly.
Coordinates are numbered from zero, so `index = i` represents coordinate
`i + 1` in the paper. -/
inductive DirectLineDesc (D : DirectLdParams) where
  | axis (base : Fin D.m → DirectScalarQ D) (index : Fin D.m)
      (baseFixed : lineRepMap (coordinateDirection index) base = base)
  | diagonal (base : Fin D.m → DirectScalarQ D) (index : Fin D.m)
      (direction : Fin D.m → DirectScalarQ D)
      (baseFixed : lineRepMap direction base = base)
      (prefixZero : ∀ j : Fin D.m, j.val < index.val → direction j = 0)
  deriving DecidableEq

/-- The kind of a directly indexed line. -/
def DirectLineDesc.kind {D : DirectLdParams} : DirectLineDesc D → LineKind
  | .axis _ _ _ => .axis
  | .diagonal _ _ _ _ _ => .diagonal

/-- The coordinate index stored in a directly indexed line. -/
def DirectLineDesc.index {D : DirectLdParams} : DirectLineDesc D → Fin D.m
  | .axis _ index _ => index
  | .diagonal _ index _ _ _ => index

/-- The canonical base point of a directly indexed line. -/
def DirectLineDesc.base {D : DirectLdParams} :
    DirectLineDesc D → Fin D.m → DirectScalarQ D
  | .axis base _ _ => base
  | .diagonal base _ _ _ _ => base

/-- The geometric direction of a directly indexed line. -/
def DirectLineDesc.direction {D : DirectLdParams} (line : DirectLineDesc D) :
    Fin D.m → DirectScalarQ D :=
  match line with
  | .axis _ index _ => coordinateDirection index
  | .diagonal _ _ direction _ _ => direction

/-- The base of a directly indexed description is fixed by its geometric
direction. -/
theorem DirectLineDesc.base_fixed {D : DirectLdParams} (line : DirectLineDesc D) :
    lineRepMap line.direction line.base = line.base := by
  cases line with
  | axis base index baseFixed => exact baseFixed
  | diagonal base index direction baseFixed prefixZero => exact baseFixed

/-- Every directly indexed diagonal description retains its prefix-zero
invariant. -/
theorem DirectLineDesc.diagonal_prefix_zero {D : DirectLdParams}
    (line : DirectLineDesc D) (hline : line.kind = .diagonal) :
    ∀ j : Fin D.m, j.val < line.index.val → line.direction j = 0 := by
  cases line with
  | axis base index baseFixed => simp [DirectLineDesc.kind] at hline
  | diagonal base index direction baseFixed prefixZero => exact prefixZero

/-- The point set represented by a directly indexed line. -/
noncomputable def DirectLineDesc.pointSet {D : DirectLdParams}
    (line : DirectLineDesc D) : Set (Fin D.m → DirectScalarQ D) :=
  linePoints line.base line.direction

/-- Turn a direct sample into its canonical axis-line description. -/
noncomputable def directALineDescOf (D : DirectLdParams)
    (sample : DirectLdSpace D) : DirectLineDesc D :=
  let direction := coordinateDirection sample.index
  let base := lineRepMap direction sample.point
  .axis base sample.index (lineRepMap_apply_self direction sample.point)

/-- Turn a direct sample into its canonical diagonal-line description. -/
noncomputable def directDLineDescOf (D : DirectLdParams)
    (sample : DirectLdSpace D) : DirectLineDesc D :=
  let direction := directPrefixProjection sample.index sample.direction
  let base := lineRepMap direction sample.point
  .diagonal base sample.index direction
    (lineRepMap_apply_self direction sample.point) (by
      intro j hj
      change directPrefixProjection sample.index sample.direction j = 0
      rw [directPrefixProjection, if_pos hj])

/-- The axis-line/point law with a directly sampled coordinate index. -/
noncomputable def directALinePointDist (D : DirectLdParams) :
    Distribution (DirectLineDesc D × (Fin D.m → DirectScalarQ D)) :=
  (uniformDistribution (DirectLdSpace D)).map fun sample =>
    (directALineDescOf D sample, sample.point)

/-- The diagonal-line/point law with a directly sampled prefix index. -/
noncomputable def directDLinePointDist (D : DirectLdParams) :
    Distribution (DirectLineDesc D × (Fin D.m → DirectScalarQ D)) :=
  (uniformDistribution (DirectLdSpace D)).map fun sample =>
    (directDLineDescOf D sample, sample.point)

/-- The equal mixture of the directly indexed axis and diagonal line-point
laws.  This is the replacement for the otherwise undefined extended-dimension
instance used at paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1020-1116`. -/
noncomputable def directLinePointDist (D : DirectLdParams) :
    Distribution (DirectLineDesc D × (Fin D.m → DirectScalarQ D)) :=
  Distribution.mix (1 / 2) (by norm_num) (by norm_num)
    (directALinePointDist D) (directDLinePointDist D)

/-- The directly indexed axis-line/point law is probabilistic. -/
theorem directALinePointDist_isProbability (D : DirectLdParams) :
    (directALinePointDist D).IsProbability := by
  exact (uniformDistribution_isProbability (DirectLdSpace D)).map _

/-- The directly indexed diagonal-line/point law is probabilistic. -/
theorem directDLinePointDist_isProbability (D : DirectLdParams) :
    (directDLinePointDist D).IsProbability := by
  exact (uniformDistribution_isProbability (DirectLdSpace D)).map _

/-- The directly indexed line-point mixture is probabilistic. -/
theorem directLinePointDist_isProbability (D : DirectLdParams) :
    (directLinePointDist D).IsProbability := by
  exact Distribution.mix_isProbability _ _ _
    (directALinePointDist_isProbability D) (directDLinePointDist_isProbability D)
    (by norm_num) (by norm_num)

/-- Two probabilistic finite distributions with the same stored support and
the same associated probability mass function are equal. -/
private theorem distribution_eq_of_support_eq_of_toPMF_eq {alpha : Type*}
    (mu nu : Distribution alpha) (hmu : mu.IsProbability)
    (hnu : nu.IsProbability) (hsupport : mu.support = nu.support)
    (hpmf : mu.toPMF hmu = nu.toPMF hnu) : mu = nu := by
  have hweight : mu.weight = nu.weight := by
    funext a
    calc
      mu.weight a = (mu.toPMF hmu a).toReal :=
        (Distribution.toPMF_apply_toReal mu hmu a).symm
      _ = (nu.toPMF hnu a).toReal := by rw [hpmf]
      _ = nu.weight a := Distribution.toPMF_apply_toReal nu hnu a
  cases mu with
  | mk muSupport muWeight muNonnegative muOutsideSupport =>
      cases nu with
      | mk nuSupport nuWeight nuNonnegative nuOutsideSupport =>
          cases hsupport
          cases hweight
          rfl

/-- Composition of two push-forwards of a probabilistic finite distribution
is the push-forward by the composite map. -/
private theorem distribution_map_map_of_isProbability
    {alpha beta gamma : Type*} [DecidableEq beta] [DecidableEq gamma]
    (mu : Distribution alpha) (hmu : mu.IsProbability)
    (f : alpha → beta) (g : beta → gamma) :
    (mu.map f).map g = mu.map (g ∘ f) := by
  apply distribution_eq_of_support_eq_of_toPMF_eq
    ((mu.map f).map g) (mu.map (g ∘ f))
    ((hmu.map f).map g) (hmu.map (g ∘ f))
  · simp [Distribution.map_support, Finset.image_image]
  · calc
      ((mu.map f).map g).toPMF ((hmu.map f).map g) =
          ((mu.map f).toPMF (hmu.map f)).map g :=
        Distribution.toPMF_map (mu.map f) (hmu.map f) g
      _ = ((mu.toPMF hmu).map f).map g := by
        rw [Distribution.toPMF_map mu hmu f]
      _ = (mu.toPMF hmu).map (g ∘ f) :=
        PMF.map_comp f (mu.toPMF hmu) g
      _ = (mu.map (g ∘ f)).toPMF (hmu.map (g ∘ f)) :=
        (Distribution.toPMF_map mu hmu (g ∘ f)).symm

/-- Projection onto the first factor of an explicit finite product
equivalence sends the uniform distribution to the uniform first marginal. -/
private theorem uniformDistribution_map_fst_of_equiv
    {alpha beta gamma : Type*}
    [Fintype alpha] [DecidableEq alpha] [Nonempty alpha]
    [Fintype beta] [DecidableEq beta] [Nonempty beta]
    [Fintype gamma] [Nonempty gamma]
    (e : alpha ≃ beta × gamma) (f : alpha → beta)
    (hf : ∀ a, f a = (e a).1) :
    (uniformDistribution alpha).map f = uniformDistribution beta := by
  classical
  have hsurjective : Function.Surjective f := by
    intro b
    let c : gamma := Classical.choice (inferInstance : Nonempty gamma)
    refine ⟨e.symm (b, c), ?_⟩
    simpa using hf (e.symm (b, c))
  apply distribution_eq_of_support_eq_of_toPMF_eq
    ((uniformDistribution alpha).map f) (uniformDistribution beta)
    ((uniformDistribution_isProbability alpha).map f)
    (uniformDistribution_isProbability beta)
  · rw [Distribution.map_support, uniformDistribution_support,
      uniformDistribution_support,
      Finset.image_univ_of_surjective hsurjective]
  · calc
      ((uniformDistribution alpha).map f).toPMF
          ((uniformDistribution_isProbability alpha).map f) =
          ((uniformDistribution alpha).toPMF
            (uniformDistribution_isProbability alpha)).map f :=
        Distribution.toPMF_map (uniformDistribution alpha)
          (uniformDistribution_isProbability alpha) f
      _ = (PMF.uniformOfFintype alpha).map f := by
        rw [uniformDistribution_toPMF]
      _ = (PMF.uniformOfFintype alpha).map
          (Prod.fst ∘ e) := by
            exact congrArg
              (fun map : alpha → beta => (PMF.uniformOfFintype alpha).map map)
              (funext fun a => by simpa [Function.comp_def] using hf a)
      _ = ((PMF.uniformOfFintype alpha).map e).map Prod.fst :=
        (PMF.map_comp e (PMF.uniformOfFintype alpha) Prod.fst).symm
      _ = (PMF.uniformOfFintype (beta × gamma)).map Prod.fst := by
        rw [PMF.uniformOfFintype_map_equiv e]
      _ = PMF.uniformOfFintype beta := by
        rw [PMF.uniformOfFintype_prod_eq_bind]
        calc
          ((PMF.uniformOfFintype beta).bind fun a =>
              (PMF.uniformOfFintype gamma).map fun b => (a, b)).map Prod.fst =
              (PMF.uniformOfFintype beta).bind (fun a =>
                ((PMF.uniformOfFintype gamma).map fun b => (a, b)).map
                  Prod.fst) :=
            PMF.map_bind (PMF.uniformOfFintype beta)
              (fun a => (PMF.uniformOfFintype gamma).map fun b => (a, b))
              Prod.fst
          _ = (PMF.uniformOfFintype beta).bind (fun a => PMF.pure a) := by
            apply congrArg (fun q : beta → PMF beta =>
              (PMF.uniformOfFintype beta).bind q)
            funext a
            calc
              ((PMF.uniformOfFintype gamma).map fun b => (a, b)).map
                  Prod.fst =
                  (PMF.uniformOfFintype gamma).map
                    (Prod.fst ∘ fun b => (a, b)) :=
                PMF.map_comp _ (PMF.uniformOfFintype gamma) Prod.fst
              _ = (PMF.uniformOfFintype gamma).map
                  (Function.const gamma a) := by rfl
              _ = PMF.pure a :=
                PMF.map_const (PMF.uniformOfFintype gamma) a
          _ = PMF.uniformOfFintype beta :=
            PMF.bind_pure (PMF.uniformOfFintype beta)
      _ = (uniformDistribution beta).toPMF
          (uniformDistribution_isProbability beta) :=
        (uniformDistribution_toPMF beta).symm

/-- A point differs from its canonical line representative by a scalar
multiple of the line direction. -/
private theorem mem_linePoints_lineRepMap {K : Type*} [Field K] {m : ℕ}
    (v u : Fin m → K) : u ∈ linePoints (lineRepMap v u) v := by
  let W : Submodule K (Fin m → K) := Submodule.span K ({v} : Set (Fin m → K))
  let T : Submodule K (Fin m → K) :=
    registerSubmodule K (canonicalComplement W)
  have hdiff : u - lineRepMap v u ∈ W := by
    simpa [lineRepMap, canonicalProjOfKernel, W, T, LinearMap.comp_apply] using
      (Submodule.sub_projection_mem
        (isCompl_registerSubmodule_canonicalComplement W).symm u)
  rcases Submodule.mem_span_singleton.mp hdiff with ⟨t, ht⟩
  refine ⟨t, ?_⟩
  rw [ht]
  abel

/-- The point and stored-index marginals of the direct axis-line law are
uniform.  This is a direct-index analogue of `lem:alnf`, required by
the repair described in `docs/paper-gaps/qpbt_ld-dimension-divisibility.tex`;
the source distribution is at
`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:243-257`.
-/
theorem directALinePointDist_point_index_marginal_uniform (D : DirectLdParams) :
    (directALinePointDist D).map Prod.snd =
        uniformDistribution (Fin D.m → DirectScalarQ D) ∧
      (directALinePointDist D).map (fun sample => sample.1.index) =
        uniformDistribution (Fin D.m) := by
  constructor
  · unfold directALinePointDist
    rw [distribution_map_map_of_isProbability
      (uniformDistribution (DirectLdSpace D))
      (uniformDistribution_isProbability (DirectLdSpace D))]
    simpa [Function.comp_def] using
      (uniformDistribution_map_fst_of_equiv
        (e := directLdSpacePointEquiv D)
        (f := fun sample : DirectLdSpace D => sample.point) (by intro; rfl))
  · unfold directALinePointDist
    rw [distribution_map_map_of_isProbability
      (uniformDistribution (DirectLdSpace D))
      (uniformDistribution_isProbability (DirectLdSpace D))]
    simpa [Function.comp_def, directALineDescOf, DirectLineDesc.index] using
      (uniformDistribution_map_fst_of_equiv
        (e := directLdSpaceIndexEquiv D)
        (f := fun sample : DirectLdSpace D => sample.index) (by intro; rfl))

/-- Every sampled direct axis line contains its paired point.  This is the
Direct-index incidence obligation corresponding to `lem:alnf` and
the repair in `docs/paper-gaps/qpbt_ld-dimension-divisibility.tex`. -/
theorem directALinePointDist_mem_line (D : DirectLdParams) :
    ∀ sample ∈ (directALinePointDist D).support,
      sample.2 ∈ sample.1.pointSet := by
  intro sample hsample
  rw [directALinePointDist, Distribution.map_support,
    uniformDistribution_support] at hsample
  rcases Finset.mem_image.mp hsample with ⟨source, _, rfl⟩
  simpa [directALineDescOf, DirectLineDesc.pointSet,
    DirectLineDesc.base, DirectLineDesc.direction] using
    (mem_linePoints_lineRepMap
      (coordinateDirection source.index) source.point)

/-- The point and stored-index marginals of the direct diagonal-line law are
uniform.  This is the direct-index analogue of `lem:dlnf`, paper
`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:261-272`,
and is a named obligation in the dimension-divisibility repair. -/
theorem directDLinePointDist_point_index_marginal_uniform (D : DirectLdParams) :
    (directDLinePointDist D).map Prod.snd =
        uniformDistribution (Fin D.m → DirectScalarQ D) ∧
      (directDLinePointDist D).map (fun sample => sample.1.index) =
        uniformDistribution (Fin D.m) := by
  constructor
  · unfold directDLinePointDist
    rw [distribution_map_map_of_isProbability
      (uniformDistribution (DirectLdSpace D))
      (uniformDistribution_isProbability (DirectLdSpace D))]
    simpa [Function.comp_def] using
      (uniformDistribution_map_fst_of_equiv
        (e := directLdSpacePointEquiv D)
        (f := fun sample : DirectLdSpace D => sample.point) (by intro; rfl))
  · unfold directDLinePointDist
    rw [distribution_map_map_of_isProbability
      (uniformDistribution (DirectLdSpace D))
      (uniformDistribution_isProbability (DirectLdSpace D))]
    simpa [Function.comp_def, directDLineDescOf, DirectLineDesc.index] using
      (uniformDistribution_map_fst_of_equiv
        (e := directLdSpaceIndexEquiv D)
        (f := fun sample : DirectLdSpace D => sample.index) (by intro; rfl))

/-- Every sampled direct diagonal line contains its paired point.  This is the
Direct-index incidence obligation corresponding to `lem:dlnf`. -/
theorem directDLinePointDist_mem_line (D : DirectLdParams) :
    ∀ sample ∈ (directDLinePointDist D).support,
      sample.2 ∈ sample.1.pointSet := by
  intro sample hsample
  rw [directDLinePointDist, Distribution.map_support,
    uniformDistribution_support] at hsample
  rcases Finset.mem_image.mp hsample with ⟨source, _, rfl⟩
  simpa [directDLineDescOf, DirectLineDesc.pointSet,
    DirectLineDesc.base, DirectLineDesc.direction] using
    (mem_linePoints_lineRepMap
      (directPrefixProjection source.index source.direction) source.point)

/-- A sampled direct diagonal direction vanishes below its stored prefix
index.  This is the direct counterpart of the third conclusion of
`lem:dlnf`, paper
`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:261-272`.
-/
theorem directDLinePointDist_prefix_zero (D : DirectLdParams) :
    ∀ sample ∈ (directDLinePointDist D).support,
      ∀ j : Fin D.m, j.val < sample.1.index.val →
        sample.1.direction j = 0 := by
  intro sample hsample j hj
  rw [directDLinePointDist, Distribution.map_support,
    uniformDistribution_support] at hsample
  rcases Finset.mem_image.mp hsample with ⟨source, _, rfl⟩
  exact DirectLineDesc.diagonal_prefix_zero
    (directDLineDescOf D source) (by
      simp [directDLineDescOf, DirectLineDesc.kind]) j hj

end

end MIPStarRE.QPBT
