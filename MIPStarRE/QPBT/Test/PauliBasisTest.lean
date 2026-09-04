import MIPStarRE.QPBT.Algebra.LowDegreeCode
import MIPStarRE.QPBT.Algebra.Pauli
import MIPStarRE.QPBT.Test.LowDegreeGame
import MIPStarRE.QPBT.Test.MagicSquare

/-!
# The Pauli basis test

This file supplies the finite question and answer alphabets, the typed
conditionally-linear question sampler, and the Boolean win predicate for the
Pauli basis test.  The quantitative soundness theorem is isolated in
`Soundness.lean`.

## References

The source-facing nodes are `def:admissible`, `def:pauli-question-distribution`,
and `def:pauli-win-predicate` in
`blueprint/src/chapter/ch13_qpbt_test.tex:269-367`; their paper origin is
`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:908-1225`.
-/

open scoped BigOperators

namespace MIPStarRE.QPBT

open MIPStarRE.LDT

noncomputable section

/-- The numerical admissible Pauli-test parameter package.  Its scalar carrier
uses the once-and-for-all model `fixedFieldModel q hq`, so the paper's fixed
self-dual-normal identification is not quantified in the test statement.  This
is `def:admissible` in
`blueprint/src/chapter/ch13_qpbt_test.tex:269-283`, paper origin
`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:958-961`.
-/
structure AdmissibleParams where
  q : ℕ
  m : ℕ
  d : ℕ
  hd : 1 ≤ d
  hq : IsAdmissibleSize q
  hdvd : m ∣ q

/-- The positivity of the ambient dimension is a proof obligation implicit in
the admissibility convention `def:admissible`, blueprint
`blueprint/src/chapter/ch13_qpbt_test.tex:269-283`, paper origin
`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:958-961`.
-/
theorem AdmissibleParams.one_le_m (P : AdmissibleParams) : 1 ≤ P.m := by
  obtain ⟨k, -, hk⟩ := P.hq
  have hq : 0 < P.q := by
    rw [hk]
    positivity
  exact Nat.pos_of_dvd_of_pos P.hdvd hq

/-- The fixed model accessor for an admissible parameter package.  It is a
compatibility view of the global `fixedFieldModel` selector, not an independently
quantified field representation.  Blueprint `ch13_qpbt_test.tex:269-283`; paper
origin `references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:958-961`.
-/
noncomputable def AdmissibleParams.model (P : AdmissibleParams) : FixedFieldModel P.q :=
  fixedFieldModel P.q P.hq

/-- The low-degree parameter view of an admissible Pauli-test package.  This is
a Lean-only bridge supporting the statement closure; it is not an additional
hypothesis of `thm:pauli`.  Blueprint
`blueprint/src/chapter/ch13_qpbt_test.tex:17-31`, paper origin
`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:958-961`.
-/
def AdmissibleParams.toLdParams (P : AdmissibleParams) : LdParams where
  q := P.q
  m := P.m
  d := P.d
  k := 1
  hm := P.one_le_m
  hd := P.hd
  hk := by decide
  hq := P.hq
  hdvd := P.hdvd

/-- The scalar carrier associated with an admissible parameter package.  It is
the globally fixed field carrier selected by `AdmissibleParams.model` in
`def:admissible`, blueprint
`blueprint/src/chapter/ch13_qpbt_test.tex:269-283`, paper origin
`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:958-961`.
-/
abbrev PauliScalar (P : AdmissibleParams) := P.model.K

/-- The six families of Pauli-test questions.  This is part of
`def:pauli-question-distribution`, blueprint `ch13_qpbt_test.tex:285-329`,
paper origin `references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:964-1120`.
-/
inductive PauliType where
  | point (W : PauliKind)
  | aline (W : PauliKind)
  | dline (W : PauliKind)
  | pauli (W : PauliKind)
  | pairW (W : PauliKind)
  | pair
  | ms (t : MsType)
  deriving DecidableEq, Repr, Inhabited, Fintype

/-- The register blocks used by the Pauli question space.  These are the
coordinates displayed in `def:pauli-question-distribution`, blueprint
`ch13_qpbt_test.tex:285-329`, paper origin
`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:964-1120`.
-/
abbrev PauliIndex (P : AdmissibleParams) :=
  (((((Fin P.m ⊕ Fin P.m) ⊕ Unit) ⊕ Fin P.m) ⊕ Unit) ⊕ Unit)

/-- The ambient Pauli question coefficient space (`def:pauli-question-distribution`,
blueprint `ch13_qpbt_test.tex:285-329`; paper origin
`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:964-1120`).
-/
abbrev PauliSpace (P : AdmissibleParams) := PauliIndex P → PauliScalar P

/-- The coefficient register indexed by the Boolean cube in
`def:generalized-pauli`, blueprint `ch11_qpbt_algebra.tex:529-571`, paper origin
`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:908-945`.
-/
abbrev PauliRegister (P : AdmissibleParams) := Cube P.m → PauliScalar P

/- The nested sum is the fixed register order
`V_X ⊕ V_Z ⊕ V_I ⊕ V_V ⊕ V_{R_X} ⊕ V_{R_Z}` from the blueprint. -/
/-- The `V_X` block of an ambient Pauli vector (`def:pauli-question-distribution`,
blueprint `ch13_qpbt_test.tex:285-329`; paper origin
`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:964-1120`). -/
def pauliXBlock {P : AdmissibleParams} (z : PauliSpace P) : Fin P.m → PauliScalar P :=
  fun i => z (.inl (.inl (.inl (.inl (.inl i)))))

/-- The `V_Z` block of an ambient Pauli vector in `def:pauli-question-distribution`,
blueprint `ch13_qpbt_test.tex:285-329`, paper origin
`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:964-1120`.
-/
def pauliZBlock {P : AdmissibleParams} (z : PauliSpace P) : Fin P.m → PauliScalar P :=
  fun i => z (.inl (.inl (.inl (.inl (.inr i)))))

/-- The scalar block `V_I` of an ambient Pauli vector in
`def:pauli-question-distribution`, blueprint `ch13_qpbt_test.tex:285-329`,
paper origin `references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:964-1120`.
-/
def pauliScalarBlock {P : AdmissibleParams} (z : PauliSpace P) : PauliScalar P :=
  z (.inl (.inl (.inl (.inr ()))))

/-- The direction block `V_V` of an ambient Pauli vector in
`def:pauli-question-distribution`, blueprint `ch13_qpbt_test.tex:285-329`,
paper origin `references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:964-1120`.
-/
def pauliDirectionBlock {P : AdmissibleParams} (z : PauliSpace P) : Fin P.m → PauliScalar P :=
  fun i => z (.inl (.inl (.inr i)))

/-- The `r_X` scalar block in the Pauli question content from
`def:pauli-question-distribution`, blueprint `ch13_qpbt_test.tex:285-329`,
paper origin `references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:964-1120`.
-/
def pauliRXBlock {P : AdmissibleParams} (z : PauliSpace P) : PauliScalar P :=
  z (.inl (.inr ()))

/-- The `r_Z` scalar block in the Pauli question content from
`def:pauli-question-distribution`, blueprint `ch13_qpbt_test.tex:285-329`,
paper origin `references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:964-1120`.
-/
def pauliRZBlock {P : AdmissibleParams} (z : PauliSpace P) : PauliScalar P :=
  z (.inr ())

/-- Select the basis-dependent point block from a Pauli question content in
`def:pauli-question-distribution`, blueprint `ch13_qpbt_test.tex:285-329`,
paper origin `references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:964-1120`.
-/
def pauliPointBlock {P : AdmissibleParams} (W : PauliKind) (z : PauliSpace P) :
    Fin P.m → PauliScalar P :=
  match W with
  | .X => pauliXBlock z
  | .Z => pauliZBlock z

/-- Read the low-degree register selected by a basis from an ambient Pauli
vector.  Lean-only coordinate plumbing for `def:pauli-question-distribution`,
blueprint `ch13_qpbt_test.tex:285-329`, paper origin
`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:964-1120`.
-/
def pauliToLd (P : AdmissibleParams) (W : PauliKind) (z : PauliSpace P) :
    LdSpace P.toLdParams :=
  fun i => match i with
  | .inl (.inl j) => pauliPointBlock W z j
  | .inl (.inr _) => pauliScalarBlock z
  | .inr j => pauliDirectionBlock z j

/-- Embed a low-degree vector into the basis-selected Pauli blocks, clearing the
other basis and the two `r` registers.  This is Lean-only coordinate plumbing
for `def:pauli-question-distribution`, blueprint
`blueprint/src/chapter/ch13_qpbt_test.tex:285-329`, paper origin
`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:964-1120`.
-/
def embedLd (P : AdmissibleParams) (W : PauliKind)
    (u : LdSpace P.toLdParams) : PauliSpace P :=
  fun i => match i with
  | .inl (.inl (.inl (.inl (.inl j)))) =>
      match W with
      | .X => u (.inl (.inl j))
      | .Z => 0
  | .inl (.inl (.inl (.inl (.inr j)))) =>
      match W with
      | .X => 0
      | .Z => u (.inl (.inl j))
  | .inl (.inl (.inl (.inr _))) => u (.inl (.inr ()))
  | .inl (.inl (.inr j)) => u (.inr j)
  | .inl (.inr _) => 0
  | .inr _ => 0

/-- The type-4 projection retaining `V_X`, `V_Z`, `V_{R_X}`, and `V_{R_Z}` from
`def:pauli-question-distribution`, blueprint `ch13_qpbt_test.tex:285-329`, paper
origin `references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:964-1120`.
-/
def pauliSharedProjection {P : AdmissibleParams} (z : PauliSpace P) : PauliSpace P :=
  fun i => match i with
  | .inl (.inl (.inl (.inl (.inl j)))) => z (.inl (.inl (.inl (.inl (.inl j)))))
  | .inl (.inl (.inl (.inl (.inr j)))) => z (.inl (.inl (.inl (.inl (.inr j)))))
  | .inl (.inl (.inl (.inr _))) => 0
  | .inl (.inl (.inr _)) => 0
  | .inl (.inr _) => z (.inl (.inr ()))
  | .inr _ => z (.inr ())

/-- The source level attached to each typed Pauli CL map.  This records the
exact levels in items 1--5 of `def:pauli-question-distribution`: point, line,
and diagonal maps have levels 1, 2, and 3, the Pauli map has level 0, and the
shared projection has level 1.  Blueprint
`blueprint/src/chapter/ch13_qpbt_test.tex:285-329`; paper origin
`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:964-1120`.
-/
def pauliCLLevel : PauliType → ℕ
  | .point _ => 1
  | .aline _ => 2
  | .dline _ => 3
  | .pauli _ => 0
  | .pairW _ => 1
  | .pair => 1
  | .ms _ => 1

/-- The typed CL dispatcher.  The point/line maps are the corresponding
low-degree maps embedded in the selected basis block; Pair, Magic Square, and
Pair/W types use the shared projection; Pauli/W is the zero-level map.  This
is the direct finite-space form of `def:pauli-question-distribution`,
blueprint `ch13_qpbt_test.tex:285-329`, paper origin
`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:964-1120`.
-/
noncomputable def pauliCL (P : AdmissibleParams) (t : PauliType) :
    PauliSpace P → PauliSpace P :=
  match t with
  | .point W => fun z => embedLd P W (ldPointCL P.toLdParams (pauliToLd P W z))
  | .aline W => fun z => embedLd P W (ldALineCL P.toLdParams (pauliToLd P W z))
  | .dline W => fun z => embedLd P W (ldDLineCL P.toLdParams (pauliToLd P W z))
  | .pauli _ => fun _ => 0
  | .pairW _ => pauliSharedProjection
  | .pair => pauliSharedProjection
  | .ms _ => pauliSharedProjection

/-- Formalization-only auxiliary: a linear map of the ambient coefficient space
is conditionally linear with a single level on the full register. -/
private theorem isCondLinearOn_one_of_linear {K ι : Type*} [Field K]
    [Fintype ι] [DecidableEq ι] (L : (ι → K) →ₗ[K] (ι → K)) :
    IsCondLinearOn K Finset.univ 1 (fun x => L x) := by
  refine ⟨.succ Finset.univ L (fun _ i hi => absurd (Finset.mem_univ i) hi)
      (fun _ => .zero), ⟨Finset.subset_univ _, fun _ => trivial⟩, ?_⟩
  funext x
  have hx : coordinateRestriction (Finset.univ : Finset ι) x = x := by
    funext i
    simp [coordinateRestriction]
  show L (coordinateRestriction Finset.univ x) + 0 = L x
  rw [hx, add_zero]

/-- Formalization-only auxiliary: extend a coefficient vector along an injective
reindexing of registers, setting every coordinate outside the image to zero. -/
private def clExtend {K κ ι : Type*} [Zero K] (f : κ → ι) (u : κ → K) : ι → K :=
  Function.extend f u 0

/-- Formalization-only auxiliary: the extension recovers the original
coordinates along an injective reindexing. -/
private theorem clExtend_apply {K κ ι : Type*} [Zero K] {f : κ → ι}
    (hf : Function.Injective f) (u : κ → K) (k : κ) :
    clExtend f u (f k) = u k :=
  hf.extend_apply u 0 k

/-- Formalization-only auxiliary: the extension vanishes at any coordinate
outside the image of the reindexing. -/
private theorem clExtend_eq_zero_of_not_mem {K κ ι : Type*} [Zero K]
    (f : κ → ι) (u : κ → K) (i : ι) (h : ∀ k, f k ≠ i) :
    clExtend f u i = 0 :=
  Function.extend_apply' u (0 : ι → K) i
    (fun hex => h hex.choose hex.choose_spec)

/-- Formalization-only auxiliary: restriction along an injective reindexing
inverts the extension. -/
private theorem clExtend_comp {K κ ι : Type*} [Zero K] {f : κ → ι}
    (hf : Function.Injective f) (u : κ → K) :
    (fun k => clExtend f u (f k)) = u :=
  funext fun k => clExtend_apply hf u k

/-- Formalization-only auxiliary: the extension of the zero vector vanishes. -/
private theorem clExtend_zero {K κ ι : Type*} [Zero K] {f : κ → ι}
    (hf : Function.Injective f) : clExtend f (0 : κ → K) = 0 := by
  funext i
  by_cases h : ∃ k, f k = i
  · obtain ⟨k, rfl⟩ := h
    simp [clExtend_apply hf]
  · simp [clExtend, Function.extend_apply' _ _ _ h]

/-- Formalization-only auxiliary: the extension is additive. -/
private theorem clExtend_add {K κ ι : Type*} [AddZeroClass K] {f : κ → ι}
    (hf : Function.Injective f) (u v : κ → K) :
    clExtend f (u + v) = clExtend f u + clExtend f v := by
  funext i
  by_cases h : ∃ k, f k = i
  · obtain ⟨k, rfl⟩ := h
    simp [clExtend_apply hf]
  · simp [clExtend, Function.extend_apply' _ _ _ h]

/-- Formalization-only auxiliary: the extension commutes with scalars. -/
private theorem clExtend_smul {K κ ι : Type*} [Semiring K] {f : κ → ι}
    (hf : Function.Injective f) (c : K) (u : κ → K) :
    clExtend f (c • u) = c • clExtend f u := by
  funext i
  by_cases h : ∃ k, f k = i
  · obtain ⟨k, rfl⟩ := h
    simp [clExtend_apply hf]
  · simp [clExtend, Function.extend_apply' _ _ _ h]

/-- Formalization-only auxiliary: transport a linear map of coefficient vectors
along an injective reindexing of registers. -/
private def clReindexLinear {K κ ι : Type*} [Field K] {f : κ → ι}
    (hf : Function.Injective f) (L : (κ → K) →ₗ[K] (κ → K)) :
    (ι → K) →ₗ[K] (ι → K) where
  toFun x := clExtend f (L (fun k => x (f k)))
  map_add' x y := by
    show clExtend f (L (fun k => (x + y) (f k))) =
      clExtend f (L (fun k => x (f k))) + clExtend f (L (fun k => y (f k)))
    have h : (fun k => (x + y) (f k)) =
        (fun k => x (f k)) + (fun k => y (f k)) := rfl
    rw [h, map_add, clExtend_add hf]
  map_smul' c x := by
    show clExtend f (L (fun k => (c • x) (f k))) =
      c • clExtend f (L (fun k => x (f k)))
    have h : (fun k => (c • x) (f k)) = c • (fun k => x (f k)) := rfl
    rw [h, map_smul, clExtend_smul hf]

/-- Formalization-only auxiliary: transport a conditionally linear syntax tree
along an injective reindexing of registers. -/
private def clReindexTerm {K κ ι : Type*} [Field K] [Fintype κ] [DecidableEq κ]
    [Fintype ι] [DecidableEq ι] {f : κ → ι} (hf : Function.Injective f) :
    {ell : ℕ} → CondLinearTerm K (ι := κ) ell → CondLinearTerm K (ι := ι) ell
  | _, .zero => .zero
  | _, .succ S₁ L₁ h rest =>
      .succ (S₁.image f) (clReindexLinear hf L₁)
        (by
          intro x i hi
          by_cases hex : ∃ k, f k = i
          · obtain ⟨k, rfl⟩ := hex
            have hk : k ∉ S₁ := fun hk => hi (Finset.mem_image_of_mem f hk)
            show clExtend f (L₁ (fun j => x (f j))) (f k) = 0
            rw [clExtend_apply hf]
            exact h _ k hk
          · show clExtend f (L₁ (fun j => x (f j))) i = 0
            simp [clExtend, Function.extend_apply' _ _ _ hex])
        (fun y => clReindexTerm hf (rest (fun k => y (f k))))

/-- Formalization-only auxiliary: the transported syntax tree is supported on
any register containing the image of the original support. -/
private theorem clReindexTerm_supportedOn {K κ ι : Type*} [Field K]
    [Fintype κ] [DecidableEq κ] [Fintype ι] [DecidableEq ι] {f : κ → ι}
    (hf : Function.Injective f) :
    ∀ {ell : ℕ} (t : CondLinearTerm K (ι := κ) ell) (S : Finset κ)
      (T : Finset ι), t.supportedOn S → S.image f ⊆ T →
      (clReindexTerm hf t).supportedOn T := by
  intro ell t
  induction t with
  | zero => intro S T _ _; trivial
  | succ S₁ L₁ hL rest ih =>
      intro S T hsupp hST
      obtain ⟨h1, h2⟩ := hsupp
      refine ⟨fun i hi => hST (Finset.image_subset_image h1 hi), fun y => ?_⟩
      refine ih (fun k => y (f k)) (S \ S₁) (T \ S₁.image f) (h2 _) ?_
      intro i hi
      obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hi
      obtain ⟨hkS, hkS₁⟩ := Finset.mem_sdiff.mp hk
      refine Finset.mem_sdiff.mpr ⟨hST (Finset.mem_image_of_mem f hkS), ?_⟩
      intro hmem
      obtain ⟨k', hk', hk'eq⟩ := Finset.mem_image.mp hmem
      exact hkS₁ (hf hk'eq ▸ hk')

/-- Formalization-only auxiliary: evaluation commutes with the transport of a
conditionally linear syntax tree along an injective reindexing. -/
private theorem clReindexTerm_eval {K κ ι : Type*} [Field K]
    [Fintype κ] [DecidableEq κ] [Fintype ι] [DecidableEq ι] {f : κ → ι}
    (hf : Function.Injective f) :
    ∀ {ell : ℕ} (t : CondLinearTerm K (ι := κ) ell) (x : ι → K),
      CondLinearTerm.eval (clReindexTerm hf t) x =
        clExtend f (CondLinearTerm.eval t (fun k => x (f k))) := by
  intro ell t
  induction t with
  | zero => intro x; exact (clExtend_zero hf).symm
  | succ S₁ L₁ hL rest ih =>
      intro x
      have hres : (fun k => coordinateRestriction (S₁.image f) x (f k)) =
          coordinateRestriction S₁ (fun k => x (f k)) := by
        funext k
        by_cases hk : k ∈ S₁
        · have hmem : f k ∈ S₁.image f := Finset.mem_image_of_mem f hk
          simp [coordinateRestriction, hk, hmem]
        · have hni : f k ∉ S₁.image f := by
            intro hmem
            obtain ⟨k', hk', hk'eq⟩ := Finset.mem_image.mp hmem
            exact hk (hf hk'eq ▸ hk')
          simp [coordinateRestriction, hk, hni]
      have hhead : clReindexLinear hf L₁ (coordinateRestriction (S₁.image f) x) =
          clExtend f (L₁ (coordinateRestriction S₁ (fun k => x (f k)))) := by
        show clExtend f (L₁ (fun k => coordinateRestriction (S₁.image f) x (f k))) = _
        rw [hres]
      have hcomp : (fun k => clReindexLinear hf L₁
            (coordinateRestriction (S₁.image f) x) (f k)) =
          L₁ (coordinateRestriction S₁ (fun k => x (f k))) := by
        rw [hhead]
        exact clExtend_comp hf _
      show clReindexLinear hf L₁ (coordinateRestriction (S₁.image f) x) +
          CondLinearTerm.eval (clReindexTerm hf (rest
            (fun k => clReindexLinear hf L₁
              (coordinateRestriction (S₁.image f) x) (f k)))) x =
        clExtend f (L₁ (coordinateRestriction S₁ (fun k => x (f k))) +
          CondLinearTerm.eval
            (rest (L₁ (coordinateRestriction S₁ (fun k => x (f k)))))
            (fun k => x (f k)))
      rw [hcomp, ih _ x, hhead, ← clExtend_add hf]

/-- Formalization-only auxiliary: conditional linearity is preserved by an
injective reindexing of registers, the coordinates outside the image of the
reindexing being set to zero. -/
private theorem isCondLinearOn_reindex {K κ ι : Type*} [Field K]
    [Fintype κ] [DecidableEq κ] [Fintype ι] [DecidableEq ι] {f : κ → ι}
    (hf : Function.Injective f) {ell : ℕ} {L : (κ → K) → (κ → K)}
    (h : IsCondLinearOn K Finset.univ ell L) :
    IsCondLinearOn K Finset.univ ell
      (fun x => clExtend f (L (fun k => x (f k)))) := by
  obtain ⟨t, hsupp, hval⟩ := h
  refine ⟨clReindexTerm hf t,
    clReindexTerm_supportedOn hf t Finset.univ Finset.univ hsupp
      (Finset.subset_univ _), ?_⟩
  funext x
  rw [clReindexTerm_eval hf t x, hval]

/-- Formalization-only auxiliary: the point projection of the ambient low-degree
coefficient space, presented as a linear map. -/
private def ldPointProjection (P : LdParams) :
    LdSpace P →ₗ[ScalarQ P] LdSpace P where
  toFun z := ldPointCL P z
  map_add' x y := by
    funext i
    rcases i with (j | u) | j <;> simp [ldPointCL]
  map_smul' c x := by
    funext i
    rcases i with (j | u) | j <;> simp [ldPointCL]

/-- Formalization-only auxiliary: the point map of the low-degree question
distribution is conditionally linear of level one, as asserted for `L_Point` in
`def:ld-question-distribution`, blueprint
`blueprint/src/chapter/ch13_qpbt_test.tex:38-49`, paper origin
`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:31-391`.
It is recorded here because only the Pauli reindexing uses it. -/
private theorem isCondLinear_ldPointCL (P : LdParams) :
    IsCondLinearOn (ScalarQ P) Finset.univ 1 (ldPointCL P) :=
  isCondLinearOn_one_of_linear (ldPointProjection P)

/-- Formalization-only auxiliary: the type-4 projection of the ambient Pauli
coefficient space, presented as a linear map. -/
private def pauliSharedProjectionLinear (P : AdmissibleParams) :
    PauliSpace P →ₗ[PauliScalar P] PauliSpace P where
  toFun z := pauliSharedProjection z
  map_add' x y := by
    funext i
    rcases i with ((((j | j) | u) | j) | u) | u <;> simp [pauliSharedProjection]
  map_smul' c x := by
    funext i
    rcases i with ((((j | j) | u) | j) | u) | u <;> simp [pauliSharedProjection]

/-- Formalization-only auxiliary: the inclusion of the low-degree register index
into the ambient Pauli register index selected by a basis. -/
def pauliLdIndex (P : AdmissibleParams) (W : PauliKind) :
    LdIndex P.toLdParams → PauliIndex P
  | .inl (.inl j) =>
      match W with
      | .X => .inl (.inl (.inl (.inl (.inl j))))
      | .Z => .inl (.inl (.inl (.inl (.inr j))))
  | .inl (.inr _) => .inl (.inl (.inl (.inr ())))
  | .inr j => .inl (.inl (.inr j))

/-- Formalization-only auxiliary: distinct low-degree registers are sent to
distinct ambient Pauli registers. -/
private theorem pauliLdIndex_injective (P : AdmissibleParams) (W : PauliKind) :
    Function.Injective (pauliLdIndex P W) := by
  intro a b hab
  cases W <;> rcases a with (j | u) | j <;> rcases b with (j' | u') | j' <;>
    simp_all [pauliLdIndex]

/-- Formalization-only auxiliary: reading the low-degree register out of an
ambient Pauli vector is restriction along `pauliLdIndex`. -/
private theorem pauliToLd_eq (P : AdmissibleParams) (W : PauliKind)
    (z : PauliSpace P) :
    pauliToLd P W z = fun k => z (pauliLdIndex P W k) := by
  funext k
  rcases k with (j | u) | j <;> cases W <;> rfl

/-- Formalization-only auxiliary: writing a low-degree vector into the ambient
Pauli registers is extension along `pauliLdIndex`. -/
private theorem embedLd_eq (P : AdmissibleParams) (W : PauliKind)
    (w : LdSpace P.toLdParams) :
    embedLd P W w = clExtend (pauliLdIndex P W) w := by
  have hf := pauliLdIndex_injective P W
  funext i
  rcases i with ((((j | j) | u) | j) | u) | u
  · cases W
    · exact (clExtend_apply hf w (Sum.inl (Sum.inl j))).symm
    · exact (clExtend_eq_zero_of_not_mem _ w _ (by
        rintro ((j' | u') | j') <;> simp [pauliLdIndex])).symm
  · cases W
    · exact (clExtend_eq_zero_of_not_mem _ w _ (by
        rintro ((j' | u') | j') <;> simp [pauliLdIndex])).symm
    · exact (clExtend_apply hf w (Sum.inl (Sum.inl j))).symm
  · exact (clExtend_apply hf w (Sum.inl (Sum.inr ()))).symm
  · exact (clExtend_apply hf w (Sum.inr j)).symm
  · exact (clExtend_eq_zero_of_not_mem _ w _ (by
      intro k
      cases W <;> rcases k with (j' | u') | j' <;> simp [pauliLdIndex])).symm
  · exact (clExtend_eq_zero_of_not_mem _ w _ (by
      intro k
      cases W <;> rcases k with (j' | u') | j' <;> simp [pauliLdIndex])).symm

/-- Formalization-only auxiliary: the typed Pauli point, axis-line, and
diagonal-line maps are the corresponding low-degree maps reindexed along
`pauliLdIndex`. -/
private theorem pauliCL_reindex (P : AdmissibleParams) (W : PauliKind)
    (L : LdSpace P.toLdParams → LdSpace P.toLdParams) :
    (fun z : PauliSpace P => embedLd P W (L (pauliToLd P W z))) =
      fun z => clExtend (pauliLdIndex P W)
        (L (fun k => z (pauliLdIndex P W k))) := by
  funext z
  rw [embedLd_eq, pauliToLd_eq]

/-- Level assertions for the typed Pauli CL maps.  These are Lean-only
proof obligations corresponding to the prose following `def:pauli-question-distribution`
(`blueprint/src/chapter/ch13_qpbt_test.tex:285-329`; paper
`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:964-1120`).
-/
theorem isCondLinear_pauliCL (P : AdmissibleParams) (t : PauliType) :
    IsCondLinearOn (PauliScalar P) Finset.univ (pauliCLLevel t) (pauliCL P t) := by
  have hshared : IsCondLinearOn (PauliScalar P) Finset.univ 1
      (pauliSharedProjection (P := P)) :=
    isCondLinearOn_one_of_linear (pauliSharedProjectionLinear P)
  cases t with
  | point W =>
      show IsCondLinearOn (PauliScalar P) Finset.univ 1
        (fun z : PauliSpace P =>
          embedLd P W (ldPointCL P.toLdParams (pauliToLd P W z)))
      rw [pauliCL_reindex P W (ldPointCL P.toLdParams)]
      exact isCondLinearOn_reindex (pauliLdIndex_injective P W)
        (isCondLinear_ldPointCL P.toLdParams)
  | aline W =>
      show IsCondLinearOn (PauliScalar P) Finset.univ 2
        (fun z : PauliSpace P =>
          embedLd P W (ldALineCL P.toLdParams (pauliToLd P W z)))
      rw [pauliCL_reindex P W (ldALineCL P.toLdParams)]
      exact isCondLinearOn_reindex (pauliLdIndex_injective P W)
        (isCondLinear_ldALineCL P.toLdParams)
  | dline W =>
      show IsCondLinearOn (PauliScalar P) Finset.univ 3
        (fun z : PauliSpace P =>
          embedLd P W (ldDLineCL P.toLdParams (pauliToLd P W z)))
      rw [pauliCL_reindex P W (ldDLineCL P.toLdParams)]
      exact isCondLinearOn_reindex (pauliLdIndex_injective P W)
        (isCondLinear_ldDLineCL P.toLdParams)
  | pauli W => exact ⟨.zero, trivial, rfl⟩
  | pairW W => exact hshared
  | pair => exact hshared
  | ms s => exact hshared

/-- A finite edge set for the typed Pauli question graph.  The self-loops and
the displayed type-incidence families are the graph used by the sampler in
`def:pauli-question-distribution`, blueprint lines 285-329, paper origin
`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:964-1120`.
-/
def pauliEdges : Finset (Sym2 PauliType) :=
  let loops := Finset.univ.image (fun t : PauliType => Sym2.mk t t)
  let lineEdges :=
    (Finset.univ : Finset PauliKind).image (fun W =>
      Sym2.mk (.point W) (.aline W)) ∪
      (Finset.univ : Finset PauliKind).image (fun W =>
        Sym2.mk (.point W) (.dline W)) ∪
      (Finset.univ : Finset PauliKind).image (fun W =>
        Sym2.mk (.point W) (.pauli W))
  let basisEdges :=
    (Finset.univ : Finset PauliKind).image (fun W =>
      Sym2.mk (.point W) (.pairW W)) ∪
      ({Sym2.mk (.point .X) (.ms (.var ⟨0, by decide⟩)),
        Sym2.mk (.point .Z) (.ms (.var ⟨4, by decide⟩))} : Finset (Sym2 PauliType))
  let pairEdges :=
    (Finset.univ : Finset PauliKind).image (fun W =>
      Sym2.mk (.pairW W) .pair)
  let msEdges' :=
    (Finset.univ : Finset (MsType × MsType)).filter (fun xy =>
      Sym2.mk xy.1 xy.2 ∈ msEdges) |>.image (fun xy =>
        Sym2.mk (.ms xy.1) (.ms xy.2))
  loops ∪ lineEdges ∪ basisEdges ∪ pairEdges ∪ msEdges'

/-- A Pauli question is a type together with a full ambient coefficient vector
(`def:pauli-question-distribution`, blueprint `ch13_qpbt_test.tex:285-329`; paper
origin `references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:964-1120`).
-/
abbrev PauliQuestion (P : AdmissibleParams) := PauliType × PauliSpace P

/-- The Pauli question carrying no additional coefficient data, as in
`def:pauli-win-predicate`, blueprint `ch13_qpbt_test.tex:356-392`, paper origin
`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:1006-1008`.
Its ambient coefficient vector is zero. -/
def pauliQuestion (P : AdmissibleParams) (W : PauliKind) : PauliQuestion P :=
  (.pauli W, 0)

/-- The ordered-edge subtype used by the Pauli question sampler.  This is
the finite carrier underlying `graphDistribution pauliEdges`; it is Lean-only
infrastructure for `def:pauli-question-distribution`, blueprint
`ch13_qpbt_test.tex:285-329`, paper origin
`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:964-1120`.
-/
abbrev PauliEdge :=
  {e : PauliType × PauliType // Sym2.mk e.1 e.2 ∈ pauliEdges}

/-- The Pauli graph has a loop, so its ordered-edge subtype is nonempty.  This
is a finite-carrier fact used only to instantiate the uniform source sampler
for `def:pauli-question-distribution`; the graph itself is the source-facing
object `pauliEdges` above (same blueprint and paper references).
-/
theorem pauliEdge_nonempty : Nonempty PauliEdge := by
  refine ⟨⟨(.point .X, .point .X), ?_⟩⟩
  simp [pauliEdges]

/-- The Pauli question distribution from `def:pauli-question-distribution`,
blueprint `ch13_qpbt_test.tex:285-329`, paper origin
`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:1070-1120`.
-/
noncomputable def pauliQuestionDistribution (P : AdmissibleParams) :
    Distribution (PauliQuestion P × PauliQuestion P) :=
  by
    classical
    letI : Nonempty PauliEdge := pauliEdge_nonempty
    exact
      Distribution.map
        (uniformDistribution (PauliEdge × PauliSpace P))
        (fun s =>
          ((s.1.1.1, pauliCL P s.1.1.1 s.2),
            (s.1.1.2, pauliCL P s.1.1.2 s.2)))

/-- The finite answer alphabet for the Pauli basis test.  Its constructors are
the seven answer forms in `def:pauli-win-predicate`, blueprint lines 331-367,
paper origin `references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:1126-1225`.
-/
inductive PauliAnswer (P : AdmissibleParams) where
  | value (a : PauliScalar P)
  | alinePoly (a : Fin (P.d + 1) → PauliScalar P)
  | dlinePoly (a : Fin (P.m * P.d + 1) → PauliScalar P)
  | pairBits (a : ZMod 2 × ZMod 2)
  | bit (a : ZMod 2)
  | msTriple (a : Fin 3 → ZMod 2)
  | pauliOutcome (a : PauliRegister P)
  deriving DecidableEq

/-- A formalization-only total relabeling from the global Pauli-test answer
alphabet to a Pauli register. It folds wrong-form answers into zero so that a
Pauli question yields a complete `PauliRegister`-indexed measurement. -/
def pauliAnswerOrZero {P : AdmissibleParams} : PauliAnswer P → PauliRegister P
  | .pauliOutcome u => u
  | _ => 0

/-- A finite sum code used only to construct the `Fintype` instance for the
answer alphabet in `def:pauli-win-predicate`, blueprint
`ch13_qpbt_test.tex:331-367`, paper origin
`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:1126-1225`.
-/
abbrev PauliAnswerCode (P : AdmissibleParams) :=
  PauliScalar P ⊕
    ((Fin (P.d + 1) → PauliScalar P) ⊕
      ((Fin (P.m * P.d + 1) → PauliScalar P) ⊕
        ((ZMod 2 × ZMod 2) ⊕
          (ZMod 2 ⊕ ((Fin 3 → ZMod 2) ⊕ PauliRegister P)))))

/-- The constructor-preserving finite-code equivalence for `PauliAnswer`.
Lean-only infrastructure for `def:pauli-win-predicate`, blueprint
`ch13_qpbt_test.tex:331-367`, paper origin
`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:1126-1225`.
-/
noncomputable def pauliAnswerEquiv (P : AdmissibleParams) :
    PauliAnswer P ≃ PauliAnswerCode P where
  toFun
    | .value a => .inl a
    | .alinePoly a => .inr (.inl a)
    | .dlinePoly a => .inr (.inr (.inl a))
    | .pairBits a => .inr (.inr (.inr (.inl a)))
    | .bit a => .inr (.inr (.inr (.inr (.inl a))))
    | .msTriple a => .inr (.inr (.inr (.inr (.inr (.inl a)))))
    | .pauliOutcome a => .inr (.inr (.inr (.inr (.inr (.inr a)))))
  invFun
    | .inl a => .value a
    | .inr (.inl a) => .alinePoly a
    | .inr (.inr (.inl a)) => .dlinePoly a
    | .inr (.inr (.inr (.inl a))) => .pairBits a
    | .inr (.inr (.inr (.inr (.inl a)))) => .bit a
    | .inr (.inr (.inr (.inr (.inr (.inl a))))) => .msTriple a
    | .inr (.inr (.inr (.inr (.inr (.inr a))))) => .pauliOutcome a
  left_inv := by
    intro x
    cases x <;> rfl
  right_inv := by
    intro x
    cases x with
    | inl a => rfl
    | inr x =>
        cases x with
        | inl a => rfl
        | inr x =>
            cases x with
            | inl a => rfl
            | inr x =>
                cases x with
                | inl a => rfl
                | inr x =>
                    cases x with
                    | inl a => rfl
                    | inr x =>
                        cases x with
                        | inl a => rfl
                        | inr a => rfl

noncomputable instance (P : AdmissibleParams) : Fintype (PauliAnswer P) :=
  Fintype.ofEquiv (PauliAnswerCode P) (pauliAnswerEquiv P).symm

instance (P : AdmissibleParams) : Inhabited (PauliAnswer P) :=
  ⟨.bit 0⟩

/-- The phase bit `γ(u_X,u_Z,r_X,r_Z)` from `eq:gamma-value`.  It uses the
fixed trace selected by `P.model`, as required by the paper's fixed
self-dual-normal representation.  Blueprint
`blueprint/src/chapter/ch13_qpbt_test.tex:331-367`; paper origin
`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:1198-1212`.
-/
noncomputable def gammaValue (P : AdmissibleParams)
    (uX uZ : Fin P.m → PauliScalar P)
    (rX rZ : PauliScalar P) : ZMod 2 :=
  fixedBinTrace P.model
    (dotProduct (rX • indicatorVec uX) (rZ • indicatorVec uZ))

/-- The commutation bit attached to a full Pauli ambient question, from
`eq:gamma-value` in `def:pauli-win-predicate`, blueprint
`ch13_qpbt_test.tex:331-367`, paper origin
`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:1198-1212`.
-/
noncomputable def pauliPairGamma (P : AdmissibleParams) (z : PauliSpace P) : ZMod 2 :=
  gammaValue P (pauliXBlock z) (pauliZBlock z)
    (pauliRXBlock z) (pauliRZBlock z)

/-- The answer constructor prescribed by each Pauli question type; this is the
well-formedness part of `def:pauli-win-predicate`, blueprint
`ch13_qpbt_test.tex:331-367`, paper origin
`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:1126-1225`.
-/
def validPauliAnswer {P : AdmissibleParams} (t : PauliType) (a : PauliAnswer P) : Bool :=
  match t, a with
  | .point _, .value _ => true
  | .aline _, .alinePoly _ => true
  | .dline _, .dlinePoly _ => true
  | .pauli _, .pauliOutcome _ => true
  | .pairW _, .bit _ => true
  | .pair, .pairBits _ => true
  | .ms (.constraint _), .msTriple _ => true
  | .ms (.var _), .bit _ => true
  | _, _ => false

/-- The axis-line versus point relation used by `def:pauli-win-predicate`,
blueprint `ch13_qpbt_test.tex:331-367`, paper origin
`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:1126-1225`.
-/
def pauliAlinePointCondition (P : AdmissibleParams) (W : PauliKind)
    (line point : PauliSpace P) (f : Fin (P.d + 1) → PauliScalar P)
    (a : PauliScalar P) : Prop :=
  -- The universal form preserves the source's zero-direction convention.
  ∀ t : PauliScalar P,
    pauliPointBlock W point =
        pauliPointBlock W line + t • coordinateDirection
          (chiIndex P.toLdParams (pauliScalarBlock line)) →
      evalCoefficient f t = a

/-- The diagonal-line versus point relation used by `def:pauli-win-predicate`,
blueprint `ch13_qpbt_test.tex:331-367`, paper origin
`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:1126-1225`.
-/
def pauliDlinePointCondition (P : AdmissibleParams) (W : PauliKind)
    (line point : PauliSpace P) (f : Fin (P.m * P.d + 1) → PauliScalar P)
    (a : PauliScalar P) : Prop :=
  ∀ t : PauliScalar P,
    pauliPointBlock W point = pauliPointBlock W line +
        t • pauliDirectionBlock line →
      evalCoefficient f t = a

/-- The raw Pauli-versus-point consistency relation from `def:pauli-win-predicate`,
blueprint `ch13_qpbt_test.tex:331-367`, paper origin
`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:1126-1225`.
-/
def pauliPointPauliCondition (P : AdmissibleParams) (W : PauliKind)
    (point : PauliSpace P) (h : PauliRegister P) (a : PauliScalar P) : Prop :=
  lowDegreeEnc h (pauliPointBlock W point) = a

/-- The Pair/W consistency relation, including the one-sided gamma gate, from
`def:pauli-win-predicate`, blueprint `ch13_qpbt_test.tex:331-367`, paper origin
`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:1126-1225`.
-/
def pauliPairCondition (P : AdmissibleParams) (W : PauliKind)
    (z : PauliSpace P) (β : ZMod 2) (bits : ZMod 2 × ZMod 2) : Prop :=
  pauliPairGamma P z ≠ 0 ∨
    (match W with
    | .X => bits.1 = β
    | .Z => bits.2 = β)

/-- The point/Pair/W trace consistency relation from `def:pauli-win-predicate`,
blueprint `ch13_qpbt_test.tex:331-367`, paper origin
`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:1126-1225`.
-/
def pauliPointPairCondition (P : AdmissibleParams) (W : PauliKind)
    (z : PauliSpace P) (a : PauliScalar P) (β : ZMod 2) : Prop :=
  pauliPairGamma P z ≠ 0 ∨
    fixedBinTrace P.model
      (a * (match W with
      | .X => pauliRXBlock z
      | .Z => pauliRZBlock z)) = β

/-- The Point/Variable consistency clause of `def:pauli-win-predicate`.
The check is gated by `gamma = 0` and only uses Variable 1 in the X basis or
Variable 5 in the Z basis.  Blueprint
`blueprint/src/chapter/ch13_qpbt_test.tex:331-367`; paper origin
`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:1126-1225`.
-/
def pauliPointVariableCondition (P : AdmissibleParams) (W : PauliKind)
    (z : PauliSpace P) (j : Fin 9) (a : PauliScalar P) (β : ZMod 2) : Prop :=
  pauliPairGamma P z = 0 ∨
    (j = ⟨0, by decide⟩ ∧ W = .X ∧
        fixedBinTrace P.model (a * pauliRXBlock z) = β) ∨
    (j = ⟨4, by decide⟩ ∧ W = .Z ∧
        fixedBinTrace P.model (a * pauliRZBlock z) = β)

/-- The Pauli win predicate, with constructor-shape rejection.  This is
`def:pauli-win-predicate` in `blueprint/src/chapter/ch13_qpbt_test.tex:331-367`,
paper origin `references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:1126-1225`.
-/
noncomputable def pauliWinPredicate (P : AdmissibleParams) :
    PauliQuestion P → PauliQuestion P → PauliAnswer P → PauliAnswer P → Bool :=
  open Classical in
  fun (tA, xA) (tB, xB) a b =>
    if validPauliAnswer tA a && validPauliAnswer tB b then
      if tA = tB then
        decide (a = b)
      else
        match tA, tB, a, b with
      | .aline W, .point W', .alinePoly f, .value u =>
          if W = W' then decide (pauliAlinePointCondition P W xA xB f u) else true
      | .point W, .aline W', .value u, .alinePoly f =>
          if W = W' then decide (pauliAlinePointCondition P W xB xA f u) else true
      | .dline W, .point W', .dlinePoly f, .value u =>
          if W = W' then decide (pauliDlinePointCondition P W xA xB f u) else true
      | .point W, .dline W', .value u, .dlinePoly f =>
          if W = W' then decide (pauliDlinePointCondition P W xB xA f u) else true
      | .point W, .pauli W', .value u, .pauliOutcome h =>
          if W = W' then decide (pauliPointPauliCondition P W xA h u) else true
      | .pauli W, .point W', .pauliOutcome h, .value u =>
          if W = W' then decide (pauliPointPauliCondition P W xB h u) else true
      | .pairW W, .pair, .bit β, .pairBits bits =>
          decide (pauliPairCondition P W xA β bits)
      | .pair, .pairW W, .pairBits bits, .bit β =>
          decide (pauliPairCondition P W xB β bits)
      | .point W, .pairW W', .value u, .bit β =>
          if W = W' then decide (pauliPointPairCondition P W xB u β) else true
      | .pairW W, .point W', .bit β, .value u =>
          if W = W' then decide (pauliPointPairCondition P W xA u β) else true
      | .ms (.constraint i), .ms (.var j), .msTriple β, .bit γ =>
          if ∃ k : Fin 3, msConstraintVars i k = j then
            decide (pauliPairGamma P xA = 0 ∨
              msWinPredicate (.constraint i) (.var j) (.triple β) (.bit γ))
          else true
      | .ms (.var j), .ms (.constraint i), .bit γ, .msTriple β =>
          if ∃ k : Fin 3, msConstraintVars i k = j then
            decide (pauliPairGamma P xB = 0 ∨
              msWinPredicate (.var j) (.constraint i) (.bit γ) (.triple β))
          else true
      | .point W, .ms (.var j), .value u, .bit β =>
          decide (pauliPointVariableCondition P W xB j u β)
      | .ms (.var j), .point W, .bit β, .value u =>
          decide (pauliPointVariableCondition P W xA j u β)
        | _, _, _, _ => true
    else false

/-- The Pauli basis test game.  This is `def:pauli-question-distribution` and
`def:pauli-win-predicate` packaged as the symmetric game of
`blueprint/src/chapter/ch13_qpbt_test.tex:285-367`, paper origin
`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:964-1225`.
-/
noncomputable def pauliBasisTest (P : AdmissibleParams) : Game where
  QuestionA := PauliQuestion P
  QuestionB := PauliQuestion P
  AnswerA := PauliAnswer P
  AnswerB := PauliAnswer P
  μ := pauliQuestionDistribution P
  μ_prob := by
    classical
    letI : Nonempty PauliEdge := pauliEdge_nonempty
    exact Distribution.IsProbability.map
      (uniformDistribution_isProbability (PauliEdge × PauliSpace P)) _
  decide := pauliWinPredicate P

end

end MIPStarRE.QPBT
