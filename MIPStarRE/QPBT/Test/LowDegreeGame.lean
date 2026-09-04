import MIPStarRE.QPBT.Algebra.FieldBasis
import MIPStarRE.QPBT.Algebra.Lines
import MIPStarRE.QPBT.Games.CondLinear
import MIPStarRE.QPBT.Games.Defs

/-!
# The low-degree game

This file introduces the finite question and answer alphabets used by the
low-degree component of the Pauli basis test.  The maps are explicit maps on
the ambient coefficient space, and their conditional-linearity levels are
established below; the line-point distributions they induce are analysed in
`MIPStarRE/QPBT/Test/LowDegreeGameTheorems.lean`.

## References

The source-facing nodes are `def:ld-game`, `def:ld-question-distribution`, and
`def:ld-win-predicate` in
`blueprint/src/chapter/ch13_qpbt_test.tex:17-156`; their paper origin is
`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:31-391`.
-/

open scoped BigOperators

namespace MIPStarRE.QPBT

open MIPStarRE.LDT

noncomputable section

/-- Numerical parameters for the low-degree game.  The ambient coefficient
space uses the once-and-for-all model `fixedFieldModel P.q P.hq`, rather than a
model supplied by each parameter record.  This is the Lean carrier for
`def:ld-game` in
`blueprint/src/chapter/ch13_qpbt_test.tex:17-156`, with paper origin
`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:31-391`.
-/
structure LdParams where
  q : ℕ
  m : ℕ
  d : ℕ
  k : ℕ
  hm : 1 ≤ m
  hd : 1 ≤ d
  hk : 1 ≤ k
  hq : IsAdmissibleSize q
  hdvd : m ∣ q

/-- The positive dimension in `LdParams` supplies the finite coordinate type
used by the uniform axis and prefix-index marginals. -/
instance (L : LdParams) : Nonempty (Fin L.m) :=
  ⟨⟨0, lt_of_lt_of_le Nat.zero_lt_one L.hm⟩⟩

/-- The fixed model accessor for an `LdParams` record.  It is a compatibility
view of the global `fixedFieldModel` selector, not an independently quantified
parameter.  Blueprint `ch13_qpbt_test.tex:17-32`; paper origin
`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:31-391`.
-/
noncomputable def LdParams.model (P : LdParams) : FixedFieldModel P.q :=
  fixedFieldModel P.q P.hq

/-- The scalar carrier selected by an `LdParams` record; this is the fixed
field carrier in `def:ld-game`, selected globally by `LdParams.model`.
Blueprint `ch13_qpbt_test.tex:17-32`, paper origin
`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:31-391`.
-/
abbrev ScalarQ (P : LdParams) := (P.model).K

/-- The three low-degree question types of `def:ld-game`, blueprint
`blueprint/src/chapter/ch13_qpbt_test.tex:17-32`, paper origin
`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:31-391`.
-/
inductive LdType where
  | point
  | aline
  | dline
  deriving DecidableEq, Repr, Inhabited, Fintype

/-- The register index used by the low-degree game (`def:ld-game`, blueprint
`ch13_qpbt_test.tex:17-32`; paper origin
`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:31-391`).
-/
abbrev LdIndex (P : LdParams) := (Fin P.m ⊕ Unit) ⊕ Fin P.m

/-- The full ambient low-degree coefficient space (`def:ld-game`, blueprint
`ch13_qpbt_test.tex:17-32`; paper origin
`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:31-391`).
-/
abbrev LdSpace (P : LdParams) := LdIndex P → ScalarQ P

/-- The point coordinates of an ambient low-degree vector in
`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:31-391`.
-/
def LdSpace.point {P : LdParams} (z : LdSpace P) : Fin P.m → ScalarQ P :=
  fun i => z (.inl (.inl i))

/-- The shared scalar coordinate of an ambient low-degree vector in
`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:31-391`.
-/
def LdSpace.seed {P : LdParams} (z : LdSpace P) : ScalarQ P :=
  z (.inl (.inr ()) )

/-- The direction coordinates of an ambient low-degree vector in
`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:31-391`.
-/
def LdSpace.direction {P : LdParams} (z : LdSpace P) : Fin P.m → ScalarQ P :=
  fun i => z (.inr i)

/-- The integer-coordinate map `χ` from the fixed field representation.  This
is `eq:chi-func` in `def:ld-question-distribution`, blueprint
`blueprint/src/chapter/ch13_qpbt_test.tex:34-59`, paper origin
`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:31-391`.
-/
noncomputable def chiIndex (P : LdParams) (s : ScalarQ P) : Fin P.m := by
  letI : NeZero P.m := ⟨by
    exact Nat.ne_of_gt (lt_of_lt_of_le Nat.zero_lt_one P.hm)⟩
  exact Fin.ofNat P.m ((binaryRepresentation P.model s).val / (P.q / P.m))

/-- The projection used in the diagonal-line map zeroes coordinates before the
chosen index and retains the suffix of the direction vector.  This is the
prefix restriction in `def:ld-question-distribution`, blueprint
`blueprint/src/chapter/ch13_qpbt_test.tex:34-59`, paper origin
`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:31-391`.
-/
def prefixProjection {P : LdParams} (i : Fin P.m) (v : Fin P.m → ScalarQ P) :
    Fin P.m → ScalarQ P :=
  fun j => if j.val < i.val then 0 else v j

/-- The point CL map, retaining the point block and clearing the auxiliary
blocks.  It is the map `L_point` of `def:ld-question-distribution`, blueprint
`blueprint/src/chapter/ch13_qpbt_test.tex:34-59`, paper origin
`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:31-391`.
-/
def ldPointCL (P : LdParams) (z : LdSpace P) : LdSpace P :=
  fun i => match i with
  | .inl (.inl j) => z (.inl (.inl j))
  | .inl (.inr _) => 0
  | .inr _ => 0

/-- The affine-line CL map.  The direction block is put through the canonical
line representative map from `def:line-representative`, while the point block
is retained (blueprint `blueprint/src/chapter/ch13_qpbt_test.tex:34-59`; paper
origin `references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:31-391`).
-/
noncomputable def ldALineCL (P : LdParams) (z : LdSpace P) : LdSpace P :=
  let i := chiIndex P (z.seed)
  let rep := lineRepMap (coordinateDirection i)
  fun i => match i with
  | .inl (.inl j) => (rep (z.point)) j
  | .inl (.inr _) => z (.inl (.inr ()))
  | .inr _ => 0

/-- The diagonal-line CL map, using the same canonical representative interface
for the direction block.  This is the `L_DLine` clause of
`def:ld-question-distribution` (blueprint
`blueprint/src/chapter/ch13_qpbt_test.tex:34-59`; paper origin
`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:31-391`).
-/
noncomputable def ldDLineCL (P : LdParams) (z : LdSpace P) : LdSpace P :=
  let i := chiIndex P (z.seed)
  let direction := prefixProjection i (z.direction)
  let rep := lineRepMap direction
  fun i => match i with
  | .inl (.inl j) => (rep (z.point)) j
  | .inl (.inr _) => z (.inl (.inr ()))
  | .inr j => direction j

/-- Dispatch the three low-degree CL maps by question type.  This is the typed
construction in `def:ld-question-distribution`, blueprint
`blueprint/src/chapter/ch13_qpbt_test.tex:34-59`, paper origin
`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:31-391`.
-/
noncomputable def ldCL (P : LdParams) : LdType → LdSpace P → LdSpace P
  | .point => ldPointCL P
  | .aline => ldALineCL P
  | .dline => ldDLineCL P

/-- Formalization-only auxiliary: the register carrying the shared scalar
coordinate of the ambient low-degree space.  It is the first register in the
concatenation exhibiting the conditional-linearity levels asserted in
`def:ld-question-distribution`, blueprint
`blueprint/src/chapter/ch13_qpbt_test.tex:34-59`, paper origin
`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:31-391`. -/
private def ldSeedRegister (P : LdParams) : Finset (LdIndex P) :=
  {Sum.inl (Sum.inr ())}

/-- Formalization-only auxiliary: the register carrying the point coordinates
of the ambient low-degree space; see `ldSeedRegister`. -/
private def ldPointRegister (P : LdParams) : Finset (LdIndex P) :=
  Finset.univ.image fun j : Fin P.m => (Sum.inl (Sum.inl j) : LdIndex P)

/-- Formalization-only auxiliary: the register carrying the direction
coordinates of the ambient low-degree space; see `ldSeedRegister`. -/
private def ldDirectionRegister (P : LdParams) : Finset (LdIndex P) :=
  Finset.univ.image fun j : Fin P.m => (Sum.inr j : LdIndex P)

/-- Formalization-only auxiliary: the linear map retaining the shared scalar
coordinate and clearing every other coordinate. -/
private def ldSeedLinear (P : LdParams) :
    LdSpace P →ₗ[ScalarQ P] LdSpace P where
  toFun x := fun i =>
    match i with
    | .inl (.inl _) => 0
    | .inl (.inr _) => x (Sum.inl (Sum.inr ()))
    | .inr _ => 0
  map_add' x y := by
    funext i
    rcases i with (j | u) | j <;> simp
  map_smul' c x := by
    funext i
    rcases i with (j | u) | j <;> simp

/-- Formalization-only auxiliary: the linear map sending the point block to its
canonical line representative in the fixed direction `v` and clearing every
other coordinate. -/
private noncomputable def ldPointCLLinear (P : LdParams) (v : Fin P.m → ScalarQ P) :
    LdSpace P →ₗ[ScalarQ P] LdSpace P where
  toFun x := fun i =>
    match i with
    | .inl (.inl j) => lineRepMap v (LdSpace.point x) j
    | .inl (.inr _) => 0
    | .inr _ => 0
  map_add' x y := by
    funext i
    rcases i with (j | u) | j
    · change lineRepMap v (LdSpace.point (x + y)) j = _
      have hpoint : LdSpace.point (x + y) = LdSpace.point x + LdSpace.point y := rfl
      rw [hpoint, map_add]
      rfl
    · simp
    · simp
  map_smul' c x := by
    funext i
    rcases i with (j | u) | j
    · change lineRepMap v (LdSpace.point (c • x)) j = _
      have hpoint : LdSpace.point (c • x) = c • LdSpace.point x := rfl
      rw [hpoint, map_smul]
      rfl
    · simp
    · simp

/-- Formalization-only auxiliary: the linear map zeroing the first `i`
coordinates of the direction block and clearing every other coordinate. -/
private def ldDirectionCLLinear (P : LdParams) (i : Fin P.m) :
    LdSpace P →ₗ[ScalarQ P] LdSpace P where
  toFun x := fun k =>
    match k with
    | .inl (.inl _) => 0
    | .inl (.inr _) => 0
    | .inr j => prefixProjection i (LdSpace.direction x) j
  map_add' x y := by
    funext k
    rcases k with (j | u) | j
    · simp
    · simp
    · change prefixProjection i (LdSpace.direction (x + y)) j =
        prefixProjection i (LdSpace.direction x) j +
          prefixProjection i (LdSpace.direction y) j
      by_cases h : j.val < i.val
      · simp only [prefixProjection, if_pos h, add_zero]
      · simp only [prefixProjection, if_neg h]
        rfl
  map_smul' c x := by
    funext k
    rcases k with (j | u) | j
    · simp
    · simp
    · change prefixProjection i (LdSpace.direction (c • x)) j =
        c • prefixProjection i (LdSpace.direction x) j
      by_cases h : j.val < i.val
      · simp only [prefixProjection, if_pos h, smul_zero]
      · simp only [prefixProjection, if_neg h]
        rfl

/-- Formalization-only auxiliary lemma: the shared-scalar map vanishes
outside the scalar register. -/
private theorem ldSeedLinear_supported (P : LdParams) :
    ∀ (x : LdSpace P) (i : LdIndex P), i ∉ ldSeedRegister P →
      ldSeedLinear P x i = 0 := by
  intro x i hi
  rcases i with (j | u) | j
  · rfl
  · cases u
    exact absurd (Finset.mem_singleton_self _) hi
  · rfl

/-- Formalization-only auxiliary lemma: the canonical-representative map
vanishes outside the point register. -/
private theorem ldPointCLLinear_supported (P : LdParams) (v : Fin P.m → ScalarQ P) :
    ∀ (x : LdSpace P) (i : LdIndex P), i ∉ ldPointRegister P →
      ldPointCLLinear P v x i = 0 := by
  intro x i hi
  rcases i with (j | u) | j
  · exact absurd (Finset.mem_image_of_mem _ (Finset.mem_univ j)) hi
  · rfl
  · rfl

/-- Formalization-only auxiliary lemma: the prefix-zeroing map vanishes
outside the direction register. -/
private theorem ldDirectionCLLinear_supported (P : LdParams) (i : Fin P.m) :
    ∀ (x : LdSpace P) (k : LdIndex P), k ∉ ldDirectionRegister P →
      ldDirectionCLLinear P i x k = 0 := by
  intro x k hk
  rcases k with (j | u) | j
  · rfl
  · rfl
  · exact absurd (Finset.mem_image_of_mem _ (Finset.mem_univ j)) hk

/-- Formalization-only auxiliary lemma: the point register is disjoint from
the scalar register. -/
private theorem ldPointRegister_subset_sdiff_seed (P : LdParams) :
    ldPointRegister P ⊆ Finset.univ \ ldSeedRegister P := by
  intro i hi
  obtain ⟨j, -, rfl⟩ := Finset.mem_image.mp hi
  simp [ldSeedRegister]

/-- Formalization-only auxiliary lemma: the direction register is disjoint
from the scalar register. -/
private theorem ldDirectionRegister_subset_sdiff_seed (P : LdParams) :
    ldDirectionRegister P ⊆ Finset.univ \ ldSeedRegister P := by
  intro i hi
  obtain ⟨j, -, rfl⟩ := Finset.mem_image.mp hi
  simp [ldSeedRegister]

/-- Formalization-only auxiliary lemma: the point register is disjoint from
both the scalar and the direction registers. -/
private theorem ldPointRegister_subset_sdiff_seed_direction (P : LdParams) :
    ldPointRegister P ⊆
      (Finset.univ \ ldSeedRegister P) \ ldDirectionRegister P := by
  intro i hi
  obtain ⟨j, -, rfl⟩ := Finset.mem_image.mp hi
  simp [ldSeedRegister, ldDirectionRegister]

/-- Formalization-only auxiliary lemma: restricting to the scalar register
leaves the shared scalar coordinate unchanged. -/
private theorem coordinateRestriction_seed (P : LdParams) (x : LdSpace P) :
    coordinateRestriction (ldSeedRegister P) x (Sum.inl (Sum.inr ())) =
      x (Sum.inl (Sum.inr ())) := by
  have hmem : (Sum.inl (Sum.inr ()) : LdIndex P) ∈ ldSeedRegister P :=
    Finset.mem_singleton_self _
  simp [coordinateRestriction, hmem]

/-- Formalization-only auxiliary lemma: restricting to the point register
leaves the point block unchanged. -/
private theorem coordinateRestriction_point (P : LdParams) (x : LdSpace P) :
    LdSpace.point (coordinateRestriction (ldPointRegister P) x) = LdSpace.point x := by
  funext j
  have hmem : (Sum.inl (Sum.inl j) : LdIndex P) ∈ ldPointRegister P :=
    Finset.mem_image_of_mem _ (Finset.mem_univ j)
  simp [LdSpace.point, coordinateRestriction, hmem]

/-- Formalization-only auxiliary lemma: restricting to the direction register
leaves the direction block unchanged. -/
private theorem coordinateRestriction_direction (P : LdParams) (x : LdSpace P) :
    LdSpace.direction (coordinateRestriction (ldDirectionRegister P) x) =
      LdSpace.direction x := by
  funext j
  have hmem : (Sum.inr j : LdIndex P) ∈ ldDirectionRegister P :=
    Finset.mem_image_of_mem _ (Finset.mem_univ j)
  simp [LdSpace.direction, coordinateRestriction, hmem]

/-- Formalization-only auxiliary: the point-register projection as a linear
map on the ambient low-degree space. -/
private def ldPointLinear (P : LdParams) :
    LdSpace P →ₗ[ScalarQ P] LdSpace P where
  toFun := ldPointCL P
  map_add' x y := by
    funext i
    rcases i with (j | u) | j <;> simp [ldPointCL]
  map_smul' c x := by
    funext i
    rcases i with (j | u) | j <;> simp [ldPointCL]

/-- The point projection is a one-level conditionally linear function. This is
the level assertion for `L_Point` in `def:ld-question-distribution`, blueprint
`blueprint/src/chapter/ch13_qpbt_test.tex:34-59`, paper
`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:203-207`. -/
theorem isCondLinear_ldPointCL (P : LdParams) :
    IsCondLinearOn (ScalarQ P) Finset.univ 1 (ldPointCL P) := by
  refine ⟨.succ Finset.univ (ldPointLinear P)
      (fun _ i hi => absurd (Finset.mem_univ i) hi) (fun _ => .zero),
    ⟨Finset.subset_univ _, fun _ => trivial⟩, ?_⟩
  funext x
  have hx : coordinateRestriction (Finset.univ : Finset (LdIndex P)) x = x := by
    funext i
    simp [coordinateRestriction]
  change ldPointCL P (coordinateRestriction Finset.univ x) + 0 = ldPointCL P x
  rw [hx, add_zero]

/-- Formalization-only auxiliary: a two-level representation of the
affine-line map as a conditionally linear function. -/
private noncomputable def ldALineTerm (P : LdParams) :
    CondLinearTerm (ScalarQ P) (ι := LdIndex P) 2 :=
  .succ (ldSeedRegister P) (ldSeedLinear P) (ldSeedLinear_supported P)
    fun y =>
      .succ (ldPointRegister P)
        (ldPointCLLinear P (coordinateDirection (chiIndex P (LdSpace.seed y))))
        (ldPointCLLinear_supported P _)
        fun _ => .zero

/-- Formalization-only auxiliary: a three-level representation of the
diagonal-line map as a conditionally linear function. -/
private noncomputable def ldDLineTerm (P : LdParams) :
    CondLinearTerm (ScalarQ P) (ι := LdIndex P) 3 :=
  .succ (ldSeedRegister P) (ldSeedLinear P) (ldSeedLinear_supported P)
    fun y =>
      .succ (ldDirectionRegister P)
        (ldDirectionCLLinear P (chiIndex P (LdSpace.seed y)))
        (ldDirectionCLLinear_supported P _)
        fun w =>
          .succ (ldPointRegister P)
            (ldPointCLLinear P (LdSpace.direction w))
            (ldPointCLLinear_supported P _)
            fun _ => .zero

/-- The conditional-linearity level of the affine-line map.  This is
`lem:ld-aline-level`, the level-2 assertion in `def:ld-question-distribution`;
blueprint `blueprint/src/chapter/ch13_qpbt_test.tex:61-71`, paper
`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:31-391`.
-/
theorem isCondLinear_ldALineCL (P : LdParams) :
    IsCondLinearOn (ScalarQ P) Finset.univ 2 (ldALineCL P) := by
  refine ⟨ldALineTerm P, ⟨Finset.subset_univ _, fun _ =>
    ⟨ldPointRegister_subset_sdiff_seed P, fun _ => trivial⟩⟩, ?_⟩
  funext x
  have hseed :
      LdSpace.seed (ldSeedLinear P (coordinateRestriction (ldSeedRegister P) x)) =
        LdSpace.seed x := coordinateRestriction_seed P x
  have hpoint : LdSpace.point (coordinateRestriction (ldPointRegister P) x) =
      LdSpace.point x := coordinateRestriction_point P x
  have hval :
      CondLinearTerm.eval (ldALineTerm P) x =
        ldSeedLinear P (coordinateRestriction (ldSeedRegister P) x) +
          (ldPointCLLinear P (coordinateDirection (chiIndex P (LdSpace.seed x)))
            (coordinateRestriction (ldPointRegister P) x) + 0) := by
    change ldSeedLinear P (coordinateRestriction (ldSeedRegister P) x) +
        (ldPointCLLinear P
            (coordinateDirection (chiIndex P
              (LdSpace.seed (ldSeedLinear P (coordinateRestriction (ldSeedRegister P) x)))))
            (coordinateRestriction (ldPointRegister P) x) + 0) = _
    rw [hseed]
  rw [hval]
  funext i
  rcases i with (j | u) | j
  · change (0 : ScalarQ P) +
        (lineRepMap (coordinateDirection (chiIndex P (LdSpace.seed x)))
          (LdSpace.point (coordinateRestriction (ldPointRegister P) x)) j + 0) =
      lineRepMap (coordinateDirection (chiIndex P (LdSpace.seed x)))
        (LdSpace.point x) j
    rw [hpoint, zero_add, add_zero]
  · change coordinateRestriction (ldSeedRegister P) x (Sum.inl (Sum.inr ())) +
        ((0 : ScalarQ P) + 0) = x (Sum.inl (Sum.inr ()))
    rw [coordinateRestriction_seed, add_zero, add_zero]
  · change (0 : ScalarQ P) + ((0 : ScalarQ P) + 0) = 0
    rw [add_zero, add_zero]

/-- The conditional-linearity level of the diagonal-line map.  This is
`lem:ld-dline-level`, the level-3 assertion in `def:ld-question-distribution`;
blueprint `blueprint/src/chapter/ch13_qpbt_test.tex:73-83`, paper origin
`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:31-391`.
-/
theorem isCondLinear_ldDLineCL (P : LdParams) :
    IsCondLinearOn (ScalarQ P) Finset.univ 3 (ldDLineCL P) := by
  refine ⟨ldDLineTerm P, ⟨Finset.subset_univ _, fun _ =>
    ⟨ldDirectionRegister_subset_sdiff_seed P, fun _ =>
      ⟨ldPointRegister_subset_sdiff_seed_direction P, fun _ => trivial⟩⟩⟩, ?_⟩
  funext x
  have hseed :
      LdSpace.seed (ldSeedLinear P (coordinateRestriction (ldSeedRegister P) x)) =
        LdSpace.seed x := coordinateRestriction_seed P x
  have hpoint : LdSpace.point (coordinateRestriction (ldPointRegister P) x) =
      LdSpace.point x := coordinateRestriction_point P x
  have hdir :
      LdSpace.direction
          (ldDirectionCLLinear P (chiIndex P (LdSpace.seed x))
            (coordinateRestriction (ldDirectionRegister P) x)) =
        prefixProjection (chiIndex P (LdSpace.seed x)) (LdSpace.direction x) := by
    funext j
    change prefixProjection (chiIndex P (LdSpace.seed x))
        (LdSpace.direction (coordinateRestriction (ldDirectionRegister P) x)) j = _
    rw [coordinateRestriction_direction]
  have hval :
      CondLinearTerm.eval (ldDLineTerm P) x =
        ldSeedLinear P (coordinateRestriction (ldSeedRegister P) x) +
          (ldDirectionCLLinear P (chiIndex P (LdSpace.seed x))
              (coordinateRestriction (ldDirectionRegister P) x) +
            (ldPointCLLinear P
                (prefixProjection (chiIndex P (LdSpace.seed x)) (LdSpace.direction x))
                (coordinateRestriction (ldPointRegister P) x) + 0)) := by
    change ldSeedLinear P (coordinateRestriction (ldSeedRegister P) x) +
        (ldDirectionCLLinear P
            (chiIndex P
              (LdSpace.seed (ldSeedLinear P (coordinateRestriction (ldSeedRegister P) x))))
            (coordinateRestriction (ldDirectionRegister P) x) +
          (ldPointCLLinear P
              (LdSpace.direction
                (ldDirectionCLLinear P
                  (chiIndex P
                    (LdSpace.seed
                      (ldSeedLinear P (coordinateRestriction (ldSeedRegister P) x))))
                  (coordinateRestriction (ldDirectionRegister P) x)))
              (coordinateRestriction (ldPointRegister P) x) + 0)) = _
    rw [hseed, hdir]
  rw [hval]
  funext i
  rcases i with (j | u) | j
  · change (0 : ScalarQ P) + ((0 : ScalarQ P) +
        (lineRepMap
          (prefixProjection (chiIndex P (LdSpace.seed x)) (LdSpace.direction x))
          (LdSpace.point (coordinateRestriction (ldPointRegister P) x)) j + 0)) =
      lineRepMap (prefixProjection (chiIndex P (LdSpace.seed x)) (LdSpace.direction x))
        (LdSpace.point x) j
    rw [hpoint, zero_add, zero_add, add_zero]
  · change coordinateRestriction (ldSeedRegister P) x (Sum.inl (Sum.inr ())) +
        ((0 : ScalarQ P) + ((0 : ScalarQ P) + 0)) = x (Sum.inl (Sum.inr ()))
    rw [coordinateRestriction_seed, add_zero, add_zero, add_zero]
  · change (0 : ScalarQ P) +
        (prefixProjection (chiIndex P (LdSpace.seed x))
            (LdSpace.direction (coordinateRestriction (ldDirectionRegister P) x)) j +
          ((0 : ScalarQ P) + 0)) =
      prefixProjection (chiIndex P (LdSpace.seed x)) (LdSpace.direction x) j
    rw [coordinateRestriction_direction, zero_add, add_zero, add_zero]

/-- The question alphabet for the low-degree game (`def:ld-game`, blueprint
`ch13_qpbt_test.tex:17-32`; paper origin
`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:31-391`).
-/
abbrev LdQuestion (P : LdParams) := LdType × LdSpace P

/-- The typed CL question distribution.  This is the inlined construction in
`def:ld-question-distribution`, blueprint `ch13_qpbt_test.tex:34-59`; paper
origin `references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:31-391`.
-/
noncomputable def ldQuestionDistribution (P : LdParams) :
    Distribution (LdQuestion P × LdQuestion P) :=
  Distribution.map
    (uniformDistribution ((LdType × LdType) × LdSpace P))
    (fun s =>
      ((s.1.1, ldCL P s.1.1 s.2), (s.1.2, ldCL P s.1.2 s.2)))

/-- The coefficient-tuple answer alphabet of the low-degree game.  Polynomial
answers are representatives with exactly the coefficient lengths printed in
the paper, as required by `def:ld-win-predicate` (blueprint
`blueprint/src/chapter/ch13_qpbt_test.tex:137-156`; paper
`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:31-391`).
-/
inductive LdAnswer (P : LdParams) where
  | pointVals (a : Fin P.k → ScalarQ P)
  | alinePolys (a : Fin P.k → Fin (P.d + 1) → ScalarQ P)
  | dlinePolys (a : Fin P.k → Fin (P.m * P.d + 1) → ScalarQ P)
  deriving DecidableEq

/-- A finite sum code used only to provide the answer alphabet's `Fintype`
instance; the public constructors are those of `def:ld-win-predicate`,
blueprint `ch13_qpbt_test.tex:137-156`, paper origin
`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:31-391`.
-/
abbrev LdAnswerCode (P : LdParams) :=
  (Fin P.k → ScalarQ P) ⊕
    ((Fin P.k → Fin (P.d + 1) → ScalarQ P) ⊕
      (Fin P.k → Fin (P.m * P.d + 1) → ScalarQ P))

/-- The constructor-preserving code equivalence for `LdAnswer` (Lean-only
finite-carrier infrastructure for `def:ld-win-predicate`, blueprint
`blueprint/src/chapter/ch13_qpbt_test.tex:137-156`, paper origin
`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:31-391`).
-/
noncomputable def ldAnswerEquiv (P : LdParams) :
    LdAnswer P ≃ LdAnswerCode P where
  toFun
    | .pointVals a => .inl a
    | .alinePolys a => .inr (.inl a)
    | .dlinePolys a => .inr (.inr a)
  invFun
    | .inl a => .pointVals a
    | .inr (.inl a) => .alinePolys a
    | .inr (.inr a) => .dlinePolys a
  left_inv := by intro x; cases x <;> rfl
  right_inv := by
    intro x
    cases x with
    | inl a => rfl
    | inr x =>
        cases x with
        | inl a => rfl
        | inr a => rfl

instance (P : LdParams) : Inhabited (LdAnswer P) :=
  ⟨.pointVals (fun _ => 0)⟩

noncomputable instance (P : LdParams) : Fintype (LdAnswer P) :=
  Fintype.ofEquiv (LdAnswerCode P) (ldAnswerEquiv P).symm

/-- Evaluation of a coefficient tuple at a field element.  This is the
representative convention used by the line answers in `def:ld-win-predicate`,
blueprint `blueprint/src/chapter/ch13_qpbt_test.tex:137-156`, paper origin
`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:31-391`.
-/
def evalCoefficient {K : Type*} [Semiring K] {n : ℕ}
    (c : Fin n → K) (t : K) : K :=
  ∑ i : Fin n, c i * t ^ i.val

/-- Check that an answer has the constructor prescribed by its question type;
Lean encoding of the rejection clause in `def:ld-win-predicate`, blueprint
`ch13_qpbt_test.tex:137-156`, paper origin
`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:31-391`.
-/
def validLdAnswer {P : LdParams} (t : LdType) (a : LdAnswer P) : Bool :=
  match t, a with
  | .point, .pointVals _ => true
  | .aline, .alinePolys _ => true
  | .dline, .dlinePolys _ => true
  | _, _ => false

/-- The axis-parallel line/point relation in `def:ld-win-predicate`, blueprint
`ch13_qpbt_test.tex:137-156`, paper origin
`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:31-391`.
-/
def alinePointCondition (P : LdParams) (line point : LdSpace P)
    (f : Fin P.k → Fin (P.d + 1) → ScalarQ P)
    (a : Fin P.k → ScalarQ P) : Prop :=
  -- Universal quantification follows the zero-direction convention in
  -- `rem:ld-win-zero-direction`.
  ∀ t : ScalarQ P,
    point.point = line.point + t • coordinateDirection (chiIndex P line.seed) →
      ∀ j : Fin P.k, evalCoefficient (f j) t = a j

/-- The diagonal line/point relation in `def:ld-win-predicate`, blueprint
`ch13_qpbt_test.tex:137-156`, paper origin
`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:31-391`.
-/
def dlinePointCondition (P : LdParams) (line point : LdSpace P)
    (f : Fin P.k → Fin (P.m * P.d + 1) → ScalarQ P)
    (a : Fin P.k → ScalarQ P) : Prop :=
  ∀ t : ScalarQ P,
    point.point = line.point + t • line.direction →
      ∀ j : Fin P.k, evalCoefficient (f j) t = a j

/-- The low-degree consistency predicate, rejecting answers of the wrong
constructor shape.  This is `def:ld-win-predicate` in
`blueprint/src/chapter/ch13_qpbt_test.tex:137-156`, paper origin
`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:31-391`.
-/
noncomputable def ldWinPredicate (P : LdParams) :
    LdQuestion P → LdQuestion P → LdAnswer P → LdAnswer P → Bool :=
  open Classical in
  fun (tA, xA) (tB, xB) a b =>
      if validLdAnswer tA a && validLdAnswer tB b then
        match tA, tB, a, b with
        | .point, .point, .pointVals u, .pointVals v => decide (u = v)
        | .aline, .point, .alinePolys f, .pointVals u =>
            decide (alinePointCondition P xA xB f u)
        | .point, .aline, .pointVals u, .alinePolys f =>
            decide (alinePointCondition P xB xA f u)
        | .dline, .point, .dlinePolys f, .pointVals u =>
            decide (dlinePointCondition P xA xB f u)
        | .point, .dline, .pointVals u, .dlinePolys f =>
            decide (dlinePointCondition P xB xA f u)
        | .aline, .aline, .alinePolys f, .alinePolys g => decide (f = g)
        | .dline, .dline, .dlinePolys f, .dlinePolys g => decide (f = g)
        | _, _, _, _ => true
      else false

/-- The low-degree game packaged as a `Game`.  This is `def:ld-game` in
`blueprint/src/chapter/ch13_qpbt_test.tex:17-156`, paper origin
`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:31-391`.
-/
noncomputable def ldGame (P : LdParams) : Game where
  QuestionA := LdQuestion P
  QuestionB := LdQuestion P
  AnswerA := LdAnswer P
  AnswerB := LdAnswer P
  μ := ldQuestionDistribution P
  μ_prob := by
    exact Distribution.IsProbability.map
      (uniformDistribution_isProbability ((LdType × LdType) × LdSpace P)) _
  decide := ldWinPredicate P

end

end MIPStarRE.QPBT
