import MIPStarRE.QPBT.Extraction.Consistency
import MIPStarRE.QPBT.Test.SoundnessDefs

/-!
# Extraction by the swap unitaries

The concrete swap operators below yield the Pauli extraction conclusion. The
local maps are constructed from the global polynomial
measurements, and all operators retain the heterogeneous Alice and Bob
placements. The generalized Pauli projectors use the field and basis fixed by
`P.model`.

## References

The extraction witness records the conclusion of blueprint `lem:qld-unitary`,
from
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1666-1860`.
The error-form comparison formalizes `lem:qld-extraction-error-form` and
supports `rem:pauli-robustness-form` in the blueprint; its paper source is
lines 1855-1858 and 1868-1876.
-/

open scoped BigOperators Matrix

namespace MIPStarRE.QPBT

open MIPStarRE.LDT MIPStarRE.Quantum

noncomputable section

/-- The concrete conclusion of `lem:qld-unitary`: the two swap maps extract an
EPR state and conjugate each player's total Pauli measurement to the canonical
Pauli projectors. The answer sum in `pauli_close` is over
`PauliRegister P`; the uniform distribution on `Unit` records that there is no
average over questions.

Blueprint `lem:qld-unitary`; paper
`14_analysis_of_the_pauli_basis_test.tex:1666-1685,1827-1859`. The swap maps
are `swapUnitary w .alice` and `swapUnitary w .bob`, defined from the
side-indexed global measurements, and use only the basis fixed by `P.model`.
-/
structure ExtractionWitness {P : AdmissibleParams} {epsilon deltaS : ℝ}
    (S : ProjectiveSetting P epsilon) (w : GlobalPairWitness S deltaS)
    (delta : ℝ) where
  /-- Each swap map is a right unitary. -/
  swap_right_unitary : ∀ side : PlayerSide,
    swapUnitary w side * (swapUnitary w side)ᴴ = 1
  /-- Each swap map is a left unitary. -/
  swap_left_unitary : ∀ side : PlayerSide,
    (swapUnitary w side)ᴴ * swapUnitary w side = 1
  /-- The auxiliary state on registers `AA'BB'`. -/
  aux : EuclideanSpace ℂ
    (ExtractionAuxRegisters P S.toStrategy.ιA S.toStrategy.ιB)
  /-- The auxiliary state is normalized. -/
  aux_norm : ‖aux‖ = 1
  /-- Applying both concrete swap maps to the expanded state extracts the ideal
  auxiliary-state/EPR tensor product. -/
  state_close :
    ‖S.applyBoth (swapUnitary w .alice) (swapUnitary w .bob) S.psiHat -
        S.idealExpState aux‖ ^ 2 ≤ delta
  /-- On the ideal extracted state, conjugated total-Pauli effects are close to
  the canonical projectors, for both players and both Pauli bases. -/
  pauli_close : ∀ (side : PlayerSide) (W : PauliKind),
    opFamilyDistSq (uniformDistribution Unit)
      (fun (_ : Unit) (h : PauliRegister P) =>
        conjBy (S.placeSide side (swapUnitary w side))
          (S.placePlayer side ((S.pauliMeas side W).effect h)))
      (fun (_ : Unit) (h : PauliRegister P) =>
        S.placeExtractedRegister side (pauliProj W h))
      (S.idealExpState aux) ≤ delta

/-- Conditional extraction for the concrete swap maps at the explicit scale
obtained by applying `deltaExtract` to `deltaConstructPaulis`. Given a
`GlobalPairWitness`, it supplies the extraction data appearing in
blueprint `lem:qld-unitary` and paper
`14_analysis_of_the_pauli_basis_test.tex:1666-1860`.

**Unfaithful:** This result assumes `w : GlobalPairWitness S deltaG`, which is
derived inside `lem:qld-unitary` rather than assumed by the paper statement.
The discrepancy is documented in
`docs/paper-gaps/qpbt_extraction-transfer.tex`. Elimination: obtain `w` from
`exists_globalPairWitness` before applying this conditional extraction result; issue
#123 tracks that composition.

**Local fix:** the positive-contraction estimate and normalization case split
repair the two numerical defects at paper lines 1743-1783 without changing the
conclusion; see `docs/paper-gaps/qpbt_extraction-transfer.tex`.

**Proof obligation:** issue #47 tracks the EPR projection argument and the
Schwartz-Zippel comparison at paper lines 1715-1858. Discharge: construct
`aux` from the EPR projection of the swapped state, use the corrected
small-error case split, and combine the point-measurement consistency with the
exact swap conjugation identities. -/
theorem exists_extractionWitness_ofGlobalPairWitness :
    ∃ C : ℝ, 1 ≤ C ∧
      ∀ (P : AdmissibleParams) (epsilon deltaG : ℝ),
        0 ≤ epsilon → epsilon ≤ 1 → 0 ≤ deltaG →
          ∀ (S : ProjectiveSetting P epsilon)
            (w : GlobalPairWitness S deltaG),
            Nonempty
              (ExtractionWitness S w
                (deltaExtract C
                  (deltaConstructPaulis C epsilon deltaG P.m P.d P.q)
                  P.m P.d P.q)) := by
  sorry

/-- The composed construction and extraction errors preserve the error family
of `thm:pauli`: when `deltaG` has the form
`deltaQld a b epsilon m d q`, the result is bounded by another member of that
family after decreasing the exponent and enlarging the universal constant.

This is `lem:qld-extraction-error-form` in the blueprint and the named
quantitative obligation behind `rem:pauli-robustness-form`; the concluding
paper comparison is at
`14_analysis_of_the_pauli_basis_test.tex:1855-1858,1868-1876`.

One may take `a' = 4 * C^2 * a` and `b' = b / 8`. Subadditivity of the
fourth root bounds the three construction terms separately. Admissibility
gives `md ≥ 1` and `q ≥ 1`, so their polynomial factors and the term `md/q`
are absorbed into the enlarged prefactor. This discharges the scalar
estimate tracked by issue #241. -/
theorem deltaExtract_le_deltaQld (C a b : ℝ) (hC : 1 ≤ C) (ha : 1 < a)
    (hb : 0 < b) (hb1 : b < 1) :
    ∃ a' b' : ℝ, 1 ≤ a' ∧ 0 < b' ∧ b' < 1 ∧
      ∀ (P : AdmissibleParams) (epsilon : ℝ), 0 ≤ epsilon →
        epsilon ≤ 1 →
        deltaExtract C
            (deltaConstructPaulis C epsilon
              (deltaQld a b epsilon P.m P.d P.q) P.m P.d P.q)
            P.m P.d P.q ≤
          deltaQld a' b' epsilon P.m P.d P.q := by
  have hC0 : 0 ≤ C := by linarith
  have ha0 : 0 ≤ a := by linarith
  have hconstant : a ≤ 4 * C ^ 2 * a := by
    have hCsq : 1 ≤ C ^ 2 := by nlinarith
    nlinarith [mul_le_mul_of_nonneg_right hCsq ha0]
  refine ⟨4 * C ^ 2 * a, b / 8, ha.le.trans hconstant, by positivity, by linarith, ?_⟩
  intro params epsilon hepsilon0 hepsilon1
  let degree : ℝ := ((params.m * params.d : ℕ) : ℝ)
  have hdegree1 : 1 ≤ degree :=
    Nat.one_le_cast.mpr (Nat.mul_pos params.one_le_m params.hd)
  have hdegree0 : 0 ≤ degree := by linarith
  have hfield1 : (1 : ℝ) ≤ (params.q : ℝ) := by
    obtain ⟨size, -, hsize⟩ := params.hq
    rw [hsize]
    exact_mod_cast Nat.one_le_pow _ _ (by norm_num)
  have hfield0 : (0 : ℝ) ≤ (params.q : ℝ) := by positivity
  let amplitude : ℝ := a * degree ^ a
  let rate : ℝ := epsilon ^ (b / 8) + (params.q : ℝ) ^ (-(b / 8)) +
    (2 : ℝ) ^ (-((b / 8) * degree))
  have hamplitude1 : 1 ≤ amplitude :=
    one_le_mul_of_one_le_of_one_le ha.le (Real.one_le_rpow hdegree1 ha0)
  have hamplitude0 : 0 ≤ amplitude := by linarith
  have hdegree_amplitude : degree ≤ amplitude :=
    (Real.self_le_rpow_of_one_le hdegree1 ha.le).trans
      (le_mul_of_one_le_left (Real.rpow_nonneg hdegree0 a) ha.le)
  have hrate0 : 0 ≤ rate := by dsimp [rate]; positivity
  have hepsilon_rate : epsilon ^ (b / 8) ≤ rate := by
    dsimp [rate]
    linarith [Real.rpow_nonneg hfield0 (-(b / 8)),
      Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 2) (-((b / 8) * degree))]
  have hfield_rate : (params.q : ℝ) ^ (-(b / 8)) ≤ rate := by
    dsimp [rate]
    linarith [Real.rpow_nonneg hepsilon0 (b / 8),
      Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 2) (-((b / 8) * degree))]
  have hroot_sum {first second third : ℝ}
      (hfirst : 0 ≤ first) (hsecond : 0 ≤ second) (hthird : 0 ≤ third) :
      (first + second + third) ^ (1 / 4 : ℝ) ≤
        first ^ (1 / 4 : ℝ) + second ^ (1 / 4 : ℝ) + third ^ (1 / 4 : ℝ) :=
    (Real.rpow_add_le_add_rpow (p := (1 / 4 : ℝ)) (add_nonneg hfirst hsecond) hthird
      (by norm_num) (by norm_num)).trans
      (add_le_add (Real.rpow_add_le_add_rpow (p := (1 / 4 : ℝ)) hfirst hsecond
        (by norm_num) (by norm_num)) le_rfl)
  have hrate_root :
      (epsilon ^ b + (params.q : ℝ) ^ (-b) + (2 : ℝ) ^ (-(b * degree))) ^
        (1 / 4 : ℝ) ≤ rate := by
    refine (hroot_sum (by positivity) (by positivity) (by positivity)).trans ?_
    rw [← Real.rpow_mul hepsilon0, ← Real.rpow_mul hfield0,
      ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
    refine add_le_add (add_le_add ?_ ?_) ?_
    · exact Real.rpow_le_rpow_of_exponent_ge' hepsilon0 hepsilon1
        (by positivity) (by linarith)
    · exact Real.rpow_le_rpow_of_exponent_le hfield1 (by linarith)
    · apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
      nlinarith [mul_nonneg hb.le hdegree0]
  have hglobal0 : 0 ≤ deltaQld a b epsilon params.m params.d params.q := by
    simp only [deltaQld, Real.rpow_eq_pow]
    positivity
  have hglobal_root :
      (deltaQld a b epsilon params.m params.d params.q) ^ (1 / 4 : ℝ) ≤
        amplitude * rate := by
    change (amplitude *
      (epsilon ^ b + (params.q : ℝ) ^ (-b) + (2 : ℝ) ^ (-(b * degree)))) ^
        (1 / 4 : ℝ) ≤ amplitude * rate
    rw [Real.mul_rpow hamplitude0 (by positivity)]
    exact mul_le_mul (Real.rpow_le_self_of_one_le hamplitude1 (by norm_num))
      hrate_root (by positivity) hamplitude0
  have hsqrt_root : (Real.sqrt epsilon) ^ (1 / 4 : ℝ) ≤ amplitude * rate := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hepsilon0]
    exact ((Real.rpow_le_rpow_of_exponent_ge' hepsilon0 hepsilon1
      (by positivity) (by linarith)).trans hepsilon_rate).trans
      (le_mul_of_one_le_left hrate0 hamplitude1)
  have hratio_root : (degree / (params.q : ℝ)) ^ (1 / 4 : ℝ) ≤ amplitude * rate := by
    rw [Real.div_rpow hdegree0 hfield0, div_eq_mul_inv, ← Real.rpow_neg hfield0]
    exact mul_le_mul
      ((Real.rpow_le_self_of_one_le hdegree1 (by norm_num)).trans hdegree_amplitude)
      ((Real.rpow_le_rpow_of_exponent_le hfield1 (by linarith)).trans hfield_rate)
      (by positivity) hamplitude0
  have hratio : degree / (params.q : ℝ) ≤ amplitude * rate := by
    rw [div_eq_mul_inv, ← Real.rpow_neg_one]
    exact mul_le_mul hdegree_amplitude
      ((Real.rpow_le_rpow_of_exponent_le hfield1 (by linarith)).trans hfield_rate)
      (by positivity) hamplitude0
  have hconstruct_root :
      (deltaConstructPaulis C epsilon
        (deltaQld a b epsilon params.m params.d params.q) params.m params.d params.q) ^
          (1 / 4 : ℝ) ≤ 3 * C * amplitude * rate := by
    unfold deltaConstructPaulis
    rw [Real.mul_rpow hC0 (by positivity)]
    calc
      C ^ (1 / 4 : ℝ) *
          (deltaQld a b epsilon params.m params.d params.q + Real.sqrt epsilon +
            degree / (params.q : ℝ)) ^ (1 / 4 : ℝ) ≤
          C * ((deltaQld a b epsilon params.m params.d params.q) ^ (1 / 4 : ℝ) +
            (Real.sqrt epsilon) ^ (1 / 4 : ℝ) +
            (degree / (params.q : ℝ)) ^ (1 / 4 : ℝ)) :=
        mul_le_mul (Real.rpow_le_self_of_one_le hC (by norm_num))
          (hroot_sum hglobal0 (by positivity) (by positivity))
          (by positivity) hC0
      _ ≤ C * (amplitude * rate + amplitude * rate + amplitude * rate) :=
        mul_le_mul_of_nonneg_left
          (add_le_add (add_le_add hglobal_root hsqrt_root) hratio_root) hC0
      _ = 3 * C * amplitude * rate := by ring
  calc
    deltaExtract C
        (deltaConstructPaulis C epsilon
          (deltaQld a b epsilon params.m params.d params.q) params.m params.d params.q)
        params.m params.d params.q ≤
        C * (3 * C * amplitude * rate + amplitude * rate) :=
      mul_le_mul_of_nonneg_left (add_le_add hconstruct_root hratio) hC0
    _ = (C * (3 * C + 1)) * (amplitude * rate) := by ring
    _ ≤ 4 * C ^ 2 * (amplitude * rate) :=
      mul_le_mul_of_nonneg_right (by nlinarith) (mul_nonneg hamplitude0 hrate0)
    _ = (4 * C ^ 2 * a) * degree ^ a * rate := by dsimp [amplitude]; ring
    _ ≤ deltaQld (4 * C ^ 2 * a) (b / 8) epsilon params.m params.d params.q :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow_of_exponent_le hdegree1 hconstant) (by positivity)) hrate0

end

end MIPStarRE.QPBT
