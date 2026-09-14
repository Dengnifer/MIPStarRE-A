import MIPStarRE.QPBT.Combining.ExtendedLineGame.RoundedPolynomialEstimates
import Mathlib.Algebra.MvPolynomial.Equiv

/-!
# Scalar and base coefficients of the rounded polynomial outcomes

The singleton polynomial is transported through the canonical field equivalence
and Mathlib's equivalence between a polynomial in a sum of variables and an
iterated polynomial ring. Its individual-degree certificate controls both levels.

## References

`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1310-1326`,
the coefficient expansion preceding `eq:qld-g-prime-bound`.
-/

open scoped BigOperators

namespace MIPStarRE.QPBT

open MIPStarRE.LDT hiding Measurement

noncomputable section

namespace ExtendedLineGame

private theorem coeff_coeff_sumRingEquiv {F A B : Type*} [CommSemiring F]
    (p : MvPolynomial (A ⊕ B) F) (a : A →₀ ℕ) (b : B →₀ ℕ) :
    ((MvPolynomial.sumRingEquiv F A B p).coeff a).coeff b =
      p.coeff (Finsupp.sumFinsuppAddEquivProdFinsupp.symm (a, b)) := by
  simp [MvPolynomial.sumRingEquiv, MvPolynomial.coeff,
    AddMonoidAlgebra.curryRingEquiv, AddMonoidAlgebra.curryAddEquiv]

private theorem totalDegree_le_of_exponents {F : Type*} [CommSemiring F]
    {n d : ℕ} (p : MvPolynomial (Fin n) F)
    (h : ∀ e ∈ p.support, ∀ i, e i ≤ d) : p.totalDegree ≤ n * d := by
  rw [MvPolynomial.totalDegree, Finset.sup_le_iff]
  intro e he
  rw [Finsupp.sum_fintype _ _ (by simp)]
  calc
    ∑ i : Fin n, e i ≤ ∑ _i : Fin n, d := Finset.sum_le_sum fun i _ => h e he i
    _ = n * d := by simp

private theorem sumRingEquiv_degrees {F : Type*} [CommSemiring F] {n d : ℕ}
    (p : MvPolynomial (Fin 2 ⊕ Fin n) F)
    (h : ∀ e ∈ p.support, ∀ i, e i ≤ d) :
    (∀ a, ((MvPolynomial.sumRingEquiv F (Fin 2) (Fin n) p).coeff a).totalDegree ≤
      n * d) ∧ (MvPolynomial.sumRingEquiv F (Fin 2) (Fin n) p).totalDegree ≤ 2 * d := by
  have hc (a : Fin 2 →₀ ℕ) (b : Fin n →₀ ℕ)
      (hb : b ∈ ((MvPolynomial.sumRingEquiv F (Fin 2) (Fin n) p).coeff a).support) :
      Finsupp.sumFinsuppAddEquivProdFinsupp.symm (a, b) ∈ p.support := by
    simpa only [MvPolynomial.mem_support_iff, coeff_coeff_sumRingEquiv] using hb
  constructor
  · intro a
    apply totalDegree_le_of_exponents
    intro b hb i
    simpa using h _ (hc a b hb) (Sum.inr i)
  · apply totalDegree_le_of_exponents
    intro a ha i
    obtain ⟨b, hb⟩ := MvPolynomial.support_nonempty.mpr
      (MvPolynomial.mem_support_iff.mp ha)
    simpa using h _ (hc a b hb) (Sum.inl i)

/-- The two base blocks, in the order `x,z` used by the extended game. -/
def baseCoordinateEquiv (m : ℕ) : Fin (2 * m) ≃ Fin m ⊕ Fin m :=
  (finCongr (by omega)).trans finSumFinEquiv.symm

/-- The scalar coordinates first, followed by the combined base coordinates. -/
def scalarBaseCoordinateEquiv (m : ℕ) : Fin (2 * m + 2) ≃ Fin 2 ⊕ Fin (2 * m) :=
  (finCombineEquiv m).trans
    ((Equiv.sumCongr (baseCoordinateEquiv m).symm (Equiv.refl _)).trans
      (Equiv.sumComm _ _))

/-- The actual singleton outcome as a polynomial in `alpha,beta` with
coefficients in the `2m` base variables, over the canonical Pauli field. -/
def scalarPolynomial (P : AdmissibleParams) (g : DirectPolyTuple P.extendedDirectLd) :
    MvPolynomial (Fin 2) (MvPolynomial (Fin (2 * P.m)) (PauliScalar P)) :=
  MvPolynomial.sumRingEquiv _ _ _
    (MvPolynomial.rename (scalarBaseCoordinateEquiv P.m)
      (MvPolynomial.map (extendedDirectScalarEquiv P).toRingHom (g (0 : Fin 1)).1))

/-- Both degree bounds follow from the genuine individual-degree certificate:
every base coefficient has degree at most `2md`, and the outer scalar
polynomial has degree at most `2d`. No degree hypothesis is added. -/
theorem scalarPolynomial_degrees (P : AdmissibleParams)
    (g : DirectPolyTuple P.extendedDirectLd) :
    (∀ a, ((scalarPolynomial P g).coeff a).totalDegree ≤ 2 * P.m * P.d) ∧
      (scalarPolynomial P g).totalDegree ≤ 2 * P.d := by
  apply sumRingEquiv_degrees
  intro e he i
  obtain ⟨v, hv, hvp⟩ := MvPolynomial.coeff_rename_ne_zero _ _ _
    (MvPolynomial.mem_support_iff.mp he)
  have hmem := MvPolynomial.support_map_subset _ _ (MvPolynomial.mem_support_iff.mpr hvp)
  have hdeg := Preliminaries.degreeOf_le_of_mem_polyFunc (g (0 : Fin 1)).2
    ((scalarBaseCoordinateEquiv P.m).symm i)
  have hvbound := (MvPolynomial.le_degreeOf_of_mem_support _ hmem).trans hdeg
  change v ((scalarBaseCoordinateEquiv P.m).symm i) ≤ P.d at hvbound
  subst e
  simpa only [Finsupp.mapDomain_equiv_apply] using hvbound

/-- The field and coordinate transports preserve the complete singleton
polynomial outcome, including its formal coefficients, not only its values. -/
theorem scalarPolynomial_injective (P : AdmissibleParams) :
    Function.Injective (scalarPolynomial P) := by
  intro g h heq
  have hs := (MvPolynomial.sumRingEquiv (PauliScalar P) (Fin 2)
    (Fin (2 * P.m))).injective heq
  have hr := MvPolynomial.rename_injective (scalarBaseCoordinateEquiv P.m)
    (scalarBaseCoordinateEquiv P.m).injective hs
  have hc := MvPolynomial.map_injective (extendedDirectScalarEquiv P).toRingHom
    (extendedDirectScalarEquiv P).injective hr
  funext j
  have hj : j = (0 : Fin 1) := @Subsingleton.elim (Fin 1) _ j 0
  subst j
  exact Subtype.ext hc

/-- The combined degree term in the recovered concentration estimate. -/
theorem scalarPolynomial_degree_term_le (P : AdmissibleParams)
    (g : DirectPolyTuple P.extendedDirectLd) :
    ((scalarPolynomial P g).support.sup fun e =>
      ((scalarPolynomial P g).coeff e).totalDegree) +
        max 1 (scalarPolynomial P g).totalDegree + 1 ≤ (2 * P.m + 2) * P.d + 1 := by
  have h := scalarPolynomial_degrees P g
  have hc : ((scalarPolynomial P g).support.sup fun e =>
      ((scalarPolynomial P g).coeff e).totalDegree) ≤ 2 * P.m * P.d :=
    Finset.sup_le fun e _ => h.1 e
  have ho : max 1 (scalarPolynomial P g).totalDegree ≤ 2 * P.d :=
    max_le (by have := P.hd; omega) h.2
  calc
    _ ≤ 2 * P.m * P.d + 2 * P.d + 1 := Nat.add_le_add_right (Nat.add_le_add hc ho) 1
    _ = _ := by ring

private theorem eval_sumRingEquiv {F A B : Type*} [CommSemiring F]
    (p : MvPolynomial (A ⊕ B) F) (u : B → F) (v : A → F) :
    MvPolynomial.eval v (MvPolynomial.map (MvPolynomial.eval u)
      (MvPolynomial.sumRingEquiv F A B p)) = MvPolynomial.eval (Sum.elim v u) p := by
  induction p using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => simp [hp, hq]
  | mul_X p i hp => cases i <;> simp [hp]

/-- Split the full joint uniform point into the base point and scalar point.
This is one equivalence of sample spaces, not four marginal identifications. -/
def scalarBaseQuestionEquiv (P : AdmissibleParams) :
    ((Fin (2 * P.m) → PauliScalar P) × (Fin 2 → PauliScalar P)) ≃
      ExtendedPointQuestion P :=
  (((baseCoordinateEquiv P.m).piCongrLeft fun _ => PauliScalar P).trans
    (Equiv.sumPiEquivProdPi fun _ : Fin P.m ⊕ Fin P.m => PauliScalar P)).prodCongr
      (finTwoArrowEquiv (PauliScalar P))

private theorem scalarBaseQuestionEquiv_direct (P : AdmissibleParams)
    (u : Fin (2 * P.m) → PauliScalar P) (v : Fin 2 → PauliScalar P) :
    (directPointExtendedQuestionEquiv P).symm (scalarBaseQuestionEquiv P (u, v)) =
      fun i => (extendedDirectScalarEquiv P).symm
        (Sum.elim v u (scalarBaseCoordinateEquiv P.m i)) := by
  apply (directPointExtendedQuestionEquiv P).injective
  rw [Equiv.apply_symm_apply, directPointExtendedQuestionEquiv_apply]
  apply Prod.ext
  · apply Prod.ext <;> funext i <;>
      simp [scalarBaseQuestionEquiv, scalarBaseCoordinateEquiv, projX, projZ,
        embX, embZ, directPointToPauli, Equiv.piCongrLeft_apply]
  · apply Prod.ext <;>
      simp [scalarBaseQuestionEquiv, scalarBaseCoordinateEquiv, alphaVar, betaVar,
        directPointToPauli]

/-- Evaluation of the nested polynomial is exactly the actual singleton readout,
including the canonical field transport and all four coordinate blocks. -/
theorem scalarPolynomial_eval (P : AdmissibleParams)
    (g : DirectPolyTuple P.extendedDirectLd)
    (u : Fin (2 * P.m) → PauliScalar P) (v : Fin 2 → PauliScalar P) :
    MvPolynomial.eval v (MvPolynomial.map (MvPolynomial.eval u) (scalarPolynomial P g)) =
      extendedPolynomialRead P (scalarBaseQuestionEquiv P (u, v)) g := by
  rw [scalarPolynomial, eval_sumRingEquiv, MvPolynomial.eval_rename,
    MvPolynomial.eval_map]
  unfold extendedPolynomialRead evalDirectPolyTupleAt
  rw [scalarBaseQuestionEquiv_direct]
  have h := (MvPolynomial.eval₂_comp (extendedDirectScalarEquiv P).toRingHom
      (fun i => (extendedDirectScalarEquiv P).symm
        (Sum.elim v u (scalarBaseCoordinateEquiv P.m i))) (g (0 : Fin 1)).1).symm
  change MvPolynomial.eval₂ (extendedDirectScalarEquiv P).toRingHom
      (fun i => extendedDirectScalarEquiv P ((extendedDirectScalarEquiv P).symm
        (Sum.elim v u (scalarBaseCoordinateEquiv P.m i)))) (g (0 : Fin 1)).1 = _ at h
  simp only [RingEquiv.apply_symm_apply] at h
  exact h

end ExtendedLineGame

end

end MIPStarRE.QPBT
