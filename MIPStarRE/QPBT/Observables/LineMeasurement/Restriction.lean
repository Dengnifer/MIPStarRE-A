import MIPStarRE.QPBT.Algebra.LowDegreeCode
import MIPStarRE.QPBT.Observables.LineMeasurement.Evaluation

/-!
# Restriction of low-degree encodings to canonical lines

This module substitutes the affine parameterization of a canonical line into a
multivariate polynomial, records the result as a degree-`m*d` coefficient
list, and bounds its degree. A multilinear low-degree encoding restricts to a
polynomial whose degree is at most the number of coordinates in which the
direction of the line is nonzero: at most `m ≤ m*d` on every line and at most
`1 ≤ d` on an axis-parallel line.

## References

The declarations formalize the restriction operation and its degree
justification in `def:expanded-line-measurement`,
`blueprint/src/chapter/ch14_qpbt_observables.tex:1034-1080`, whose paper
source is `references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:535-557`.
-/

open scoped BigOperators

namespace MIPStarRE.QPBT

open MIPStarRE.LDT

noncomputable section

/-- Substitute the affine parameterization of a canonical line into a
multivariate polynomial. This is the polynomial `g_h(u₀ + tv)` used in
`def:expanded-line-measurement`, paper
`14_analysis_of_the_pauli_basis_test.tex:535-557`, blueprint
`ch14_qpbt_observables.tex:1034-1080`. -/
noncomputable def polynomialOnLine (L : LdParams) (line : LineDesc L)
    (g : MvPolynomial (Fin L.m) (ScalarQ L)) : Polynomial (ScalarQ L) :=
  MvPolynomial.eval₂Hom _root_.Polynomial.C
    (fun i : Fin L.m =>
      (_root_.Polynomial.C (line.base i) +
        _root_.Polynomial.X * _root_.Polynomial.C (line.direction i) :
        Polynomial (ScalarQ L))) g

/-- The degree-`m*d` coefficient list obtained by restricting `g` to `line`.
This is the concrete restriction operation in `def:expanded-line-measurement`,
paper `14_analysis_of_the_pauli_basis_test.tex:535-557`, blueprint
`ch14_qpbt_observables.tex:1034-1080`. -/
noncomputable def restrictToLine (L : LdParams) (line : LineDesc L)
    (g : MvPolynomial (Fin L.m) (ScalarQ L)) : DegPoly L (L.m * L.d) :=
  fun i => (polynomialOnLine L line g).coeff i.val

/-- Each coordinate of the affine parameterization of a line is a polynomial
of degree at most one in the line parameter. Formalization-only auxiliary for
the degree justification in `def:expanded-line-measurement`, paper
`14_analysis_of_the_pauli_basis_test.tex:548-557`. -/
private theorem natDegree_lineCoordinate_le (L : LdParams) (line : LineDesc L)
    (i : Fin L.m) :
    (_root_.Polynomial.C (line.base i) +
        _root_.Polynomial.X * _root_.Polynomial.C (line.direction i) :
        Polynomial (ScalarQ L)).natDegree ≤ 1 := by
  refine (Polynomial.natDegree_add_le _ _).trans (max_le ?_ ?_)
  · simp
  · refine Polynomial.natDegree_mul_le.trans ?_
    simp

/-- A coordinate in which the direction of the line vanishes is constant along
the line. Formalization-only auxiliary for the axis-parallel case of
`def:expanded-line-measurement`, paper
`14_analysis_of_the_pauli_basis_test.tex:548-557`. -/
private theorem natDegree_lineCoordinate_eq_zero (L : LdParams)
    (line : LineDesc L) (i : Fin L.m) (hi : line.direction i = 0) :
    (_root_.Polynomial.C (line.base i) +
        _root_.Polynomial.X * _root_.Polynomial.C (line.direction i) :
        Polynomial (ScalarQ L)).natDegree = 0 := by
  rw [hi, map_zero, mul_zero, add_zero, Polynomial.natDegree_C]

/-- Restricting a multilinear low-degree encoding to a line has degree at most
the sum of any coordinatewise degree bounds on the affine parameterization.
This is the multilinearity argument behind the degree justification in
`def:expanded-line-measurement`, paper
`14_analysis_of_the_pauli_basis_test.tex:548-557`, blueprint
`ch14_qpbt_observables.tex:1034-1080`. -/
theorem polynomialOnLine_lowDegreeEncoding_natDegree_le_sum (L : LdParams)
    (line : LineDesc L) (h : Cube L.m → ScalarQ L) (bound : Fin L.m → ℕ)
    (hbound : ∀ i : Fin L.m,
      (_root_.Polynomial.C (line.base i) +
          _root_.Polynomial.X * _root_.Polynomial.C (line.direction i) :
          Polynomial (ScalarQ L)).natDegree ≤ bound i) :
    (polynomialOnLine L line (lowDegreeEncoding h)).natDegree ≤
      ∑ i : Fin L.m, bound i := by
  classical
  unfold polynomialOnLine lowDegreeEncoding
  rw [map_sum]
  refine Polynomial.natDegree_sum_le_of_forall_le _ _ ?_
  intro y _
  rw [MvPolynomial.smul_eq_C_mul, map_mul, MvPolynomial.eval₂Hom_C]
  refine (Polynomial.natDegree_C_mul_le _ _).trans ?_
  unfold indicatorPoly
  rw [map_prod]
  refine (Polynomial.natDegree_prod_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
  by_cases hy : y i = true
  · rw [if_pos hy, MvPolynomial.eval₂Hom_X']
    exact hbound i
  · rw [if_neg hy, map_sub, map_one, MvPolynomial.eval₂Hom_X']
    refine (Polynomial.natDegree_sub_le _ _).trans (max_le ?_ (hbound i))
    simp

/-- Restricting a multilinear low-degree encoding to a line has degree at most
`m*d`. This is the degree justification in `def:expanded-line-measurement`,
paper `14_analysis_of_the_pauli_basis_test.tex:535-557`, blueprint
`ch14_qpbt_observables.tex:1034-1080`. -/
theorem polynomialOnLine_lowDegreeEncoding_natDegree_le (L : LdParams)
    (line : LineDesc L) (h : Cube L.m → ScalarQ L) :
    (polynomialOnLine L line (lowDegreeEncoding h)).natDegree ≤ L.m * L.d := by
  refine (polynomialOnLine_lowDegreeEncoding_natDegree_le_sum L line h
    (fun _ => 1) (fun i => natDegree_lineCoordinate_le L line i)).trans ?_
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    smul_eq_mul, mul_one]
  exact Nat.le_mul_of_pos_right L.m L.hd

/-- On an axis-parallel line, the restricted low-degree encoding has degree at
most one: only the coordinate carrying the direction varies along the line.
This is the axis-parallel degree assertion in
`def:expanded-line-measurement`, paper
`14_analysis_of_the_pauli_basis_test.tex:548-557`, blueprint
`ch14_qpbt_observables.tex:1034-1080`. -/
theorem polynomialOnLine_lowDegreeEncoding_natDegree_le_one_of_axis
    (L : LdParams) (line : LineDesc L) (haxis : line.kind = .axis)
    (h : Cube L.m → ScalarQ L) :
    (polynomialOnLine L line (lowDegreeEncoding h)).natDegree ≤ 1 := by
  classical
  cases line with
  | diagonal base seed direction baseFixed prefixZero =>
      simp [LineDesc.kind] at haxis
  | axis base seed baseFixed =>
      refine (polynomialOnLine_lowDegreeEncoding_natDegree_le_sum L _ h
        (fun i => if i = chiIndex L seed then 1 else 0) ?_).trans ?_
      · intro i
        by_cases hij : i = chiIndex L seed
        · rw [if_pos hij]
          exact natDegree_lineCoordinate_le L _ i
        · rw [if_neg hij]
          refine le_of_eq (natDegree_lineCoordinate_eq_zero L _ i ?_)
          change coordinateDirection (chiIndex L seed) i = 0
          simp [coordinateDirection, hij]
      · simp

/-- A degree-`m*d` coefficient list actually lies in the embedded degree-`d`
subspace when all coefficients above `d` vanish. This is the coefficient
interpretation of `deg_d(line) ⊆ deg_md(line)` in
`def:expanded-line-measurement`, paper
`14_analysis_of_the_pauli_basis_test.tex:548-557`. -/
def DegPoly.FitsDegree {L : LdParams} {c : ℕ} (d : ℕ)
    (f : DegPoly L c) : Prop :=
  ∀ i : Fin (c + 1), d < i.val → f i = 0

/-- On an axis-parallel line, the restriction of a low-degree encoding lies in
the embedded degree-`d` subspace. This is the final assertion of
`def:expanded-line-measurement`, paper
`14_analysis_of_the_pauli_basis_test.tex:548-557`, blueprint
`ch14_qpbt_observables.tex:1034-1080`. -/
theorem restrictToLine_lowDegreeEncoding_fitsDegree_of_axis (L : LdParams)
    (line : LineDesc L) (haxis : line.kind = .axis)
    (h : Cube L.m → ScalarQ L) :
    (restrictToLine L line (lowDegreeEncoding h)).FitsDegree L.d := by
  intro i hi
  unfold restrictToLine
  apply Polynomial.coeff_eq_zero_of_natDegree_lt
  calc
    (polynomialOnLine L line (lowDegreeEncoding h)).natDegree ≤ 1 :=
      polynomialOnLine_lowDegreeEncoding_natDegree_le_one_of_axis L line haxis h
    _ ≤ L.d := L.hd
    _ < i.val := hi

/-! ## Evaluation of the restriction along the line -/

/-- Evaluating the substituted polynomial at a parameter evaluates the
multivariate polynomial at the corresponding point of the line.
Formalization-only auxiliary relating `polynomialOnLine` to the evaluation
classes of `def:ideg-deg-polynomials`, paper
`14_analysis_of_the_pauli_basis_test.tex:51-62`. -/
theorem eval_polynomialOnLine (L : LdParams) (line : LineDesc L)
    (g : MvPolynomial (Fin L.m) (ScalarQ L)) (t : ScalarQ L) :
    Polynomial.eval t (polynomialOnLine L line g) =
      MvPolynomial.eval (line.base + t • line.direction) g := by
  unfold polynomialOnLine
  rw [← Polynomial.coe_evalRingHom, MvPolynomial.coe_eval₂Hom,
    MvPolynomial.eval₂_comp_left]
  have h1 : (Polynomial.evalRingHom t).comp
      (Polynomial.C : ScalarQ L →+* Polynomial (ScalarQ L)) =
        RingHom.id (ScalarQ L) := by
    ext a
    simp
  have h2 : ((Polynomial.evalRingHom t) ∘ fun i : Fin L.m =>
      (_root_.Polynomial.C (line.base i) +
        _root_.Polynomial.X * _root_.Polynomial.C (line.direction i) :
        Polynomial (ScalarQ L))) = line.base + t • line.direction := by
    funext i
    simp only [Function.comp_apply, Polynomial.coe_evalRingHom,
      Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_X,
      Polynomial.eval_C, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  rw [h1, h2]
  rfl

/-- The coefficient-list evaluation of a restriction agrees with polynomial
evaluation once the degree bound `m*d` holds. Formalization-only auxiliary
for the evaluation classes of `def:ideg-deg-polynomials`, paper
`14_analysis_of_the_pauli_basis_test.tex:51-62`. -/
theorem evalCoefficient_restrictToLine (L : LdParams) (line : LineDesc L)
    (g : MvPolynomial (Fin L.m) (ScalarQ L))
    (hg : (polynomialOnLine L line g).natDegree ≤ L.m * L.d) (t : ScalarQ L) :
    evalCoefficient (restrictToLine L line g) t =
      Polynomial.eval t (polynomialOnLine L line g) := by
  unfold evalCoefficient restrictToLine
  rw [Polynomial.eval_eq_sum_range' (Nat.lt_succ_of_le hg) t]
  exact Fin.sum_univ_eq_sum_range
    (fun i => (polynomialOnLine L line g).coeff i * t ^ i) (L.m * L.d + 1)

/-- The restriction of a bounded-degree polynomial evaluates, at a point of
the line, to the value of the polynomial. Formalization-only auxiliary for
the exact ancillary consistency in items 2 and 3 of `lem:qld-comm-line-cons`,
paper `14_analysis_of_the_pauli_basis_test.tex:569-620`. -/
theorem evaluatesTo_restrictToLine (L : LdParams) (line : LineDesc L)
    (g : MvPolynomial (Fin L.m) (ScalarQ L))
    (hg : (polynomialOnLine L line g).natDegree ≤ L.m * L.d)
    (u : Fin L.m → ScalarQ L) (hu : u ∈ line.pointSet) :
    EvaluatesTo line (restrictToLine L line g) u (MvPolynomial.eval u g) := by
  refine ⟨hu, fun t ht => ?_⟩
  rw [evalCoefficient_restrictToLine L line g hg, eval_polynomialOnLine, ht]

/-- Partial evaluation of a bounded-degree restriction at a point of the
line. -/
theorem evalOpt_restrictToLine (L : LdParams) (line : LineDesc L)
    (g : MvPolynomial (Fin L.m) (ScalarQ L))
    (hg : (polynomialOnLine L line g).natDegree ≤ L.m * L.d)
    (u : Fin L.m → ScalarQ L) (hu : u ∈ line.pointSet) :
    evalOpt line u (restrictToLine L line g) = some (MvPolynomial.eval u g) :=
  (evalOpt_eq_some_iff line u _ _).mpr
    (evaluatesTo_restrictToLine L line g hg u hu)

/-- The restriction of a low-degree encoding evaluates, at a point of the
line, to the value `g_h(u) = h · ind_m(u)` of the encoding. This is the exact
ancillary consistency between the line and point Pauli projectors used in
items 2 and 3 of `lem:qld-comm-line-cons`, paper
`14_analysis_of_the_pauli_basis_test.tex:569-620`. -/
theorem evalOpt_restrictToLine_lowDegreeEncoding (L : LdParams)
    (line : LineDesc L) (h : Cube L.m → ScalarQ L)
    (u : Fin L.m → ScalarQ L) (hu : u ∈ line.pointSet) :
    evalOpt line u (restrictToLine L line (lowDegreeEncoding h)) =
      some (dotProduct h (indicatorVec u)) := by
  rw [evalOpt_restrictToLine L line _
    (polynomialOnLine_lowDegreeEncoding_natDegree_le L line h) u hu]
  congr 1
  exact lowDegreeEnc_eq_dotProduct h u

end

end MIPStarRE.QPBT
