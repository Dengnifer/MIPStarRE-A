import MIPStarRE.QPBT.Algebra.LowDegreeCodeTheorems
import MIPStarRE.QPBT.Combining.Defs

/-! # Polynomial decoding for Pauli extraction

This module provides the Chapter 16 decoder on the Chapter 15 bounded
polynomial representative type.  The generic retained-value decoder and its
specialization to polynomial representatives live in
`Algebra/LowDegreeCodeTheorems`; this module states the corresponding maps on
`Poly P` used in the extraction chapter.

## References

The decoder is blueprint `def:decoding-map`, with its extraction use in
blueprint `sec:separating` and paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1419-1450`.
The restricted decoder identity and its encoding hypothesis are documented in
`docs/paper-gaps/qpbt_decoding-identity.tex:87-123`.
-/

open scoped BigOperators

namespace MIPStarRE.QPBT

open MIPStarRE.LDT MIPStarRE.LDT.Preliminaries

/-! ## Representative evaluation and decoding -/

/-- Evaluate the polynomial representative carried by `Poly P`.

This is polynomial evaluation on the source's `\ideg_{d,m}(\F_q)` carrier.  It
does not identify representatives that induce the same polynomial function. -/
noncomputable def evalPoly {P : AdmissibleParams} (g : Poly P)
    (x : Fin P.m → PauliScalar P) : PauliScalar P :=
  MvPolynomial.eval x g.1

/-- Decode a bounded polynomial while retaining only values in `H`.

This is the `H`-parameterized form of `def:decoding-map`; `decodeAt` remains
the decoding map for arbitrary functions.  The Boolean cube is embedded in
`PauliScalar P` by `cubeEmbed`. -/
noncomputable def decodeOn {P : AdmissibleParams}
    (H : Finset (PauliScalar P)) (g : Poly P) : PauliRegister P :=
  decodeAt H (fun x => evalPoly g x)

/-- Full-field specialization of `decodeOn` used in Chapter 16.

The retained-value set is `Finset.univ`, so every field value is kept.  This
choice is the correction recorded in
`docs/paper-gaps/qpbt_decoding-identity.tex:87-123`. -/
noncomputable abbrev decodeOnUniv {P : AdmissibleParams} (g : Poly P) :
    PauliRegister P :=
  decodeOn (Finset.univ : Finset (PauliScalar P)) g

/-- The full-field decoder `\operatorname{Dec}_{\F_q}` on `Poly P`.

The map `decodeFqRep` has the same definition on arbitrary polynomial
representatives; `decodeFq` restricts its domain to the bounded-degree class
`Poly P`. -/
noncomputable abbrev decodeFq {P : AdmissibleParams} (g : Poly P) :
    PauliRegister P :=
  decodeOnUniv g

/-! ## The encoding image -/

/-- Membership of a multilinear encoding in the bounded representative class.

Each indicator factor has degree zero away from its own variable and degree at
most one in that variable, so the multilinear encoding has individual degree at
most one, and hence at most `P.d` using `P.hd`.  This is the degree
side-condition implicit in the source's `g_h` construction, not an extra
hypothesis of the decoding identity.  See blueprint
`def:low-degree-encoding`, and paper
`references/qpbt-paper/04_preliminaries.tex:832-897`. -/
theorem lowDegreeEncoding_mem_poly {P : AdmissibleParams}
    (h : PauliRegister P) :
    lowDegreeEncoding h ∈
      MIPStarRE.LDT.Preliminaries.polyFunc P.m (PauliScalar P) P.d := by
  rw [MvPolynomial.mem_restrictDegree]
  intro s hs i
  apply (MvPolynomial.monomial_le_degreeOf i hs).trans
  rw [lowDegreeEncoding]
  refine (MvPolynomial.degreeOf_sum_le i Finset.univ _).trans ?_
  refine Finset.sup_le fun y _ => ?_
  refine (show MvPolynomial.degreeOf i
      (h y • indicatorPoly (K := PauliScalar P) y) ≤
      MvPolynomial.degreeOf i (indicatorPoly (K := PauliScalar P) y) from ?_).trans ?_
  · simpa only [MvPolynomial.smul_eq_C_mul] using
      MvPolynomial.degreeOf_C_mul_le (indicatorPoly (K := PauliScalar P) y) i (h y)
  rw [indicatorPoly]
  refine (MvPolynomial.degreeOf_prod_le i Finset.univ _).trans ?_
  calc
    ∑ j, MvPolynomial.degreeOf i
        (if y j then
          (MvPolynomial.X j : MvPolynomial (Fin P.m) (PauliScalar P))
        else 1 - MvPolynomial.X j) ≤
        ∑ j, if i = j then 1 else 0 := by
      apply Finset.sum_le_sum
      intro j _
      split
      · exact le_of_eq (MvPolynomial.degreeOf_X i j)
      · exact (MvPolynomial.degreeOf_sub_le i 1 (MvPolynomial.X j)).trans_eq (by
          simp [MvPolynomial.degreeOf_X])
    _ = 1 := by simp
    _ ≤ P.d := P.hd

/-- The multilinear encoding as a bounded polynomial representative.

The individual-degree bound is supplied by `lowDegreeEncoding_mem_poly`. -/
noncomputable def encodingPoly {P : AdmissibleParams} (h : PauliRegister P) :
    Poly P :=
  ⟨lowDegreeEncoding h, lowDegreeEncoding_mem_poly h⟩

/-- A `Poly P` outcome is an encoding when its decoder reconstructs the same
underlying polynomial representative.

This is the explicit support restriction required by the corrected Chapter 16
decoding argument.  It is the `Poly` view of `IsEncodingRep`; no unrestricted
decoder/evaluation identity is asserted.  See
`docs/paper-gaps/qpbt_decoding-identity.tex:87-123`. -/
def IsEncoding {P : AdmissibleParams} (g : Poly P) : Prop :=
  lowDegreeEncoding (decodeFq g) = g.1

/-! ## Decoder companions -/

/-- Linearity of the full-field decoder on bounded representatives.

This is the additive linearity of blueprint
`lem:qld-decoder-linearity`, used in the symmetry step of the source
argument at
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1546-1550`
and blueprint `lem:qld-construct-the-paulis`.  It does not assert
evaluation equality for non-encoding representatives.  See
`docs/paper-gaps/qpbt_decoding-identity.tex:87-123`. -/
theorem decodeFq_add {P : AdmissibleParams} (g h : Poly P) :
    decodeFq (g + h) = decodeFq g + decodeFq h := by
  funext y
  simp [decodeOn, decodeAt, evalPoly, MvPolynomial.eval_add]

/-- Scalar linearity of the full-field decoder on bounded representatives.

This companion has the same source scope as `decodeFq_add` and does not
strengthen the restricted decoder identity.  See
`docs/paper-gaps/qpbt_decoding-identity.tex:87-123`. -/
theorem decodeFq_smul {P : AdmissibleParams} (c : PauliScalar P) (g : Poly P) :
    decodeFq (c • g) = c • decodeFq g := by
  funext y
  simp [decodeOn, decodeAt, evalPoly, MvPolynomial.smul_eval]

/-- The full-field decoder is a left inverse to `encodingPoly`.

This is the identity `\operatorname{Dec}(g_h)=h` of
blueprint `lem:qld-decoder-linearity`, for
the full-field decoder specified at
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1419-1420`.
The degree proof is separated into `lowDegreeEncoding_mem_poly`; no additional
encoding or interpolation hypothesis is introduced.  See
`docs/paper-gaps/qpbt_decoding-identity.tex:87-123`. -/
theorem decodeFq_lowDegreeEncoding {P : AdmissibleParams}
    (h : PauliRegister P) :
    decodeFq (encodingPoly h) = h := by
  funext y
  simpa only [decodeFq, decodeOnUniv, decodeOn, decodeAt, evalPoly,
    encodingPoly, lowDegreeEnc, Finset.mem_univ, if_true] using
      congrFun
        (decodeAt_lowDegreeEnc
          (Finset.univ : Finset (PauliScalar P)) h
            (fun z => Finset.mem_univ (h z))) y

/-- Decoder/evaluation agreement for an encoding representative only.

The hypothesis `hg : IsEncoding g` is mandatory.  For a general bounded
polynomial, Boolean-cube values determine its multilinear interpolant, which
need not equal the original representative.  This is the corrected form of
the source step at
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1483-1492`;
see `docs/paper-gaps/qpbt_decoding-identity.tex:87-123`.

**Local fix:** The source's unrestricted identity is false, as witnessed by
`g(x) = x^2` over a field with more than two elements.  The encoding restriction
and representative semantics are documented in
`docs/paper-gaps/qpbt_decoding-identity.tex:87-123`. -/
theorem decodeFq_dotProduct_indicatorVec {P : AdmissibleParams}
    {g : Poly P} (hg : IsEncoding g) (x : Fin P.m → PauliScalar P) :
    dotProduct (decodeFq g) (indicatorVec x) = evalPoly g x := by
  unfold IsEncoding at hg
  calc
    dotProduct (decodeFq g) (indicatorVec x) = lowDegreeEnc (decodeFq g) x :=
      (lowDegreeEnc_eq_dotProduct (decodeFq g) x).symm
    _ = evalPoly g x := by simp [lowDegreeEnc, evalPoly, hg]

end MIPStarRE.QPBT
