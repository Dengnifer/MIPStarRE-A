import MIPStarRE.QPBT.Algebra.LowDegreeCodeTheorems
import MIPStarRE.QPBT.Combining.Defs

/-! # Polynomial decoding for Pauli extraction

This module provides the Chapter 16 decoder on the Chapter 15 bounded
polynomial representative type.  The generic retained-value decoder and its
specialization to polynomial representatives live in
`Algebra/LowDegreeCodeTheorems`; this module states the corresponding maps on
`Poly P` used in the extraction chapter.

## References

The decoder is `def:decoding-map`, blueprint
`blueprint/src/chapter/ch11_qpbt_algebra.tex:445-455`, with the extraction use
at `blueprint/src/chapter/ch16_qpbt_extraction.tex:11-20` and paper
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

The proof that the multilinear encoding has individual degree at most one,
and hence at most `P.d` using `P.hd`, is a named proof obligation.  It is the
degree side-condition implicit in the source's `g_h` construction, not an
extra hypothesis of the decoding identity.  See
`blueprint/src/chapter/ch11_qpbt_algebra.tex:381-401` and paper
`references/qpbt-paper/04_preliminaries.tex:832-897`.

**Proof obligation:** issue #47 tracks the individual-degree calculation. -/
theorem lowDegreeEncoding_mem_poly {P : AdmissibleParams}
    (h : PauliRegister P) :
    lowDegreeEncoding h ∈
      MIPStarRE.LDT.Preliminaries.polyFunc P.m (PauliScalar P) P.d := by
  sorry

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

This is the linearity used in the source's regrouping calculation at paper
`14_analysis_of_the_pauli_basis_test.tex:1442-1450` and blueprint
`ch16_qpbt_extraction.tex:11-20`.  It is a proof obligation; it does not
assert evaluation equality for non-encoding representatives.  See
`docs/paper-gaps/qpbt_decoding-identity.tex:87-123`.

**Proof obligation:** issue #47 tracks the regrouping calculation. -/
theorem decodeFq_add {P : AdmissibleParams} (g h : Poly P) :
    decodeFq (g + h) = decodeFq g + decodeFq h := by
  sorry

/-- Scalar linearity of the full-field decoder on bounded representatives.

This companion has the same source and proof-gap status as `decodeFq_add` and
does not strengthen the restricted decoder identity.  See
`docs/paper-gaps/qpbt_decoding-identity.tex:87-123`.

**Proof obligation:** issue #47 tracks scalar linearity. -/
theorem decodeFq_smul {P : AdmissibleParams} (c : PauliScalar P) (g : Poly P) :
    decodeFq (c • g) = c • decodeFq g := by
  sorry

/-- The full-field decoder is a left inverse to `encodingPoly`.

This is the source identity `\operatorname{Dec}(g_h)=h` from
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1805-1822`.
The degree proof is separated into `lowDegreeEncoding_mem_poly`; no additional
encoding or interpolation hypothesis is introduced.  See
`docs/paper-gaps/qpbt_decoding-identity.tex:87-123`.

**Proof obligation:** issue #47 tracks the decoder/encoding calculation. -/
theorem decodeFq_lowDegreeEncoding {P : AdmissibleParams}
    (h : PauliRegister P) :
    decodeFq (encodingPoly h) = h := by
  sorry

/-- Decoder/evaluation agreement for an encoding representative only.

The hypothesis `hg : IsEncoding g` is mandatory.  For a general bounded
polynomial, Boolean-cube values determine its multilinear interpolant, which
need not equal the original representative.  This is the corrected form of
the source step at
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1483-1492`;
see `docs/paper-gaps/qpbt_decoding-identity.tex:87-123`.

**Proof obligation:** issue #47 tracks the restricted evaluation calculation. -/
theorem decodeFq_dotProduct_indicatorVec {P : AdmissibleParams}
    {g : Poly P} (hg : IsEncoding g) (x : Fin P.m → PauliScalar P) :
    dotProduct (decodeFq g) (indicatorVec x) = evalPoly g x := by
  sorry

end MIPStarRE.QPBT
