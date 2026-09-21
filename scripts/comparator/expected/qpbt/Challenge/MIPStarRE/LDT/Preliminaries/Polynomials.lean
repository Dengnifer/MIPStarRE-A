import Mathlib

/-! Challenge mirror of `MIPStarRE/LDT/Preliminaries/Polynomials.lean`.

One challenge module per contributing library module, importing the
mirrors of the library modules this one imports.  The partition is
what makes Lean generate the same auxiliary declarations, under the
same names, as the library does. -/

open scoped BigOperators MatrixOrder Matrix ComplexOrder
namespace MIPStarRE.LDT.Preliminaries

-- source: MIPStarRE/LDT/Preliminaries/Polynomials.lean:25-29  (MIPStarRE.LDT.Preliminaries.polyFunc)
/-- `\polyfunc{m}{q}{d}` from the paper's definition of low-individual-degree
polynomials. This is Mathlib's `MvPolynomial.restrictDegree` submodule. -/
noncomputable abbrev polyFunc (m : ℕ) (K : Type*) [CommSemiring K] (d : ℕ) :
    Submodule K (MvPolynomial (Fin m) K) :=
  MvPolynomial.restrictDegree (Fin m) K d
end MIPStarRE.LDT.Preliminaries
