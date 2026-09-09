import MIPStarRE.QPBT.Combining.DirectLowDegree.Game
import MIPStarRE.QPBT.Combining.DirectLowDegree.Transport.Combining.Polynomial

/-!
# The combined parameters of the simultaneity reduction

The extension of the quantum soundness of the low individual degree test from
simultaneity parameter `1` to a general simultaneity parameter `k` applies the
case `k = 1` once, to a directly indexed low-degree game whose dimension is
`m + k` and whose simultaneity parameter is `1`.  This module records that
parameter map, the polynomial-tuple outcomes it carries, and the two maps
relating outcomes of the two games: the combining map, which sends a tuple of
`k` polynomials in `m` variables to the one-component tuple consisting of the
combined polynomial in `m + k` variables, and its total left inverse, which
returns the components of a combined polynomial and an arbitrary tuple
otherwise.

The field, the degree, and the admissibility of the field size are inherited
unchanged; only the dimension and the simultaneity parameter change.  The
degree is inherited because the combining map is linear in the fresh
coordinates, so it raises no individual degree above `d` when `1 ≤ d`; this is
where the individual-degree formulation differs from the total-degree
formulation of the source, which passes from degree `d` to degree `d + 1`.

## References

* `references/neexp-paper/05_quantum_preliminaries.tex:1409-1503`
* `references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:413-458`
* `blueprint/src/chapter/ch13_qpbt_test.tex:240-250`
* `docs/paper-gaps/qpbt_ld-simultaneous-sandwich.tex`
-/

open scoped BigOperators

namespace MIPStarRE.QPBT

open MIPStarRE.LDT
open MIPStarRE.LDT.Preliminaries

noncomputable section

/-! ## The combined parameter tuple -/

/-- The parameters of the game to which the reduction applies the case of
simultaneity parameter `1`: the dimension grows from `m` to `m + k` and the
simultaneity parameter becomes `1`, while the field size, the degree, and the
admissibility hypothesis are unchanged. -/
def DirectLdParams.combined (D : DirectLdParams) : DirectLdParams where
  q := D.q
  m := D.m + D.k
  d := D.d
  k := 1
  hm := le_trans D.hm (Nat.le_add_right D.m D.k)
  hd := D.hd
  hk := le_refl 1
  hq := D.hq

@[simp] theorem DirectLdParams.combined_q (D : DirectLdParams) :
    D.combined.q = D.q := rfl

@[simp] theorem DirectLdParams.combined_m (D : DirectLdParams) :
    D.combined.m = D.m + D.k := rfl

@[simp] theorem DirectLdParams.combined_d (D : DirectLdParams) :
    D.combined.d = D.d := rfl

@[simp] theorem DirectLdParams.combined_k (D : DirectLdParams) :
    D.combined.k = 1 := rfl

/-- The combined parameters carry the same scalar field: the field model is
selected by the field size and its admissibility proof, both unchanged. -/
theorem directScalarQ_combined (D : DirectLdParams) :
    DirectScalarQ D.combined = DirectScalarQ D := rfl

/-- The scalar field of a directly indexed low-degree game has `q` elements. -/
theorem card_directScalarQ (D : DirectLdParams) :
    Fintype.card (DirectScalarQ D) = D.q := by
  rw [Fintype.card_congr (binaryRepresentation D.model), Fintype.card_fin]

/-- The one-element index set of the combined simultaneity parameter. -/
instance (D : DirectLdParams) : Unique (Fin D.combined.k) :=
  show Unique (Fin 1) from inferInstance

/-! ## The combining map on game outcomes -/

/-- The combined polynomial of a tuple of direct polynomial representatives:
`(u, α) ↦ ∑_{r < k} α_r g_r(u)`, of individual degree at most `d` in the
`m + k` variables of the combined parameters.

Source `references/neexp-paper/05_quantum_preliminaries.tex:1425-1435`. -/
def directCombinedPolynomial (D : DirectLdParams) (g : DirectPolyTuple D) :
    PolyIndex D.combined.m (DirectScalarQ D) D.d :=
  ⟨combinePolyTuple (fun r => (g r).1),
    combinePolyTuple_mem_polyFunc D.hd _ fun r => (g r).2⟩

@[simp] theorem directCombinedPolynomial_val (D : DirectLdParams) (g : DirectPolyTuple D) :
    (directCombinedPolynomial D g).1 = combinePolyTuple (fun r => (g r).1) :=
  rfl

/-- Evaluating the combined polynomial at a point of the combined space with
point part `u` and combining part `α` gives `∑_{r < k} α_r g_r(u)`. -/
theorem directCombinedPolynomial_eval (D : DirectLdParams) (g : DirectPolyTuple D)
    (u : Fin D.m → DirectScalarQ D) (α : Fin D.k → DirectScalarQ D) :
    MvPolynomial.eval (combinedPoint u α) (directCombinedPolynomial D g).1 =
      ∑ r : Fin D.k, α r * evalDirectPolyTupleAt u g r := by
  rw [directCombinedPolynomial_val, combinePolyTuple_eval_combinedPoint]
  rfl

/-- The combining map is injective on polynomial tuples. -/
theorem directCombinedPolynomial_injective (D : DirectLdParams) :
    Function.Injective (directCombinedPolynomial D) := by
  intro g g' h
  have hval : combinePolyTuple (fun r => (g r).1) =
      combinePolyTuple (fun r => (g' r).1) := congrArg Subtype.val h
  have hcomp := combinePolyTuple_injective hval
  funext r
  exact Subtype.ext (congrFun hcomp r)

/-- The one-component polynomial tuple of the combined game carrying the
combined polynomial of a tuple. -/
def directCombinedTuple (D : DirectLdParams) (g : DirectPolyTuple D) :
    DirectPolyTuple D.combined :=
  fun _ => directCombinedPolynomial D g

@[simp] theorem directCombinedTuple_apply (D : DirectLdParams) (g : DirectPolyTuple D)
    (r : Fin D.combined.k) :
    directCombinedTuple D g r = directCombinedPolynomial D g := rfl

/-! ## Recovering the polynomial tuple -/

/-- A polynomial in the variables of the combined parameters is combined when it
is the combined polynomial of a tuple.  This is the source's exact linearity in
the combining variables, together with the individual-degree bound on the
components.  Source
`references/neexp-paper/05_quantum_preliminaries.tex:1462-1477`. -/
def IsDirectCombined (D : DirectLdParams)
    (p : PolyIndex D.combined.m (DirectScalarQ D) D.d) : Prop :=
  ∃ g : DirectPolyTuple D, directCombinedPolynomial D g = p

theorem isDirectCombined_directCombinedPolynomial (D : DirectLdParams)
    (g : DirectPolyTuple D) : IsDirectCombined D (directCombinedPolynomial D g) :=
  ⟨g, rfl⟩

/-- The polynomial tuple represented by a polynomial in the variables of the
combined parameters: its components when it is combined, and the zero tuple
otherwise.  The source leaves the value on non-combined outcomes arbitrary; the
zero tuple is one admissible choice, and the estimates use only the value on
combined outcomes.  Source
`references/neexp-paper/05_quantum_preliminaries.tex:1477-1483`. -/
def directTupleOfCombined (D : DirectLdParams)
    (p : PolyIndex D.combined.m (DirectScalarQ D) D.d) : DirectPolyTuple D := by
  classical
  exact if h : IsDirectCombined D p then h.choose else fun _ => 0

/-- The components of a combined polynomial are the tuple it combines. -/
@[simp] theorem directTupleOfCombined_directCombinedPolynomial (D : DirectLdParams)
    (g : DirectPolyTuple D) :
    directTupleOfCombined D (directCombinedPolynomial D g) = g := by
  classical
  have hex : IsDirectCombined D (directCombinedPolynomial D g) :=
    isDirectCombined_directCombinedPolynomial D g
  rw [directTupleOfCombined, dif_pos hex]
  exact directCombinedPolynomial_injective D hex.choose_spec

/-- The polynomial tuple represented by an outcome of the combined game. -/
def directTupleOfCombinedTuple (D : DirectLdParams)
    (p : DirectPolyTuple D.combined) : DirectPolyTuple D :=
  directTupleOfCombined D (p default)

@[simp] theorem directTupleOfCombinedTuple_directCombinedTuple (D : DirectLdParams)
    (g : DirectPolyTuple D) :
    directTupleOfCombinedTuple D (directCombinedTuple D g) = g := by
  rw [directTupleOfCombinedTuple, directCombinedTuple_apply,
    directTupleOfCombined_directCombinedPolynomial]

end

end MIPStarRE.QPBT
