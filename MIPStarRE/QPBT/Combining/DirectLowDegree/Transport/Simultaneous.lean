import MIPStarRE.LDT.Preliminaries.PolynomialAgreement
import MIPStarRE.LDT.Test.MainTheorem.MainFormal
import MIPStarRE.QPBT.Combining.DirectLowDegree.Transport.Consistency.Defect
import MIPStarRE.QPBT.Combining.DirectLowDegree.Transport.Error
import MIPStarRE.QPBT.Combining.DirectLowDegree.Transport.PassConversion
import MIPStarRE.QPBT.Games.Sandwich

/-!
# Simultaneous polynomial measurements for the direct low-degree game

This module applies the quantum soundness theorem of the low individual
degree test to each coordinate of a projective strategy for the directly
indexed low-degree game, combines coordinate polynomial projective
measurements into a polynomial-tuple POVM by the palindromic product of
`lem:ld-sandwich`, transports the Schwartz--Zippel collision estimate to the
direct polynomial representatives, and, for simultaneity parameter `1`,
packages the coordinate conclusions as the polynomial-tuple conclusion of
`lem:ld-soundness`.

## The simultaneity obstruction

For simultaneity parameter `k ≥ 2` the coordinate conclusions alone do not
determine simultaneous polynomial measurements, so no palindromic combination
of the coordinate measurements can be consistent with a joint point
measurement in general.  Let `q = 2^s`, let the degree be `1`, and let Bob
measure the univariate polynomials `g = g₀ + g₁ x` once in the standard basis
`|g⟩` and once in the Fourier basis attached to the symmetric pairing
`⟨h, g⟩ = h₀ g₁ + h₁ g₀`.  In characteristic two every evaluation functional
`h ↦ h(u)` is represented by an isotropic vector of this pairing, so at every
point `u` the value-level coarse-grainings `Q^{1,u}_{[a]}` (Fourier basis) and
`Q^{2,u}_{[b]}` (standard basis) commute, and on the maximally entangled state
Alice may answer point questions with the joint projective measurement
`P^u_{a,b} = (Q^{1,u}_{[a]} Q^{2,u}_{[b]})ᵀ`.  All coordinate consistencies of
`lem:ld-soundness` then hold with defect `0` and distinct polynomials collide
at a uniform point with probability `1 / q`, but the sandwiched POVM has
`∑_{g₂(u) = b} |g₂⟩⟨g₂| Q^{1,u}_{[a]} |g₂⟩⟨g₂| = q⁻¹ Q^{2,u}_{[b]}`, whose
consistency defect against `P^u` is `1 - 1/q`; more strongly, every
polynomial-pair POVM on Bob's side has defect at least `1 - 2/q` against
`P^u`.  No bound of the form `C k √(δ + m d / q)` holds for a universal `C`.
The source obtains the general case not coordinatewise but by the combining
reduction of Theorem 4.43 in the NEEXP paper, which applies the `k = 1`
theorem once, in dimension `m + k`, to a combined strategy; that reduction is
not formalized here.  The two-measurement pasting estimate (Fact 4.35 there)
does not apply either, since it evaluates the two coordinates at
independently sampled points while the low-degree game evaluates all
coordinates at one point.  The counterexample and the resulting formal
status are recorded in `docs/paper-gaps/qpbt_ld-simultaneous-sandwich.tex`.

## References

* `references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:413-458`
* `references/qpbt-paper/06_nonlocal_games_and_mipstar.tex:465-501`
* `references/neexp-paper/05_quantum_preliminaries.tex:912-1060` and `:1409-1503`
* `references/ldt-paper/test_definition.tex:180-202`
* `blueprint/src/chapter/ch13_qpbt_test.tex:170-215`
* `docs/paper-gaps/qpbt_ld-dimension-divisibility.tex`
* `docs/paper-gaps/qpbt_ld-simultaneous-sandwich.tex`
-/

open scoped BigOperators Matrix MatrixOrder ComplexOrder

namespace MIPStarRE.QPBT

open MIPStarRE.LDT
open MIPStarRE.LDT.Preliminaries
open MIPStarRE.Quantum

noncomputable section

/-! ## Direct polynomial collision estimate -/

/-- Two distinct direct polynomial representatives agree at a uniformly
sampled direct point with probability at most `m d / q`.

This is the Schwartz--Zippel estimate `polynomialAgreement_avg_le_mdq` of the
low individual degree test, read through the polynomial and point
identifications of the direct low-degree game; it is the collision
hypothesis of `lem:ld-sandwich` (blueprint `ch12_qpbt_games.tex:454-480`,
paper `references/qpbt-paper/06_nonlocal_games_and_mipstar.tex:465-501`). -/
theorem directPolynomialAgreement_avg_le_mdq (D : DirectLdParams)
    (g g' : PolyIndex D.m (DirectScalarQ D) D.d) (hneq : g ≠ g') :
    avgOver (uniformDistribution (Fin D.m → DirectScalarQ D))
        (fun u => if MvPolynomial.eval u g.1 = MvPolynomial.eval u g'.1 then
          (1 : Error) else 0) ≤
      (D.m * D.d : Error) / D.q := by
  letI := D.toLDTFieldModel
  let gLdt := directPolyEquivPolynomial D g
  let g'Ldt := directPolyEquivPolynomial D g'
  have hneqLdt : gLdt ≠ g'Ldt := by
    intro heq
    exact hneq ((directPolyEquivPolynomial D).injective heq)
  calc
    avgOver (uniformDistribution (Fin D.m → DirectScalarQ D))
        (fun u => if MvPolynomial.eval u g.1 = MvPolynomial.eval u g'.1 then
          (1 : Error) else 0) =
      avgOver (uniformDistribution (Fin D.m → DirectScalarQ D))
        (fun u => if gLdt (directPointEquiv D u) =
          g'Ldt (directPointEquiv D u) then (1 : Error) else 0) := by
            apply avgOver_congr
            intro u
            simp only [gLdt, g'Ldt, directPolyEquivPolynomial_apply]
            exact if_congr
              ((directScalarEquiv D).injective.eq_iff.symm) rfl rfl
    _ = avgOver (uniformDistribution (Point D.toLDTParameters))
        (fun u : Point D.toLDTParameters =>
          if gLdt u = g'Ldt u then (1 : Error) else 0) := by
      simpa using
        (avgOver_uniform_equiv (directPointEquiv D)
          (fun u : Fin D.m → DirectScalarQ D =>
            if gLdt (directPointEquiv D u) =
              g'Ldt (directPointEquiv D u) then (1 : Error) else 0))
    _ ≤ (D.m * D.d : Error) / D.q :=
      polynomialAgreement_avg_le_mdq D.toLDTParameters gLdt g'Ldt hneqLdt

/-! ## Palindromic tuple measurements -/

/-- Combine coordinate polynomial projective measurements into a tuple-valued
POVM by the ordered palindromic product of `lem:ld-sandwich` (blueprint
`ch12_qpbt_games.tex:454-507`, paper
`references/qpbt-paper/06_nonlocal_games_and_mipstar.tex:465-501`).

No commutativity between different coordinate measurements is assumed. -/
noncomputable def directSandwichPolynomialMeasurement
    (D : DirectLdParams) {iota : Type*} [Fintype iota] [DecidableEq iota]
    (G : Fin D.k → PolyMeas D.m (DirectScalarQ D) D.d iota)
    (hG : ∀ r, Measurement.IsProjective (G r)) :
    DirectPolyMeasTuple D iota := by
  let hmeasurement := sandwichProduct_isMeasurement
    (G := fun r (_ : Unit) => G r) (hG := fun r (_ : Unit) => hG r) ()
  exact Quantum.Measurement.ofSumEqOne
    (fun g => sandwichProduct (fun r (_ : Unit) h => (G r).effect h) () g)
    hmeasurement.1 hmeasurement.2

/-- The effects of the tuple POVM are its defining palindromic products. -/
@[simp] theorem directSandwichPolynomialMeasurement_effect
    (D : DirectLdParams) {iota : Type*} [Fintype iota] [DecidableEq iota]
    (G : Fin D.k → PolyMeas D.m (DirectScalarQ D) D.d iota)
    (hG : ∀ r, Measurement.IsProjective (G r))
    (g : DirectPolyTuple D) :
    (directSandwichPolynomialMeasurement D G hG).effect g =
      sandwichProduct (fun r (_ : Unit) h => (G r).effect h) () g :=
  rfl

/-- Relabeling a polynomial projective measurement of the low individual
degree test by direct polynomial representatives preserves projectivity. -/
theorem directPolynomialMeasurement_isProjective
    (D : DirectLdParams) :
    letI := D.toLDTFieldModel
    ∀ {iota : Type*} [Fintype iota] [DecidableEq iota]
      (G : ProjMeas (Polynomial D.toLDTParameters) iota),
      Measurement.IsProjective (directPolynomialMeasurement D G) := by
  letI := D.toLDTFieldModel
  intro iota _ _ G g
  rw [directPolynomialMeasurement_effect]
  refine { isIdempotentElem := ?_, isSelfAdjoint := ?_ }
  · exact G.proj (directPolyEquivPolynomial D g)
  · exact (Matrix.nonneg_iff_posSemidef.mp
      (G.outcome_pos (directPolyEquivPolynomial D g))).1.isSelfAdjoint

/-! ## Coordinatewise low individual degree soundness -/

/-- Quantum soundness of the low individual degree test (`thm:main-formal`,
paper `references/ldt-paper/test_definition.tex:180-202`) applied to one
coordinate of a projective strategy for the direct low-degree game.

The coordinate strategy passes the test with failure probability at most
`3 ε`, and the theorem is instantiated at the auxiliary sampling parameter
`directLdAuxParameter D`; both numerical side conditions of the theorem follow
from the positivity of the dimension and of the degree.  Blueprint
`ch13_qpbt_test.tex:170-215`, paper
`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:413-458`. -/
theorem directCoordinateMainFormal
    (D : DirectLdParams) (S : Strategy (directLdGame D))
    (hS : S.IsProjective) (r : Fin D.k) (ε : Error)
    (hwin : 1 - ε ≤ S.value) :
    letI := D.toLDTFieldModel
    ∃ GA : ProjMeas (Polynomial D.toLDTParameters) S.ιA,
      ∃ GB : ProjMeas (Polynomial D.toLDTParameters) S.ιB,
        ConsRel (directCoordinateProjStrat D S hS r).state
            (uniformDistribution (Point D.toLDTParameters))
            (IdxProjMeas.toIdxSubMeas
              (directCoordinateProjStrat D S hS r).pointMeasurementA)
            (polynomialEvaluationFamily D.toLDTParameters GB.toSubMeas)
            (Test.mainFormalError D.toLDTParameters
              (directLdAuxParameter D) (3 * ε)) ∧
          ConsRel (directCoordinateProjStrat D S hS r).state
            (uniformDistribution (Point D.toLDTParameters))
            (polynomialEvaluationFamily D.toLDTParameters GA.toSubMeas)
            (IdxProjMeas.toIdxSubMeas
              (directCoordinateProjStrat D S hS r).pointMeasurementB)
            (Test.mainFormalError D.toLDTParameters
              (directLdAuxParameter D) (3 * ε)) ∧
          ConsRel (directCoordinateProjStrat D S hS r).state
            (uniformDistribution Unit)
            (constSubMeasFamily GA.toSubMeas)
            (constSubMeasFamily GB.toSubMeas)
            (Test.mainFormalError D.toLDTParameters
              (directLdAuxParameter D) (3 * ε)) := by
  letI := D.toLDTFieldModel
  exact Test.mainFormal D.toLDTParameters
    (directCoordinateProjStrat D S hS r) (3 * ε)
    (directCoordinate_passes D S hS r ε hwin).soundnessHypothesis
    (directLdAuxParameter D) (four_hundred_mul_le_directLdAuxParameter D)
    (directLdAuxParameter_pos D)

/-! ## One-coordinate tuples -/

/-- Relabeling an outcome by a constant tuple over a one-element index set is
selected by the value of the tuple at the unique index. -/
private theorem const_tuple_eq_iff {iota beta : Type*} [Unique iota]
    (v : iota → beta) (b : beta) :
    v = (fun _ => b) ↔ v default = b := by
  constructor
  · intro h
    exact congrFun h default
  · intro h
    funext i
    rw [Unique.eq_default i]
    exact h

/-- The effect of a tuple-relabeled measurement at a constant tuple over a
one-element index set is the effect of the relabeling by the unique
coordinate. -/
private theorem postprocess_effect_const_tuple
    {alpha beta iota d : Type*} [Fintype alpha] [DecidableEq alpha]
    [Fintype beta] [DecidableEq beta] [Fintype iota] [DecidableEq iota]
    [Unique iota] [Fintype d] [DecidableEq d]
    (M : Quantum.Measurement alpha d) (f : alpha → iota → beta) (b : beta) :
    (M.postprocess f).effect (fun _ => b) =
      (M.postprocess (fun a => f a default)).effect b := by
  simp only [Quantum.Measurement.postprocess_effect]
  exact Finset.sum_congr
    (Finset.filter_congr fun a _ => const_tuple_eq_iff (f a) b)
    (fun _ _ => rfl)

/-- Reading a measurement as a one-coordinate tuple measurement does not
change its effects. -/
private theorem postprocess_const_tuple_effect_self
    {alpha iota d : Type*} [Fintype alpha] [DecidableEq alpha]
    [Fintype iota] [DecidableEq iota] [Unique iota] [Fintype d] [DecidableEq d]
    (M : Quantum.Measurement alpha d) (p : alpha) :
    (M.postprocess (fun a (_ : iota) => a)).effect (fun _ => p) = M.effect p := by
  rw [postprocess_effect_const_tuple]
  simp only [Quantum.Measurement.postprocess_effect, Finset.filter_eq',
    Finset.mem_univ, if_true, Finset.sum_singleton]

/-- The identification of values with constant tuples over a one-element
index set. -/
private def constTupleEquiv (iota beta : Type*) [Unique iota] :
    beta ≃ (iota → beta) where
  toFun b := fun _ => b
  invFun v := v default
  left_inv _ := rfl
  right_inv v := by
    funext i
    rw [Unique.eq_default i]

/-- The polynomial-tuple conclusion of `lem:ld-soundness` for simultaneity
parameter `1`: the coordinate conclusions of the low individual degree
theorem, read as one-coordinate tuples.

The three consistency defects carry the error of `thm:main-formal` at the
auxiliary parameter `directLdAuxParameter D` and pass bound `3 ε`; its
absorption into the error function `deltaLd` is
`exists_directLdTransportConstants`.  For simultaneity parameter at least `2`
the coordinate conclusions do not determine simultaneous polynomial
measurements; see the module docstring and
`docs/paper-gaps/qpbt_ld-simultaneous-sandwich.tex`.  Blueprint
`ch13_qpbt_test.tex:170-215`, paper
`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:413-458`. -/
theorem exists_directSimultaneousPolynomialMeasurements_of_k_eq_one
    (D : DirectLdParams) (hk : D.k = 1) (S : Strategy (directLdGame D))
    (hS : S.IsProjective) (ε : Error) (hwin : 1 - ε ≤ S.value) :
    ∃ GA : DirectPolyMeasTuple D S.ιA,
      ∃ GB : DirectPolyMeasTuple D S.ιB,
        consistencyDefect
            (uniformDistribution (Fin D.m → DirectScalarQ D))
            (fun u outcome =>
              heteroKron
                (((S.A (directLdPointQuestionOf D u)).postprocess
                  (directLdPointValuesOrZero D)).effect outcome) 1)
            (fun u outcome =>
              heteroKron 1
                ((GB.postprocess (evalDirectPolyTupleAt u)).effect outcome))
            S.ψ ≤
          Test.mainFormalError D.toLDTParameters (directLdAuxParameter D) (3 * ε) ∧
        consistencyDefect
            (uniformDistribution (Fin D.m → DirectScalarQ D))
            (fun u outcome =>
              heteroKron
                ((GA.postprocess (evalDirectPolyTupleAt u)).effect outcome) 1)
            (fun u outcome =>
              heteroKron 1
                (((S.B (directLdPointQuestionOf D u)).postprocess
                  (directLdPointValuesOrZero D)).effect outcome))
            S.ψ ≤
          Test.mainFormalError D.toLDTParameters (directLdAuxParameter D) (3 * ε) ∧
        consistencyDefect (uniformDistribution Unit)
            (fun _ g => heteroKron (GA.effect g) 1)
            (fun _ g => heteroKron 1 (GB.effect g))
            S.ψ ≤
          Test.mainFormalError D.toLDTParameters (directLdAuxParameter D) (3 * ε) := by
  letI := D.toLDTFieldModel
  haveI hU : Unique (Fin D.k) :=
    { default := ⟨0, by omega⟩
      uniq := fun i => Fin.ext (by have := i.isLt; omega) }
  obtain ⟨GA₀, GB₀, h1, h2, h3⟩ :=
    directCoordinateMainFormal D S hS default ε hwin
  refine ⟨(directPolynomialMeasurement D GA₀).postprocess (fun g _ => g),
    (directPolynomialMeasurement D GB₀).postprocess (fun g _ => g), ?_, ?_, ?_⟩
  · have h1' := directPointPolynomial_consistencyDefect_le D S hS default GB₀ _ h1
    refine ((consistencyDefect_outcome_equiv _
      (constTupleEquiv (Fin D.k) (DirectScalarQ D)) _ _ S.ψ).symm.trans
      (consistencyDefect_congr _ _ _ _ _ S.ψ ?_ ?_)).trans_le h1'
    · intro u a
      show heteroKron (((S.A (directLdPointQuestionOf D u)).postprocess
        (directLdPointValuesOrZero D)).effect (fun _ => a)) 1 = _
      rw [postprocess_effect_const_tuple]
      rfl
    · intro u a
      show heteroKron 1 ((((directPolynomialMeasurement D GB₀).postprocess
        (fun g _ => g)).postprocess (evalDirectPolyTupleAt u)).effect
          (fun _ => a)) = _
      rw [MIPStarRE.Quantum.Measurement.postprocess_comp,
        postprocess_effect_const_tuple]
      rfl
  · have h2' := directPolynomialPoint_consistencyDefect_le D S hS default GA₀ _ h2
    refine ((consistencyDefect_outcome_equiv _
      (constTupleEquiv (Fin D.k) (DirectScalarQ D)) _ _ S.ψ).symm.trans
      (consistencyDefect_congr _ _ _ _ _ S.ψ ?_ ?_)).trans_le h2'
    · intro u a
      show heteroKron ((((directPolynomialMeasurement D GA₀).postprocess
        (fun g _ => g)).postprocess (evalDirectPolyTupleAt u)).effect
          (fun _ => a)) 1 = _
      rw [MIPStarRE.Quantum.Measurement.postprocess_comp,
        postprocess_effect_const_tuple]
      rfl
    · intro u a
      show heteroKron 1 (((S.B (directLdPointQuestionOf D u)).postprocess
        (directLdPointValuesOrZero D)).effect (fun _ => a)) = _
      rw [postprocess_effect_const_tuple]
      rfl
  · have h3' := directPolynomialPolynomial_consistencyDefect_le D S GA₀ GB₀ _ h3
    refine ((consistencyDefect_outcome_equiv _
      (constTupleEquiv (Fin D.k) (PolyIndex D.m (DirectScalarQ D) D.d)) _ _
        S.ψ).symm.trans
      (consistencyDefect_congr _ _ _ _ _ S.ψ ?_ ?_)).trans_le h3'
    · intro _ p
      show heteroKron (((directPolynomialMeasurement D GA₀).postprocess
        (fun g _ => g)).effect (fun _ => p)) 1 = _
      rw [postprocess_const_tuple_effect_self]
    · intro _ p
      show heteroKron 1 (((directPolynomialMeasurement D GB₀).postprocess
        (fun g _ => g)).effect (fun _ => p)) = _
      rw [postprocess_const_tuple_effect_self]

end

end MIPStarRE.QPBT
