import MIPStarRE.QPBT.Combining.DirectLowDegree.Transport.BranchComparison

/-!
# Value of the seed-fiber dilation

The correlated seed-fiber dilation `ldStrategyToDirect` reads a strategy for
the seed-indexed low-degree game as a strategy for the directly indexed game.
This module shows that the dilation preserves the value exactly.

The direct game asks the canonical questions of a common direct sample.  In
each residue block the dilated strategy asks the original strategy the seeded
canonical questions of that sample; since canonicalizing a canonical sample
changes nothing, these are the seed-indexed questions of the common sample
carrying that residue.  The Born weight of the dilation is the uniform average
of the original Born weights over the residue, the predicates agree after
parsing, and the seed-indexed sample is a direct sample together with a
uniform residue, so the two averages coincide branch by branch, including the
point/point, line/line, and wrong-form clauses and the zero-direction
convention.

## References

- `references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:214-458`
- `blueprint/src/chapter/ch13_qpbt_test.tex:38-121`
- `docs/paper-gaps/qpbt_ld-dimension-divisibility.tex`
-/

open scoped BigOperators MatrixOrder Matrix ComplexOrder

namespace MIPStarRE.QPBT

open MIPStarRE.LDT
open MIPStarRE.Quantum

noncomputable section

/-- Prefix restriction is idempotent. -/
private theorem directPrefixProjection_idem (D : DirectLdParams) (i : Fin D.m)
    (v : Fin D.m → DirectScalarQ D) :
    directPrefixProjection i (directPrefixProjection i v) = directPrefixProjection i v := by
  funext j
  unfold directPrefixProjection
  split_ifs <;> rfl

/-- Canonicalizing the seeded embedding of a canonical direct sample gives the
canonical seeded sample of the original direct sample: the seed-indexed
question asked in a residue block of the dilation is the seed-indexed
question of the common sample carrying that residue. -/
theorem ldCL_ldSpaceOfDirectResidue_directLdMap (L : LdParams) (t : LdType)
    (sample : DirectLdSpace L.toDirectLdParams) (residue : Fin (L.q / L.m)) :
    ldCL L t (ldSpaceOfDirectResidue L
        (directLdMap L.toDirectLdParams t sample) residue) =
      ldCL L t (ldSpaceOfDirectResidue L sample residue) := by
  cases t with
  | point =>
      funext idx
      rcases idx with (j | ⟨⟩) | j <;> rfl
  | aline =>
      funext idx
      rcases idx with (j | ⟨⟩) | j
      · simp only [ldCL, ldALineCL, ldSpaceOfDirectResidue_point,
          ldSpaceOfDirectResidue_seed, directLdMap, chiIndex_seedOfIndexResidue]
        exact congrFun (lineRepMap_apply_self _ _) j
      · rfl
      · rfl
  | dline =>
      funext idx
      rcases idx with (j | ⟨⟩) | j
      · simp only [ldCL, ldDLineCL, ldSpaceOfDirectResidue_point,
          ldSpaceOfDirectResidue_seed, ldSpaceOfDirectResidue_direction, directLdMap,
          chiIndex_seedOfIndexResidue]
        show lineRepMap
            (directPrefixProjection sample.index
              (directPrefixProjection sample.index sample.direction))
            (lineRepMap (directPrefixProjection sample.index sample.direction)
              sample.point) j =
          lineRepMap (directPrefixProjection sample.index sample.direction) sample.point j
        rw [directPrefixProjection_idem]
        exact congrFun (lineRepMap_apply_self _ _) j
      · rfl
      · simp only [ldCL, ldDLineCL, ldSpaceOfDirectResidue_seed,
          ldSpaceOfDirectResidue_direction, directLdMap, chiIndex_seedOfIndexResidue]
        show directPrefixProjection sample.index
            (directPrefixProjection sample.index sample.direction) j =
          directPrefixProjection sample.index sample.direction j
        rw [directPrefixProjection_idem]

/-- Accepted Born mass at a fixed pair of seed-indexed questions. -/
private def ldAcceptedMass (L : LdParams) (S : Strategy (ldGame L))
    (x y : LdQuestion L) : ℝ :=
  ∑ a : LdAnswer L, ∑ b : LdAnswer L,
    if ldWinPredicate L x y a b then outcomeWeight S x y a b else 0

/-- Accepted Born mass at a fixed pair of direct questions. -/
private def directAcceptedMass (D : DirectLdParams) (S : Strategy (directLdGame D))
    (x y : DirectLdQuestion D) : ℝ :=
  ∑ a : DirectLdAnswer D, ∑ b : DirectLdAnswer D,
    if directLdWinPredicate D x y a b then outcomeWeight S x y a b else 0

/-- At the canonical direct questions of a common direct sample, the accepted
mass of the dilation is the uniform residue average of the accepted mass of
the original strategy at the seeded canonical questions. -/
private theorem directAcceptedMass_ldStrategyToDirect (L : LdParams)
    (S : Strategy (ldGame L)) (tA tB : LdType)
    (sample : DirectLdSpace L.toDirectLdParams) :
    directAcceptedMass L.toDirectLdParams (ldStrategyToDirect L S)
        (tA, directLdMap L.toDirectLdParams tA sample)
        (tB, directLdMap L.toDirectLdParams tB sample) =
      (Fintype.card (Fin (L.q / L.m)) : ℝ)⁻¹ * ∑ residue : Fin (L.q / L.m),
        ldAcceptedMass L S
          (tA, ldCL L tA (ldSpaceOfDirectResidue L sample residue))
          (tB, ldCL L tB (ldSpaceOfDirectResidue L sample residue)) := by
  classical
  have hwin : ∀ (residue : Fin (L.q / L.m)) (a b : DirectLdAnswer L.toDirectLdParams),
      directLdWinPredicate L.toDirectLdParams
          (tA, directLdMap L.toDirectLdParams tA sample)
          (tB, directLdMap L.toDirectLdParams tB sample) a b =
        ldWinPredicate L
          (tA, ldCL L tA (ldSpaceOfDirectResidue L sample residue))
          (tB, ldCL L tB (ldSpaceOfDirectResidue L sample residue))
          ((ldDirectAnswerEquiv L).symm a) ((ldDirectAnswerEquiv L).symm b) := by
    intro residue a b
    rw [← ldWinPredicate_parse, parseLdQuestion_ldCL_ofDirectResidue,
      parseLdQuestion_ldCL_ofDirectResidue, Equiv.apply_symm_apply,
      Equiv.apply_symm_apply]
  have hseeded : ∀ (t : LdType) (residue : Fin (L.q / L.m)),
      seededLdQuestion L (t, directLdMap L.toDirectLdParams t sample) residue =
        (t, ldCL L t (ldSpaceOfDirectResidue L sample residue)) := by
    intro t residue
    exact congrArg (fun z => (t, z))
      (ldCL_ldSpaceOfDirectResidue_directLdMap L t sample residue)
  have hmass : ∀ residue : Fin (L.q / L.m),
      ldAcceptedMass L S
          (tA, ldCL L tA (ldSpaceOfDirectResidue L sample residue))
          (tB, ldCL L tB (ldSpaceOfDirectResidue L sample residue)) =
        ∑ a' : DirectLdAnswer L.toDirectLdParams,
          ∑ b' : DirectLdAnswer L.toDirectLdParams,
            if directLdWinPredicate L.toDirectLdParams
                (tA, directLdMap L.toDirectLdParams tA sample)
                (tB, directLdMap L.toDirectLdParams tB sample) a' b' then
              outcomeWeight S
                (tA, ldCL L tA (ldSpaceOfDirectResidue L sample residue))
                (tB, ldCL L tB (ldSpaceOfDirectResidue L sample residue))
                ((ldDirectAnswerEquiv L).symm a') ((ldDirectAnswerEquiv L).symm b')
            else 0 := by
    intro residue
    unfold ldAcceptedMass
    rw [← Equiv.sum_comp (ldDirectAnswerEquiv L).symm]
    refine Finset.sum_congr rfl fun a' _ => ?_
    rw [← Equiv.sum_comp (ldDirectAnswerEquiv L).symm]
    refine Finset.sum_congr rfl fun b' _ => ?_
    rw [hwin residue a' b']
  unfold directAcceptedMass
  simp only [hmass]
  calc
    ∑ a' : DirectLdAnswer L.toDirectLdParams,
        ∑ b' : DirectLdAnswer L.toDirectLdParams,
          (if directLdWinPredicate L.toDirectLdParams
              (tA, directLdMap L.toDirectLdParams tA sample)
              (tB, directLdMap L.toDirectLdParams tB sample) a' b' then
            outcomeWeight (ldStrategyToDirect L S)
              (tA, directLdMap L.toDirectLdParams tA sample)
              (tB, directLdMap L.toDirectLdParams tB sample) a' b'
          else 0) =
        ∑ a' : DirectLdAnswer L.toDirectLdParams,
          ∑ b' : DirectLdAnswer L.toDirectLdParams,
            ∑ residue : Fin (L.q / L.m),
              (Fintype.card (Fin (L.q / L.m)) : ℝ)⁻¹ *
                (if directLdWinPredicate L.toDirectLdParams
                    (tA, directLdMap L.toDirectLdParams tA sample)
                    (tB, directLdMap L.toDirectLdParams tB sample) a' b' then
                  outcomeWeight S
                    (tA, ldCL L tA (ldSpaceOfDirectResidue L sample residue))
                    (tB, ldCL L tB (ldSpaceOfDirectResidue L sample residue))
                    ((ldDirectAnswerEquiv L).symm a') ((ldDirectAnswerEquiv L).symm b')
                else 0) := by
      refine Finset.sum_congr rfl fun a' _ => Finset.sum_congr rfl fun b' _ => ?_
      by_cases hc : directLdWinPredicate L.toDirectLdParams
          (tA, directLdMap L.toDirectLdParams tA sample)
          (tB, directLdMap L.toDirectLdParams tB sample) a' b' = true
      · simp only [hc, eq_self_iff_true, if_true]
        rw [← Finset.mul_sum, ← strategyBornWeight_eq_outcomeWeight,
          ldStrategyToDirect_bornWeight]
        simp only [hseeded, strategyBornWeight_eq_outcomeWeight]
      · simp [hc]
    _ = ∑ a' : DirectLdAnswer L.toDirectLdParams,
          ∑ residue : Fin (L.q / L.m),
            ∑ b' : DirectLdAnswer L.toDirectLdParams,
              (Fintype.card (Fin (L.q / L.m)) : ℝ)⁻¹ *
                (if directLdWinPredicate L.toDirectLdParams
                    (tA, directLdMap L.toDirectLdParams tA sample)
                    (tB, directLdMap L.toDirectLdParams tB sample) a' b' then
                  outcomeWeight S
                    (tA, ldCL L tA (ldSpaceOfDirectResidue L sample residue))
                    (tB, ldCL L tB (ldSpaceOfDirectResidue L sample residue))
                    ((ldDirectAnswerEquiv L).symm a') ((ldDirectAnswerEquiv L).symm b')
                else 0) :=
      Finset.sum_congr rfl fun a' _ => Finset.sum_comm
    _ = ∑ residue : Fin (L.q / L.m),
          ∑ a' : DirectLdAnswer L.toDirectLdParams,
            ∑ b' : DirectLdAnswer L.toDirectLdParams,
              (Fintype.card (Fin (L.q / L.m)) : ℝ)⁻¹ *
                (if directLdWinPredicate L.toDirectLdParams
                    (tA, directLdMap L.toDirectLdParams tA sample)
                    (tB, directLdMap L.toDirectLdParams tB sample) a' b' then
                  outcomeWeight S
                    (tA, ldCL L tA (ldSpaceOfDirectResidue L sample residue))
                    (tB, ldCL L tB (ldSpaceOfDirectResidue L sample residue))
                    ((ldDirectAnswerEquiv L).symm a') ((ldDirectAnswerEquiv L).symm b')
                else 0) :=
      Finset.sum_comm
    _ = _ := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun residue _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun a' _ => ?_
      rw [Finset.mul_sum]

/-- The correlated seed-fiber dilation preserves the value exactly: the
direct game's value of `ldStrategyToDirect L S` is the seed-indexed game's
value of `S`.  Both values are averages over the ordered type pair and the
common sample; the direct sample together with a uniform residue is the
seed-indexed sample, and the dilation realizes, in each residue block, the
original strategy at the seed-indexed questions of that sample. -/
theorem ldStrategyToDirect_value_eq (L : LdParams) (S : Strategy (ldGame L)) :
    (ldStrategyToDirect L S).value = S.value := by
  classical
  letI : Nonempty (Fin (L.q / L.m)) :=
    Fin.pos_iff_nonempty.mp L.seedFiberCard_pos
  have hsymm : ∀ b : ((LdType × LdType) × DirectLdSpace L.toDirectLdParams) ×
      Fin (L.q / L.m),
      (ldQuestionSeedFiberEquiv L).symm b =
        (b.1.1, ldSpaceOfDirectResidue L b.1.2 b.2) :=
    fun b => rfl
  change avgOver (directLdQuestionDistribution L.toDirectLdParams)
      (fun xy => directAcceptedMass L.toDirectLdParams (ldStrategyToDirect L S) xy.1 xy.2) =
    avgOver (ldQuestionDistribution L) (fun xy => ldAcceptedMass L S xy.1 xy.2)
  unfold directLdQuestionDistribution ldQuestionDistribution
  rw [Distribution.avgOver_map, Distribution.avgOver_map,
    avgOver_uniform_equiv (ldQuestionSeedFiberEquiv L)]
  simp only [hsymm]
  rw [avgOver_uniform_prod (fun (src : (LdType × LdType) × DirectLdSpace L.toDirectLdParams)
      (residue : Fin (L.q / L.m)) =>
      ldAcceptedMass L S
        (src.1.1, ldCL L src.1.1 (ldSpaceOfDirectResidue L src.2 residue))
        (src.1.2, ldCL L src.1.2 (ldSpaceOfDirectResidue L src.2 residue)))]
  apply avgOver_congr
  intro src
  rw [directAcceptedMass_ldStrategyToDirect, avgOver_uniform_eq_inv_card_mul_sum]

end

end MIPStarRE.QPBT
