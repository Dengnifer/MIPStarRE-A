import MIPStarRE.QPBT.Test.MagicSquareTheorems.Basic

/-!
# Perfect strategies for the Magic Square game

This file contains the state of the perfect strategy and states the
construction from two anticommuting consistent binary measurements.

## References

The source statement is `thm:ms-from-ac` in
`blueprint/src/chapter/ch13_qpbt_test.tex:251-261`, from
`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:654-722`.
-/

open scoped BigOperators Matrix

namespace MIPStarRE.QPBT

open MIPStarRE.LDT MIPStarRE.Quantum

noncomputable section

/-- The state of the perfect strategy constructed in `thm:ms-from-ac`. -/
noncomputable def msPerfectState (ι : Type*) [Fintype ι] [DecidableEq ι]
    [Nonempty ι] : EuclideanSpace ℂ ((ι × ZMod 2) × (ι × ZMod 2)) :=
  reindexState prodShuffle (vecTensor (eprState ι) (eprState (ZMod 2)))

/-- `thm:ms-from-ac`: any anticommuting pair of projective binary
measurements, consistent on an EPR state, extends to a value-one SPCC Magic
Square strategy. Blueprint `ch13_qpbt_test.tex:251-261`, paper
`08_classical_and_quantum_low_degree_tests.tex:654-722`.

The local index type is arbitrary, finite, and nonempty; no field model or QPBT
parameter is assumed. The equality `hι` identifies the target local Hilbert
space with the constructed tensor factor. -/
theorem exists_ms_perfect_strategy_of_anticommuting
    {ι : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (A B : Measurement (ZMod 2) ι)
    (hA : MIPStarRE.QPBT.Measurement.IsProjective A)
    (hB : MIPStarRE.QPBT.Measurement.IsProjective B)
    (hcA : MIPStarRE.QPBT.Measurement.IsConsistentOn A (eprState ι))
    (hcB : MIPStarRE.QPBT.Measurement.IsConsistentOn B (eprState ι))
    (hac : obsOf A * obsOf B = -(obsOf B * obsOf A)) :
    ∃ S : SymmetricStrategy msGameSymm, ∃ hι : S.ι = (ι × ZMod 2),
      S.IsSPCC ∧ S.toStrategy.value = 1 ∧
      reindexState (Equiv.prodCongr (Equiv.cast hι) (Equiv.cast hι)) S.ψ =
        msPerfectState ι ∧
      ∀ b : ZMod 2,
        reindexOp (Equiv.cast hι.symm) ((S.M (.var 0)).effect (.bit b)) =
            heteroKron (A.effect b) (1 : Op (ZMod 2)) ∧
          reindexOp (Equiv.cast hι.symm) ((S.M (.var 4)).effect (.bit b)) =
            heteroKron (B.effect b) (1 : Op (ZMod 2)) := by
  sorry

end

end MIPStarRE.QPBT
