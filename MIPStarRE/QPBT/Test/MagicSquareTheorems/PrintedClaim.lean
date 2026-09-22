import MIPStarRE.QPBT.Test.MagicSquareTheorems

/-! # The unasserted printed Magic Square rigidity claim

This module retains the unrestricted extraction assertion as a proposition.
The two independent copies used for the two question orientations refute it,
even for symmetric strategies. The proved theorem `exists_ms_rigidity` has
additional variable-agreement hypotheses and a different error bound.

## References

* `references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:620-652`,
  `thm:ms-rigidity`.
* `docs/paper-gaps/qpbt_ms-rigidity-symmetric-strategies.tex`.
* Issue #688, continuing the statement comparison of issues #105 and #172.
-/

namespace MIPStarRE.QPBT

open MIPStarRE.LDT MIPStarRE.Quantum

/-- **Source statement, unasserted:** The full extraction assertion of
`thm:ms-rigidity`, printed at
`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:620-652`.

The strategy ranges over the existing finite-dimensional `Strategy msGame`
domain, including both question orientations and arbitrary POVMs. The value
equality is the printed hypothesis. One universal constant bounds the state
distance, all four bit-measurement distances, and both anticommutator distances
at the printed scale `sqrt epsilon`. There is no agreement, symmetry, or
projectivity hypothesis. The indices `0` and `4` denote variables 1 and 5.
The effects are the prescribed answers `MsAnswer.bit b` themselves, without
the wrong-form completion performed by `msBitOrZero` in the corrected theorem.

As in the four printed measurement estimates, the anticommutator distances are
evaluated on the extracted ideal state. The final generic distance convention
in the paper instead names the original state, on which the transported
operators cannot act; this necessary typing correction is recorded separately
in `docs/paper-gaps/qpbt_ms-rigidity-symmetric-strategies.tex`.

This definition asserts nothing and is not a hypothesis of any construction.
The independent-copy counterexample and its symmetric role-flag version in
that note refute this claim at zero error. The corrected blueprint node
`thm:ms-rigidity` links to `exists_ms_rigidity`, not a proof of this proposition.
Retention under issue #688 does not certify adoption of the correction. -/
def PrintedMagicSquareRigidityClaim : Prop :=
  ∃ C : ℝ, 1 ≤ C ∧ ∀ epsilon : ℝ, 0 ≤ epsilon →
    ∀ S : Strategy msGame, S.value = 1 - epsilon →
      ∃ w : MsRigidityWitness S,
        let distanceA (j : Fin 9) (W : PauliKind) : ℝ :=
          opFamilyDistSq (uniformDistribution Unit)
            (fun _ b => heteroKron
              (conjIsometry w.φA ((S.A (.var j)).effect (.bit b))) 1)
            (fun _ b => heteroKron
              (heteroKron (idealMagicBitProj W b) (1 : Op w.ιA'')) 1)
            (idealMsState w.aux)
        let distanceB (j : Fin 9) (W : PauliKind) : ℝ :=
          opFamilyDistSq (uniformDistribution Unit)
            (fun _ b => heteroKron 1
              (conjIsometry w.φB ((S.B (.var j)).effect (.bit b))))
            (fun _ b => heteroKron 1
              (heteroKron (idealMagicBitProj W b) (1 : Op w.ιB'')))
            (idealMsState w.aux)
        let obsA (j : Fin 9) : Op S.ιA :=
          (S.A (.var j)).effect (.bit 0) - (S.A (.var j)).effect (.bit 1)
        let obsB (j : Fin 9) : Op S.ιB :=
          (S.B (.var j)).effect (.bit 0) - (S.B (.var j)).effect (.bit 1)
        let XA := heteroKron (conjIsometry w.φA (obsA 0)) (1 : Op ((Fin 2 → ZMod 2) × w.ιB''))
        let ZA := heteroKron (conjIsometry w.φA (obsA 4)) (1 : Op ((Fin 2 → ZMod 2) × w.ιB''))
        let XB := heteroKron (1 : Op ((Fin 2 → ZMod 2) × w.ιA'')) (conjIsometry w.φB (obsB 0))
        let ZB := heteroKron (1 : Op ((Fin 2 → ZMod 2) × w.ιA'')) (conjIsometry w.φB (obsB 4))
        ‖isometryTensor w.φA w.φB S.ψ - idealMsState w.aux‖ ≤ C * Real.sqrt epsilon ∧
        distanceA 0 .X ≤ C * Real.sqrt epsilon ∧
        distanceA 4 .Z ≤ C * Real.sqrt epsilon ∧
        distanceB 0 .X ≤ C * Real.sqrt epsilon ∧
        distanceB 4 .Z ≤ C * Real.sqrt epsilon ∧
        opDistSq (uniformDistribution Unit) (fun _ => XA * ZA)
          (fun _ => -(ZA * XA)) (idealMsState w.aux) ≤ C * Real.sqrt epsilon ∧
        opDistSq (uniformDistribution Unit) (fun _ => XB * ZB)
          (fun _ => -(ZB * XB)) (idealMsState w.aux) ≤ C * Real.sqrt epsilon

end MIPStarRE.QPBT
