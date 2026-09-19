import Lean
import MIPStarRE.QPBT.Test.Soundness
import MIPStarRE.QPBT.Test.QubitForm
import MIPStarRE.QPBT.Test.LowDegreeGameTheorems
import MIPStarRE.QPBT.Test.Completeness
import MIPStarRE.QPBT.Test.Soundness.ProjectiveSetting
import MIPStarRE.QPBT.Test.Soundness.NaimarkAssembly
import MIPStarRE.QPBT.Test.Soundness.OperatorTransfer
import MIPStarRE.QPBT.Combining.Lines
import MIPStarRE.QPBT.Combining.Apply
import MIPStarRE.QPBT.Combining.ActualErrorBounds
import MIPStarRE.QPBT.Games.Symmetrization

/-!
# Axiom audits for the quantum Pauli basis test

Reviewer-facing, machine-checked evidence that the QPBT headline results rest on
nothing beyond Lean's three standard axioms.  Before this module the claim was
reproducible only by running a throwaway metaprogram outside the repository; a
reader of the artifact could not re-derive it.

Each audit below both **prints** the axiom set of a headline declaration and
**fails elaboration** unless that set is exactly

`{Classical.choice, Quot.sound, propext}`.

So the module is a compile-time regression test, not a report: if a `sorry`
(`sorryAx`), a new `axiom` declaration, or any other unexpected dependency ever
reaches one of these theorems, `lake build MIPStarRE.QPBT.Test.AxiomAudit`
fails and CI goes red.  The printed lines remain in the build log as the
positive record.

This mirrors `MIPStarRE/LDT/Test/AxiomAudit.lean`, which uses the same
`Lean.collectAxioms` mechanism for the classical low-individual-degree track.
Like that module, this one is built explicitly as a CI target rather than
imported from the `MIPStarRE.QPBT` umbrella, so the audits stay out of normal
downstream imports while still acting as regression tests.

## What is audited

The declarations are the QPBT headline results, in dependency order from the
soundness statement down to the combining and extraction layers:

* `pauli_soundness` — the main theorem (blueprint `thm:pauli`).
* `pauli_soundness_qubit` — its qubit form (`cor:pauli-binary`).
* `exists_ld_soundness` — quantum low-degree soundness (`lem:ld-soundness`).
* `exists_spcc_value_one` and `honestStrategy_isSPCC` — completeness, which is
  what keeps the soundness hypothesis non-vacuous.
* `exists_combinedLinesWitness`, `exists_extendedLinesWitness_established`,
  `exists_globalPairWitness`, `exists_actual_rounded_global_pair_error_bound` —
  the combining layer.
* `exists_projective_setting_isometry_bounds`,
  `exists_arbitrary_strategy_isometry_bounds`,
  `pauli_soundness_deltaQld_ofExtractionWitness` — the extraction layer.
* `exists_symmetric_projective_strategy_approx` — the symmetrization interface.

`exists_extendedLinesWitness_established` and
`exists_symmetric_projective_strategy_approx` are the two *corrected* forms
recorded in `docs/paper-gaps/qpbt-gap-register.md`; they are audited here
precisely because they are the statements that were repaired against the source,
so a regression in them is the one most likely to go unnoticed.
-/

open Lean Elab Command

namespace MIPStarRE.QPBT.Test.AxiomAudit

/-- The axioms Lean's own core development uses, and the only ones a QPBT
headline declaration may depend on. -/
private def standardAxioms : Array Name :=
  (#[``propext, ``Classical.choice, ``Quot.sound] : Array Name).qsort Name.lt

private def resolveDeclIdent (id : TSyntax `ident) : CommandElabM Name := do
  liftCoreM <| Lean.Elab.realizeGlobalConstNoOverloadWithInfo id

end MIPStarRE.QPBT.Test.AxiomAudit

open MIPStarRE.QPBT.Test.AxiomAudit in
/-- Print the axioms of a declaration and fail elaboration unless they are
exactly `propext`, `Classical.choice` and `Quot.sound`.

The failure branch names `sorryAx` explicitly when it is present, because that
is the diagnosis a reader wants first: an unexpected `sorryAx` means a proof
was left open, while any other extra axiom means a new assumption entered the
development. -/
elab "audit_standard_axioms " id:ident : command => do
  let declName ← resolveDeclIdent id
  let axioms := (← Lean.collectAxioms declName).qsort Name.lt
  logInfo m!"axioms of '{declName}': {axioms.toList}"
  unless axioms == standardAxioms do
    if axioms.contains ``sorryAx then
      throwError
        m!"'{declName}' depends on `sorryAx`: a proof it relies on is still " ++
          m!"open.  Axioms: {axioms.toList}"
    else
      throwError
        m!"'{declName}' depends on axioms {axioms.toList}, expected exactly " ++
          m!"{standardAxioms.toList}"

/-! ### Main theorem and its qubit form -/

audit_standard_axioms MIPStarRE.QPBT.pauli_soundness
audit_standard_axioms MIPStarRE.QPBT.pauli_soundness_qubit

/-! ### Quantum low-degree soundness -/

audit_standard_axioms MIPStarRE.QPBT.exists_ld_soundness

/-! ### Completeness

Audited alongside soundness because it is what rules out the reading in which
`pauli_soundness` is vacuous: `exists_spcc_value_one` produces a value-one
strategy for every admissible parameter set. -/

audit_standard_axioms MIPStarRE.QPBT.exists_spcc_value_one
audit_standard_axioms MIPStarRE.QPBT.honestStrategy_isSPCC

/-! ### Combining layer -/

audit_standard_axioms MIPStarRE.QPBT.exists_combinedLinesWitness
audit_standard_axioms MIPStarRE.QPBT.exists_extendedLinesWitness_established
audit_standard_axioms MIPStarRE.QPBT.exists_globalPairWitness
audit_standard_axioms MIPStarRE.QPBT.exists_actual_rounded_global_pair_error_bound

/-! ### Extraction layer -/

audit_standard_axioms MIPStarRE.QPBT.exists_projective_setting_isometry_bounds
audit_standard_axioms MIPStarRE.QPBT.exists_arbitrary_strategy_isometry_bounds
audit_standard_axioms MIPStarRE.QPBT.pauli_soundness_deltaQld_ofExtractionWitness

/-! ### Symmetrization interface -/

audit_standard_axioms MIPStarRE.QPBT.exists_symmetric_projective_strategy_approx
