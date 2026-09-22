import Lean
import MIPStarRE.QPBT.Test.MagicSquareTheorems.PrescribedRigidity

/-!
# Axiom audit of prescribed Magic Square extraction

The completed one-way construction, agreement transfer, original prescribed
products, and both seven-bound theorems must use exactly Lean's three standard
axioms. This focused check fails if any proof acquires additional proof debt.

## References

`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:620-646`,
`docs/paper-gaps/qpbt_ms-rigidity-symmetric-strategies.tex`, issue #701.
-/

open Lean Elab Command

run_cmd do
  let expected := (#[``propext, ``Classical.choice, ``Quot.sound] : Array Name).qsort Name.lt
  for name in #[
      ``MIPStarRE.QPBT.exists_ms_one_way_rigidity_with_constraints,
      ``MIPStarRE.QPBT.ms_variable_distance_le_agreement,
      ``MIPStarRE.QPBT.MagicSquareRigidity.ms_prescribed_anticommutator_norm_A,
      ``MIPStarRE.QPBT.MagicSquareRigidity.ms_prescribed_anticommutator_norm_B,
      ``MIPStarRE.QPBT.exists_ms_prescribed_rigidity_separate_errors,
      ``MIPStarRE.QPBT.exists_ms_rigidity_prescribed_answers] do
    let axioms := (← Lean.collectAxioms name).qsort Name.lt
    logInfo m!"axioms of '{name}': {axioms.toList}"
    unless axioms == expected do
      throwError "Unexpected axioms in {name}: {axioms.toList}"
