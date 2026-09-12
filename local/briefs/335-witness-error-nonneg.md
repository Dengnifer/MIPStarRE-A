# Issue 335: Witness error nonnegativity

## Goal

Derive `0 <= deltaQ` from a supplied `CombinedPointsWitness` and
`0 <= deltaL` from a supplied `ExtendedLinesWitness`. These facts discharge
arithmetic side conditions for later scalar error estimates; they are not new
hypotheses on the paper-facing construction.

## Mathematical Route

- Apply `DistanceCalculus.opFamilyDistSq_nonneg` to the `AA'`--`BA''`
  specialization of `CombinedPointsWitness.self_consistent`.
- Expand the completed `AA'`--`BA''` line-point defect termwise.
- Use `ExtendedLineGame.stateQForm_pairState_eq_AA'_BA''` to transport every
  off-diagonal term to `pairState setting`.
- Its operator is the Kronecker product of two POVM effects, hence is positive
  semidefinite by `MIPStarRE.Quantum.kronecker_nonneg`; apply
  `DistanceCalculus.stateQForm_nonneg`.
- Combine nonnegativity of the completed defect with
  `ExtendedLinesWitness.consistent_alice`.

## Scope

Add a single proof module and its root re-export. Do not alter witness
structures, source-facing hypotheses, completed-evaluation bridges, game
strategies, or passing-value claims. No new axiom, proof hole, producer,
symmetry assumption, or positivity premise is permitted.

## Provenance

- Parent issue #119.
- Closed prerequisites #244 and #302.
- `references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:689-709`.
- `references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1020-1034`.
- Blueprint `lem:qld-4-10` and `lem:qld-4-13`.

## Validation

- Type-check `MIPStarRE/QPBT/Combining/WitnessErrorNonneg.lean`.
- Scan changed Lean files for `sorry` and `axiom`.
- Check the axioms of both public witness lemmas.
- Run the installed hook check and publish through checked push.
