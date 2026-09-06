# Exact binary transport of a supplied soundness witness

Date: 2026-09-06. Packet: #246.

## Scope and source

This packet proves an exact change of coordinates for an already supplied
`PauliSoundnessWitness P S`. It does not construct such a witness from the
success probability of a strategy. The only implementation file changed is
`MIPStarRE/QPBT/Test/QubitForm.lean`; this audit is the other changed file.

The source passages are:

- `references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:1470-1492`,
  Corollary `cor:pauli-binary` and its proof by post-composition;
- `references/qpbt-paper/04_preliminaries.tex:1173-1260`, Lemma
  `lem:pauli-binary`, especially the fixed-basis construction and Fourier
  inversion in `eq:qudit-to-qubit-pauli-1`;
- `references/qpbt-paper/06_nonlocal_games_and_mipstar.tex:258-271`,
  Definition `def:povm-distance`, whose summands are squared vector norms.

The matching blueprint entries are `lem:pauli-binary` in
`blueprint/src/chapter/ch11_qpbt_algebra.tex` and `cor:pauli-binary` in
`blueprint/src/chapter/ch13_qpbt_test.tex`. No blueprint file or tag is changed.
In particular, this packet does not provide new evidence for the existing
source-corollary `\leanok` tag: its existence proof is still open.

## Construction and exact identities

Write
\[
  I=\operatorname{Cube}(P.m),\qquad
  R=(I\to P.\mathrm{model}.K),\qquad
  Q=(I\times\operatorname{Fin}(P.\mathrm{model}.\mathrm{basisDim})\to\mathbb F_2).
\]
The map `BinaryWitnessTransport.labelEquiv P.model` is the equivalence
\(e:R\simeq Q\) obtained by applying the stored binary basis coordinates at
every position and then uncurrying. Its value is the existing `kappaVec`.
There is no newly chosen basis or arbitrary bijection of the field.

Self-duality gives equality of the field trace pairing and the dot product of
the bit coordinates. Addition is also preserved. These two facts identify the
matrix entries of both the shift and phase observables. Applying the proved
finite Fourier inversion formula then gives the forward projector identity
\[
  \operatorname{Matrix.reindex}(e,e)(\operatorname{pauliProj}(W,u))
  =\operatorname{qubitPauliProj}(W,\kappa(u)).
\]
This is `BinaryWitnessTransport.pauli_projector_reindex`. Its index type is
arbitrary and finite, so the actual cube register needs no conversion to a
`Fin` register. The existing public `exists_qubitIsometry` theorem is unchanged.
Its coordinate-level implementation is private and specialized to `Fin L`;
the arbitrary-index calculation here uses the public trace and Fourier APIs,
without changing that separately owned algebra file.

For a supplied witness \(w\), let
\[
  e_A=\mathrm{id}_{w.\iota_A'}\times e,\qquad
  e_B=\mathrm{id}_{w.\iota_B'}\times e,\qquad
  e_{AB}=e_A\times e_B.
\]
Mathlib's `LinearIsometryEquiv.piLpCongrLeft` supplies the Euclidean permutation
isometries \(U_A,U_B\). The constructor `PauliSoundnessWitness.toQubit` sets
\(\phi_A^{\mathrm{bit}}=U_A\circ w.\phi_A\) and
\(\phi_B^{\mathrm{bit}}=U_B\circ w.\phi_B\). Both auxiliary carriers and their
instances, the auxiliary vector, and its normalization proof are preserved.

The EPR calculation uses two special properties of the permutation: equality
of labels is preserved and the two label types have equal cardinality. Thus
its normalization coefficient is unchanged. The theorem
`BinaryWitnessTransport.ideal_state_reindex` proves
\[
  \operatorname{reindexState}(e_{AB},\operatorname{idealState}(P,w.\mathrm{aux}))
  =\operatorname{idealQubitState}(P,w.\mathrm{aux}).
\]
It respects the existing ordering
\(((A'\times R)\times(B'\times R))\); the auxiliary factor is not permuted.
No claim is made that \(U\otimes U\) preserves EPR for an arbitrary complex
unitary.

Post-composition reindexes the joint extracted state and each conjugated local
effect. The lifted-effect lemmas include the identity on the other player's
whole local space. The ideal-projector lemmas include the other three identity
factors. Mathlib's `Matrix.submatrix_mulVec_equiv` then identifies the actions
of the transported operator differences on the transported ideal state.
Euclidean norm preservation gives the three endpoints:

- `qubit_state_error_to_qubit`;
- `qubit_operator_distance_a_to_qubit`;
- `qubit_operator_distance_b_to_qubit`.

All three are equalities. The operator sums remain over `PauliRegister P` and
retain squared vector norms. No triangle inequality, changed reference state,
rescaled error, or altered soundness constant occurs.

## Statement-integrity audit

### Exact transport

- **Assumptions:** a supplied `PauliSoundnessWitness P S`, consisting of finite
  auxiliary spaces, local isometries, and a normalized auxiliary vector. The
  coordinate lemmas use the fixed field model and the usual finite-type and
  decidable-equality instances. The generic EPR lemma also assumes nonempty
  carriers, as required by `eprState`.
- **Conclusions:** a constructed qubit witness with the same auxiliary data,
  equal state error, and equal Alice and Bob operator-family distances.
- **Verdict:** exact Lean-only transport of existing data. No success
  assumption, error parameter, bound, intertwining assumption, or new witness
  hypothesis is added to a source-level theorem. This is not an existence
  theorem disguised as a conditional proof.

### Preserved source corollary

- **Paper assumptions:** admissible parameters and a strategy succeeding with
  probability at least \(1-\varepsilon\), with universal constants
  \(a\geq1\) and \(0<b<1\) preceding those parameters.
- **Lean assumptions:** the same quantifier order and success hypothesis,
  `P : AdmissibleParams`, and the existing explicit condition `0 ≤ ε`.
  Finite Hilbert-space carriers and the fixed self-dual field coordinates are
  the existing formal encoding.
- **Paper conclusion:** existence of local qubit-extraction isometries and a
  unit auxiliary state satisfying the state-error bound and both ideal-state
  operator-family comparisons, at the stated soundness scale.
- **Lean conclusion:** the same three bounds packaged by
  `QubitSoundnessWitness`, `idealQubitState`, the two squared-distance
  functionals, and the unchanged `deltaQld`.
- **Verdict:** faithful boundary hypotheses; the source-facing statement is
  unchanged. Its docstring, statement, and original `sorry` proof were checked
  byte-for-byte against the starting commit. The correction of the source's
  final binary factor range is already documented in
  `docs/paper-gaps/qpbt_pauli-binary-factor-index.tex`; no further source
  correction is required for this transport.

## Validation

- `lake env lean MIPStarRE/QPBT/Test/QubitForm.lean` passes. The only warning is
  the retained `pauli_soundness_qubit` proof hole.
- `rg -n "sorry|axiom" MIPStarRE/QPBT/Test/QubitForm.lean` reports only
  `516:  sorry`. The count is unchanged from the starting commit.
- Kernel axiom checks of the constructor, projector transport, EPR transport,
  shuffled ideal-state identity, and all three endpoints report only
  `propext`, `Classical.choice`, and `Quot.sound`. None depends on `sorryAx`.
  The checks compile the edited source through `lake env lean --stdin`, rather
  than inspecting an older cached object.
- The import of `Test.Soundness` is replaced by `Test.SoundnessDefs`.
  No new declaration calls the unfinished parent soundness theorem.
- The forbidden-token and debugging-command scan is empty; `git diff --check`
  passes. Git hooks were installed and their installation check passed.
- A full build is skipped under `local/protocols/build-cache.md`, section 7:
  the machine-wide lock was held by PID 2714178 when checked. No bare build,
  lock override, shared-cache write, main refresh, CI, review, or publication
  was performed. File-level and axiom-check logs are under
  `~/.cache/mipstarre-dev/issue-246-{check,axioms}.log`.

## Open obligations and handoff

The only retained hole in the edited file is `pauli_soundness_qubit`. Its
missing content is source-level existence from successful strategies, not the
transport of supplied data. Once `pauli_soundness` has an independent completed
proof, the source proof strategy can obtain its witness and apply the exact
identities proved here. That future argument is not implemented by treating
the currently unfinished theorem as a proved fact.

The upstream extraction issues are described in
`docs/paper-gaps/qpbt_extraction-transfer.tex`, including the range-projection
transfer that must be established from actual extraction data. That note is
not itself a proof of soundness existence. No new proof obligation or source
assumption is introduced, and this packet does not discharge those analytic
obligations.

A separate reviewer should first inspect the projector-reindex orientation,
the post-composition order in `toQubit`, preservation of the auxiliary state,
and the unchanged field-valued answer sums. The remaining validation item is
a full build when the machine-wide lock is available.
