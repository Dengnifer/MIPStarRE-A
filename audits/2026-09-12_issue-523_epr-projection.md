# Issue #523: EPR projection prerequisite

Session: `prover-523-20260912-01`, starting at 2026-09-12 05:04:36 UTC.
Base: `ae124f8f09ee002444ac5b9711822c0f1daae142`.

## Result

The named target `exists_extractionWitness_ofGlobalPairWitness` remains open.
Its signature, error scale, quantifiers, and existing `sorry` are unchanged.
No axiom, proof hole, or load-bearing assumption is added. This packet proves
the independent EPR projection and auxiliary normalization prerequisites.

The source is `references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex`,
`lem:qld-unitary`, lines 1666-1860. The new calculations correspond to
lines 1725-1783. The blueprint records them separately at
`thm:qld-epr-projection-estimates`; neither `lem:qld-unitary` nor its conditional
given-witness auxiliary is marked proved.

## Mathematics

For the characteristic-two Pauli label space V, define
H_W = |V|^{-1} sum_u tau_W(u) tensor tau_W(u). Fourier inversion identifies
H_Z with the diagonal projection onto equal labels. The simultaneous shift
average H_X then gives H_X H_Z = |EPR><EPR| with coefficient |V|^{-1},
not the normalized-trace density coefficient. These identities hold also when
the coordinate index is empty, since V is still nonempty.

For any finite auxiliary register R, I_R tensor H_W is a contraction, being an
average of unitaries. If a unit vector theta has both correlations at least
1 - delta/2, expansion of its squared distance from each correlation average
bounds that distance by sqrt(delta). Splitting
theta - H_X H_Z theta into the two successive errors gives a projection
distance at most 2 sqrt(delta). This proves the corrected estimate without
the numerical errors at paper lines 1753-1763.

The partial inner product with EPR defines aux_0. The new coordinate identity
proves that aux_0 tensor EPR is exactly the projected state, including the
actual heterogeneous six-register placement. Reusing the existing auxiliary
normalization theorem gives a unit aux at distance at most twice the projection
error. When the projection vanishes, a normalized reference vector obtained
from the original strategy and one EPR pair handles that case. The resulting
state estimate, once the correlation premise has been derived, is at most
4 sqrt(delta), or 16 delta in squared norm.

## Reuse and history

The search covered the complete saved history of `Extraction/Unitary.lean`
and the extraction directory across all refs, including saved open-PR commits.
No completed proof of the target at its current statement was found.

- `scout-123-extraction-isometry-20260906-01.last.md` identified the missing
  projection calculation and the existing normalization theorem.
- Saved commit `9b75a5f858141a2900d7c77921366184eeae80d3`, retained in
  `389fdcb65b777cd7065b8ea225d27350c1697dd9`, supplies the coordinate permutation,
  ideal-state permutation equality, ideal norm, and reference auxiliary vector.
  Those five small declarations are reused in `EPRState.lean`, with the same
  public names and proofs specialized only in variable spelling. The rest of
  that branch is not imported. Its duplicate `psiHat_norm` was not copied.
- The normalization proof invokes the current
  `MagicSquareRigidity.exists_unit_residual`; it does not reprove normalization.
- The existing private `tauObservable_X_apply` and `tauObservable_Z_apply` in
  `Algebra/PauliTheorems.lean` are made public without changing their proofs.
  Fourier inversion, Pauli unitarity, tensor norm preservation, and matrix
  coordinate transport are reused from current Mathlib/project declarations.
- Saved swap-conjugation proofs include `7ed13392` and `ef166338`. They belong
  to the separate conjugation packets and are not copied here.

The committed session ledger contains six completed relevant scout/prover
records: prover-240-20260906-01, scout-123-extraction-isometry-20260906-01,
prover-242-20260906-01 and -02, and prover-245-20260906-01 and -02.
Their known combined wall time is 7,395 seconds; recorded input tokens total
24,256,025, including 23,113,344 cached input tokens, and output tokens total
139,412. These are prerequisite/scouting costs, not six failed attempts at
the full target. The historical `prover-121-native-20260907` row has unknown
wall time and usage; it is not counted as zero. This is a lower bound on the
relevant historical cost, not a reset of that episode. The dispatcher will
record this session's additional usage separately.

## Statement integrity

Paper assumptions: an admissible projective setting and the global measurement
constructed earlier in the paper. The correlation bounds follow internally
from its consistency properties. Paper conclusions: normalized auxiliary state,
state extraction, and total-Pauli measurement comparison at the stated scale.

Lean target assumptions: the same original domain and error restrictions, with
the pre-existing explicit `GlobalPairWitness S deltaG` premise. Lean target
conclusions: unchanged `ExtractionWitness` at the unchanged nested
`deltaExtract` / `deltaConstructPaulis` scale. Verdict: the existing extra
global-witness premise remains conditional, with its unfaithful marker intact;
this packet introduces no statement drift and does not certify the target.

The new projection lemma assumes only a unit vector and its explicit two
correlation inequalities. It proves an independently valid analytic implication,
not existence of those correlations for the swapped state. Its blueprint entry
displays these hypotheses. The auxiliary normalization lemma has no correlation
or nonvanishing premise and is valid for every normalized six-register vector.

## Verification

Focused Lean checks pass for both new modules, the Pauli theorem module, and
the target module. The new modules emit no warnings. The target has only its
existing proof-hole warning. All ten inspected new or newly public proof
declarations have axiom closure exactly `propext`, `Classical.choice`, and
`Quot.sound`; the target still additionally uses `sorryAx`.

The source-header audit reports no changes. Hook installation, whitespace,
100-character Lean line checks, proof-integrity token scans, file-length guard,
and blueprint LaTeX conventions pass. Blueprint web rendering succeeds with
the existing missing-bibliography warnings. Full blueprint synchronization
retains pre-existing stale index entries; the new entries resolve.
Publication and exact-head CI outcomes are recorded in the session final
message and GitHub evidence rather than predicted here.

## Remaining work

1. Derive the two correlation inequalities for the swapped state from
   `tildeObs_selfConsistent`, exact swap conjugation, and uniform reindexing by
   a nonzero basis element. The consistency theorem is still a `sorry` at base.
2. Combine point-measurement consistency, evaluated Pauli measurements, exact
   measurement conjugation, EPR transpose transport, and the polynomial
   collision bound. Transfer the entire overlap operator between states to
   avoid an answer-cardinality factor. Both point-consistency declarations and
   both conjugation declarations remain `sorry` at base.
3. Choose universal constants before the parameters and absorb both estimates
   into the unchanged extraction scale. Populate both player orientations.
4. Compose with `exists_globalPairWitness` for the source-facing theorem only
   after that separate construction is proved. The later isometry range
   projection transfer is a separate downstream obligation.

No counterexample or new mathematical non-derivability claim is asserted.

## Publication checkpoint

PR #544 publishes this partial result. At `4109e55a`, pre-push dependency
builds and the full locked CI Lean build passed. CI caught an undefined
`ketbra` macro in the new blueprint text; replacing it by the existing
`ket`/`bra` notation makes `leanblueprint pdf` pass. The CI workflow-fixture
suite independently failed `test_dispatch_command_selects_routine_sol_and_reasoned_hard_astra`
because its temporary dry-run dispatcher returned exit 4. The six invoking
model/effort variables were unset before CI. This packet does not change that
fixture or the workflow machinery. The remaining CI proof-debt, proof-evasion,
file-length, and paper-gap checks passed. Final-head CI must be rerun after
publishing the PDF correction; the session's 60-minute limit precludes another
complete CI cycle. No reviewer was launched and no merge was attempted.
