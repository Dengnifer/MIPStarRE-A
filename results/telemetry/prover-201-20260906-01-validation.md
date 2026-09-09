# Issue 201 integration validation — September 6, 2026

Session: `prover-201-20260906-01`; issue #201; PR #205.
This is integration evidence, not an independent mathematical review or CI status.

## Preserved work and integration

The primary checkout's
`results/telemetry/sessions/mathfix-201-20260906-03.last.md` supplied the slot-6
handoff. Its eight uncommitted files, including the untracked `SchmidtMirror.lean`
and source-faithfulness brief, were committed without editing their contents in
`c14ea3a3139a76d4ed81a9423f8f22f5aa125853`. The commit contains 1,778 insertions
and 273 deletions. SHA-256 checks confirmed all eight files remained byte-identical
to their initial session contents after integration.

Fetched `github/main` at `516758b8fe4bba2fd06669c2325aa65132a0ab84` was merged
without conflicts in `fe74413d25ddb7b5bba5f1d043a20c0b18351ec4`. Both commits
ran normal hooks; the integration also passed the reference-transaction
merge-loss guard. No hook override, push, main-branch merge, subagent, independent
review, or full build was performed.

## Validation

- Actual pinned toolchain: Lean 4.32.0, as recorded in `lean-toolchain`.
- Eight focused modules type-checked before integration: SchmidtMirror,
  CodewordConsistency, PinchedReduction, CrossMove, Assembly, Sandwich,
  QPBT, and the project root. Fresh artifacts were written only under
  `/tmp/publish-201-check`, seeded from the branch-private compiled artifacts.
  This is not a clean rebuild of the incoming main changes.
- All five changed/new Lean files have zero `sorry|axiom` matches and zero
  matches for the checked kernel-bypass identifiers.
- Five declaration dependency checks, including `exists_pasting_error`, report
  only `propext`, `Classical.choice`, and `Quot.sound`, with no `sorryAx`.
- All 1,544 blueprint declaration links resolved against the freshly checked
  pre-integration root. Blueprint web succeeded both before and after integration.
- Normal merge hooks ran 485 script tests successfully. Statement-origin,
  proof-obligation metadata, proof-debt, conclusion-shaped hypothesis,
  unfaithful-marker, explicit-axiom, paper-gap style, LaTeX, and whitespace gates
  passed. The installed-hook check passed before and after integration.
- Global blueprint synchronization still reports 231 findings, matching the
  slot-6 handoff's reported count; it is not a green global synchronization check.
- The source-header checker reports zero findings, but does not replace the
  explicit mathematical comparison below.

Logs are `/tmp/publish-201-lean.log`, `/tmp/publish-201-axioms-decls.log`,
`/tmp/publish-201-commit.log`, `/tmp/publish-201-merge-commit.log`,
`/tmp/publish-201-merged-blueprint.log`, and `/tmp/publish-201-sync.log`.

## Statement-integrity comparison

The source is `lem:pasting`,
`references/qpbt-paper/06_nonlocal_games_and_mipstar.tex:504-525`.
Its hypotheses comprise conditional collisions, projectivity of the second
codeword family and joint answer measurement, two forward marginal comparisons,
and joint self-consistency, in a probability distribution and normalized-state
setting. Lean retains these three comparisons, nonnegative error parameters,
and finite-type/decidability boundary instances. The source-facing theorem adds
zero register-exchange, symmetry, or construction assumptions. The previous
four-comparison theorem remains separately named and proved.

Both conclusions compare the joint answers with the same coarse-grained
ordered sandwich `G₂ G₁ G₂`. The universal error is chosen before the types,
distribution, measurements, and state. The retained scalar correction is
`(3 * C + 19) * (η^(1/4) + δ^(1/8))`, for universal `C ≥ 1`, rather than a
product forced to vanish on either coordinate axis. Verdict: faithful boundary
hypotheses and the documented additive-error correction; no additional operator
hypothesis or altered sandwich conclusion. Independent review must certify this
comparison and the proof, including the retained 25-node descendant inventory.

## Operator handoff

Run the ordinary publication/CI tail and independent review on the resulting
exact head. The downstream combining/extraction gaps remain explicitly tracked;
generic pasting completion does not discharge them. No mathematical search or
new proof debt was introduced by this integration session.
