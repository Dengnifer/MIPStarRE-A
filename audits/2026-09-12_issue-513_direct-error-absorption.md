# Direct-game error absorption: independent second attempt at issue #513

## Result

The statement and proof hole of `exists_globalPairWitness` are unchanged from
the pinned base `d647a4818ef43092aa66404834b99f2cb292ede8`. This attempt proves
two numerical prerequisites in `Combining/DirectPassingErrorBounds.lean`.
Neither theorem assumes a point witness, a line witness, or a global pair
witness. Their hypotheses concern only real functions and scalar constants.

Let `p(epsilon)` be a polynomial point error and `f(epsilon,rho)` a polynomial
line error in the corrected additive sense of `IsPolyErr` and `IsPolyErr₂`.
For `c >= 0` and a real dimension `D >= 1`, the first theorem proves

\[
\min\{1,3(\sqrt{p(\epsilon)+cD f(\epsilon,\rho)}+\rho)\}
\le D g(\epsilon,\rho)
\]

for a polynomial error function `g`, uniformly for nonnegative arguments.
The point error and the line error both occur under the square root.
The dimension factor is retained. The probability cap permits this statement
on the entire nonnegative quadrant even when the two errors have different
power bounds.

For `rho = md/q`, put

\[
\eta=3(\sqrt{p(\epsilon)+cmf(\epsilon,\rho)}+\rho).
\]

The second theorem proves that, for fixed `a >= 1`, `0 < b <= 1`, and
`C >= 0`, there are universal `A > 1` and `0 < B < 1` such that

\[
\min\{1,C(\delta_{\rm ld}(a,b,\eta+\epsilon,q,2m+2,d,1)
  +\sqrt{p(\epsilon)}+\rho)\}
\le A(md)^A(\epsilon^B+q^{-B}+2^{-Bmd}).
\]

The constants are chosen before the admissible parameters and the test
error. The `deltaLd` input uses the full passing envelope, not its cap.
The proof first handles the cap using the first theorem and the existing
`exists_global_pair_error_bound`. If `eta > 1`, low-degree soundness at the
capped input `1 + epsilon` already has error at least one. Applying the
existing absorption with final scale `C + 1` then bounds the final cap in
the uncapped statement as well. The additive `epsilon` allows a positive
soundness input whenever the original test error is positive.

## Source and reused content

The source read before the proof was
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1267-1288`,
`lem:qld-4-7`, followed by its blueprint entry. The closing substitution was
checked at paper lines 1380-1404, especially `eq:qld-sgg-mhat-sandwich`.
The new bounds are separately labelled Lean-only scalar results:
`thm:qld-direct-passing-polynomial-bound` and
`thm:qld-direct-global-pair-error-bound`. The source theorem remains
`notready`.

All saved Git refs were searched for the target and relevant error bounds.
The following existing work is distinguished from this attempt:

- The first attempt's immutable checkpoint is the audit
  `2026-09-12_issue-513_pair-completion.md` at commit
  `dd9b0850380b32e7ec721e2bd4f7e1f8a42a572b`, PR #535. Its recovered
  completion constructions and new retained-overlap estimates are not copied
  or rederived here. That worktree was read only.
- `exists_global_pair_error_bound` was already present on main, with saved
  history `0f4ef053` and naming correction `fc18d3ab`. The new proof invokes
  it rather than repeating its real-power and dimension estimates.
- `directPassingErrorEnvelope`, from `2fe0b6b8`, and
  `ExtendedLineGame.strategy_value_ge_directPassingErrorEnvelope`, from
  `50ba6804`, are present at the pinned base. Their actual argument is
  `deltaQ + deltaL`, with collision contribution `md/q`. This is the
  expression treated by the new lemmas.
- Main's `exists_direct_ld_soundness` supplies the three directly indexed
  soundness bounds. Its public statement and axiom closure were checked.
- Saved commit `7b232dfa` includes
  `exists_direct_polynomial_measurements_of_supplied_witnesses`, originally
  `0ca9cfca`. Its statement takes both witnesses and returns POVMs on the
  original expanded spaces. It asserts neither projectivity nor existence
  of a polynomial-pair witness. It is not imported or used in this proof.

## Remaining obligations

The new result closes the numerical substitution for the actual direct-game
passing envelope. It does not prove that all measurements in the source
construction exist. In particular:

1. The source strategy must produce the extended-line witness with the
   established line error. A helper that takes this witness is not its
   construction.
2. Direct soundness yields polynomial POVMs. The target requires projective
   polynomial-pair measurements on `S.ExpandedLocalSpace side`. Applying
   Naimark dilation changes the space, while compression of a projective
   measurement generally gives a POVM; the required projectivity and space
   must therefore be proved together.
3. The ordered correlations `eq:qld-g-42` and `eq:qld-g-43`, the concentration
   estimate `eq:qld-g-non-separable`, and the retained point-overlap bounds
   leading to `eq:qld-sgg-mhat-sandwich` remain necessary. They must preserve
   the soundness and point-error contributions and both heterogeneous
   placements. This packet assumes none of these operator inequalities.
4. The first attempt's completion bounds can be used only after those
   retained-overlap estimates are established. The scalar theorem here
   absorbs their displayed final error; it cannot supply the estimates.

These are missing constructions, not a counterexample to the source theorem.
The separate defects in the printed seed-indexed soundness import remain
documented in `docs/paper-gaps/qpbt_ld-dimension-divisibility.tex`. Using the
direct theorem does not certify that printed tensor-code reduction.

## Statement-integrity audit

- Paper assumptions: admissible parameters and a projective Pauli-basis
  strategy with value at least `1 - epsilon`, for positive `epsilon`.
- Lean assumptions: the same preexisting `AdmissibleParams`, positive error,
  and `ProjectiveSetting`. The target acquires no new input.
- Paper conclusion: constants `a > 1`, `0 < b < 1`, chosen universally,
  and projective measurements of global polynomial pairs on both expanded
  local spaces, consistent with the opposite point measurements for each
  Pauli basis, with the specified error function.
- Lean conclusion: unchanged `GlobalPairWitness` and `deltaQld`, with the
  same quantifier order, constants, and four consistency requirements.
- Verdict: target statement preserved with its existing finite-space
  encoding; proof incomplete. The new scalar statements are independent
  auxiliary estimates and are not replacements for the source theorem.

## Validation

- Focused Lean checks of the new module and `Apply.lean` pass. The new module
  has no warnings, direct proof holes, axiom declarations, or kernel bypasses.
  `Apply.lean` retains its five existing holes.
- Fresh object files were generated in this worktree's private build tree.
  The runtime harness
  `~/.cache/mipstarre-dev/sessions/prover-513-20260912-02-axioms.lean` checks
  both new public theorems, the reused absorption theorem, direct soundness,
  the supplied-strategy passing bound, and the target. All except the target
  use only `propext`, `Classical.choice`, and `Quot.sound`. The target still
  lists `sorryAx`.
- `leanblueprint web` passes with existing missing-bibliography warnings;
  blueprint synchronization passes. The source theorem's completion status
  is unchanged.
- Hook installation and whitespace checks pass. Exact-head CI and PR
  publication are reported in the PR and final session handoff, not assumed
  by this checkpoint.

## Cost accounting

The three earlier #119 prover sessions recorded in the first checkpoint have
1927 seconds of total session span, 18,472,194 input tokens, 18,088,320 cached
input tokens, and 56,839 output tokens (including 17,733 reasoning tokens).
The two later #119 scout records have unknown active-time attribution and
nonadditive token snapshots; they remain excluded from these sums, not
erased from the history.

The completed dispatcher receipt for `prover-513-20260912-01` records
`2026-09-12T04:56:37Z` through `2026-09-12T05:56:39Z`, 3602 seconds,
13,083,296 input tokens, 12,717,696 cached input tokens, and 30,819 output
tokens (including 10,671 reasoning tokens). Thus the additive recorded
predecessor totals are 5529 session-seconds, 31,555,490 input tokens,
30,806,016 cached input tokens, and 87,658 output tokens, including 28,404
reasoning tokens. Cached input is part of input and reasoning is part of
output; neither is added a second time. Session span is not a measurement
of active proof time.

This second attempt is separately dispatched as `prover-513-20260912-02`,
starting at `2026-09-12T05:41:53Z`, with a 60-active-minute bound and no
descendants. Its final usage belongs to its own dispatcher receipt. The
overlap in calendar time with the first attempt does not reset either
budget or make their token totals nonadditive. No historical telemetry is
edited by this packet.
