# Global polynomial-pair transport: independent third attempt

## Result

The source theorem `exists_globalPairWitness` remains unproved. Its public
statement, proof, and blueprint status are unchanged from pinned main
`fd83ecda4ec0bf8397687eff9ebcc034525d0dd6`.

This attempt independently typechecks the composition of the saved pair
completion with current-main projective rounding. It does not add a
conditional producer or duplicate a completed packet. In particular, issue
#278 was confirmed closed through the primary repository's `gh_common.py`;
its proof is already present at this base. No duplicate PR is opened.

## Source and predecessor receipts

The paper passage read was
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1267-1404`,
especially `lem:qld-4-7`, `eq:qld-g-non-separable`,
`eq:qld-sgg-completeness`, and `eq:qld-sgg-mhat-sandwich`.
The matching blueprint entry is `lem:qld-4-7`.

The read-only predecessors are:

- First attempt: `dd9b0850380b32e7ec721e2bd4f7e1f8a42a572b`, PR #535,
  `audits/2026-09-12_issue-513_pair-completion.md`. Its
  `PairCompletion.lean` recovers the injective polynomial combination,
  restriction, and completion, and proves retained-overlap estimates.
- Second attempt: `2f8f5cc4631db2db23f76513a2f7f56dffc8fa4f`, PR #545,
  `audits/2026-09-12_issue-513_direct-error-absorption.md`. Its scalar
  bounds retain both point and line errors in the actual passing envelope.
  GitHub reports the PR open; the dispatcher receipt reports a failed session,
  not a completed final handoff.
- Existing rounding: `a418f28629cdd8fcba054f7eed04d5d1a8e04621`,
  `projective_rounding_preserves_postprocessed_consistency`. This is the
  proof for closed issue #278. It is reused, not rederived.
- Existing scalar absorption: `exists_global_pair_error_bound`, already
  on main, with naming correction `fc18d3ab042cbaafeebf44b12b2f6e9b525fac13`.

The target and its saved application-file history were inspected. Neither of
the two #513 predecessor checkpoints discharges it.

## Verified composition and quantifiers

Let A and B be complete measurements on extended polynomials, on the two
original local spaces, with cross-player consistency defect at most delta.
For a unit state and delta >= 0, the existing rounding theorem chooses
projective measurements R_A and R_B on those same spaces. Fix a completion
pair p, and let c_p send a combined polynomial to its unique pair and every
other outcome to p.

Postprocessing R_A and R_B by c_p gives projective pair measurements P_A
and P_B. These measurements are chosen before every finite question,
intermediate-answer, and final-answer type, probability law mu, readout
maps l_x and e_x, opposite measurement N_x, and comparison error eta.

For each orientation, if the completed original POVM, first read by l_x and
then by e_x, has defect at most eta against N_x, the corresponding rounded
measurement has defect at most

$$
 R(\delta,\eta)=\delta+\sqrt{220\,\delta^{1/4}}+
                  2\sqrt{\delta+\eta}.
$$

The proof applies the existing transport with the single outcome map
`g => e_x (l_x (c_p g))` and uses `Measurement.postprocess_comp` twice.
It loses no additional constant and retains the universal quantifiers.
A polynomial line readout followed by evaluation is one permissible choice
of the two maps; a point readout is obtained by making the first map the
identity. The check does not identify a concrete line carrier with the
source verifier law, nor assert its comparison bound.

This refines the predecessor receipts' projectivity warning: compression
alone does not preserve projectivity, but same-space projective rounding
with simultaneous transport is already available once the original
cross-player polynomial consistency estimate is supplied.

## Remaining mathematical obligations

The verified composition is not a construction from the Pauli strategy.
The following steps remain explicit:

1. Construct the extended-line witness from the source strategy with a valid
   error estimate, rather than assume the witness.
2. Apply direct soundness and prove the required cross-player consistency
   of the compressed polynomial measurements on the relevant expanded
   local spaces.
3. Prove both ordered correlations `eq:qld-g-42` and `eq:qld-g-43`,
   concentration on separated combined polynomials, and the retained
   overlaps for both bases and both register placements.
4. Account for rounding in the final numerical substitution. The saved
   second attempt absorbs the paper-shaped expression containing deltaLd,
   the square root of the point error, and md/q. The displayed rounding
   bound also contains a delta^(1/8) term and a square root of delta+eta.
   The successful compatibility checks do not identify those expressions
   or prove their final absorption.

There is no counterexample to the source existence statement in this
attempt. The obstruction is the missing construction and estimates above,
not failure of postprocessing to retain universal quantifiers.

## Verification

Focused checks completed successfully on this pinned main:

- `ErrorObstruction.lean` and `RoundingTransport.lean` were compiled into
  the worktree's private object tree because its initial snapshot lacked
  their object files.
- `Apply.lean` was freshly compiled. Its five preexisting holes remain.
- The exact saved `PairCompletion.lean` source, followed by the explicit
  two-map compatibility proof, typechecks in the runtime harness
  `~/.cache/mipstarre-dev/sessions/prover-513-20260912-03-composition.lean`.
  SHA-256: `b216a84e53eef71b8d1dfb1417e1480ab6b4cf5af19937cf6f5759d6cf53fb2d`.
- The exact saved `DirectPassingErrorBounds.lean` source typechecks in
  `~/.cache/mipstarre-dev/sessions/prover-513-20260912-03-errors.lean`.
  SHA-256: `eee132ddd5e9cb022b52118cc59f5422cf7a230bee944d8384021e7b3cf5ca4f`.
- Axiom checks for the composed transport, completion estimate, rounding
  transport, existing absorption, and both saved public scalar bounds list
  only `propext`, `Classical.choice`, and `Quot.sound`.
- The freshly compiled target still lists `sorryAx`.
- The Lean source and blueprint diff against the pinned base is empty.

Only this audit is committed. The harnesses are compatibility evidence, not
new production declarations. No full build, blueprint build, publication,
exact-head CI, reviewer, or merge is claimed for this evidence-only
checkpoint. Existing PRs and other worktrees were not modified.

## Statement-integrity audit

- Paper assumptions: admissible parameters, positive test error, and a
  projective Pauli strategy of value at least one minus that error.
- Lean assumptions: unchanged `AdmissibleParams`, positive error, and
  `ProjectiveSetting`; no new premise.
- Paper conclusion: universal a > 1 and 0 < b < 1, and projective polynomial
  pair measurements on each expanded local space, with both point-consistency
  displays for every Pauli basis and the stated deltaQld error.
- Lean conclusion: unchanged `GlobalPairWitness` with the same constants,
  domain, quantifier order, and four consistency requirements.
- Verdict: statement preserved; proof remains incomplete. The compatibility
  theorem tests an existing auxiliary and is not substituted for the target.

## Cumulative costs and checkpoint

This is `prover-513-20260912-03`, dispatched at 07:30:41Z. The third-attempt
instruction has a 25-active-minute bound, superseding the embedded
60-minute text; no new scope was started after 08:00Z.

The three #119 prover receipts total 1927 session-seconds. Attempt one adds
3602, and attempt two adds 2001, for 7530 recorded predecessor session-seconds.
These are summed session spans, not measured active proof time. The two
#119 scout spans retain their unknown attribution and are not added.

Known additive predecessor usage remains 31,555,490 input, 30,806,016 cached
input, and 87,658 output tokens, including 28,404 reasoning tokens. Attempt
two's receipt has `usage: null` and `usage_scope: unknown`; its tokens are
unknown, not zero. Cached input is part of input; reasoning is part of output.
The current attempt's final usage belongs to its dispatcher receipt.

The closed #278 issue also preserves the parent B8 history of twelve
math-fix attempts and 24242 seconds. This broader episode is not reset;
it is not added to the narrower totals without an attribution check.
The next mathematical gate is the missing source-derived operator estimates,
followed by absorption of the actual composed error.
