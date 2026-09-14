# Independent validation of two historical Sol edits

Date: 2026-09-07. Read-only validation began at 14:12:45Z; findings recorded
at approximately 14:28Z. Validator: `/root/relay3_honest_recovery`, native UUID
`01a07aef-fef3-7a10-ba1c-55acdfa4f1ff`, Astra Ultra, relay-3. This is an
independent historical evidence check, not a canonical PR review, policy
approval, model-capability benchmark, or routing activation.

## Verdict

| Claim | Verdict | Boundary |
| --- | --- | --- |
| PR229: Sol made the reviewer-prescribed nonsemantic terminology corrections | Supported | The two-file artifact changes comments/docstrings only. |
| PR185: Sol made two reviewer-prescribed identifier renames and their two caller updates | Supported | This credits only the four Lean line replacements, not the rest of the commit. |
| The entire PR185 Sol artifact was nonsemantic | Unsupported | It also adds 38 blueprint lines making mathematical scope, dependency, and proof-status decisions. |
| Both narrow edits passed exact-head CI and relevant independent Astra review | Supported | Astra prose review for PR229; Astra code review for PR185. PR229's code review model is unknown. |
| The qualified Lean edits required subsequent changes before the final PR heads | Not observed | The relevant file diffs are empty and their first-parent path logs contain no later changes. This is not a claim about the entire PRs. |
| These two cases establish reliable broader Sol proof, statement, blueprint, runtime, or security-control work | Insufficient | No such qualification follows from these narrow examples. |

The defensible common class is an exact, independently prescribed textual
correction whose nonsemantic boundary can be checked. Identifier changes are
nonsemantic with respect to the mathematical statement/proof here, but are
still public API changes: this evidence does not qualify independent naming
design, arbitrary API changes, or incomplete caller migrations.

## Evidence Basis

The primary auditor supplied precise source paths and claims. I independently
read the actual Git artifacts, committed session receipts, actual rollout
metadata and patch tool calls, and targeted GitHub reviews/statuses through
`local/bin/gh_common.py`. I did not infer model identity from role labels,
bot commit authorship, missing registry fields, or default-model assumptions.

Committed receipt/registry inspection used audit pin
`5924b3acec0d1ad5fe38b8a93ac5e950e2daa071`. Relevant registry entries have
missing model/effort fields; attribution instead comes from the actual
`session_meta` and `turn_context` records below. Runtime observations establish
the recorded effective model and CLI effort, not provider-measured internal
reasoning. Rollout filenames use local time; all explicit times below are UTC.

The dispatch and enforcement notes were read:
`/tmp/qpbt-sol-routing-audit-dispatch-20260907.json` and
`/tmp/qpbt-sol-routing-enforcement-20260907.md`. Their runtime catalog evidence
is not used as task-capability evidence. No new Sol session was launched.

## PR229: Prescribed Terminology

- Base: `af97ea9171beb99a47f2594495e37be353056a71`.
- Sol artifact: `6e754fc61c33e4013f7a8c246fa807c55eb48091`.
- Exact prior review: `5122160565`, 2026-09-05T17:09:51Z, on the base above.
  F1 prescribes replacing "mature error" with the error bound of the low
  individual degree theorem; F2 prescribes Hilbert-space wording in place of
  the carrier terminology.
- Complete artifact: two files, six insertions and six deletions, all within
  comments/docstrings in `MIPStarRE/QPBT/Combining/DirectLowDegree/Soundness.lean`
  and `MIPStarRE/QPBT/Combining/DirectLowDegree/SeedIndexedSoundness.lean`.
  The replacements match the review's terminology. No declaration, theorem
  assumption, proof, or executable Lean content changes in this diff.

Sol provenance is `prover-pr229-20260906-02`, UUID
`01a07298-5b8a-75b2-bd7e-54b4b4c15cb4`. Actual rollout:
`/home/drx/.codex/sessions/2026/09/06/rollout-2026-09-06T01-23-02-01a07298-5b8a-75b2-bd7e-54b4b4c15cb4.jsonl`.
Its session metadata at 17:23:02.802Z identifies this UUID, the issue-135
worktree, and base `af97ea9`. Its turn context at 17:23:02.836Z records
`gpt-5.6-sol`, effort `ultra`. The actual `exec` custom tool call at
17:25:21.017Z invokes `tools.apply_patch` with the two-file terminology patch.
The committed session receipt is
`results/telemetry/sessions/prover-pr229-20260906-02.last.md`; registry line 607
at the audit pin matches this UUID/rollout. The artifact commit timestamp,
17:32:41Z, matches the registry session end. Author-reported tests are not
substituted for the independent CI evidence.

At exact head `6e754fc`:

- `local-ci/summary`: success, 17:38:49Z, recorded duration 144 seconds.
  Build, blueprint render, paper gaps, blueprint sync, file length, proof debt,
  and proof evasion report success. Statement-origin reports success with an
  explicit no-relevant-LDT/scripts/workflow-change skip; it was not an executed
  source-faithfulness audit for this patch.
- Review `5122284090`: submitted 17:42:07Z, exact-head project verdict
  APPROVED, code/prose APPROVED, no findings. Its prose explicitly accepts the
  two corrected terminology findings. `local-review/summary` succeeds at
  17:42:09Z with zero unresolved findings.

The independently verified Astra reviewer is the prose reviewer,
`reviewer-pr229-20260906-06`, UUID
`01a072a6-ed02-7f20-8008-ca9701c649ff`, with rollout
`/home/drx/.codex/sessions/2026/09/06/rollout-2026-09-06T01-38-57-01a072a6-ed02-7f20-8008-ca9701c649ff.jsonl`.
Session metadata at 17:38:57.606Z binds this separate reviewer to head
`6e754fc`; turn context at 17:38:57.647Z records `gpt-6-astra`, `ultra`.
`results/telemetry/sessions/reviewer-pr229-20260906-06.last.md` verifies that
head and the patch, and accepts the final wording changes. The code reviewer
`reviewer-pr229-20260906-05` has no rollout/model attribution in the inspected
registry; its Astra identity is **unknown**, not inferred.

Final PR head: `5dadb158d7130b580ab58523259914328ba4adc4`.
GitHub records merge `3f00de0ca3a527bff1c7ebe1f9ae4df128b30b2b` at
2026-09-05T17:59:57Z. The artifact-to-final diff over both Sol-edited files is
empty; their first-parent path log over that interval is empty. This supports
retention of these wording changes, not Sol authorship of the underlying
transport proofs or absence of unrelated PR work.

## PR185: Prescribed Renames, Not Blueprint Decisions

- Base: `6dd979e64927e916b22598f95905e321cc2da8b1`.
- Sol artifact: `d82bc5a65b70d6f5eee156ee909faa0fd436ef19`.
- Exact prior review: `5122171686`, 2026-09-05T17:11:15Z, on this base.
  Code F1 prescribes the exact names `aline_winning_condition` and
  `dline_winning_condition` in place of `alineWinningCondition` and
  `dlineWinningCondition`, together with their callers; statements need not
  change. The separate prose request concerns a scoped blueprint entry.
- The qualified portion in
  `MIPStarRE/QPBT/Observables/WinImplications/LowDegree.lean` is precisely two
  declaration renames and two corresponding caller replacements: four old/new
  line pairs. Types, hypotheses, conclusions, and proof content are otherwise
  retained.
- The full commit is two files, 42 insertions and four deletions. The other
  38 inserted lines in `blueprint/src/chapter/ch14_qpbt_observables.tex` add a
  scoped mathematical lemma, select seven completed conclusions, describe its
  proof/dependencies, and assign Lean completion tags. Those decisions are
  **excluded**, including any claim that Sol established the scope or proof
  status of the paper-facing result.

Sol provenance is `prover-pr185-20260906-02`, UUID
`01a07298-5d85-7711-8e5a-6687173d1aad`. Actual rollout:
`/home/drx/.codex/sessions/2026/09/06/rollout-2026-09-06T01-23-03-01a07298-5d85-7711-8e5a-6687173d1aad.jsonl`.
Session metadata at 17:23:03.291Z binds that UUID to the issue-112 worktree and
base `6dd979e`. Both turn contexts, 17:23:03.330Z and 17:39:23.734Z, record
`gpt-5.6-sol`, `ultra`. The actual `exec`/`tools.apply_patch` call at
17:32:57.365Z contains the four Lean substitutions and initial blueprint
addition. Further patch calls at 17:36:28.110Z, 17:39:42.186Z, and
17:40:24.026Z revise blueprint proof/dependencies/formatting. These are direct
authorship evidence, but also demonstrate that the historical job as a whole
was not confined to the proposed nonsemantic class.

Registry line 617 and
`results/telemetry/sessions/prover-pr185-20260906-02.last.md` match the source
session. The artifact commit timestamp and registry end agree at 17:45:31Z.

At exact head `d82bc5a`:

- `local-ci/summary`: success, 18:17:39Z, duration 153 seconds. The same seven
  active checks listed for PR229 succeed; statement-origin again succeeds by
  an explicit no-relevant-change skip, not an executed source-origin audit.
- Review `5122448776`: submitted 18:20:48Z, exact-head project verdict
  APPROVED, code/prose APPROVED, no findings. The code review explicitly says
  the naming finding is resolved and nine existing companion/observable holes
  remain. `local-review/summary` succeeds at 18:20:50Z, zero unresolved.

The independently verified Astra code reviewer is
`reviewer-pr185-20260906-03`, UUID
`01a072ca-74f9-73f2-b372-c19033bd66be`, with actual rollout
`/home/drx/.codex/sessions/2026/09/06/rollout-2026-09-06T02-17-45-01a072ca-74f9-73f2-b372-c19033bd66be.jsonl`.
Session metadata at 18:17:46.168Z binds this separate reviewer to `d82bc5a`;
turn context at 18:17:46.201Z records `gpt-6-astra`, `ultra`.
`results/telemetry/sessions/reviewer-pr185-20260906-03.last.md` confirms the
exact patch, resolved naming finding, and retained existing holes. Review of
the seven underlying winning-implication proofs does not transfer authorship
or capability credit for those proofs to this Sol edit.

Final PR head: `a6db27dad36863fde66394b3579070ae09d7f3c2`.
GitHub records merge `696af829056ede3b1b63b8b42e2cec143c47464d` at
2026-09-05T19:23:18Z. The artifact-to-final `LowDegree.lean` diff and its
first-parent path log are empty. In contrast, the blueprint has a later
25-insertion/14-deletion diff, with first-parent change
`769f1c447011fafdb77f3ed295c66122ce88305c` (`fix(QPBT): reconcile main APIs
with exact-winning proofs`). That later blueprint's mathematical content was
not independently audited here, because it is outside the qualified class.
No no-rework claim is made for the whole commit or blueprint.

## Limits and Disposition

The cited GitHub reviews are native state `COMMENTED` with the project's
exact-head APPROVED marker/body and successful local-review status, not native
GitHub `APPROVED` review-state claims. Separate UUIDs, artifact-pinned reviewer
metadata, and actual review receipts support independence for the relevant
prose/code checks; no undocumented model attribution is supplied.

Two selected successful historical examples do not establish a long-run
success rate, failure frequency, cost advantage, comparative latency, or
robustness under different prompts. They do not establish qualification for
new mathematical explanations, theorem statements, proof repair, proof-status
tags, source-faithfulness judgments, security/lease/auth/model-policy edits,
runtime behavior, CI/review gate design, or autonomous task selection.

Routing remains inactive pending the final audit matrix, reviewed enforcement,
and the coordinator's normal activation gates. No policy, credential, source,
worktree, GitHub object, primary telemetry, or goal status was changed by this
validation. Only this requested `/tmp` report was written. No workers were
spawned or interrupted. Relay-3/Astra Ultra, native cap nine, total eleven,
external admission zero, and preserved B8 totals of 13 attempts / 26509 working
seconds remain unchanged. All audit read commands were terminal at reporting.
