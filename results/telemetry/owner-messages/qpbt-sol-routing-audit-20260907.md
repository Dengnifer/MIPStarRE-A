# Historical Sol Routing Audit

September 7, 2026. Read-only initial pass by Astra, thread
`01a07bd1-9344-7d93-b71e-fd5881bd8ac9`, under root
`01a076bc-f4ad-7813-805b-c8b4dac71a14`. Committed evidence is pinned at
`5924b3acec0d1ad5fe38b8a93ac5e950e2daa071`; GitHub evidence was read through
the primary `local/bin/gh_common.py`. The companion machine-readable report is
`/tmp/qpbt-sol-routing-matrix-20260907.json`.

## Decision

One narrow execution class has sufficient historical support to recommend
**conditional future qualification**, not activation: a prover acting as an
autofixer applies an externally adjudicated, exact nonsemantic replacement
specification to existing prose or declaration names and the named callers.
The two independently accepted examples are C01 and C02 below. This does not
authorize discovering mathematical corrections, deciding source scope, editing
proofs, changing completion tags, or general cleanup. Both underlying proof
developments are excluded from the Sol credit assigned to those fixes.

All actual routing remains Astra. Main must first consume the separately
assigned independent validation of these two cases and pass the proposed
policy change through normal review. Unknown classes fail closed to Astra.
No model, effort, account, lease, prompt, allowlist, source, telemetry, or
enforcement file was changed by this audit; only these two requested outputs
were written. No new Sol probe, launch, model alias, or effort downgrade ran.

## Method And Coverage

The committed registry has 947 raw rows, 928 distinct names and 770 nonempty
thread identities. The first-60-event identity inventory identifies 542 rows
whose initial rollout model is exactly `gpt-5.6-sol`: 538 names, 444 threads.
Their raw role counts are blueprint 2, orc 49, prover 135, reviewer 340, scout
13 and splitter 3. These are metadata counts, not 542 validated outcomes.
Fifty-one rows have unresolved model identity and are not attributed by time.
`gpt-6-sol`, `gpt-5.6-luna` and `gpt-5` are not aliases of the audited model;
in particular the invalid `gpt-6-sol` failure is not a Sol capability sample.

The bounded case matrix contains 22 selected Sol tasks across the six roles,
including prover-as-autofixer work. All model-bearing turn contexts in those
selected threads were inspected, as were selected independent Astra reviewer
and repair threads. The matrix gives each pinned registry line, session name,
context lines, actual artifact, acceptance head, review ID and rework limit.
The registry's `rollout` field resolves the exact local model-evidence path.
The selected contexts record `ultra`, except the sampler-cleanup and two
scouting cases, which record `high`. These are recorded requests/context
settings, not provider-measured effort or proof of future compatibility.

The existing `model-comparison/latest.md` is not a routing qualification:
its older 622-row report mixed rollout evidence, 38 time-rule assignments and
one lane-log assignment; its outcome join was by branch, not by authored
artifact and accepted head. Its 362-reviewer Sol approval statistics do not
measure reviewer recall. We did not execute `compare.py`, which writes files
and uses a direct GitHub path outside the required wrapper.

This is purposive sampling, not a controlled experiment. Early Sol handled
the general workload; later Sol assignments were deliberately selected as
easy. Cache warmth, shared build queues, changing APIs, review iterations,
missing archives, inherited proof holes and model/effort transitions confound
time or token comparisons. Resumed tasks, duplicate rows, multiple labels for
one thread, paired reviewers, and carried reviews are not independent cases.
The opportunity denominator for each job class, reviewer false-negative
denominator, and complete subsequent-rework denominator remain unavailable.
No statistical reliability, global success rate, speed advantage or model
ranking is claimed.

## Two Supported Cases

**C01, exact reviewer-directed prose substitutions, PR229.** Sol task
`prover-pr229-20260906-02`, registry line 607, thread
`01a07298-5b8a-75b2-bd7e-54b4b4c15cb4`, has `gpt-5.6-sol`/`ultra` in rollout
turn context line 8. Its committed last-message artifact identifies the two
requested wording fixes. Autofix commit
`6e754fc61c33e4013f7a8c246fa807c55eb48091` changes six comment lines in each
direction across two files, with no proof or statement edit. The requested
wording is [review 5122160565](https://github.com/Dengnifer/MIPStarRE-A/pull/229#pullrequestreview-5122160565).
Exact-head CI succeeded at 17:38:49Z on September 5; independent, rollout-
verified Astra prose reviewer `reviewer-pr229-20260906-06` accepted that exact
head in [review 5122284090](https://github.com/Dengnifer/MIPStarRE-A/pull/229#pullrequestreview-5122284090).
Both authored files are byte-identical at final accepted head `5dadb158...`.
The code-review lane's model is unknown; it is not silently counted as Astra.
The low-degree transport mathematics beneath these comments is not credited
to this Sol task.

**C02, exact requested names and caller substitutions, PR185.** Sol task
`prover-pr185-20260906-02`, registry line 617, thread
`01a07298-5d85-7711-8e5a-6687173d1aad`, records Sol/`ultra` in both turn
contexts, lines 8 and 428. [Review 5122171686](https://github.com/Dengnifer/MIPStarRE-A/pull/185#pullrequestreview-5122171686)
supplies the exact snake_case names. Commit
`d82bc5a65b70d6f5eee156ee909faa0fd436ef19` implements two declaration renames
and two caller updates in `LowDegree.lean`. Exact-head CI succeeded at
18:17:39Z; rollout-verified Astra code reviewer `reviewer-pr185-20260906-03`
accepted it in [review 5122448776](https://github.com/Dengnifer/MIPStarRE-A/pull/185#pullrequestreview-5122448776),
explicitly disposing of the naming finding. That Lean file is byte-identical
at final accepted head `a6db27da...`. Nine pre-existing companion holes remain
disclosed. The same commit also adds 38 blueprint lines: **those mathematical
scope/completion decisions and the underlying seven winning proofs are not
part of the proposed Sol qualification**.

These are two distinct accepted execution examples, not two general proof
successes. Their common narrow operation is applying an already-decided
replacement specification. A new inference about terminology, theorem scope
or a citation is outside that operation and must escalate.

## Counterevidence And Limits

- **C03, mathematical prose is not mechanical text.** Sol autofix
  `60f0af95...` on PR153 corrected requested ceiling/note issues and passed
  exact CI, but independent Astra [review 5121978192](https://github.com/Dengnifer/MIPStarRE-A/pull/153#pullrequestreview-5121978192)
  found a natural/base-two logarithm discrepancy. A later `87beb8fe...`
  repair was needed before acceptance. It is not credited to that Sol task;
  this pass did not establish the later fixer's model. This is additional
  semantic rework, not a claim that every originally requested fix failed.
- **C13, a source/status audit failed its own completion claim.** Sol's
  `11415a87...` paper-gap audit reported no unsupported blueprint claim
  remaining. PR184 [review 5114612823](https://github.com/Dengnifer/MIPStarRE-A/pull/184#pullrequestreview-5114612823)
  found a paper-labelled attainment statement replaced/certified by a
  given-strategy helper, plus incorrect status reports. Multiple repairs
  followed. At final head `7316ed0d...`, CI was green but the review summary
  still failed with eight unresolved findings. The later merge is not a
  clean independent-acceptance example.
- **C09, bulk citation rewriting introduced semantic mistakes.** Sol's
  PR202 head `02f7b876...` passed CI, but [review 5117661430](https://github.com/Dengnifer/MIPStarRE-A/pull/202#pullrequestreview-5117661430)
  found nine issues, including sole-nearby-label precedence over the exact
  locator, missed unknown labels and wrong theorem citations. `d7d73137...`
  repairs the reported areas. Further Astra fixes and a separate Astra
  terminal review were needed later; the final repaired migration is not
  credited solely to the initial Sol author.
- **C10/C11, useful reviewers but no blanket review qualification.** The
  PR202 findings led to concrete fixes. Sol's PR227 finding that a regression
  subprocess inherited the production review kill switch led to exactly the
  fixture-only change in `35f54095...`; exact CI and independent Astra
  [review 5121986321](https://github.com/Dengnifer/MIPStarRE-A/pull/227#pullrequestreview-5121986321)
  accepted the fix. These demonstrate actionable findings, not recall of
  all mathematical, security or runtime defects. C12's Sol approval on PR228
  has no independent review-accuracy audit; carried approvals add no evidence.
- **C04/C06, preserve the acceptance distinction.** The six-file helper
  consolidation `2c033acc...` has successful exact CI and independent Sol
  review on `453498f4...`, later carried through merges. This is one accepted
  authoring example, not several. Sampler cleanup `71f37684...` has a local
  artifact and self-check report, but no published GitHub commit or
  independent acceptance found. It cannot serve as a second accepted case.
- **C07/C08 are positive counterevidence to a blanket inability claim.**
  Decoder and Pauli/cancellation tasks produced nontrivial proof artifacts
  `79093740...` and `67f77e48...`, with explicit source-boundary/debt reports.
  Their complete independent exact-head acceptance chains were not traced in
  this bounded pass. This limits qualification; it is not evidence that Sol
  cannot prove mathematics.
- **C14-C17, reports and inventories are not automatically validated.** Two
  splitter threads created concrete issue inventories and two scout threads
  produced detailed source/API maps. The exact archived outputs exist, but
  independent completeness/source-correctness acceptance was not established.
  Created issue counts, plausible lemma lists and exit 0 are insufficient.
- **C18/C19, only one fully accepted merge-recovery sample.** Sol's
  `227bc711...` recovery on PR236 has green exact CI and independent Astra
  [review 5123077698](https://github.com/Dengnifer/MIPStarRE-A/pull/236#pullrequestreview-5123077698),
  checking raw multiplicities and all incoming paths. Sol's PR205 recovery
  `a711fec0...` has no exact-head statuses. Later Astra refresh `71bedebd...`
  has its own acceptance; that evidence cannot be transferred backward.
- **C20/C21/C22, keep authorship and privilege separate.** Sol implemented
  PR238's initial `954c1bc0...`, accepted by Astra with exact CI. Later Astra
  changes added `codex-policy-shim.sh` and continuation/budget logic and
  generated new findings; these must not be charged wholesale to Sol, nor
  may Sol be credited with those final repairs. The PR233 source merge
  preceded the selected Sol deployment task entirely. Sol's earlier PR205
  partial contract/commutator work explicitly left the pasting construction
  open; later Astra mathfix work is separately identified in the matrix.

## Routing Boundaries

| Role and Job Class | Initial Decision |
| --- | --- |
| Prover-as-autofixer: externally specified nonsemantic substitutions | Supported bounded candidate, C01/C02; inactive pending validation/policy review |
| Prover: new proofs, generalized helpers, shared mathematical contracts | Astra; insufficient same-class independent acceptance and higher risk |
| Blueprint: source comparison, error exposition, citation inference, completion/scope tags | Astra; concrete semantic/status counterexamples |
| Reviewer: authoritative mathematical/security/runtime verdict | Astra; no measured review recall or independent validation of approvals |
| Reviewer/scout: deterministic advisory findings | Useful examples, but provisional; not a replacement for the required reviewer |
| Scout/splitter: source/API maps, proof decomposition, issue dependencies | Astra until independently accepted same-class examples are established |
| Orc: telemetry-only guarded merge recovery | Provisional, one fully accepted exact-head case |
| Orc/prover/reviewer: runtime/security controls and protective tests | Astra regardless of isolated successes; high privilege |
| Mathfix/frontier/adjudication or unknown scope | Astra; no qualifying Sol mathfix cohort |

The candidate class needs a dispatcher-owned exact file/replacement allowlist,
statement/proof equality modulo the approved names/comments, caller checks,
unchanged explicit proof debt, exact-head CI, independent Astra review and
the normal merge gate. The worker must not self-classify or enlarge scope.
Ambiguous meaning, source interpretation, additional code edits, any substantive
finding or integrity failure transfers the task to Astra without budget reset.

Runtime effort compatibility belongs to main/meta's documented verification.
The inspected enforcement note correctly distinguishes catalog configuration
from provider/task evidence. Historical Sol `ultra` or `high` labels do not
authorize a new effort choice, downgrade or alias. Incompatibility means no
Sol dispatch and retention of Astra. Main stays Astra/`ultra`; relay-3 only,
11 total slots, nine native descendants and zero external admission remain
unchanged. B8 remains at 13 attempts and 26,509 working seconds.

## Independent Validation

Root separately assigned Astra validator `/root/relay3_honest_recovery`,
thread `01a07aef-fef3-7a10-ba1c-55acdfa4f1ff`, to C01/C02 only. Its report is
`/tmp/qpbt-sol-routing-audit-validation-20260907.md`. The completed independent
report was read before final handoff and supports only the two narrow
components. Main must consume both
reports and the normally reviewed policy change before any class activation.
This audit does not write or authorize enforcement code.

The validator's concluding findings were received before handoff: actual Sol
tool-call patches, exact artifacts, CI, separate Astra acceptance and unchanged
authored Lean paths support the narrow C01/C02 components. Important limits
are explicit in the matrix:
PR185's entire commit is not nonsemantic and included within-rollout blueprint
rework, followed by 25 additions/14 deletions in the blueprint before its final
head (first-parent change `769f1c447011fafdb77f3ed295c66122ce88305c`);
the PR229 code-review lane remains model-unknown; historical
statement-origin statuses were skipped-success, not executed source audits.
No proof, blueprint-scope, API-design, security or runtime decision is qualified
by these samples. The routing activation flag remains false.
