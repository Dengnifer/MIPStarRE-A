# Protocol evolution ledger

Dated amendments to the protocols in this directory (and to `AGENTS.md`).
Every entry cites its trigger per `meta.md`. Newest last.

## 2026-08-30 — Founding: localization of the parent GitHub workflow

**Trigger:** project start (user directive): continue the self-evolved
workflow of LionSR/MIPStarRE with all GitHub operations replaced by local
ones; record telemetry for a research paper.

**Change:** created `local/` (DESIGN.md, protocols/, personas/, bin/),
`issues/`, `prs/`, `results/telemetry/`. `.github/` frozen as reference.
Initial protocols derived from a 7-reader study of the parent snapshot
(507e81220); the parent's post-mortem comments were ported as invariants
(single cache writer, review-after-green-CI, fix serialization + combined
iteration cap, trusted prompts, untrusted-data framing, bracket-free naming).

**Expected effect:** parity with the parent workflow's guard set from day one,
minus GitHub event plumbing, which becomes explicit script invocation.

## 2026-08-30 — Worktree bootstrap resets vendored packages

**Trigger:** events.md 2026-08-30 "Dirty vendored package blocks
`lake exe cache get`" (first build attempt failed).

**Change:** `worktree-setup.sh` resets dirty vendored package git trees
before `lake exe cache get`; the ProofWidgets fresh-state workaround from
docgen.yml:56-64 is kept alongside it.

**Expected effect:** cache fetch never aborts on inherited package dirt.

## 2026-08-30 — Fan-in data passed by path, not inline

**Trigger:** events.md 2026-08-30 "Workflow critic stalled on oversized
prompt" (study-fleet critic failure).

**Change:** orchestration rule in `sessions.md` scope: synthesis/critic
agents receive large upstream results as file paths to read, with inline
context capped; adopted for all future fan-in stages.

**Expected effect:** no stalled synthesis agents; reproducible fan-in cost.

## 2026-08-30 — Post-verification repair of drafted guards

**Trigger:** the founding verification pass (Fable verifier over the 7-builder
draft) live-demonstrated four defects and several dangling references; full
report archived in the session telemetry for 2026-08-30.

**Change:**
- `pr_merge.py`: review-verdict glob fixed to the `<sha>-*.md` files
  `review.sh` actually writes (the gate could never accept a reviewed PR);
  dead `fixes/pending` probe removed; fix-quiescence gate now probes the same
  mkdir lock `autofix.sh` holds (`locks/fix-<branch>.lock`, pid-liveness);
  cap env unified to `MIPSTARRE_FIX_CAP`.
- `autofix.sh`: releases its fix lock before the cap-time forced review
  (`review.sh` refuses to review under a live fix lock, so the terminal
  bot-fix commit was never reviewed).
- Machine-wide full-build mutex unified to `$CACHE_ROOT/.full-build-lock`
  across `cache-warmer.sh`, `warm-worktree.sh`, `ci.sh`, and the linter sweep
  (three uncoordinated locks before); `ci.sh` stale-break made
  liveness-first — a live owner is never broken by age (the initial build ran
  ~7 h against a 3 h age threshold).
- `MIPSTARRE_CACHE_DIR` → `MIPSTARRE_CACHE_ROOT` everywhere; octal-safe id
  parsing (`10#`) in `review.sh`/`autofix.sh`/`agent.sh` (ids 0008/0009
  crashed); `dispatch.sh` maps role `orc` → `orchestrator.md`; verdict files
  written atomically; template/persona citations no longer point at
  files that do not exist.

**Expected effect:** the merge gate accepts exactly the reviewed-and-green
PRs it was specified to accept; every full build contends on one mutex.

**Outcome (same day):** post-fix smoke reruns pass (see events.md).

## 2026-08-30 — Warmer seeds its first build from the primary checkout

**Trigger:** first live run of `cache-warmer.sh`: it cloned the primary repo
into `hot-main/repo` and was about to recompile ~9000 modules from source,
although the primary checkout already held a complete built `.lake` for the
same keyhash (events.md, "first warmer run").

**Change:** `cache-warmer.sh` gains `seed_hot_repo_lake`: when the hot
checkout lacks `.lake/build` and the primary checkout has one under the same
keyhash, `.lake/build` (and `.lake/packages` if absent) are cloned
copy-on-write before `lake exe cache get`/`lake build` — the local analogue
of the parent CI's restore-by-key-prefix (pr-ci.yml:144-160); the subsequent
`lake build` reduces to a trace check.

**Expected effect:** the initial warm costs minutes, not a duplicate
multi-hour compile; same mechanism covers re-seeding after a cache wipe.

## 2026-08-30 — Whitespace gate exempts byte-faithful paper mirrors

**Trigger:** the stage-2 commit of `references/qpbt-paper/` and
`references/neexp-paper/` was rejected by the pre-commit whitespace check:
the arXiv sources carry trailing whitespace and blank lines at EOF, and
normalizing them would break the mirrors' byte-identity claim (their whole
point). The LDT-era mirror never collided with the gate because it was
imported already-clean.

**Change:** `.githooks/pre-commit` runs `git diff --cached --check` with
`':(exclude)references/'`. Project prose and code keep the gate; verbatim
external sources do not.

**Expected effect:** mirrors commit unmodified; the fidelity claim in each
mirror README stays checkable forever.

## 2026-08-30 — Registry root resolves to the primary checkout

**Trigger:** running `ci.sh` from inside a PR worktree wrote the CI manifest
and `pr.md` updates to the worktree's own copy of `prs/` — a forked registry
(events.md would call this a split-brain record; caught during the stage-3
blueprint PR).

**Change:** `ci.sh`, `review.sh`, `autofix.sh`, `agent.sh` re-point their
repo root at the primary checkout via `git rev-parse --git-common-dir`
(same resolution `cache-warmer.sh` and `telemetry.py` already used), so the
registry stays single-instance regardless of the invocation directory.

**Expected effect:** identical registry writes from any worktree; no forked
issue/PR records.

## 2026-08-30 — Paper-gap bibliography entries cite repository paths

**Trigger:** review round 4 of PR #0001 flagged the new `gap:` bibliography
entries for using repository paths where the parent policy expects published
site URLs.

**Change:** localized convention — with no public site, `gap:` entries'
`note` fields carry the in-repository note path (`docs/paper-gaps/…`);
`local/bin/site.sh` serves rendered notes locally. Recorded as a comment at
the entries in `blueprint/src/references.bib`.

**Expected effect:** reviewers and tooling treat repo-path citations as the
sanctioned local form; no dangling public URLs.

## 2026-08-30 — Review round cap with operator adjudication

**Trigger:** events.md, "Review loop non-convergent at the tail (PR #0001)":
five review rounds with finding counts 33, 26, 18, 12, 17 — the tail
oscillates because each round's fresh reviewer re-audits new text at
unbounded depth and cannot see prior adjudications.

**Change:** `local/protocols/review.md` gains: after **four** full review
rounds on one PR, the operator may adjudicate the remaining findings
instead of iterating — each remaining finding is either fixed, or ticked
in the current ledger with a written reason and converted to a tracked
issue; the merge may then proceed with `review_state: ADJUDICATED`
recorded in `pr.md` and the merge commit citing the adjudication. The
analogous parent mechanism is the combined bot-fix iteration cap with one
terminal review (pr-review.yml:69-72): iteration is bounded, the tail is
a human decision, and nothing is silently dropped — every unfixed finding
becomes an issue.

**Expected effect:** review loops terminate with an explicit, auditable
decision; stage-appropriate depth disputes move into the tracker instead
of blocking scaffolding merges indefinitely.

## 2026-08-31 — Merges auto-resolve registry-path conflicts with the base

**Trigger:** PR #0001's merge aborted twice on conflicts confined to
registry files (`prs/…/pr.md`, telemetry session captures) that the branch
had accumulated from earlier mis-rooted tool runs; aligning the branch's
registry to main went stale within minutes because `pr.md` mutates on main
continuously.

**Change:** `pr_merge.py` completes a conflicted merge automatically when
every conflicted path lies under `issues/`, `prs/`, or `results/telemetry/`,
resolving those paths with the base's version — correct by the
single-instance-registry protocol. Conflicts touching any other path still
abort untouched.

**Expected effect:** registry residue on branches can never block or
corrupt a merge; content conflicts remain a human decision.

## 2026-08-31 — Review lanes run in parallel

**Trigger:** stage-3 telemetry: ~30 h of PR #0001's wall time was the
review-fix loop, and each round ran the code and prose lanes sequentially
although they are independent per head SHA.

**Change:** `review.sh` dispatches the code and prose reviewer sessions
concurrently and parses sequentially. Failure semantics unchanged: a
code-lane crash blocks the PR (and reaps the still-running prose lane);
a prose-lane failure only warns. The parent ran the two as separate
parallel CI jobs (pr-review.yml), so this restores parent-level
concurrency the local port had serialized.

**Expected effect:** review wall time per round approximately halves.

## 2026-08-31 — Migration to ghz; main session handed to codex; GitHub mirror

**Trigger:** user directive: migrate the project to ghz:/home/drx/MIPStarRE-qpbt,
hand the orchestrating main-session role to a codex session there (GPT
models in place of Claude models), and mirror the repository to the private
GitHub monorepo Dengnifer/MIPStarRE-qpbt as the MIPStarRE-A/ subtree.

**Change:**
- `local/personas/main.md`: the main-session persona (operator role,
  operating loop, standing duties) — model-agnostic by construction.
- `HANDOFF.md`: state snapshot and immediate next steps at handoff.
- `local/bin/main-session.sh`: starts/resumes the interactive codex main
  session anchored at the repository root.
- `local/bin/github-sync.sh`: git-subtree mirror of main to GitHub
  (repo-scoped deploy key; full history under MIPStarRE-A/). The mirror is
  a surface only: issues, PRs, CI, reviews, and the registry remain local
  and authoritative; run the sync after each merge to main.
- macOS-only operational bits (caffeinate wake assertions) retire; the
  server does not sleep.

**Expected effect:** identical workflow semantics on the new host; the
model-family switch of the operator is a recorded telemetry datum, not a
protocol change.

## 2026-08-31 — Re-hybridization: GitHub-native issues/PRs for track A

**Trigger:** owner decision after the repository restructure (standalone
`Dengnifer/MIPStarRE-A` with its own PR space; umbrella
`MIPStarRE-qpbt` aggregates A and B as submodules). The founding
localization replaced GitHub because it was unavailable as a surface;
with it restored, the owner chose GitHub-native records.

**Change:** issues/PRs move to GitHub (seed migration:
`results/telemetry/github-migration-map.md`); CI and reviews continue to
EXECUTE locally and will post statuses/verdicts to the PR once the
tooling adaptation (HANDOFF.md step 0, owned by the incoming main
session) lands; `github-sync.sh` becomes a plain retry-hardened push;
the local registry becomes a write-through offline fallback,
authoritative in conflicts until the adaptation completes.

**Expected effect:** familiar review surfaces and separate per-track PR
management, at the cost of link-dependence for record operations — an
accepted trade recorded as a workflow-evolution datum: localization and
re-hybridization are both responses to the environment, which is the
paper's thesis in miniature.

## 2026-08-31 — GitHub is the sole active workflow authority

**Trigger:** owner decision 2026-08-31, follow-on to the re-hybridization entry;
see `results/telemetry/events.md`, "Write-through adapter superseded during
implementation."

**Change:** the write-through fallback is retired. GitHub numbers, labels,
sub-issue relations, pull-request metadata, exact-head statuses, reviews, and
merge state are the only active lifecycle records. Local execution retains
runtime locks/logs and append-only research telemetry. The former issue/PR
trees remain immutable under `results/telemetry/registry-archive/`; atomic
GitHub snapshots are audit data and never mutation authority.

All lifecycle commands use one retry-classifying, marker-idempotent shared
GitHub layer. CI and review publish exact-head evidence, auto-fix counts complete
GitHub-visible commit history, and merge uses a final head recheck plus
`--match-head-commit`. A clean exact-head `COMMENT` review with a clean ledger
and successful summary is sufficient; GitHub approval is not a gate.

**Expected effect:** remote outages fail closed without creating shadow state,
ambiguous mutations reconcile against GitHub, and every lifecycle consumer
observes one authoritative issue/PR history.

## 2026-09-01 — Merge evidence is one full-SHA run contract

**Trigger:** the issue 0007 post-audit incident recorded in
`results/telemetry/events.md`, "Post-audit merge evidence admitted incomplete
bindings," together with the owner's decision that independent clean review is
published as a GitHub `COMMENT` and never requires approval or
`reviewDecision`.

**Change:** CI manifests and statuses bind one run to the full PR head and base.
Review attestations additionally bind the canonical body digest, findings,
event, and two successful distinct dispatcher sessions with matching completion
telemetry. A clean attestation uses `COMMENT` with no fallback. The merge gate
holds the review lock, reserves the fix lock, and applies the same strict
evaluator before preparation and immediately before guarded merge. Idempotent
POST/PATCH operations make at most one mutation attempt and reconcile ambiguous
results only by authoritative read-back.

**Expected effect:** stale bases, mixed runs, reused or failed reviewer sessions,
late adverse reviews, concurrent fix activity, and ambiguous duplicate writes
fail closed without reintroducing GitHub approval as a gate.

## 2026-09-01 — Evidence binds clean committed comparisons

**Trigger:** the issue 0007 incident in `results/telemetry/events.md`,
"Post-hardening audit found evidence could outlive its committed comparison."

**Change:** `ci.md`, `review.md`, `autofix.md`, and `issues-prs.md` now make a
clean feature worktree part of CI and review evidence, distinguish readable
failure or incomplete attestations from gate-complete success, specify strict
state-preserving review output, and permit only same-run summary recovery.
Review and auto-fix share ownership-stamped branch leases; reviewer identities
and run ids cannot cross distinct attestations; final mutations repeat their
guards after idempotency lookup; trusted refs resolve to commits; and
auto-fix retains the original full remote head/base and fetched local base
through every dispatch, commit, and leased push while tracking intentional
local head advancement. Review-fix consumes its canonical count and body from
one attestation snapshot. A superseded fixer stops before local advancement;
after a wrapper-owned commit, it starts no new phase and completes only the
original-comparison leased publication handoff, including any phase already in
progress. Explicit phase failures and signal exits remain failures while owned
locks are cleaned up. Findings and verdict sentinels reject prefix lookalikes,
and a canonical finding location is a relative repository path with a positive
line number or the literal `-`.

**Expected effect:** dirt, failed CI, malformed reviewer output, stale bases,
lost or cancelled leases, unrelated pending statuses, prompt-ref aliases, and
reviewer-session replay all fail closed without creating a local registry or
duplicating an already published review.

## 2026-09-01 - Merge integrity is server-enforced without approval

**Trigger:** owner decision follow-on for issue 0007 and the incident recorded
in `results/telemetry/events.md`, "Final merge-integrity audit found that client
evidence and server enforcement were still separate contracts."

**Change:** CI now publishes a pending summary before work and finalizes its
run/digest status only after immutable manifest and step-status read-back.
Every local review is a `COMMENT`; findings produce a failing summary, while a
clean attestation produces success. Merge validates exact zero-approval classic
protection and all effective rules on the actual base, holds CI/review/fix
leases through publication and merge, and uses one match-head mutation with
read-back-only recovery. Adjudication is an unedited exact-comparison record of
at least four distinct validated review rounds whose unresolved source findings
have exhaustive fixed-with-evidence or tracked-to-open-issue dispositions.

**Expected effect:** approval is neither requested nor counted, while stale
bases, weak protection, bypass actors, mixed adjudication rounds, incomplete
dispositions, concurrent producers, and ambiguous duplicate merges fail
closed against GitHub's sole authoritative state.

## 2026-09-01 - Gate evidence has one principal and proven merge topology

**Trigger:** the issue 0007 incident in `results/telemetry/events.md`, "Final
gate audit found publication identity and merge topology were not
authoritative."

**Change:** `ci.md`, `review.md`, `autofix.md`, and `issues-prs.md` now bind CI
comments, review `COMMENT` rows, adjudications, and CI/review statuses to one
validated `MIPSTARRE_GITHUB_ACTOR`, defaulting to the repository owner. Every
workflow invocation verifies the authenticated `gh` user. Comment copies from
other actors are ignored, while status selection remains globally latest and
therefore fails on a newer untrusted row. Adjudication selects exactly one
unedited trusted exact-comparison record strictly after its source review.

The merge gate accepts absent or null classic bypass allowances as empty but
rejects malformed or nonempty actor lists; classic `app_id` and effective
`integration_id` producers must be null or `-1`. Repository settings must
enable merge commits. One-shot read-back permits GitHub to advance the reported
base SHA, but proves the result is a two-parent commit ordered frozen base then
head; any other already-merged result is external/nonconforming. Ownership-
ambiguous partial locks remain fail-closed with documented manual recovery and
live locks remain exclusive.

**Expected effect:** copied markers, status impersonation, prefix poisoning,
producer-app substitution, disabled merge commits, and squash/rebase or foreign
merge results cannot satisfy the local gate, without adding an approval or
`reviewDecision` requirement.

## 2026-09-01 - Final recovery preserves zero-approval guards

**Trigger:** the issue 0007 incident in `results/telemetry/events.md`, "Final
workflow recovery audit exposed five remaining guard gaps."

**Change:** `review.md`, `ci.md`, and `issues-prs.md` now specify an explicit
`review.sh --new-round` path after complete exact-comparison evidence while
keeping ordinary reruns idempotent and incomplete publication recovery
dispatch-free. A globally latest untrusted or creator-missing review summary is
recoverable by a newer trusted digest-bound final status; a trusted mismatch
still fails closed. Shared per-PR CI leases use directory age during owner
initialization, unique ownership tokens, and rename-before-delete cleanup.
Merge policy rejects classic and effective linear-history requirements, and
adjudication orders review rows against issue comments by strict timestamp
without an id tie-break.

**Expected effect:** operators can produce four independently attested rounds
through the supported CLI without weakening CI, identity, comparison, bot, or
lock guards; poisoned summaries and stale partial locks have bounded recovery;
replacement locks, merge-only topology, and equal-time chronology remain
fail-closed.

## 2026-09-01 - Final transitions are serialized before rename

**Trigger:** the issue 0007 incident in `results/telemetry/events.md`, "Final
serialization audit found lock-transition and review-attempt races."

**Change:** `ci.md`, `review.md`, and `issues-prs.md` now require one persistent
per-lock `flock` transition mutex for CI stale breaking and merge cleanup.
Canonical directory identity and complete dead-owner or releasing-owner
evidence are revalidated under that mutex before rename; partial locks always
require explicit operator recovery. Provisional review statuses bind a
fingerprint of the full base SHA, run, attempt state, exact head/context digest,
and trusted creator. Only explicit `--new-round` may supersede a canonical
unattested pending or aborted attempt. Present classic linear-history data must
be a well-formed object reporting `enabled=false`.

**Expected effect:** two breakers cannot both transition one stale lease, old
cleanup cannot move a replacement directory, and failed review rounds remain
retryable without making ordinary reruns, wrong-base attempts, or arbitrary
trusted conflicts recoverable. Zero-approval clean `COMMENT` attestation plus
trusted exact-head local-review summary remains the review gate.

## 2026-09-01 - Shared runtime locks use one complete claim protocol

**Trigger:** the issue 0007 incident in `results/telemetry/events.md`,
"Lock-unification audit found incompatible transition participants."

**Change:** `ci.md`, `review.md`, `autofix.md`, `issues-prs.md`,
`build-cache.md`, and `local/README.md` now specify one helper-owned record for
CI, review, fix, merge, full-build, warmer-writer, and cache-telemetry leases.
The record binds directory identity, PID, random UUID token, structured owner
metadata, and its digest. Acquisition, complete-dead-owner recovery, exact
release, and claim-bound cancellation revalidate under the persistent sibling
mutex. Malformed, ownerless, partial, and foreign-host records require manual
recovery. The zero-approval clean `COMMENT` plus exact-summary review gate is
unchanged.

**Expected effect:** no participant can rename, delete, or cancel a replacement
directory from a pre-mutex observation; review and auto-fix retain queueing,
supersession, signal cleanup, and cap-time handoff; and all full-build callers
enforce one machine-wide exclusion contract.

## 2026-09-01 - Runtime and publication ambiguity fail closed

**Trigger:** the issue 0007 incident in `results/telemetry/events.md`, "Final
audit found descendant, publication, and post-merge ambiguity."

**Change:** runtime-lock acquisition now refuses every complete existing claim;
dead-parent recovery is explicit because descendants may survive. Dispatcher
and workspace-write agent sessions use exact helper-owned leases, while
autofix cancellation is restricted under the transition mutex to prior
`autofix ` owners. Signal wrappers preserve 130/143 and exact cleanup.
Publication guards run after status, comment, and review writes or adoption;
transient reconciliation reads retry without a second mutation, and a review
whose POST may have begun is never overwritten with an ambiguous abort. Merge
requires `draft` exactly false; after verified remote topology, local refresh
and cleanup warn and defer rather than reversing the reported result. Workflow
triggers cover both lock and warmer implementations, and protected-tree tests
are pinned to archival commit `c8f1999`.

**Expected effect:** surviving descendants retain exclusion, human and
automatic writers cannot cancel across owner classes, ambiguous accepted
reviews remain idempotently recoverable, and a proven GitHub merge cannot be
misreported because later local telemetry or cleanup is dirty. The
zero-approval clean `COMMENT` review gate remains unchanged.

## 2026-09-01 - Close-out audit preserves liveness and protected history

**Trigger:** the issue 0007 incidents in `results/telemetry/events.md`, "Late
first-phase cancellation could strand auto-fix work," "Protected workflow
changes could bypass regression tests," "PR label replacement retried an
ambiguous write," "Archival session telemetry invalidated valid review
evidence," and "Contributor guidance still described inactive GitHub Actions."

**Change:** the final pre-dispatch auto-fix cancellation check is now the
phase-start linearization point: a later canonical exact-claim cancellation may
finish the active phase's one wrapper commit and leased push, while malformed
cancellation or lost ownership fails closed. Workflow classifiers and hooks
cover `.github/` and the immutable registry archive, including deletions and
rename sources. PR label replacement reads first, performs one retry-free
`PUT`, and reconciles by authoritative read-back. Reviewer evidence accepts one
original `done` row plus field-preserving `archived` projections and rejects
identity changes or cross-session thread reuse. Contributor guidance now names
the local GitHub-native tools rather than inactive Actions.

**Expected effect:** authorized supersession cannot strand a dirty auto-fix
tree; protected history cannot evade tests by deletion or rename; ambiguous
label writes cannot clobber concurrent updates; archival telemetry remains
valid evidence without enabling replay; and operators see the actual live
workflow. The trusted exact-head clean `COMMENT` plus
`local-review/summary=success` remains the zero-approval review gate.

## 2026-09-01 - Resumed dispatch respects the Codex CLI boundary

**Trigger:** the issue 0007 incident in `results/telemetry/events.md`, "Resumed
dispatch placed parent options after the subcommand."

**Change:** `dispatch.sh` now places the working directory and sandbox options
on `codex exec` before the optional `resume` subcommand, while JSON capture,
last-message output, model, and effort options remain valid for either mode.
The workflow suite checks both fresh and resumed dry-run argv shapes.

**Expected effect:** a resumed session starts in the requested worktree and
sandbox instead of failing before event capture, so continuity and telemetry
remain available through the only sanctioned dispatcher.

## 2026-09-01 - Session allocation remains single-instance

**Trigger:** the issue 0007 incident in `results/telemetry/events.md`,
"Bootstrap dispatch reused a session name across worktrees."

**Change:** the operator guide and session protocol again require invoking
workflow tools through the primary checkout. The recovery rule preserves both
original bundles in a dated collision archive, retains the primary allocation,
and assigns the next free sequence to a byte-identical copy of the colliding
feature bundle. The session, build, and stage telemetry schemas and append-only
pipeline are unchanged.

**Expected effect:** all dispatches scan one registry and capture directory
under the shared allocator lock, while any bootstrap collision remains
reconstructible without overloading a stable session name or rewriting source
evidence.
