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
