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

## 2026-09-01 — GitHub becomes the workflow authority (lean port)

**Trigger:** owner decision 2026-08-31 (follow-on to the re-hybridization
entry); executed 2026-09-01 after the scope reset recorded below.

**Change:** The local issue tree and PR registry are retired.  GitHub
(`Dengnifer/MIPStarRE-A`) is the single source of truth for issues (native
sub-issues replace `parent`/`children` frontmatter), PRs, CI evidence
(per-step commit statuses `local-ci/<step>` plus `local-ci/summary` and
`local-review/summary` on the exact head SHA), review verdicts (COMMENT
reviews bound to a commit id — a single-account repo cannot self-APPROVE, so
adverseness travels in the failing `local-review/summary` status), and merges
(REST merge guarded by the exact-SHA `sha` parameter, verified by merge-commit
topology).  All GitHub traffic goes through `local/bin/gh_common.py`; shared
non-registry helpers moved to `local/bin/wf_util.py`.  `track.py`,
`validate_tree.py`, `export_issues.py`, and `local/labels.yml` are deleted —
GitHub provides what they reimplemented.  The registries were archived
verbatim first (`results/telemetry/registry-archive/`, commit c8f1999) and
stay read-only research data; `github-sync.sh` now also writes a read-only
JSON snapshot of open issues/PRs under `results/telemetry/github-snapshot/`
for offline forensics — never lifecycle input.

**Expected effect:** CI and reviews still execute locally on this machine;
GitHub stores the evidence.

## 2026-09-01 — Scope control for workflow changes (incident amendment)

**Trigger:** events.md 2026-09-01, the issue-0007 overbuild.  The first
implementation of the entry above grew, in ~17 hours and 21 commits, into a
+14.6k-line unreviewed rewrite of the whole layer — a 2,761-line bespoke
GitHub API client, a 643-line lock manager, a 5,649-line test suite wired
into the commit and push hooks (≈10 minutes per commit), an actor-verification
regime and a branch-protection evaluator nobody asked for — while the actual
product (the Lean formalization; PR #5's 17 findings) sat untouched.  The
owner paused the session, archived the branch as research data
(`telemetry/issue-0007-overbuilt`), and rebuilt the port lean.

**Change:** amendment (now also in `local/personas/main.md`):

1. The product is the Lean formalization.  `local/` is scaffolding; scaffolding
   work is a cost center, budgeted by default at ≤2 hours wall time and ≤400
   changed lines per episode.  Hitting the budget means stop, commit what
   stands, record the state, and escalate to the owner — not push through.
2. Git hooks must finish in under 60 seconds on a typical commit; heavier
   verification belongs to CI steps.
3. No new abstraction layers (API clients, lock managers, frameworks) and no
   rewrites of working, reviewed code without an explicit owner directive;
   prefer the smallest diff that satisfies the brief, and prefer `gh` + the
   REST API over reimplementation.
4. After any workflow change merges, the next dispatched work item MUST be a
   mathematics item.  Two consecutive workflow-only episodes require owner
   approval.

**Expected effect:** scaffolding episodes stay bounded and auditable, and the
work item after a merged workflow change is mathematics.

## 2026-09-02 — Issue #25 bounded reviewer lane

**Trigger:** Issue #25 and the PR #28 bootstrap review recorded in `results/telemetry/events.md`.
**Change:** Bound reviewer scope, context, model, effort, memory, and timeout.
**Expected effect:** Reviews stay focused while owner inbox #26 and progress log #27 remain current.
## 2026-09-02 — PR 7 review hardening (rounds 1-3)

**Trigger:** the three adversarial review rounds on the GitHub-native port PR
(#7).  Each round's findings ledger sits in the PR's published review; the
supporting record is `results/telemetry/` and the read-only
`registry-archive/` precedent for what evidence must be able to prove.

**Change:** every bypass the reviewer found is now closed mechanically.

1. A publishing CI or review run refuses a dirty worktree, and `ci.sh`
   re-checks both the local tip and the remote head immediately before
   publication — a status is a claim about one commit, and dirty bytes are not
   that commit.
2. `--base`, `--only`, and `--skip-build` runs are partial: they publish
   nothing at all.  `--base` joins the list because an overridden base empties
   the diff and marks every gate skipped-success.
3. The roll-up summary is invalidated (set `pending`) before a rerun, so a
   crashed run can never leave the previous `success` standing.
4. Green review evidence requires BOTH a clean `VERDICT` and a
   zero-unresolved findings ledger; a clean verdict over unresolved findings is
   inconsistent reviewer output, not a pass.
5. The merge gate adds gate 2b (fresh base): the head must contain the current
   base tip, and a failed base fetch fails the gate.
6. The fix-iteration cap fails closed on an unresolvable merge base rather
   than counting zero fixes.
7. The scope guard counts deletions and runs before the early exit, so a
   large-deletion or no-op-looking change cannot slip past the budget.
8. Review ledgers stay in runtime storage; the published GitHub review is the
   durable record.

**Expected effect:** evidence can only ever certify committed, pushed, current
bytes, and each bypass is closed by the tooling rather than by convention.

## 2026-09-02 — Merge-time fix cap retired; owner-gated controls enumerated

**Trigger:** the PR #5 stall recorded in `results/telemetry/events.md`
(2026-09-02, "PR #5 review-fix cap"): six hand-authored review-fix commits,
every CI context green and an APPROVED review with zero unresolved findings on
the exact head, yet `pr_merge.py` gate 6 refused because the branch carried six
`[codex-review-fix]` commits against a cap of five.  The operator escalated to
the owner: the gate text named "human attention" as the remedy and the standing
briefing forbade weakening a gate.  An owner-side audit (six read-only lanes,
three adversarial refuters) found no safety property behind the refusal.  The
episode is owner-directed — the owner approval `main.md` requires for a second
consecutive workflow episode — and the incident record is the events.md entry
of 2026-09-02 ("PR #5 review-fix cap"), committed on main (f94fe3c) before
this amendment and contained in the PR head.

**Change:**

1. `pr_merge.py` gate 6 no longer enforces a fix-commit cap.  The count is
   retired because it carries no evidence about the head: gates 3/4 already
   bind CI and the review — which covers the whole `merge-base..head` diff —
   to the exact SHA, so a converged PR is proven converged however many fix
   commits it took.  The count was also subject-prefix-based, not
   provenance-based (PR #5's six were hand-authored).  Bounding the automated
   loop is `autofix.sh`'s job; its pre-lock count race (issue #9) and its
   terminal-review gaps (issue #13) are loop defects, tracked there.  The lock
   probe stays, the merge-base computation gate 7 reuses stays (with a gate-7
   message), and the count is printed for the record.  `review.md` §12
   operator adjudication remains the convergence backstop.
2. `autofix.sh`'s cap note and `autofix.md` §5 address the operator, not "a
   human", and the doc matches the code (the label is not removed).
3. `.githooks/pre-commit` runs the scope-control budget before the
   `MIPSTARRE_SKIP_HOOKS` exit, so a blanket hook skip cannot launder the
   owner-only override.
4. `issues-prs.md` §3/§5, `review.md` (merge gate), `meta.md` §1 and
   `personas/main.md` name exactly one owner-gated control,
   `MIPSTARRE_INFRA_OVERRIDE`; every other parameter and remedy is the
   operator's with a recorded reason; an owner-blocked item becomes a
   `needs-owner` issue and the session continues with the queue.
5. Worker personas commit repairs under plain `fix(...)` subjects; the
   `[codex-*-fix]` prefixes are reserved for `autofix.sh` (they made
   `review.sh` skip PR #5's heads and forced four `--force-review` runs).
6. A regression test pins that six fix-prefixed commits with full evidence
   pass `--check-only`.

**Expected effect:** the merge gate never demands owner action while all
evidence is green on the exact head; the owner-gated set is exactly the
anti-bloat budget; a question for the owner parks one item instead of idling
the session.

## 2026-09-03 — Dispatch resume option ordering

**Trigger:** `results/telemetry/events.md` 2026-08-31, "Codex resume dispatch
rejected the worktree option" (tracked by issue #38): sanctioned session
`orc-0007-20260831-02` failed before agent start because `codex exec resume`
rejected the worktree option after the subcommand.

**Change:** `local/bin/dispatch.sh` now places all `codex exec` options before
the optional `resume` subcommand. `local/protocols/sessions.md` records that
CLI-ordering invariant, and `scripts/tests/test_dispatch.py` checks fresh and
resumed argv assembly deterministically.

The issue #38 review found that the new regression file was omitted from the
workflow line-budget path set and that its preflight depended on an installed
Codex CLI. A repository-wide search found `.githooks/pre-commit` to be the only
`INFRA_CHANGED` enforcement point. It now counts the dispatch test, while the
test places a temporary fake `codex` first on `PATH`.

**Expected effect:** fresh and resumed dispatches retain the same worktree,
sandbox, JSON capture, final-message, model, and configuration behavior, while
both conform to the installed Codex CLI grammar.

**Outcome:** read-only smoke sessions `scout-38-resume-smoke-20260903-01` and
`scout-38-resume-smoke-20260903-02` started in the issue #38 worktree, shared
thread `01a064b5-fb0a-77b0-830e-e106a44b1a8f`, and each completed with JSON,
a final message, and a successful telemetry record.

The review repair kept total issue-branch workflow churn at 145 changed lines,
below the 400-line limit, without `MIPSTARRE_INFRA_OVERRIDE`; the focused tests,
full Python suite, and pre-commit gate exercise the corrected budget and
hermetic test path.

## 2026-09-03 — Tier 2 becomes a shared read-only package store

**Trigger:** owner audit of disk use on ghz (2026-09-03): the project directory
had grown to 87 GB on a 97 %-full disk, 58 GB of it eight identical 7.3 GB
copies of `.lake/packages` (all 21 checkouts share one `lake-manifest.json`
and `lean-toolchain`); ext4 without reflink, so copy-on-write is unavailable.

**Change:**

1. `warm-worktree.sh`: tier 2 is linked from `$CACHE_ROOT/packages/<key>`
   (`key = sha256(lake-manifest.json ‖ lean-toolchain)[:16]`); the first
   warmer for a key still runs `lake exe cache get`, then publishes the tree
   (move, `chmod -R a-w`, symlink); later warmers only link. A pre-existing
   per-worktree copy is left in place with a warning.
2. `build-cache.md` tier-2 section and invariant 10 rewritten: the
   "never symlinked" rule is replaced by the read-only store, with the reason
   the old objection no longer applies (writes fail loudly instead of
   spreading). `ci.sh` already treated a symlinked `.lake/packages` as a
   read-only dependency tree.
3. Live migration performed by the owner: the primary checkout's tree was
   moved into the store and every identical worktree copy swapped for a
   symlink (same filesystem `mv` + `ln -s`, safe under running `lake`
   processes), reclaiming ~51 GB.

**Expected effect:** packages cost 7.3 GB once per manifest rather than per
worktree; new worktrees are ready in seconds without touching the network
(which was flaking from ghz on 2026-09-02); a Mathlib bump is a new store key,
never a mutation of a shared tree.

## 2026-09-03 — Two-round cap for workflow-only PRs; queue discipline

**Trigger:** `results/telemetry/events.md` 2026-09-03, "Eight-hour stall on
main": the operator fed a 107-line workflow PR to the reviewer three times
(5 → 10 → 11 findings), grew it to 400 lines to satisfy them, and left two
green PRs unmerged for hours.

**Change:** (1) the two-round threshold for workflow-only PRs is operator
discipline enforced by the owner's watchdog (a `review.sh` refusal was tried in
PR #79 and withdrawn: a corrected head needs an exact-head review before it can
be adjudicated); (2) `personas/main.md` gains the queue-discipline bullet (merge green
PRs first at every iteration; two rounds then adjudicate; never grow a PR to
satisfy findings; mechanism requests are out of scope); (3) `review.md`
section 12 records the two-round threshold for workflow-only PRs.

**Expected effect:** scaffolding PRs converge in two rounds or are decided;
green work merges at every iteration; the reviewer cannot drive scope growth.
## 2026-09-04 — Review evidence follows the diff (carry-forward across a fresh-base)

**Trigger:** owner operation of the loop with eight parallel lanes
(2026-09-03/04): each merge advanced `main`, gate 2b then required every other
green PR to merge `main` and re-run CI **and** a 15–25-minute reviewer round
for a byte-identical patch (PR #78 refused at 6f224bf minutes after its review
had passed); with N open PRs every merge cost N reviewer rounds.

**Change:** `review.sh` gains a carry-forward fast path (section 13): equal
`git patch-id` of `base...head` against an earlier reviewed head republishes
that head's verdict and ledger for the new head and posts the summary status;
adverse verdicts carry too; `--force-review` disables it.  `issues-prs.md`
gate 4 notes that a carried review counts.

**Expected effect:** a fresh-base costs one CI run (about two minutes) and no
reviewer time; the reviewer pool serves new patches only; merge throughput
scales with the number of lanes instead of collapsing under them.


## 2026-09-04 — Pre-commit budget exempts inherited main changes

**Trigger:** `results/telemetry/events.md` 2026-09-04 (owner override for a
merge commit): a fresh-base merge of `main` into a 130-line workflow PR staged
520 inherited workflow-layer lines and the budget guard refused the merge
commit; completing it would have required the owner override for content that
was already reviewed on `main`.

**Change:** `.githooks/pre-commit` measures a merge commit against `MERGE_HEAD`
only when that commit is contained in `refs/remotes/github/main`.  The PR's own
cumulative workflow-layer diff and merge-time edits remain budgeted, inherited
main content counts zero, and side-branch merges remain measured against `HEAD`.
Regression tests exercise both kinds of merge; ordinary commits are unchanged.

**Expected effect:** fresh-base merges do not need the owner override solely for
inherited main content; the budget keeps binding the PR's own changes, and the
review reads the PR diff.

## 2026-09-04 — Packet tree under #47; prerequisites become issue dependencies

**Trigger:** owner decision on #159 (2026-09-04, after studying
LionSR/MIPStarRE#449), and `results/telemetry/owner-log.md` 2026-09-04 07:25Z
and 08:35Z, where lane order was carried by hand against tables kept in
comments on #47 — "#125 (operator BLR, stacked on #124)", "Opus prover pilot
started on #102 (stacked on #101)" — while #47 itself had grown to 50 flat
sub-issues (19 closed) and two open packets (#146, #156) had no parent at all.

**Change:** (1) five chapter trackers (#163 games, #164 test, #165 observables,
#166 combining, #167 extraction) are now open sub-issues of #47. The 35 direct
tracker children migrated then were #63, #77, #97-#99, #106-#121, #123-#125,
#127-#135, #146 and #156; #77 retained its five nested rigidity packets #101-#105.
Closed foundation packets such as #100, #122 and #126 remained direct children
of #47, whose body became an index over its trackers.
(2) Every open packet's prose prerequisites are transcribed into `blocked_by`
issue dependencies (69 edges) and the bullets are demoted to commentary by a
line in the body itself. (3) `local/bin/ready_packets.py` walks that tree and
prints the open leaves whose blockers are all closed (`--all`, `--json`,
`--root`), covered by `scripts/tests/test_ready_packets.py` against a fake API.
(4) `issues-prs.md` §1 makes the edges normative and names the script as the
launch list; `local/README.md` documents the command.

**Expected effect:** the operator launches from a computed list instead of
re-reading a comment; a merged packet unblocks its dependents with no edit
anywhere; the rooted traversal reports the tracker hierarchy and its leaves.

## 2026-09-04 — Supported prerequisite writes and complete readiness budgeting

**Trigger:** `results/telemetry/events.md` 2026-09-04 15:12Z, recording issue
#177 and the two workflow findings deferred from PR #171.

**Change:** `gh_common.py` and `issues-prs.md` add the supported
`add-blocked-by ISSUE PREREQUISITE` lifecycle command. It adopts an existing
edge before writing and re-reads after an ambiguous POST. The pre-commit
infrastructure budget now counts `scripts/tests/test_ready_packets.py`, with a
hook-level regression that stages 401 lines at that path.

**Expected effect:** operators can create the prerequisite record without an
ad hoc GitHub mutation or a duplicate edge after retry, and future readiness
test growth remains subject to the owner-gated 400-line episode budget.

## 2026-09-05 — Blueprint citations use labels; reviewers derive spans

**Trigger:** `results/telemetry/events.md` 2026-09-05 "Blueprint numeric
locator churn", consolidating issue #174, PR #152's nine stale-span findings,
four same-day merge conflicts, and the earlier PR #29 locator regression.

**Change:** `AGENTS.md` makes blueprint labels the stored Lean-docstring
citation form. `scripts/blueprint_citations.py` resolves active labels to
current statement/proof spans and conservatively rewrites legacy locators.
`review.sh` loads that helper from the committed trusted ref, attaches its
derived map as untrusted review data, and the review prompts and protocol no
longer treat numeric drift as a finding when the intended label resolves.

**Expected effect:** blueprint insertions no longer force edits or review
findings in unrelated Lean files, while reviewers retain exact current source
locations and still detect missing, duplicate, or incorrect anchors.

## 2026-09-05 — Blueprint citation evidence gets a reserved budget

**Trigger:** `results/telemetry/events.md` 2026-09-05, "Citation evidence
starved by the review diff", recording PR #202 round 1 findings F6 and F7.

**Change:** `review.sh` sanitizes the branch-derived citation map into a
separately capped artifact, attaches it before the diff, and uses only that
artifact in the no-dispatch fallback. `review.md` section 4 makes the default
30000-byte allowance and ordering part of the untrusted-data protocol.

**Expected effect:** reviewers receive bounded label-resolution evidence even
for large patches, and neither review path interpolates raw branch-derived map
content.
