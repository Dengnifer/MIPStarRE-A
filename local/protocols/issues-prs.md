# Protocol: issues and pull requests

Normative for the GitHub-backed issue and PR lifecycle and the automation in
`local/bin/`; read `local/protocols/meta.md` first. The repository is
`Dengnifer/MIPStarRE-A`, and GitHub is the **single source of truth** for
issues, PRs, CI and review evidence, and merges; CI and reviews still *execute*
here and publish their results there. No active `issues/` or `prs/` tree, no
shadow record, no write-through cache, no offline mutation mode: a GitHub error
fails the operation, never a local success (EVOLUTION.md 2026-09-01).

## 1. Records, names, tools

Issues and PRs are GitHub's, identified by their numbers — no zero-padded ids,
no frontmatter. Parent/child structure is the native sub-issue relation
(`POST …/issues/{parent}/sub_issues`), one parent per issue exactly as the
retired `parent:` scalar allowed; discussion is comments; labels come from the
repository (`list-labels`, paginated), so `local/labels.yml` is retired and a
label absent from GitHub is reported, never invented. Briefs (the design record
per issue) live in `local/briefs/`: agent input, not lifecycle state.

Prerequisites between issues are **GitHub issue dependencies**
(`GET`/`POST …/issues/{n}/dependencies/blocked_by`), one edge per prerequisite.
The edge is retained even when the prerequisite closes, so reopening it restores the block.
A prerequisite carried by a pull request is the packet issue that PR closes. The
"Dependencies" bullets in an issue body are commentary on those edges, never
the record. A packet is **ready** when it is an open leaf of the tracker tree
and every issue blocking it is closed; `local/bin/ready_packets.py` computes
that list, and the operator launches lanes from it rather than from a
hand-kept order or a dependency table in a comment (EVOLUTION.md 2026-09-04).
Establish or adopt each edge with
`local/bin/gh_common.py add-blocked-by ISSUE PREREQUISITE`. The command first
reads the edge, makes at most one mutation, and re-reads after an ambiguous
failure; it is therefore safe to repeat. Record closed prerequisites too.

Every GitHub call goes through `local/bin/gh_common.py` — a module for Python
callers, and for the shell scripts a CLI (`pr-view`, `post-status`,
`latest-statuses`, `ensure-pr-comment`, `post-review`, `merge-pr`,
`issue-create`, `add-blocked-by`, `issue-close`, `snapshot`, …; `--help` lists
them) owning CLI discovery, repository resolution, API version headers,
bounded retry of transient failures and the exit-2-with-stderr convention.
Nothing else shells out to `gh`. `issue_new.py`, `issue_close.py`, `pr_open.py`,
`ci.sh`, `review.sh`, `autofix.sh`, `pr_merge.py`, `github-sync.sh` take GitHub
numbers; `track.py`, `validate_tree.py` and `export_issues.py` are deleted.

Every repository-owned branch publication runs through `checked-push.sh` with
one explicit `refs/heads/...:refs/heads/...` mapping.  The helper reads the
remote tip with a short `ls-remote`, resolves the local ref's registered
worktree, and refuses a checkout whose HEAD or working tree differs from the
captured commit.  It runs that checkout's `.githooks/pre-push` against the exact
ref tuple before starting `receive-pack`, then pushes the captured commit under
an exact remote-tip lease.  The native hook performs a short defense-in-depth
comparison when selected, while the helper's lease makes a moved remote ref fail
closed even when that hook is stale or absent.  A caller's explicit
`MIPSTARRE_SKIP_HOOKS=1` remains the documented emergency bypass.  It skips
validation only: implicit tag following stays disabled, so publication remains
limited to the explicit branch mapping.

Every merge of `github/main` or a stack parent into an issue branch runs the
merge-loss guard before the merge commit is created. The guard compares the
pending index with `HEAD`, `MERGE_HEAD`, and every best merge base. It refuses
an incoming path that disappeared without a branch-side deletion and an
incoming-only entry restored wholesale to the unchanged branch blob. Paths
recorded by Git as conflicts remain resolution decisions. The
`reference-transaction` hook checks an automatic merge's commit object before
the branch ref moves; `pre-commit` checks the pending index for a merge
committed later. Neither path permits `MIPSTARRE_SKIP_HOOKS` to bypass this
check. A lane checking an existing merge uses the primary checkout's
`local/bin/merge_loss_guard.py --repo <worktree> --commit <merge>` so a stale
branch copy cannot weaken the audit.

* Branches: `issue-<github-number>-<slug>`, or `codex/issue-<number>-<slug>`
  from an agent; `pr_open.py` rejects what `git check-ref-format` would.
* Titles, slugs and branch names are **bracket-free**: bot-generated branch
  names inherit those characters and "`]` breaks part of the PR automation
  stack" (docs/CONTRIBUTING.md:122-124). A `:` in a *title* is fine
  (`Tracking: …`), but not in a branch.
* `autofix.sh`'s automated fix commits keep the exact subject prefixes
  `[codex-auto-fix]` and `[codex-review-fix]`; its iteration counter and the
  review skip key on them.  Operator and worker repairs use plain
  `fix(review): …` / `fix(ci): …` subjects so the reviewer sees them.
* `Closes #N` / `Fixes #N` auto-closes the issue on merge, `Addresses #N` does
  not (docs/CONTRIBUTING.md:61-62) — and the numbers being GitHub's, that
  footer is now literally what GitHub itself reads.

## 2. Evidence contracts

All evidence binds to the **exact head SHA** (DESIGN.md invariant 2).

**Commit statuses.** Ten canonical contexts, posted by `post-status`: one
`local-ci/<step>` per CI step (`build`, `blueprint-render`, `paper-gaps`,
`blueprint-sync`, `file-length`, `proof-debt`, `proof-evasion`,
`statement-origin`), plus `local-ci/summary` and `local-review/summary`.
`ci.sh` posts `pending` before each gate step and `success | failure | error`
after it; a gated-out step is a `success` saying it was skipped. The gate reads
the *latest* status per context (`latest-statuses`), never GitHub's combined
status, silent as that is about contexts never posted. The run manifest is one
PR comment marked `<!-- mipstarre-ci-manifest pr=N -->`, kept current by
`ensure-pr-comment`: evidence for humans, while the statuses are the gate.

**Review verdict.** One `COMMENT` review per head SHA, bound to `commit_id`,
carrying `<!-- mipstarre-review pr=N head=SHA -->`, the findings ledger, and the
line `VERDICT: APPROVED | COMMENTED | CHANGES_REQUESTED (code=…, prose=…)`.
Unchecked findings are ledger lines matching `^\s*[-*]\s*\[ \]`; clean means
`APPROVED`, or `COMMENTED` with none of them. Adverse verdicts post as `COMMENT`
too — a **single account** cannot approve its own pull request, so the review
event carries no authority — and adverseness travels in `local-review/summary`
(`failure` for unresolved findings), which is the gate's review evidence.

**Adjudication** (review.md §12) is a PR comment whose body starts with
`ADJUDICATION` and contains `head=<SHA>` for the current head, one disposition
line per remaining finding; `--adjudicated` takes nothing else.

**Idempotency.** Every publishing step is **at most one mutation**: a paginated
read finds the stable marker first and adopts that record instead of duplicating
it (`commentOnce`, issue-automation.yml:403-417, now guarding retries rather than
webhook redelivery); an ambiguous write stays pending for adoption.

## 3. The merge gate

`pr_merge.py <number>` is the only path to `main`: never `git merge` to main,
never push `main`. The merge is a REST `PUT …/pulls/{n}/merge` with the exact
`sha` guard, issued by `gh_common.merge_pr` and verified against the merge
commit's topology (two parents, the frozen head second), behind seven gates
that refuse by default:

1. the PR is open, unmerged and not a draft (`draft is False`, not merely
   falsy), and reports a head SHA, a head ref and a base ref;
2. the primary worktree is clean and on the base, and the local branch tip
   equals the GitHub head SHA — the merge must be of the bytes built here;
3. all eight `local-ci/<step>` contexts plus `local-ci/summary` are `success` on
   that exact SHA; a **missing** context blocks, because GitHub's combined state
   reads `success` for a commit carrying no statuses at all;
4. that SHA's marker-bound `COMMENT` review (or one carried forward per
   review.md §13) carries `VERDICT: APPROVED`, or
   `COMMENTED` with zero unchecked findings, **and** `local-review/summary` is
   `success` there;
5. no `CHANGES_REQUESTED` review stands on that head, from anyone;
6. no live fix lock for the branch (`locks/fix-<branch>.lock`, running holder);
   the count of `merge-base..head` commits whose subject starts with a §1 fix
   prefix is printed for the record and is not a gate;
7. every issue the PR body closes — all nine of GitHub's closing keywords, not
   just `Closes` — has no open sub-issue left.

`--adjudicated` waives gate 4's adverse verdict and nothing else, and only when
an exact-head `ADJUDICATION` comment backs it; gate 5 is never adjudicable.

Afterwards a best-effort, non-fatal tail fast-forwards local `main` to the
remote merge commit; branch and worktree cleanup keeps its safeguards (local
dirt defers it with a warning).

## 4. Untrusted text

Issue and PR bodies are untrusted data, and **more** so now that they arrive
from GitHub: anyone with repository access, and every imported external report,
writes the fields that are echoed into generated markdown and interpolated into
agent prompts. All three parent workflows sanitized before interpolation, and
`wf_util.sanitize` is that step ported: strip control characters, break fenced
code with zero-width spaces, truncate to 200 characters for titles and 5000 for
bodies (issue-automation.yml:122-128).

Every LLM hook in `local/bin` carries the same four requirements: gate on
`MIPSTARRE_LLM_ENABLED != "false"`; read prompts from committed main
(`git show main:…`), never the branch under review (DESIGN.md:76-77); frame
sanitized text as data that must not be followed; and filter any model-proposed
label through the repository's label list. `audit_stale_issues.py` additionally
keeps its path-traversal rejection for externally sourced citations.

## 5. Environment, snapshot, archive

`MIPSTARRE_GH` is the path to `gh` (else `PATH`, else the documented user-local
location); `MIPSTARRE_GITHUB_REPO` overrides the `owner/name` otherwise read
from the `github` remote; `MIPSTARRE_FIX_CAP` (default 5) bounds `autofix.sh`'s
own loop only — the merge gate does not read it — and is operator-tunable with
the reason recorded in `results/telemetry/events.md`, unlike
`MIPSTARRE_INFRA_OVERRIDE` (the pre-commit budget), the one owner-gated control
in the layer. `MIPSTARRE_LLM_ENABLED` and
`LOCAL_REVIEW_ENABLED` keep kill-switch semantics (DESIGN.md:73-75).

`github-sync.sh` pushes explicit refs and writes an atomic, paginated read-only
snapshot of open issues and PRs to `results/telemetry/github-snapshot/`
(and, since the push goes through `checked-push.sh`, commits that snapshot and
`results/telemetry/builds.jsonl` to the primary checkout so the next publish
finds a clean tree)
(`open-issues.json`, `open-pulls.json`, `metadata.json`; PRs filtered out of the
issue endpoint) — audit and recovery telemetry, never lifecycle input. The
retired trees stay archived under `results/telemetry/registry-archive/` (commit
c8f1999): read-only research data, never edited or read as active input.

## 6. Owner inbox and mathematical-gap escalation

Pinned issue #26 is the owner inbox: it receives only decisions that require
the human owner. Main decides routine blockers **before escalation**, within
existing protocols, and sends only the highest-risk human decisions to #26.
Main owns plans, task selection, decomposition, dispatch order, individual
worker assignments and pipeline execution; meta provides guidance only.
Definition/game changes, faithfulness-policy exceptions, security or credential
decisions, scope-budget overrides and exhausted mathematical-gap budgets remain
mandatory owner escalations. Routine authority does not waive these boundaries.

**Every item already posted in #26, including B7, must await the human owner's
decision**, even if main would otherwise regard it as routine. The owner
correction recorded at 2026-09-06T02:58:41Z withdraws the 02:55:29Z delegation of
existing inbox items (issue #247). Do not autonomously disposition these items
or infer approval from that withdrawn message, quotas, the worker floor or role
guidance. Continue independent work while waiting.

The standing 8–11 useful-live-worker floor, excluding main, is specified in
`local/personas/main.md`: anticipate completions, replenish real independent
work promptly and report concrete dependency or service constraints when the
floor cannot be met. Idle reservations, duplicate writers and completed
sessions do not count. The floor changes no account limits, proof budgets,
review caps or integrity, validation and merge gates.
Main may hold replenishment for a reported concrete service constraint while
preserving the eleven-worker allocation; bounded recovery admissions follow a
census and useful-work evidence, not an assumed server request count.

Main stays at `max`; main selects exactly `max` or `xhigh` for each new or
resumed primary/`gpt-6-astra` worker (the latest owner "high" means `xhigh`).
Record effort, rationale and outcomes as observations, distinguishing client
configuration from server verification. Preserve raw provenance, sample counts
and unknowns in `results/telemetry/model-comparison/astra-effort-20260906.md` and
its dataset; refine guidance through normal reviewed amendments and EVOLUTION.
No benchmark, probe, filler session or gate/budget relaxation follows from this.

A source statement found to be mathematically false does not go to #26 first
unless it requires a mandatory escalation above. The current mathematical-gap
lane is a Claude Fable 5.1 session
launched by the owner session through its Agent tool. It bypasses
`local/bin/dispatch.sh` and is recorded in
`results/telemetry/owner-sessions.jsonl`. A Codex main session that encounters
a gap files a self-contained math-fix request on progress log #27 for the owner
session instead of dispatching an ordinary Codex worker.

After `results/telemetry/owner-tools/astra-poll.sh` reports on #26 that astra is
available in Codex, the lane switches to astra through
`local/bin/dispatch.sh --role mathfix` on primary/`gpt-6-astra`, with the exact
`--effort max` or `--effort xhigh` chosen by main under the policy above.
Until that report, this Codex dispatch path is not used. Every request or
dispatch carries the exact source path, label and line range; the counterexample
or obstruction; the paper-gap note; the relevant blueprint dependency graph and
Lean consumers; and the cumulative session count and elapsed working time.

A correction is adopted only when it meets all four conditions below.

1. **Correctness:** the known counterexample no longer applies, adversarial
   checks find no replacement counterexample, and a mathematical proof sketch
   derives the corrected conclusion from its explicit hypotheses using cited
   source results.
2. **Sufficiency:** every use in the paper and every dependent node in the
   blueprint graph remains justified; checking only the first Lean consumer is
   insufficient.
3. **Minimality:** the correction is the closest sufficient statement to the
   source, with no unnecessary hypothesis or weakened conclusion and no change
   to a mathematical definition or game.
4. **Lean convergence:** the corrected statement type-checks and all affected
   downstream consumers compile. Lean success alone does not establish the
   preceding three conditions.

The operator iterates mathematics and Lean for at most ten `mathfix` sessions
or about one and a half working days per gap, whichever comes first. The budget
is shared across the owner-launched Fable lane and the future astra lane; a
model or telemetry change does not reset it. If the correction requires
changing a mathematical definition or game, the operator stops and escalates
immediately. If the ordinary budget expires without a converged correction,
#26 receives the attempted statements, counterexamples, proof sketches, and
unresolved consumer failures. A still-running attempt is not grounds to reset
the count.

An adopted correction follows the ordinary CI and independent-review gates. The
operator announces it in one line on progress log #27 and records it in the
paper-gap note, `results/telemetry/events.md`, and
`results/telemetry/design-decisions.md`. That announcement informs the owner; it
is not a request for a decision.
