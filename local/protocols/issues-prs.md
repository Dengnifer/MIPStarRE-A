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

Every GitHub call goes through `local/bin/gh_common.py` — a module for Python
callers, and for the shell scripts a CLI (`pr-view`, `post-status`,
`latest-statuses`, `ensure-pr-comment`, `post-review`, `merge-pr`,
`issue-create`, `issue-close`, `snapshot`, …; `--help` lists them) owning CLI
discovery, repository resolution, API version headers, bounded retry of
transient failures and the exit-2-with-stderr convention. Nothing else shells
out to `gh`. `issue_new.py`, `issue_close.py`, `pr_open.py`, `ci.sh`,
`review.sh`, `autofix.sh`, `pr_merge.py`, `github-sync.sh` take GitHub numbers;
`track.py`, `validate_tree.py` and `export_issues.py` are deleted.

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
4. that SHA's marker-bound `COMMENT` review carries `VERDICT: APPROVED`, or
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
(`open-issues.json`, `open-pulls.json`, `metadata.json`; PRs filtered out of the
issue endpoint) — audit and recovery telemetry, never lifecycle input. The
retired trees stay archived under `results/telemetry/registry-archive/` (commit
c8f1999): read-only research data, never edited or read as active input.
