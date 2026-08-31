**Audit Result**

The GitHub-only migration is not yet operational. Root `issues/` and `prs/` are already absent, but 12 active executables still depend on them. `issue_new.py` and `housekeeping.sh standup` can recreate `issues/`; the remaining readers fail because the registries are gone. `local/labels.yml` also remains authoritative.

No files were changed and no GitHub request was made.

**Executable Inventory**

| Action | Exact files | Concrete finding |
|---|---|---|
| Retire | [track.py](/home/drx/MIPStarRE-qpbt/.worktrees/issue-0007-github-native-workflow/local/bin/track.py:635), [validate_tree.py](/home/drx/MIPStarRE-qpbt/.worktrees/issue-0007-github-native-workflow/local/bin/validate_tree.py:314), [export_issues.py](/home/drx/MIPStarRE-qpbt/.worktrees/issue-0007-github-native-workflow/local/bin/export_issues.py:85) | These are the registry data layer, registry consistency validator, and local-to-`gh` exporter. GitHub enforces issue identity, labels, and parentage; the stale auditor already accepts GitHub-shaped JSON. |
| Rewrite | [issue_new.py](/home/drx/MIPStarRE-qpbt/.worktrees/issue-0007-github-native-workflow/local/bin/issue_new.py:406), [issue_close.py](/home/drx/MIPStarRE-qpbt/.worktrees/issue-0007-github-native-workflow/local/bin/issue_close.py:61) | Replace sequence allocation, frontmatter, parent mutation, and activity sections with marker-based GitHub creation, label validation, sub-issue API calls, close reason, and optional comment. |
| Rewrite | [pr_open.py](/home/drx/MIPStarRE-qpbt/.worktrees/issue-0007-github-native-workflow/local/bin/pr_open.py:197) | It currently only creates `prs/<id>/pr.md`, `ci/`, and `reviews/`. It must push one explicit feature ref and create/adopt the unique GitHub PR. |
| Rewrite | [ci.sh](/home/drx/MIPStarRE-qpbt/.worktrees/issue-0007-github-native-workflow/local/bin/ci.sh:540), [review.sh](/home/drx/MIPStarRE-qpbt/.worktrees/issue-0007-github-native-workflow/local/bin/review.sh:364) | Both resolve PR state from `pr.md`. CI commits manifests; review writes verdict files. Replace those with exact-head statuses, runtime artifacts, marker comments, and one commit-bound review. Preserve all eight canonical CI steps and parallel review lanes. |
| Rewrite | [autofix.sh](/home/drx/MIPStarRE-qpbt/.worktrees/issue-0007-github-native-workflow/local/bin/autofix.sh:382), [pr_merge.py](/home/drx/MIPStarRE-qpbt/.worktrees/issue-0007-github-native-workflow/local/bin/pr_merge.py:406) | Replace local manifests, verdicts, counters, and flags with GitHub statuses, reviews, labels, and commit history. Remove direct `git merge`, registry-conflict handling, issue-closing bookkeeping, and `--allow-unreviewed`; merge only through guarded `gh pr merge`. |
| Rewrite | [agent.sh](/home/drx/MIPStarRE-qpbt/.worktrees/issue-0007-github-native-workflow/local/bin/agent.sh:246), [housekeeping.sh](/home/drx/MIPStarRE-qpbt/.worktrees/issue-0007-github-native-workflow/local/bin/housekeeping.sh:128) | Agent context must come from GitHub. Housekeeping standup and stale-audit must read paginated GitHub data; standup must stop writing root issue files. Linter and README jobs are otherwise independent. |
| Rewrite, adjacent | [github-sync.sh](/home/drx/MIPStarRE-qpbt/.worktrees/issue-0007-github-native-workflow/local/bin/github-sync.sh:13) | It currently retries every failure and runs forbidden `git push github --all`. Replace with explicit ref synchronization and the atomic audit snapshot. |
| Retire authority | [local/labels.yml](/home/drx/MIPStarRE-qpbt/.worktrees/issue-0007-github-native-workflow/local/labels.yml:1) | It explicitly declares itself the label source of truth. Any retained classification aliases must be advisory; every emitted label must be validated against paginated repository labels. |

`dispatch.sh`, `telemetry.py`, `main-session.sh`, `site.sh`, and the build-cache executables do not consume either root registry. `scripts/audit_stale_issues.py` should remain unchanged apart from receiving its JSON through the shared GitHub reader.

**Personas And Documents**

Eight personas contain active registry contracts and require rewriting: [main](/home/drx/MIPStarRE-qpbt/.worktrees/issue-0007-github-native-workflow/local/personas/main.md:25), [orchestrator](/home/drx/MIPStarRE-qpbt/.worktrees/issue-0007-github-native-workflow/local/personas/orchestrator.md:84), [prover](/home/drx/MIPStarRE-qpbt/.worktrees/issue-0007-github-native-workflow/local/personas/prover.md:23), [scout](/home/drx/MIPStarRE-qpbt/.worktrees/issue-0007-github-native-workflow/local/personas/scout.md:91), [reviewer](/home/drx/MIPStarRE-qpbt/.worktrees/issue-0007-github-native-workflow/local/personas/reviewer.md:93), [prose-reviewer](/home/drx/MIPStarRE-qpbt/.worktrees/issue-0007-github-native-workflow/local/personas/prose-reviewer.md:106), [blueprint](/home/drx/MIPStarRE-qpbt/.worktrees/issue-0007-github-native-workflow/local/personas/blueprint.md:67), and [splitter](/home/drx/MIPStarRE-qpbt/.worktrees/issue-0007-github-native-workflow/local/personas/splitter.md:105). `simplifier.md` has no registry dependency. Reviewer agents should still be denied direct GitHub mutation; the trusted wrapper publishes their runtime output.

The direct normative-document set is [AGENTS.md](/home/drx/MIPStarRE-qpbt/.worktrees/issue-0007-github-native-workflow/AGENTS.md:16), [local/README.md](/home/drx/MIPStarRE-qpbt/.worktrees/issue-0007-github-native-workflow/local/README.md:15), [local/DESIGN.md](/home/drx/MIPStarRE-qpbt/.worktrees/issue-0007-github-native-workflow/local/DESIGN.md:32), [issues-prs.md](/home/drx/MIPStarRE-qpbt/.worktrees/issue-0007-github-native-workflow/local/protocols/issues-prs.md:3), [ci.md](/home/drx/MIPStarRE-qpbt/.worktrees/issue-0007-github-native-workflow/local/protocols/ci.md:27), [review.md](/home/drx/MIPStarRE-qpbt/.worktrees/issue-0007-github-native-workflow/local/protocols/review.md:26), [autofix.md](/home/drx/MIPStarRE-qpbt/.worktrees/issue-0007-github-native-workflow/local/protocols/autofix.md:41), and [sessions.md](/home/drx/MIPStarRE-qpbt/.worktrees/issue-0007-github-native-workflow/local/protocols/sessions.md:166).

Additional active documentation omitted by name from the brief includes [README.md](/home/drx/MIPStarRE-qpbt/.worktrees/issue-0007-github-native-workflow/README.md:5), current-repository commands in [CONTRIBUTING.md](/home/drx/MIPStarRE-qpbt/.worktrees/issue-0007-github-native-workflow/docs/CONTRIBUTING.md:263) and [stale_issue_audit.md](/home/drx/MIPStarRE-qpbt/.worktrees/issue-0007-github-native-workflow/docs/stale_issue_audit.md:63), plus the obsolete `\localissue` definition in [command.tex](/home/drx/MIPStarRE-qpbt/.worktrees/issue-0007-github-native-workflow/docs/paper-gaps/command.tex:9).

Three active QPBT notes use `\localissue{0002}`: [combined-lines](/home/drx/MIPStarRE-qpbt/.worktrees/issue-0007-github-native-workflow/docs/paper-gaps/qpbt_combined-lines-error-term.tex:55), [dimension-divisibility](/home/drx/MIPStarRE-qpbt/.worktrees/issue-0007-github-native-workflow/docs/paper-gaps/qpbt_ld-dimension-divisibility.tex:56), and [symmetrization](/home/drx/MIPStarRE-qpbt/.worktrees/issue-0007-github-native-workflow/docs/paper-gaps/qpbt_symmetrization-attainment.tex:41). Migration telemetry says local issue `0002` was closed and not migrated, so these require an explicit historical-archive citation or a newly assigned GitHub issue. The legacy `\ghissue` and `\ghpr` macros must not be globally redirected because they intentionally cite LionSR history.

Historical `EVOLUTION.md` entries should remain intact; append the required superseding entry after [the fallback entry](/home/drx/MIPStarRE-qpbt/.worktrees/issue-0007-github-native-workflow/local/protocols/EVOLUTION.md:215). The interrupted write-through incident is already recorded accurately in [events.md](/home/drx/MIPStarRE-qpbt/.worktrees/issue-0007-github-native-workflow/results/telemetry/events.md:151), so it should not be duplicated.

**Dependencies And Gaps**

```text
shared GitHub layer
├── issue_new / issue_close / agent / housekeeping
├── pr_open
├── ci -> review -> autofix
├── statuses + review ledger -> pr_merge
├── github-sync -> audit snapshot
└── blueprint_lean_sync comment publication
```

- [blueprint_lean_sync.py](/home/drx/MIPStarRE-qpbt/.worktrees/issue-0007-github-native-workflow/scripts/blueprint_lean_sync.py:1070) is a second GitHub client using `urllib`, `GITHUB_TOKEN`, and soft failure. Its comment path and [tests](/home/drx/MIPStarRE-qpbt/.worktrees/issue-0007-github-native-workflow/scripts/tests/test_blueprint_lean_sync.py:827) should use the shared layer or be retired.
- Base-ref semantics affect [ci.sh](/home/drx/MIPStarRE-qpbt/.worktrees/issue-0007-github-native-workflow/local/bin/ci.sh:630), [pre-push](/home/drx/MIPStarRE-qpbt/.worktrees/issue-0007-github-native-workflow/.githooks/pre-push:38), [worktree-setup.sh](/home/drx/MIPStarRE-qpbt/.worktrees/issue-0007-github-native-workflow/local/bin/worktree-setup.sh:139), [cache-warmer.sh](/home/drx/MIPStarRE-qpbt/.worktrees/issue-0007-github-native-workflow/local/bin/cache-warmer.sh:523), `check_source_statement_changes.py`, and `blueprint_axiom_audit_needed.py`. They currently depend on synthetic `origin/main`; the real `github/main` ref must become one coherent fetched-base contract.
- Neither hook directly consumes a registry. However, [pre-commit](/home/drx/MIPStarRE-qpbt/.worktrees/issue-0007-github-native-workflow/.githooks/pre-commit:34) runs tests only for `scripts/` changes, while CI classifies only `ci.sh`, its protocol, and frozen workflow YAML as “workflow” changes. Changes to the shared layer or other lifecycle scripts can therefore skip the new suite.
- No current test creates or reads root `issues/` or `prs/`; there is consequently no regression protection. The two workflow tests inspect frozen `.github` precedent only.
- The brief leaves standup publication, post-create classification/scout orchestration, previous-review ledger carry-forward, and three-file snapshot generation atomicity underspecified. Each needs one deterministic remote/runtime contract, without introducing another authority.

**Fake-gh Matrix**

| Area | Deterministic cases and assertions |
|---|---|
| Shared layer | CLI precedence, repo env/remote discovery, harmless auth probe, headers, pagination, bounded retries for connection/timeout/429/5xx, no retry for permanent 4xx, token absent from argv/logs. |
| Issues | Successful create; ambiguous create then marker-based adoption; paginated labels; missing-label error; child database-ID lookup and sub-issue POST; both close reasons and optional comment. |
| PRs | Real temporary bare `github` remote; exact feature-ref push; assert no `--all` or `main` push; empty-diff refusal; create/adopt/update; GitHub-number footer. |
| CI | Eight `local-ci/*` contexts; pending then final; skipped as success; partial run publishes no gate set; marker-bound manifest update; local and remote head races. |
| Review | Exact `commit_id`; clean `COMMENT` plus successful summary; unresolved `REQUEST_CHANGES` plus failed summary; self-review rejection fallback; marker idempotency; moved-head refusal. |
| Auto-fix | Paginated labels/statuses/reviews/commits; exact-prefix iteration count; lock and supersession; cap removes opt-in label and posts one marked comment. |
| Merge | Refuse every missing, failing, stale, adverse, locked, over-cap, and incomplete-adjudication case; valid call is exactly guarded `gh pr merge --merge --match-head-commit`; assert no direct merge/main push/admin/auto mode. |
| Snapshot | Paginated issue and PR reads; remove PR objects from issue output; simulated failure leaves the prior generation intact; metadata published last; lifecycle commands never read snapshots. |
| Repository guard | Static scan plus runtime smoke in a temporary repository; assert no command creates root trees. Narrowly allow REST `/issues/...`, frozen precedent, explicit historical prose, and `registry-archive`; make hooks and workflow gating run this suite for every lifecycle/shared-layer change. |

No build or test suite was run because this was a read-only audit.