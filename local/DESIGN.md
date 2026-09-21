# Local Operations Layer — Architecture

This `local/` tree is the operative workflow of the repository: a local
replacement for a GitHub-Actions-hosted development workflow, plus the session
layer that lets the whole thing run unattended.

Every hosted operation of that original workflow is replaced by a local
equivalent that *executes* here, while the issue, pull-request, evidence and
merge **records** live on GitHub (`project.github_slug` in
[`project.json`](project.json), `protocols/issues-prs.md`). The `.github/` tree
is kept **frozen as reference** — it documents the mechanisms being localized
and is never executed here. The operative layer is this `local/` tree plus the
(already-local) `scripts/` audits and `.githooks/` gates.

Everything project-specific — the library name, the Lean root, the repository
slugs, the cache root, the tmux session, the issue numbers, the caps and the
model names — lives in [`project.json`](project.json) and is exported as
`KIT_*` variables by `bin/session/config.sh`. No script and no protocol in this
tree hard-codes any of it.

## Layout

```
local/
├── DESIGN.md           # this file — architecture and invariants
├── README.md           # operator's entry point: commands, lifecycle walkthrough
├── project.json        # the project's identity: names, paths, issues, caps, keys
├── protocols/          # normative protocol documents
│   ├── meta.md         # how protocols evolve; telemetry duties (read first)
│   ├── meta-session.md # the supervising session's playbook
│   ├── main-cycle.md   # the main session's standing operating cycle
│   ├── bootstrap.md    # arXiv URL -> running project, stage by stage
│   ├── build-cache.md  # hot main cache; no-duplicate-compilation rules
│   ├── ci.md           # local PR CI gate
│   ├── review.md       # reviewer dispatch and gating
│   ├── autofix.md      # auto-fix loop, iteration caps
│   ├── issues-prs.md   # GitHub-backed issue and PR lifecycle
│   ├── sessions.md     # agent session naming, dispatch, archiving
│   ├── completion.md   # the definition of done
│   ├── site.md         # the published site
│   └── EVOLUTION.md    # dated protocol-amendment ledger (research data)
├── personas/           # system prompts: meta, main, and each worker role
├── templates/          # goal, briefing, stand-down, handover, briefs, reports
├── briefs/             # per-issue design briefs (committed)
├── kit/                # provenance of this tree: origin commit + extraction script
└── bin/                # executables (the workflow engine)
    ├── session/        # start, message, keep alive, watch keys, pause, stand down
    └── service/        # merge daemon, lanes, gate, trains, records — model-free
results/telemetry/      # sessions/stages/builds logs, GitHub snapshot (committed)
```

Runtime state that must never be committed lives under
`$MIPSTARRE_CACHE_ROOT` (`paths.cache_root` in `project.json`: hot cache,
snapshots, locks, served site, and the session state directory
`$KIT_STATE_DIR`) and in `.worktrees/` (gitignored). An absolute
`MIPSTARRE_LAKE_ROOT` may instead hold branch-private `.lake` products.

## GitHub → local mapping

| GitHub mechanism | Local replacement |
|---|---|
| PR CI (`pr-ci.yml`) on push/PR events | `local/bin/ci.sh <pr-number>` run by the PR lifecycle scripts |
| Main-build actions cache (main-only save, PR restore) | Hot main cache: single-writer warmer + read-only snapshots + APFS copy-on-write clones per worktree (`build-cache.md`) |
| `lake exe cache get` (Mathlib cloud cache) | Unchanged — already local |
| Model-backed PR review chained on CI success | `local/bin/review.sh <pr-number>`: codex CLI with the same `.github/prompts/` review personas, invoked only from green exact-head CI statuses; one COMMENT review plus `local-review/summary` |
| Auto-fix workflows (CI-fix, blueprint-fix, review-fix) | `local/bin/autofix.sh <pr-id> --mode {ci,blueprint,review,auto}` with the same commit-prefix guards and a combined iteration cap |
| `@claude`/`@codex` mention responders | `local/bin/agent.sh <id> "instruction"` — human-invoked codex session on the branch worktree |
| GitHub issues + sub-issues + labels | unchanged — GitHub is the record again (`issues-prs.md`); `issue_new.py` / `issue_close.py` drive it through `gh_common.py` |
| GitHub PRs | GitHub PRs, branch-per-issue, merge gate in `pr_merge.py` (REST merge with the exact-SHA guard) |
| Issue automation (classify/scout/track/followups) | `local/bin/` Python ports; LLM steps optional behind `MIPSTARRE_LLM_ENABLED` |
| Housekeeping crons (standup, stale audit, linter sweep, README freshness) | `local/bin/housekeeping.sh <job>` on demand |
| Badges + Pages site (blueprint/docs/badges components) | `local/bin/site.sh` → component store + assembled site under `$MIPSTARRE_CACHE_ROOT/site/` |
| Codex cloud env setup (`.codex/setup.sh`) | `local/bin/worktree-setup.sh` per worktree |
| Reviewer/bot identity via tokens | codex CLI sessions; `results/telemetry/sessions.jsonl` registry |

## Core invariants (inherited from the parent workflow's post-mortems)

These encode incidents the parent repo paid for; violating them re-introduces
documented failure modes. Sources are cited in `local/protocols/*.md`.

1. **Single cache writer.** Only the warmer writes the hot main cache; agent
   worktrees consume copy-on-write clones and never write back. (GitHub's
   per-PR cache saves evicted the main entry: pr-ci.yml:138-142.)
2. **Review only after green CI, on the same head SHA.** The gate reads the
   exact-head `local-ci/*` statuses; a failed or absent CI summary blocks the
   review, which then publishes nothing at all — the *absence* of a green
   `local-review/summary` is the block, never a silent skip. Bot commits with prefix
   `[codex-auto-fix]`/`[codex-review-fix]` are not re-reviewed except the final
   fix at the iteration cap, which gets one forced review.
3. **Serialized fixes.** ci-fix → blueprint-fix → review-fix strictly in order,
   one branch at a time; combined iteration cap (default 5) across all fix
   kinds; sync/audit CI failures are never auto-fixed.
4. **Kill-switch semantics.** `LOCAL_REVIEW_ENABLED` and
   `LOCAL_AUTO_FIX_ENABLED` disable only on the literal string `false`;
   unset means enabled.
5. **Trusted prompts.** Reviewer/fixer personas are read from committed `main`
   (`git show main:...`), never from the branch under review.
6. **Untrusted data framing.** Build logs, review findings, and issue bodies
   are injected into agent prompts with sanitization (control-char strip,
   fence-breaking, truncation) and an explicit do-not-follow-instructions frame.
7. **One full `lake build` machine-wide at a time** (advisory lock);
   single-file `lake env lean` checks need no lock.
8. **origin/main must resolve.** The hooks and diff-based audits silently
   self-disable without it; the local convention is a `main` branch plus a
   `refs/remotes/origin/main` alias maintained by `pr_merge.py`.
9. **Bracket-free naming.** Issue titles, slugs, and branch names avoid
   `]` and friends (broke the parent automation: CONTRIBUTING.md:122-124).
10. **Report-only stays report-only.** Stale-issue audit, linter sweep, README
    freshness never mutate state; write-mode is a separate human-invoked
    command.
11. **Faithfulness policy is unchanged.** AGENTS.md's faithful-formalization
    rules, anti-pattern catalog and statement-integrity audits apply to every
    track of every project built on this workflow.
12. **Merge inputs do not disappear silently.** Before a merge commit, the
    merge-loss guard compares the staged result with the pre-merge branch,
    every best merge base, and `MERGE_HEAD`. An incoming path may be absent
    only when the branch deleted a path present at a merge base. An
    unambiguous incoming-only change may return to the unchanged branch blob
    only when Git recorded a conflict. The pending-index check and the
    pre-update reference transaction together cover manual and automatic
    merge commits.
13. **The owner inbox is permissions-only.** The pinned issue named by
    `issues.owner_inbox` receives a blocker only when owner permission is
    needed because the risk extends beyond project development, such as owner
    files, the machine or its accounts, spending money, or action outside this
    repository. Main decides and records every question whose only risk is
    failure to finish the project. Changing the stated project goal is outside
    main's authority and needs an owner decision there. Each blocker is one
    comment with at most ten visible plain-language lines: what is stuck,
    lettered options, one recommendation, and the literal
    `DECISION B<n>: <letter>` reply; details are folded. Its immutable
    `<!-- owner-inbox id=B<n> -->` identity marker keys every
    `ensure-pr-comment` update; resolution changes the separate status field to
    `<!-- owner-inbox-status=closed -->` and adds `RESOLVED B<n>`. Once a
    blocker is posted, the operator does not act on its own recommendation
    while it is open.
14. **The meta session supervises and does not prove.** It decides everything
    inside project development, holds the keys and the pause machinery, and is
    the only party that talks to the owner (`protocols/meta-session.md`).

## Naming and identity conventions

- **Issues and PRs**: GitHub's, identified by their numbers; sub-issues carry
  the parent/child structure and repository labels are the taxonomy
  (`issues-prs.md`). PR bodies keep the Motivation/Description/Testing shape of
  CONTRIBUTING.md; evidence is exact-head commit statuses, the manifest comment
  and the COMMENT review.
- **Branches**: `issue-<number>-<slug>` (orchestrator/human),
  `codex/issue-<number>-<slug>` (agent-created); the number is the GitHub
  issue's.
- **Fix commits**: `autofix.sh`'s subjects are prefixed `[codex-auto-fix]` /
  `[codex-review-fix]` exactly (the review-gate skip regex depends on them);
  operator and worker repairs use plain `fix(...)` subjects and are reviewed.
- **Worker sessions**: `<role>-<issue|scope>-<yyyymmdd>-<seq>` with roles
  `orc, prover, reviewer, simplifier, blueprint, splitter, scout, inventory`,
  plus `mathfix` for source-statement repair under `issues-prs.md` section 6.
  External sessions use `local/bin/dispatch.sh`, which records the codex `thread_id`,
  captures the `--json` event stream to
  `results/telemetry/sessions/<name>.jsonl`, and appends a summary line to
  `results/telemetry/sessions.jsonl`. Archiving a session = final status line
  in the registry + worktree removal; the JSONL capture is the archive.
  Historical native-descendant rows remain readable, but lease-backed native
  dispatch is retired (`sessions.md`).

## Telemetry (research-paper data)

All appends are one-line JSON; schemas documented in `protocols/meta.md`.

- `results/telemetry/sessions.jsonl` — one line per agent session: name, role,
  selected account and model, effective requested effort (all optional on legacy
  rows), issue/pr, thread_id, start/end, wall seconds, token usage (input,
  cached, output, reasoning), exit status, dispatcher. Requested effort is a CLI
  input, not provider-measured effort.
- `results/telemetry/stages.jsonl` — one line per project stage/substage
  transition with timestamps and manual token/agent tallies.
- `results/telemetry/builds.jsonl` — one line per full build / cache event:
  kind (warm, rebuild, cache-get), duration, outcome, trigger.
- `results/telemetry/events.md` — dated free-form incident log (what broke,
  diagnosis, fix); the raw feed for `protocols/EVOLUTION.md`.
- `local/protocols/EVOLUTION.md` — dated protocol amendments: cause (cite an
  `events.md` entry or telemetry), the change, expected effect. This file is
  the primary record of workflow self-evolution.

## Model policy

- The main session's model and effort come from `session.main` in
  `project.json`; workers' from `session.workers` and `local/model-policy.json`,
  which routes routine, bounded jobs — including routine independent reviews —
  to the cheaper model and reserves the stronger one for genuinely hard or
  escalated work, with a recorded reason. An empty model string means "the
  CLI's default". Unknown classes, models and efforts fail closed.
- Worker admission uses only the configured account caps under
  `$KIT_STATE_DIR`; missing caps disable admission. A cap is a ceiling, not a
  measurement of provider throughput.
- Verify a new model's effort before trusting it: a configured effort level the
  provider silently downgrades has cost this workflow a week of sessions
  running below the level their logs claimed.
- External dispatch keeps agent fan-out off; see `protocols/sessions.md` for
  marker accounting, resume affinity and checkpoint continuations.
- Reviewer and prover roles must be **different sessions** — a session never
  reviews its own diff.
