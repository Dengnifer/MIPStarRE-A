# Local Operations Layer — Architecture

This repository is a local-only continuation of the workflow that
[LionSR/MIPStarRE](https://github.com/LionSR/MIPStarRE) evolved on GitHub while
formalizing the low individual degree test (LDT, arXiv:2009.12982). The active
track here is the **quantum Pauli basis test (QPBT)** from MIP\*=RE
(arXiv:2001.04383, primary) and NEEXP in MIP\* (arXiv:1904.05870, secondary).

Every GitHub-hosted operation of the parent workflow is replaced by a local
equivalent. The `.github/` tree is kept **frozen as reference** — it documents
the mechanisms being localized and is never executed here. The operative layer
is this `local/` tree plus the (already-local) `scripts/` audits and
`.githooks/` gates, which port unchanged.

## Layout

```
local/
├── DESIGN.md          # this file — architecture and invariants
├── README.md          # operator's entry point: commands, lifecycle walkthrough
├── protocols/         # normative protocol documents
│   ├── meta.md        # how protocols evolve; telemetry duties (read first)
│   ├── build-cache.md # hot main cache; no-duplicate-compilation rules
│   ├── ci.md          # local PR CI gate
│   ├── review.md      # reviewer dispatch and gating
│   ├── autofix.md     # auto-fix loop, iteration caps
│   ├── issues-prs.md  # issue tree and PR registry
│   ├── sessions.md    # agent session naming, dispatch, archiving
│   └── EVOLUTION.md   # dated protocol-amendment ledger (research data)
├── personas/          # system prompts for locally dispatched agents
└── bin/               # executables (the workflow engine)
issues/                # dynamic issue tree (committed)
prs/                   # PR registry (committed)
results/telemetry/     # sessions/stages/builds logs (committed)
```

Runtime state that must never be committed lives in `~/.cache/mipstarre-dev/`
(hot cache, snapshots, locks, served site) and `.worktrees/` (gitignored).

## GitHub → local mapping

| GitHub mechanism | Local replacement |
|---|---|
| PR CI (`pr-ci.yml`) on push/PR events | `local/bin/ci.sh <pr-id>` run by the PR lifecycle scripts |
| Main-build actions cache (main-only save, PR restore) | Hot main cache: single-writer warmer + read-only snapshots + APFS copy-on-write clones per worktree (`build-cache.md`) |
| `lake exe cache get` (Mathlib cloud cache) | Unchanged — already local |
| Model-backed PR review chained on CI success | `local/bin/review.sh <pr-id>`: codex CLI with the same `.github/prompts/` review personas, invoked only from a green `ci.sh`; verdict files under `prs/<id>/reviews/` |
| Auto-fix workflows (CI-fix, blueprint-fix, review-fix) | `local/bin/autofix.sh <pr-id> --mode {ci,blueprint,review,auto}` with the same commit-prefix guards and a combined iteration cap |
| `@claude`/`@codex` mention responders | `local/bin/agent.sh <id> "instruction"` — human-invoked codex session on the branch worktree |
| GitHub issues + sub-issues + labels | `issues/` markdown tree with YAML frontmatter (`issues-prs.md`); `labels.yml` taxonomy |
| GitHub PRs | `prs/` registry, branch-per-issue, merge gate in `pr_merge.py` |
| Issue automation (classify/scout/track/followups) | `local/bin/` Python ports; LLM steps optional behind `MIPSTARRE_LLM_ENABLED` |
| Housekeeping crons (standup, stale audit, linter sweep, README freshness) | `local/bin/housekeeping.sh <job>` on demand |
| Badges + Pages site (blueprint/docs/badges components) | `local/bin/site.sh` → component store + assembled site in `~/.cache/mipstarre-dev/site/` |
| Codex cloud env setup (`.codex/setup.sh`) | `local/bin/worktree-setup.sh` per worktree |
| Reviewer/bot identity via tokens | codex CLI sessions; `results/telemetry/sessions.jsonl` registry |

## Core invariants (inherited from the parent workflow's post-mortems)

These encode incidents the parent repo paid for; violating them re-introduces
documented failure modes. Sources are cited in `local/protocols/*.md`.

1. **Single cache writer.** Only the warmer writes the hot main cache; agent
   worktrees consume copy-on-write clones and never write back. (GitHub's
   per-PR cache saves evicted the main entry: pr-ci.yml:138-142.)
2. **Review only after green CI, on the same head SHA.** A failed CI yields
   `review_state: blocked`, never a silent skip. Draft/bot commits with prefix
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
    rules, anti-pattern catalog, and statement-integrity audits apply to QPBT
    exactly as to LDT.

## Naming and identity conventions

- **Issues**: `issues/NNNN-slug.md`, 4-digit zero-padded id from `issues/.seq`.
  Frontmatter: `id, title, state (open|closed), state_reason
  (completed|not-planned|null), parent, children, labels, pinned, created,
  updated, agent_session`. Labels validated against `local/labels.yml`.
- **PRs**: `prs/NNNN-slug/` directory with `pr.md` (frontmatter: `id, branch,
  issue, base, state (open|merged|closed), head_sha, ci_status, review_state,
  fix_iterations, auto_fix, labels, created, merged_commit`; body =
  Motivation/Description/Testing per CONTRIBUTING.md), `ci/` (per-SHA result
  manifests), `reviews/` (per-SHA verdict files).
- **Branches**: `issue-<id>-<slug>` (orchestrator/human), `codex/issue-<id>-<slug>`
  (agent-created). The `issue-(\d+)` regex stays load-bearing for tracking.
- **Fix commits**: subjects prefixed `[codex-auto-fix]` / `[codex-review-fix]`
  exactly (the review-gate regex depends on them).
- **Agent sessions**: `<role>-<issue|scope>-<yyyymmdd>-<seq>` with roles
  `orc, prover, reviewer, simplifier, blueprint, splitter, scout`. Dispatched
  only via `local/bin/dispatch.sh`, which records the codex `thread_id`,
  captures the `--json` event stream to
  `results/telemetry/sessions/<name>.jsonl`, and appends a summary line to
  `results/telemetry/sessions.jsonl`. Archiving a session = final status line
  in the registry + worktree removal; the JSONL capture is the archive.

## Telemetry (research-paper data)

All appends are one-line JSON; schemas documented in `protocols/meta.md`.

- `results/telemetry/sessions.jsonl` — one line per agent session: name, role,
  issue/pr, thread_id, start/end, wall seconds, token usage (input, cached,
  output, reasoning), exit status, dispatcher.
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

- codex CLI (`gpt-5.6-sol`, ultra effort) drives orchestrator/prover/reviewer/
  simplifier sessions (`codex exec`, `codex exec review`).
- Claude-side subagents: easy/mechanical tasks run on Opus-tier; Fable-tier is
  reserved for hard reasoning (proof strategy, protocol synthesis, adversarial
  verification).
- Reviewer and prover roles must be **different sessions** — a session never
  reviews its own diff.
