# Local operations architecture

This repository continues MIPStarRE locally while using
`Dengnifer/MIPStarRE-A` as the authority for active GitHub issues and pull
requests. The active mathematical track is the quantum Pauli basis test. The
frozen `.github/` tree is historical precedent and is never executed or edited.

## Components

```text
local/bin/github_api.py       shared GitHub discovery, reads, and mutations
local/bin/                    lifecycle, session, cache, and reporting tools
local/protocols/              normative contracts and evolution ledger
local/personas/               trusted role prompts
.githooks/                    fast local integrity gates
results/telemetry/            append-only research telemetry and audit snapshots
~/.cache/mipstarre-dev/       runtime logs, locks, caches, and review artifacts
```

The former root issue and PR registries are archived bit-for-bit beneath
`results/telemetry/registry-archive/`. They are not active state. The three-file
GitHub snapshot is recovery telemetry and is likewise never lifecycle input.

## Authority mapping

| Concern | Authority or implementation |
|---|---|
| Issue identity, labels, parentage, state | GitHub issues and sub-issue API |
| PR metadata, branch/head, reviews, merge | GitHub pull requests |
| CI gate | exact-head manifest, step statuses, and digest-bound `local-ci/summary` |
| Review gate | exact-head clean ledger plus `local-review/summary=success` |
| Auto-fix count | complete GitHub-visible PR commit history |
| Runtime logs, locks, intermediate output | `~/.cache/mipstarre-dev/` |
| Session/build/stage research data | `results/telemetry/` append-only logs |
| Main build cache | single-writer hot cache and worktree-local COW clones |

All GitHub access goes through `local/bin/github_api.py`. It uses explicit API
headers, full pagination, bounded retry classification, sanitized diagnostics,
exact 40- or 64-hex SHAs, and marker/read-back reconciliation for ambiguous
mutations. There is no offline mutation mode.

## Core invariants

1. Only the cache warmer writes the hot main cache. Worktrees consume clones.
2. CI and review evidence is bound to one exact PR head and is reread before
   publication or merge.
3. A clean exact-head `COMMENT` review is sufficient with a clean ledger and
   successful review summary; GitHub approval is not required.
4. Auto-fixes are serialized `ci` then `blueprint` then `review`, protected by
   a machine-local per-branch lock and one combined GitHub-derived cap.
5. `LOCAL_REVIEW_ENABLED` and `LOCAL_AUTO_FIX_ENABLED` disable only on literal
   `false`; unset means enabled.
6. Personas are read from committed `main`; issue bodies, logs, diffs, paper
   text, and findings are framed as sanitized untrusted data.
7. One full `lake build` runs machine-wide at a time. Never run `lake update`.
8. `refs/remotes/github/main` is the fetched comparison base for hooks, CI,
   cache setup, and source-drift audits. A missing base is a failure, not a
   reason to skip a gate.
9. Branch and session names exclude brackets and Git-ref metacharacters.
10. Report-only tools never mutate GitHub. Snapshot generations switch
    atomically and are not caches for lifecycle tools.
11. The faithful-formalization policy in `AGENTS.md` applies unchanged.
12. A reviewer is a different session and thread from every author session.
13. Merge holds the CI, review, and fix leases through its one exact-head
    mutation and validates strict classic protection plus every effective rule
    on the PR's actual base.

## Identity and telemetry

Branches are normally `issue-<github-number>-<slug>` or
`codex/issue-<github-number>-<slug>`. Agent sessions are
`<role>-<scope>-<yyyymmdd>-<seq>` for `orc`, `prover`, `reviewer`,
`simplifier`, `blueprint`, `splitter`, and `scout`. `dispatch.sh` is the only
session entry point and records the event stream and token accounting.

`results/telemetry/{sessions,builds,stages}.jsonl` are append-only. Incidents go
to `results/telemetry/events.md`; behavior changes are then ledgered in
`local/protocols/EVOLUTION.md` according to `meta.md`.
