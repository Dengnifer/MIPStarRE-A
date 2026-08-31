---
id: "0007"
title: "Adapt workflow to GitHub-native records"
state: "open"
state_reason: null
parent: null
children: []
labels: ["bug", "ci", "documentation", "infrastructure"]
pinned: false
created: "2026-08-31T13:48:38Z"
updated: "2026-08-31T14:22:05Z"
agent_session: null
---

## Current behavior

The local lifecycle scripts create and mutate only the committed registries under
`issues/` and `prs/`. Local CI and review record their conclusions only in PR
frontmatter and per-head artifacts. The repository has moved to the standalone
`Dengnifer/MIPStarRE-A` GitHub repository, but the operative scripts and normative
protocols still describe a local-only surface.

The migration seed maps local issues `#0001`, `#0004`, `#0005`, and `#0006` to
GitHub issues `#1` through `#4`, and local PR `#0003` to GitHub PR `#5`; see
`results/telemetry/github-migration-map.md`. The owner decision is recorded in the
2026-08-31 re-hybridization entry of `local/protocols/EVOLUTION.md` and in
`HANDOFF.md` step 0.

## Expected behavior

GitHub is the ordinary issue and PR surface for track A. The lifecycle tools use
`gh` to create and update GitHub issues and pull requests, post local CI commit
statuses, and post local review verdicts. The committed local registry remains a
complete write-through record and permits work to continue during transient link,
CLI, or authentication failures.

The integration must be retry-hardened, idempotent under a retry after an
ambiguous failure, and explicit about unsynchronized operations. It must never
turn a missing `gh`, missing authentication, or network outage into silent success.
The local merge gate remains authoritative for CI/review eligibility and must not
push or merge a head that has not passed that gate.

## Scope

- Adapt `issue_new.py` and `issue_close.py` to create/close GitHub issues while
  preserving atomic local records and parent/child bookkeeping.
- Adapt `pr_open.py` and `pr_merge.py` to publish branches and create/update the
  corresponding GitHub pull requests without weakening the local gate.
- Have `ci.sh` post a commit status for the exact checked head SHA.
- Have `review.sh` publish the exact-head review verdict and findings to the
  corresponding GitHub PR.
- Make `github-sync.sh` a retry-hardened push for the standalone repository.
- Add shared configuration, retry, idempotency, and offline-fallback machinery
  rather than duplicating shell fragments across entry points.
- Update `AGENTS.md`, `local/README.md`, `local/DESIGN.md`, the affected protocol
  documents, and `EVOLUTION.md` so the normative text matches enforcement.
- Add deterministic tests using a fake `gh`; tests must not mutate GitHub.

## Acceptance criteria

- Online create/update paths are demonstrated against a fake `gh`, including
  local-to-GitHub number mapping and repeated invocation after ambiguous failure.
- Offline and unauthenticated paths preserve a usable local record, emit an
  actionable warning, and retain enough state for an explicit retry/reconciliation.
- CI and review publication is bound to the same head SHA as the local manifest
  and verdict; stale-head publication is rejected.
- Merge remains impossible without green same-head local CI and an acceptable
  same-head local review.
- Existing migrated records use the seed mapping without creating duplicates.
- The issue tree and script tests pass, and no workflow test performs a real
  network mutation.

## Reproduction / environment

At project handoff on 2026-08-31, the `github` remote points to
`git@github.com:Dengnifer/MIPStarRE-A.git`. A `gh` binary exists under
`~/.local/bin`, but this main session initially had no `gh` on `PATH`, and
`gh auth status` reported no authenticated host. This is a required degraded
mode, not a reason to bypass the tracked adaptation.

## Initial classification

Applied by `local/bin/issue_new.py` (deterministic keyword pass, no model): `bug`, `ci`, `documentation`

## Activity

- GitHub issue [#6](https://github.com/Dengnifer/MIPStarRE-A/issues/6) was
  created from this local record during the write-through adapter transition.
