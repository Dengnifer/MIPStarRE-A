# Meta-protocol — how this workflow evolves

Read this before any other protocol. It governs how the protocols themselves
change, and the telemetry duties that make the project usable as research data.

## Standing principles

1. **Protocols are normative until amended.** An agent that finds a protocol
   wrong, ambiguous, or costly does not silently deviate: it follows the
   protocol (or stops), records the friction in
   `results/telemetry/events.md`, and proposes an amendment.
2. **Amendments are evidence-driven.** Every change to a file under
   `local/protocols/` or to `AGENTS.md` must append an entry to
   `local/protocols/EVOLUTION.md` citing its trigger: an `events.md` incident,
   a telemetry observation (e.g. repeated duplicate builds in
   `builds.jsonl`), or an upstream policy decision by the user. No trigger,
   no amendment.
3. **The parent repo is precedent, not law.** The GitHub-era mechanism (frozen
   under `.github/`, mapped in `local/DESIGN.md`) is the default answer to
   "how should this work?"; deviations are fine when the local setting
   genuinely differs, and must be recorded in `EVOLUTION.md` with the reason.
4. **De-automation is a valid evolution step.** The parent workflow repeatedly
   demoted LLM agents to deterministic scripts once the mechanical half of a
   job was understood (issue-automation.yml:13-21), and demoted CI jobs to
   notices when resources were exhausted. Prefer the cheapest mechanism that
   holds the invariant.
5. **Two memory disciplines.** Reports and session records are append-only and
   never rewritten (supersede with dated status notes). Protocol documents
   and paper-gap notes are living documents that are rewritten in place
   (history lives in git and `EVOLUTION.md`). Do not mix the two.

## Amendment procedure

1. Write the incident/observation in `results/telemetry/events.md` (dated).
2. Draft the protocol edit.
3. Append to `local/protocols/EVOLUTION.md`:
   `## YYYY-MM-DD — <short title>` with fields **Trigger** (cite events.md
   entry or telemetry line), **Change** (files + gist), **Expected effect**,
   and, when known later, **Outcome**.
4. Commit protocol edit and ledger entry together, `docs(local)` scope.
5. If the change alters guard semantics (locks, caps, gates, kill switches),
   grep `local/` for every enforcement point and update all of them in the
   same commit — the parent repo maintained such consistency invariants
   through cross-referencing comments; we inherit the same drift risk.

## Telemetry duties

Schemas (all JSONL, one object per line; timestamps ISO-8601 with offset):

- `results/telemetry/stages.jsonl` —
  `{ts, stage, event: start|end|milestone, note?, tokens_note?}`
  Stages: `1-skeleton`, `2-references`, `3-blueprint`, `4.1-minimal`,
  `4.2-full-skeleton`, `4.3-proofs` (extend as needed).
- `results/telemetry/sessions.jsonl` —
  `{name, role, issue, pr?, thread_id, start, end, wall_s,
    usage: {input, cached_input, cache_write, output, reasoning},
    exit, dispatcher, worktree, status: active|done|failed|archived}`
  Written only by `local/bin/dispatch.sh` / `telemetry.py`.
- `results/telemetry/builds.jsonl` —
  `{ts, kind: warm|rebuild|cache-get|ci-build, trigger, seconds, outcome,
    sha?, note?}`
- `results/telemetry/events.md` — dated bullets; free prose; one incident per
  bullet: symptom → diagnosis → fix → lesson.

Duties:

- **Every agent session goes through `dispatch.sh`** so token usage and wall
  time land in `sessions.jsonl`. A session started any other way is a
  telemetry hole; if one happens, backfill a line with `dispatcher: manual`.
- **Every full build** (warmer, CI, cold rebuild) lands in `builds.jsonl`.
- **Stage transitions** are logged by the orchestrator (main session) at the
  moment they happen, not reconstructed later.
- Claude-side (non-codex) subagent fleets are summarized into `stages.jsonl`
  as `milestone` entries with token totals, since they bypass `dispatch.sh`.

## Research-data invariants

The project doubles as a study of a self-evolving formalization workflow.
Three artifacts must therefore stay trustworthy:

- `EVOLUTION.md` — complete: every protocol change has an entry.
- `events.md` — honest: failures are recorded as failures, including agent
  mistakes, wasted builds, and reverted work.
- `sessions.jsonl` + `stages.jsonl` — quantitative: per-stage cost
  (time, tokens, session counts) reconstructible by a script, not by memory.
