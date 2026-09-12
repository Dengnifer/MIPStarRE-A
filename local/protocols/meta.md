# Meta-protocol — how this workflow evolves

Read this before any other protocol. It governs how the protocols themselves
change, and the telemetry duties that make the project usable as research data.

## Standing principles

1. **Protocols are normative until amended.** An agent that finds a protocol
   wrong, ambiguous, or costly does not silently deviate: it follows the
   protocol (or stops), records the friction in
   `results/telemetry/events.md`, and proposes an amendment — a dispatched
   worker proposes it to the operator; the operator amends directly under the
   procedure below, an `events.md` incident being a sufficient trigger.  Owner
   sign-off is needed only for the escalations named in the standing briefing.
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
  `{name, role, model?, account?, requested_effort?, issue, pr?, thread_id,
    start, end, wall_s, usage: {input, cached_input, cache_write, output, reasoning},
    exit, dispatcher, worktree, status: active|done|failed|archived|refused,
    endpoint, failure_class, failure_detail?, failure_endpoint?, retries_seen,
    key_label?, override_mode?, override_source?}`
  Written only by `local/bin/dispatch.sh` / `telemetry.py`. New dispatches always
  supply `account` (`primary` or `second`) and the exact resolved `model`
  passed to the CLI (environment override, otherwise selected-account config).
  External rows use allocator accounts `primary|second`; native rows use the
  active key label (`space` or historical `relay-1`) in both `account` and
  `key_label`, with `dispatcher: native`.
  `status: refused` means the dispatch was never admitted, or died before any
  model turn: it is **not** a failed attempt and must not be scored against a
  proof packet's budget. `failure_class` is one of `none`, `refused`,
  `endpoint_down`, `concurrency_limit`, `endpoint_5xx`, `retries_exhausted`,
  `timeout`, `task_failure`, `unknown` (`sessions.md` §4.1); `unknown` is the
  safe default and the capacity controller treats it as neutral. `key_label` is
  recorded for **both** accounts and matches `[a-z0-9.-]{1,40}`; `endpoint` is
  on every row, so a key moved between homes keeps the identity failures and
  health are attributed to. `override_mode` / `override_source` appear only
  while an owner model override is in force, and the Sol:Astra ratio audit
  **excludes** those rows rather than reading them as violations.
  When the dispatcher supplies a reasoning override, `requested_effort` is its
  effective value after model-specific normalization. It records the CLI request,
  not provider-measured effort. All three fields remain optional for historical
  rows and legacy replay callers.
- `results/telemetry/owner-sessions.jsonl` —
  `{name, role, model, issue, pr?, worktree?, base?, start, end?, wall_s?,
    status, tokens?, tool_uses?, findings_fixed?, commits?, note?}`.
  Written only by the owner session and `/tmp/claude-lane-prep.sh` /
  `/tmp/claude-lane-finish.sh`; `tokens` is the harness-reported subagent total.
  For `role: mathfix`, `issue` identifies the gap whose shared budget is charged.
- `results/telemetry/builds.jsonl` —
  `{ts, kind: warm|rebuild|cache-get|ci-build, trigger, seconds, outcome,
    sha?, note?}`
- `results/telemetry/events.d/<YYYY-MM-DD>-<session>.md` — dated bullets; free
  prose; one incident per bullet: symptom → diagnosis → fix → lesson. **This is
  where new bullets go.** `telemetry.py event` writes the shard for (today, the
  writing session), so two sessions never touch one path and a merge of `main`
  cannot conflict on the log — append-only telemetry conflicted on nearly every
  merge on 2026-09-12. The shard label is `MIPSTARRE_SESSION` (or `--session`).
- `results/telemetry/events.md` — the same log before sharding. It keeps its
  full history and is **never rewritten**; it carries a header pointing at
  `events.d/`. Read the two together with
  `telemetry.py events --since YYYY-MM-DD [--until D] [--format md|json]`,
  which merges them in date order; every existing reader that greps `events.md`
  still finds the history it always found.

Duties:

- **Every external Codex session goes through `dispatch.sh`** so token usage and wall
  time land in `sessions.jsonl`. A session started any other way is a
  telemetry hole; if one happens, backfill a line with `dispatcher: manual`.
- **Incidents go to `events.d/`**, one shard per (date, session), through
  `telemetry.py event`. Never hand-append to `events.md`: it is the pre-shard
  history and is not rewritten.
- **The recorded model is the model that ran.** No tool may rewrite a model
  between the policy's selection and the CLI — a PATH shim that did so on
  2026-09-12 made `sessions.jsonl` name a model no session used. A run-wide
  model decision is a policy override (`override_mode`, `override_source`).
- Historical native descendants were recorded with `telemetry.py native-record`
  under `sessions.md`:
  `dispatcher: native`, root/parent IDs, key label, actual model/requested effort,
  worktree, timestamps and status. `observed_usage` preserves raw cumulative rollout
  counters, but `usage` remains null with `usage_scope: unknown`; parent inclusion
  of descendants is unverified. Never convert missing usage to zero or sum these
  observations. Private homes and credential data are not serialized. Requested
  CLI Ultra is distinct from wire/returned Max seen in owner migration receipts;
  absent request-specific wire evidence stays null, not inferred from configuration.
- **Every full build** (warmer, CI, cold rebuild) lands in `builds.jsonl`.
- **Stage transitions** are logged by the orchestrator (main session) at the
  moment they happen, not reconstructed later.
- Claude-side (non-Codex) subagent fleets are recorded in
  `owner-sessions.jsonl` and summarized into `stages.jsonl` as `milestone`
  entries with token totals, since they bypass `dispatch.sh`.

## Research-data invariants

Model-policy records (#301) retain `requested_model`, `selected_model`,
`effective_model` only when observed, `job_class`, and `model_policy` with
routine/hard classification and the explicit hardness/escalation rationale.
External capture without model evidence records effective model as null, not the
CLI argument. Historical native observations retain all bound current-turn contexts; mixed
models/efforts and requested/observed mismatches fail closed. Prior/forked contexts
are not attributed to a new job. Requested effort remains distinct from provider
effort; missing usage remains unknown and historical records are not rewritten.
`dispatch_kind` is new/resume/grandfathered; `activation_at` fixes the accounting
boundary. Ratio reports count actual distinct new threads with matching observed
and selected models, with a rolling 100-dispatch window and separate cumulative
counts. Unknowns may resolve from later observations; conflicts remain unknown.
Main, pre-activation workers and resumes do not count. Preserve predecessor and
cumulative-budget links recorded when a model change required a fresh native identity.

The project doubles as a study of a self-evolving formalization workflow.
Three artifacts must therefore stay trustworthy:

- `EVOLUTION.md` — complete: every protocol change has an entry.
- `events.md` + `events.d/` — honest: failures are recorded as failures,
  including agent mistakes, wasted builds, and reverted work.
- `sessions.jsonl` + `stages.jsonl` — quantitative: per-stage cost
  (time, tokens, session counts) reconstructible by a script, not by memory.
