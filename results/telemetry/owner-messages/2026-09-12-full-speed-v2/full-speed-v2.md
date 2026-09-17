# Full speed mode v2 — design

**Status:** design, not yet implemented. Written 2026-09-12 after the full speed run
04:17Z–08:33Z (`snapshot/run-summary.md`), from four audits of the run
(capacity/accounts, merge throughput, lanes/dispatch/self-repair, owner interface).

**Goal.** The owner gives ONE briefing at the start of a run — keys and their limits,
duration or "until my word", speed tier, pause deadline — and afterwards receives only
the half-hourly one-line estimate on the estimate issue and prose progress on the
progress log. Every intervention the owner made on 2026-09-12 becomes an automatic
mechanism, a single-file switch, or a self-healing loop, and every fix lives in the
repository (`local/bin`, `local/protocols`, `local/personas`,
`results/telemetry/owner-tools`) rather than in `/tmp`.

**Binding constraints** (AGENTS.md, `local/protocols/*`, `local/DESIGN.md`):

- Proof-integrity mechanisms are untouchable: `.githooks/pre-commit`,
  `.githooks/pre-push`, `.githooks/reference-transaction`, `local/bin/merge_loss_guard.py`,
  `local/bin/checked-push.sh`, the seven `pr_merge.py` gates, the eight canonical
  `local-ci/<step>` contexts and the `local-review/summary` contract. Nothing in this
  design changes any of them. Where a current tool *bypasses* one
  (`MIPSTARRE_SKIP_HOOKS=1` in the lane runner's fallback push), this design deletes
  the bypass, which strengthens the gate rather than altering it.
- Every repository change goes through a reviewed PR that closes an issue; one PR per
  issue; the merge daemon alone calls `pr_merge.py`.
- Runtime state stays under `~/.cache/mipstarre-dev/`; nothing runtime is committed.
- Agents never invoke `codex` directly; worker sessions go through `local/bin/dispatch.sh`.
- Workflow work is a cost, not an achievement: `local/personas/main.md` §Scope control
  (≤2 h and ≤1000 changed lines per workflow change) applies to every work item below;
  each item is sized to stay inside it.

**Non-goals.** No new abstraction layer, no framework, no daemon supervisor beyond the
single loop that already exists, no rewrite of reviewed code. The merge train
(`pr_train.py`, issue #502 / PR 507) stays where it is — see §9 Deferred.

---

## 0. The control loop in one picture

```
              run-brief.json  (owner writes once)
                     |
                run_mode.py apply
                     |
        watchdog/run-mode.json  ── speed ──> codex shim (service_tier)
                     |         ── caps ───> capacity_controller.py
                     |         ── issues ─> estimate_post.py / ready_report.py
                     |         ── target ─> goal-keeper.sh, main persona
                     v
   capacity_controller.py  <── refusals/deaths per endpoint (telemetry.py failure_class)
        |  writes max-codex-{primary,second}, max-codex, health-<account>.json
        v
   account_router.reserve  <── dispatch.sh (spool + retry, branch claim)
        |
        v
   lane.sh ──> ci.sh ──> review.sh ──> merge-daemon.sh ──> pr_merge.py (gates unchanged)
        |                                    |
        `── needs-attention marker ──> janitor.sh ──> orc repair / requeue / retire
```

Two rules make this a loop rather than a pile of scripts:

1. **Every number the owner states lives in exactly one file** (`run-brief.json`), and
   every component reads it through one tool (`run_mode.py get KEY`). Nothing is
   transcribed by hand into a second place.
2. **Every failure writes a classified, machine-readable record**, and exactly one
   component consumes each class. Nothing is rediscovered by `grep` on the day.

---

## 1. The owner's one-time briefing and the mode file

### 1.1 The briefing

Template committed at `results/telemetry/owner-tools/run-brief.template.json`. The owner
copies it to `~/.cache/mipstarre-dev/watchdog/run-brief.json` and edits the values. This
is the only artifact the owner authors for a run.

```json
{
  "schema": "mipstarre-run-brief/1",
  "run": {
    "label": "full speed 2026-09-13",
    "start": "2026-09-13T04:00:00Z",
    "dispatch_cutoff": "2026-09-13T08:00:00Z",
    "pause_deadline_min": 15,
    "speed": "fast",
    "occupancy_target": 0.8,
    "progress_issue": 27,
    "estimate_issue": 168,
    "owner_inbox_issue": 500
  },
  "accounts": [
    { "name": "primary", "label": "relay-us7",
      "endpoint": "relay-us7", "codex_home": "~/.codex",
      "nominal_limit": 5, "external_reserved": 0, "enabled": true },
    { "name": "second", "label": "space",
      "endpoint": "api.finite-dimensional.space",
      "codex_home": "~/.cache/mipstarre-dev/codex-home-yxy",
      "nominal_limit": 30, "external_reserved": 2, "enabled": true }
  ],
  "models": { "override": null }
}
```

Field semantics, all of them answers to a question the owner had to answer by message
on 2026-09-12:

| Field | Replaces | Meaning |
|---|---|---|
| `accounts[].nominal_limit` | "5 on the primary; 10 → 40 → 20 → 30 on yxy" | A **ceiling**, never a target. The controller may sit below it forever and must never go above it. |
| `accounts[].external_reserved` | "the forked local session shares the yxy key; limit it to 2" | Slots on that key the pipeline must not use. Subtracted from the ceiling. |
| `accounts[].endpoint` | manual capture forensics | The label failures and health are attributed to, so a key moved between homes keeps its identity. |
| `accounts[].enabled` | `echo 0 > max-codex-primary` | `false` means the pipeline never dispatches there at all. |
| `run.dispatch_cutoff` | "work 4 h, extend 1 h, finalize" | After it, no new dispatch starts; running work finishes. The literal string `"until my word"` is accepted and means no cutoff. |
| `run.pause_deadline_min` | "pause within 15 minutes" | The deadline budget for §5. |
| `run.speed` | three hand patches of the shim | `fast` sets `service_tier="priority"` in the shim and the 30-minute estimate cadence; `default` unsets both. |
| `run.occupancy_target` | "should be close to 30", "40 or more", "32 or more" | A fraction of the effective cap. `run_mode.py get floor` returns the integer floor everything quotes. |
| `run.progress_issue` / `estimate_issue` / `owner_inbox_issue` | prose | Validated once; `estimate.sh` fails loudly instead of silently no-op'ing on a missing `watchdog/estimate-issue`. |
| `models.override` | the `sol->astra` rewrite hidden in the PATH shim | `null` = published `local/model-policy.json`; `"astra-all"` = every role runs the hard model, recorded in telemetry (§2, L2). |

### 1.2 The mode file

`local/bin/run_mode.py` is the only writer of `~/.cache/mipstarre-dev/watchdog/run-mode.json`.

- `run_mode.py apply [--brief PATH]` — validates the brief (unknown key, missing
  endpoint, non-integer limit, `external_reserved >= nominal_limit`, occupancy > 1,
  unknown speed, unknown override, issue numbers not positive integers all fail), writes
  `run-mode.json` atomically (temp file + `os.replace`), derives the cap files, appends a
  `stages.jsonl` row with the brief's `sha256`, and appends one row to
  `results/telemetry/design-decisions.md`.
- `run_mode.py show` — human-readable dump; used to render the goal-keeper's goal text
  and the main session's cycle text, so no literal caps are ever embedded in a script.
- `run_mode.py get KEY` — one value on stdout (`speed`, `floor`, `cap.primary`,
  `endpoint.second`, `progress_issue`, …). This is the single accessor every other
  component uses.
- `run_mode.py set speed fast|default` — the mid-run speed switch. Regenerates the PATH
  shim from the committed template; refuses (printing the diff) when the live shim
  differs from the template, so an emergency hand-edit is never silently discarded.
- `run_mode.py pause` / `resume` — §5.

**Derived cap files.** `run-mode.json` is the record; `watchdog/max-codex-primary`,
`max-codex-second` and `max-codex` remain as *derived outputs* so
`account_router.py` and the lane runner need no change in the same PR. The starting cap
per account is

```
cap0 = clamp(1, nominal_limit - external_reserved, last_measured_limit or nominal_limit - external_reserved)
```

and `max-codex` is mechanically the sum of the effective per-account caps. It has **no
admission meaning** (the router reads only the per-account files) and is kept because
`status-snapshot.sh` and the lane runner's `cap()` read it; `local/protocols/capacity.md`
says so in one sentence and `sessions.md` §4.1 cross-references it.

**Failure behaviour.** A missing or invalid brief is a hard, loud failure at `apply`
time — never "zero capacity" and never "unlimited". The message names the template path
and the exact destination path. `run_mode.py` refuses to write an empty or non-numeric
cap file under any circumstance; the current `/tmp/owner-resume.sh` would write empty cap
files today and every dispatch would exit 4 with `invalid literal for int()`. That latent
break is fixed by construction.

---

## 2. Every owner intervention, its mechanism, its knobs, its failure behaviour

The eight items are `run-summary.md` §"Owner interventions this time".

### Item 1 — Capacity: limits restated, ~90 dead sessions, ten hand cap edits

**Mechanism: an AIMD capacity controller with per-endpoint health.**

| | |
|---|---|
| **Component** | `local/bin/capacity_controller.py`, supervised by `results/telemetry/owner-tools/capacityd.sh` (60 s tick), installed by the versioned installer (§7). |
| **Inputs** | `run-mode.json` (ceiling, `external_reserved`, `enabled`, endpoint); `results/telemetry/sessions.jsonl` rows carrying `failure_class` and `endpoint` (see Item 7 below and §2/L-series); `accounts/<account>/` live markers. |
| **Knob file** | `local/capacity-policy.json` (committed): per account `{floor, ceiling_source: "brief", aimd: {increase: 1, quiet_window_s: 120, decrease: 0.75}, health: {fivexx_threshold: 3, fivexx_window_s: 120, probe_backoff_s: 30, probe_backoff_max_s: 600, probes_to_recover: 2}}`, plus `failure_patterns` (the provider strings) and `priority_classes` (reserved for the deferred admission ordering). |
| **Runtime state** | `watchdog/capacity/state.json` (the record), `watchdog/capacity/health-<account>.json`, `watchdog/capacity/limit-estimate.json`; the three `max-codex*` files are derived outputs of the same writer. |
| **Increase** | `refusals_5m == 0 and deaths_5m == 0 and live >= cap - 1` for a full `quiet_window_s` → `cap += 1`. One slot per window, never more. |
| **Decrease** | On the **first** refusal: `cap = max(floor, min(cap, live_at_first_refusal - 1))`. On a further refusal inside the same window: `cap = max(floor, ceil(cap * 0.75))`. |
| **Endpoint down** | `endpoint_5xx` deaths ≥ 3 within 120 s → health `down`, cap 0 immediately, independent of AIMD. This is the 05:30Z–05:58Z relay-us7 outage that cost 69 sessions and was answered by a human typing `echo 0`. |
| **Recovery** | Half-open: after `probe_backoff_s` (doubling to 10 min) one `codex exec --sandbox read-only`, trivial prompt, that account's `CODEX_HOME`, `timeout 60`, single-flight under a lock. Two consecutive successes → cap 1, then AIMD climbs. One failure doubles the backoff. |
| **Failure behaviour** | `unknown` failure class is **neutral** — neither increase nor decrease — so a provider wording change degrades to today's static behaviour instead of collapsing the cap. A malformed `capacity-policy.json` or `run-mode.json` makes the controller exit nonzero and leave the cap files untouched; the supervisor logs and retries. Two writers are impossible by protocol: the controller is the sole writer, and `watchdog/capacity/hold` (an operator touch-file) freezes the cap where it is without stopping health handling. |
| **Owner input still needed** | Only the brief's `nominal_limit`, `external_reserved`, `endpoint` per key — once, before the run. |

**Undeclared sharers** (the forked Claude session on the owner's Mac) need no
identification: they appear as refusals and AIMD walks the cap down. The gap is recorded
as `external_inferred = nominal_limit - external_reserved - measured_limit` in
`limit-estimate.json` and printed by `status-snapshot.sh`, so a persistent invisible
consumer is a number rather than a mystery.

**Carrying the measurement forward.** `limit-estimate.json` records `measured_limit` (the
highest concurrency sustained ≥10 min with zero refusals) and `observed_refusal_floor`.
`run_mode.py apply` seeds the next run's starting cap at
`min(nominal - external_reserved, last_measured_limit)`, so a run starts *below* the cliff
instead of above it. The measured limits are written into the pause handoff (§5).

### Item 2 — Occupancy: idle slots, dead fixers, a hand-fed queue

Four distinct causes, four mechanisms:

| Cause (observed) | Mechanism | Knob / failure behaviour |
|---|---|---|
| `model_policy.py` rejects an explicit astra request for routine jobs, so the owner's "all workers astra" could only be done by a shim rewrite that made `sessions.jsonl` record `sol` for astra sessions | `models.override` in the brief → `watchdog/model-override` runtime knob + an `override` object accepted by `load_policy`. When active, `select_model` returns `policy.hard_model` for every role/job class and stops rejecting an explicit astra request; `override_mode` and `override_source` travel into the per-session model-policy file and into `sessions.jsonl`. The `sol->astra` rewrite is deleted from the shim. | The override may only narrow **toward** the hard model and may never lower effort. Override-period rows are excluded from the Sol:Astra ratio audit by their `override_mode` field rather than read as violations. |
| `autofix.sh` defaults `MIPSTARRE_FIX_MODEL=gpt-6-astra`, which the policy preflight rejects, so every fixer died at exit 4 before reaching a model | `FIX_MODEL="${MIPSTARRE_FIX_MODEL:-}"` (empty = dispatcher default, which is what the script's own header documents). Genuinely hard fixes use `--job-class escalated --hardness-reason "…"`, not a bare model. | A startup self-check runs `model_policy.py --role prover --job-class general --model "$FIX_MODEL" --field model` once and dies with the policy's own message before any worktree work — one loud line instead of N silent deaths. Same guard in `review.sh`. |
| Lanes serialize behind one global launch lock held across a six-hour wait (~2.4 launches/minute max, and a lane whose cap never opens blocks every other lane) | `lane.sh` polls for a free slot **without** the lock; the lock is taken only around the `dispatch.sh` call; the post-launch `sleep 25` becomes a short jittered hold. One `cap()` definition, reading the per-account caps through `account_router.py`, not a hard-coded 9. The dead `MAXR` is deleted. | A bounded wait; on expiry the lane writes `<N>.needs-attention` with reason `no-slot`, which the janitor and the hourly report see — instead of a silent six-hour sleep. |
| An empty dispatch queue while the main session wrote 25-minute reports | Turn cap from run-mode (8 minutes in `fast`), a file-based `watchdog/main-inbox/` queue the keeper drains on its tick so a nudge never waits for a turn to end, and the standing-report shape of §6 that makes the reports short by construction. | The keeper's goal text is rendered from `run_mode.py show`; it can no longer contain stale literal caps like "primary 0, second 22, total 22". |

Plus **one-writer enforcement**: `dispatch.sh` takes a branch claim
(`$CACHE_ROOT/locks/branch-<branch>.claim`, holding role/pid/session) for the whole
session, refusing with exit 5 and naming the holder unless `--allow-concurrent` is given.
Read-only reviewers are exempt (they do not write the tree, and a lane's own review step
must not refuse against its own prover claim). This is the "two loops on one branch"
(autofix + prover on PR 342) that forced a `git stash push` preamble into every meta wave.

### Item 3 — Progress visibility

See §6. `estimate_post.py` is the single writer of the estimate issue and renders exactly
two lines; prose progress is the main session's standing duty on the progress log, written
into `local/personas/main.md` so it is not dictated in a pause message.

### Item 4 — Merge throughput

See §3.

### Item 5 — Lane-runner defects fixed only in `/tmp`

| Defect | Mechanism | Failure behaviour |
|---|---|---|
| Lane id ≠ issue number: meta lanes numbered `1000+PR` made `gh issue view 1342` empty and `pr_open.py --issue 1342` exit 2, after which the lane's **fallback pushed with `MIPSTARRE_SKIP_HOOKS=1`** and a hand-forged pre-push tuple, losing `checked-push.sh`'s `--force-with-lease` and its post-preflight re-verification | `local/bin/lane.sh` derives `N` from the branch (`issue-<N>-<slug>`, the same regex `pr_open.py` uses) and hard-fails when the positional id, the branch prefix and `gh issue view N` disagree. **The entire fallback block is deleted**: publication goes through `pr_open.py` → `checked-push.sh` only. | A `pr_open` failure writes `<N>.needs-attention` with the reason and stops; the janitor picks it up. Throughput drops until the janitor runs, which is why the janitor lands before or with this change. |
| Modules outside the `MIPStarRE.QPBT` import closure get no olean, so the per-file pre-push gate failed on every lane | `scripts/check_umbrella_imports.py` as a reachability check inside the existing `local-ci/build` step (§3.6), plus the v20 explicit changed-module build kept as belt-and-braces in `lane.sh` | The check never edits `MIPStarRE/QPBT.lean` (the operator serializes re-exports); it lists each unreachable module with the exact `import` line and the re-export file it belongs in. The known orphan (`MIPStarRE/QPBT/Combining/Points.lean`) is fixed in the same PR so the guard does not turn CI red on arrival. |
| PR 213's lane worktree held a different branch than the PR, so the refresh never pushed | `lane.sh` resolves worktrees registry-first (`git worktree list --porcelain` on `refs/heads/$BR`), exactly as `autofix.sh:resolve_worktree` already does; the shared implementation is `local/bin/worktree_resolve.sh` | A mismatch writes `<N>.needs-attention` reason `worktree-mismatch` and stops, instead of silently no-op'ing. The janitor reports that class for operator repair rather than guessing which worktree to move. |

### Item 6 — Speed tier and schedule

`run.speed` in the brief; `run_mode.py set speed` mid-run; the shim regenerated from the
committed `results/telemetry/owner-tools/owner-bin-codex` template rather than patched by
an `assert old in s` string surgery against a 90-character substring. The main session's
TUI launcher becomes `local/bin/main-session.sh`, which reads `run_mode.py get` for model,
effort, `CODEX_HOME` and `speed` and invokes `codex` **through the shim path** — the
2026-09-12 launcher `exec`'d an absolute `~/.local/bin/codex` and therefore never received
the speed tier. `launch_qpbt_main.sh` and `main-session-astra-v3.sh` are retired with an
`EVOLUTION.md` entry. Cadence lives in the mode file and the crontab is **regenerated**
from it by `install-crons.sh` (backup, then install from a file under `$W`), never edited
in place by `sed` — the 2026-09-12 pause chain wiped the crontab once through a `sed`
delimiter bug.

### Item 7 — Message delivery to the main session

One tracked `results/telemetry/owner-tools/owner-say.sh --mode idle|interrupt|terminal`:

- `idle` — the v4 rule that ended the 20-minute hang: idleness judged on the **last four
  non-empty lines only** (a stale "esc to interrupt" in the scrollback must not count).
- `interrupt` — Escape after the grace, send, then `/goal resume`.
- `terminal` — Escape, send, **do not resume**, and write `watchdog/goal-hold` so the
  keeper cannot re-resume. On 2026-09-12 the terminal stop order was sent at 08:19Z and
  the same script auto-resumed the goal at 08:24Z.

`goal-keeper.sh` takes `TURN_MAX` from run-mode, renders its goal text from
`run_mode.py show`, and drains `watchdog/main-inbox/` on its two-minute tick.

**Telemetry honesty.** With the model override in the policy layer (Item 2),
`sessions.jsonl` records the model that actually ran; the shim no longer rewrites it.

### Item 8 — Superseded and duplicate work

`local/bin/pr_janitor.py` (§4) closes a PR only when **both** mechanical conditions hold —
empty three-dot diff against `github/main` **and** the head reachable from main — with one
idempotent `<!-- pr-janitor:superseded -->` comment naming the SHAs. It never closes an
issue and never touches a PR with a nonempty diff. The same pass drops lane state for
branches with no open PR (the 20 stale 1xxx lanes) and refuses a second lane or fix loop
on a branch that already has one. Every retirement is one line in the hourly report.

---

## 3. Merge-throughput design

Nine merges in 3 h 05 m, gaps of 16–70 minutes. The structural ceiling is
*refresh-then-merge-one*: gate 2b requires `github/main` to be an ancestor of the head
(modulo passive telemetry advances), so each merge invalidates every other refreshed head
and N approved PRs cost N full builds and N CI runs, serialized.

This design **does not touch gate 2b**. The batching fix (a merge train with a locally
re-verified receipt) is a merge-gate change that already has an issue and a PR
(#502 / PR 507) and is deferred to them (§9). Everything below raises throughput without
going near `pr_merge.py`.

### 3.1 Remove the conflict class (the biggest single win)

Append-only telemetry logs conflicted on nearly every merge of main. Two changes:

- **`.gitattributes` at the repository root**, committed, with
  `results/telemetry/*.md merge=union`, `results/telemetry/**/*.md merge=union`,
  `results/telemetry/*.jsonl merge=union`, `results/telemetry/**/*.jsonl merge=union`, and
  `local/protocols/EVOLUTION.md merge=union`. The operator's 2026-09-12 fix lived in
  `$(git rev-parse --git-common-dir)/info/attributes` on one host and is lost on any fresh
  clone. `local/bin/worktree-setup.sh` asserts it is in effect
  (`git check-attr merge -- results/telemetry/events.md`) exactly as it already asserts the
  hooks.
- **Shard the event log.** `telemetry.py event` writes to
  `results/telemetry/events.d/<YYYY-MM-DD>-<session>.md`; two sessions never touch one
  path. `events.md` keeps its full history unchanged (7929 lines are not rewritten) and
  gains a short header pointing at `events.d/`; `telemetry.py events --since` reads both so
  existing readers (`proof-status`, the owner tools) keep working. The new paths are inside
  the `results/telemetry` allowlist `pr_merge._is_tolerated_telemetry_path` already
  tolerates, so sharding does not perturb gate 2b.

### 3.2 Self-repairing refreshes

A failed refresh currently does nothing but `touch pr<N>.failed`; repair existed only as a
`/tmp` one-shot the operator invoked, with a `-mmin -15` window, so anything that failed
more than 15 minutes before a tick was invisible forever and the 2 h marker backoff then
hid the PR from the scan as well.

`merge-daemon.sh` classifies each failed refresh from the lane log —
`merging github/main conflicted` → `merge`, `lake build … failed` → `build`,
`pre-push gate failed` → `preflight`, `Reconnecting... 5/5` / 503 / concurrency → `infra` —
and hands `merge` and `build` to the janitor's repair path (§4), one attempt per
`(PR, head)`. Infra failures are retried, not repaired. Repair concurrency shares the PAR
budget so repairs cannot starve merges.

### 3.3 Markers that carry a reason

`pr<N>.failed` becomes a JSON record `{pr, head, ts, class, reason, attempts, lane_log}`.
Backoff by class: `infra` 5 min; `conflict`/`build` until the repair finishes;
`preflight` 15 min; `gate` until the head changes. Automatic clearing keys on an
observable change, never on elapsed time alone:

- the PR head SHA changed, or
- the recorded reason string no longer appears in a dry run of the failing step, or
- the installed `tools-version` (§7) is newer than the marker, which clears every
  `preflight`/`build` marker — this is exactly the 05:44Z situation where eleven unrelated
  PRs stayed blocked after the systemic lane bugs had been fixed, and was answered by
  `rm` and by `( sleep 1500; rm -f … )`.

Every live marker with its reason is one line in the hourly report (§6), so a stuck marker
is never silent.

### 3.4 Parallelism sized by the machine, and one build at a time

`PAR` was a hand-typed constant (default 1; set to 8 at 05:44Z) on a host at load 90–150
shared with other users, while each refresh lane started a **full `lake build` outside**
`ci.sh`'s machine-wide lock and then queued on that lock in CI. Two changes:

- `PAR = clamp(1, floor((nproc - load1) / cores_per_build), free_worker_slots)`,
  re-evaluated every loop, `cores_per_build` a single knob in
  `results/telemetry/owner-tools/daemon.conf` (default 16). The chosen PAR and its inputs
  are logged on every scan line.
- The lane's pre-push build goes through the same lock helper `ci.sh` uses, restoring
  DESIGN.md invariant 7 ("at most one full `lake build` machine-wide"). A single lane is
  slower in the worst case; N lanes stop thrashing the NVMe cache and the CI queue.

### 3.5 Retire what should not be a candidate

The retirement pass of §2 Item 8 runs inside the daemon scan: a PR already on main never
enters a candidate list again, never absorbs a refresh or a review re-run, and never
inflates the ready-but-open count the owner is asked to interpret.

### 3.6 Reachability guard

`scripts/check_umbrella_imports.py` walks `MIPStarRE/**/*.lean` (excluding `*/Test/*`),
computes the transitive import closure of the re-export roots (`MIPStarRE.lean`,
`MIPStarRE/LDT.lean`, `MIPStarRE/QPBT.lean` and the per-directory re-export files AGENTS.md
requires to be preserved), and exits nonzero listing each unreachable module with the
exact `import` line and the re-export file it belongs in. It runs inside the **existing**
`local-ci/build` step, so the eight canonical contexts and therefore `pr_merge.py` gate 3
are unchanged. A PR that introduces an orphan fails in CI, not three hours later in a lane.

### 3.7 Measure it

`results/telemetry/merge-latency.jsonl`, one row per state transition
(`{pr, head, event: ready|refresh_start|refresh_end|merged|failed, class, reason, seconds, par}`),
written by the daemon and by `ready_report.py`. The hourly report prints merges/hour,
median ready-to-merged minutes and the top blocking class — the "is it progressing?"
answer that was manual archaeology on 2026-09-12. Until §3.1 lands the file is dated per
run (`merge-latency-YYYY-MM-DD.jsonl`) so no two writers share a path.

---

## 4. The self-repair janitor

`local/bin/janitor.sh` — one idempotent pass, safe to run from cron or from the daemon
loop, keyed on record fields and never on date globs (the 2026-09-12 recovery script
globbed `*20260912*.jsonl` and filtered lane numbers with `/[0-9]{3}\.needs-attention$`,
so lanes below 100 and the 1xxx lanes were never repaired).

| Pass | Input | Action | Cap / ledger |
|---|---|---|---|
| **Dead sessions** | `results/telemetry/sessions.jsonl` rows with `status: active` whose pid is dead (`account_router.live_pids`) and whose capture ends in an exhausted reconnect / 5xx / concurrency refusal | re-dispatch the same role on the same PR **and the same head**; mark the abandoned row `failed` so telemetry stops showing it live | at most 2 per `(pr, role, head_sha)`, ledger `watchdog/janitor/retries.jsonl`. Never re-dispatch a session whose capture shows a clean end. |
| **Parked lanes** | `watchdog/lanes/*.needs-attention`, no digit or age filter | classify the recorded reason (`merge conflicted` / `build failed` / `gate failed` / `no commits ahead` / `uncommitted worker changes` / `worktree-mismatch` / `no-slot`); dispatch an orc for the first two with the brief from `local/briefs/lane-repair-merge.md` / `lane-repair-build.md`; relaunch the tail via `local/bin/lane.sh` with `SKIP_DISPATCH=1` | 2 repairs per lane; the worktree must be clean and not mid-merge before a relaunch; classes it cannot fix stay parked and appear in the report |
| **Superseded PRs** | every open PR | `pr_janitor.py`: close only when the three-dot diff against `github/main` is empty **and** the head is reachable from main, with one idempotent marker comment | never closes an issue; anything else goes to the report |
| **Stale lane state** | `watchdog/lanes/<N>.*` | delete for lanes whose PR is closed or merged | — |
| **Spool expiry** | `watchdog/capacity/spool/*.json` | drop entries past the run's `dispatch_cutoff` | — |

The repair briefs are committed text, not shell string literals, and keep the current
constraints verbatim: *never drop a theorem or a proof; no sorry, no admit, no new axiom;
check every touched file with `lake env lean`; do not push (the lane pushes)*. A repair
that deletes paths main carries still fails the lane's post-merge `merge_loss_guard` check
— that guard is untouched.

**Retry and spool on the dispatch side.** `dispatch.sh` writes the full request (role,
issue, worktree, persona ref, effort, job class, prompt path, attempt, deadline) to
`watchdog/capacity/spool/<name>.json` **before** reserving. On a `refused` /
`concurrency_limit` / `endpoint_5xx` / `retries_exhausted` outcome it does not exit: it
sleeps a jittered exponential backoff (base 30 s, cap 10 min) and re-reserves, up to
`MIPSTARRE_DISPATCH_ATTEMPTS` (default 5) or the dispatch cutoff, then exits with a
distinct code leaving the spool entry for the janitor. Router refusal becomes retryable
rather than `die 4`.

Two safety rules on that retry, both load-bearing:

1. **A transient-class retry never consumes a proof packet attempt** and never resets its
   budget; the budget fields in `account_router.continuation()` are untouched and the
   retried dispatch reuses the same name with an attempt suffix so telemetry keeps one
   episode.
2. **A retry is gated on endpoint health.** A retry against an account whose
   `health-<account>.json` says `down` waits for half-open; it does not fire. Five
   client-side retries are precisely how 69 refusals became 69 deaths.

---

## 5. Pause within 15 minutes, and resume

One tracked script, `results/telemetry/owner-tools/owner-pause.sh [--deadline 15m] [--reason …]`,
replacing the four `/tmp` variants (`owner-pause.sh`, `owner-pause-v2.sh`,
`owner-pause-fast.sh`, `final-pause.sh`) whose chain hard-coded a timestamp, edited the
crontab three times in sequence without a backup, and clobbered the saved caps.

**Phases** (offsets from the owner's word; the deadline comes from
`run.pause_deadline_min`, default 15):

| T | Phase | Detail |
|---|---|---|
| +0:00 | Stop admission | `run_mode.py pause` → caps to 0 **and the pre-pause caps saved inside `capacity/state.json`** (not in a second file that a later phase can clobber); `touch watchdog/drain`. |
| +0:30 | Release waiters | `account_router.reserve` checks `watchdog/drain` each loop and exits cleanly with a distinct status, so queued dispatches release themselves instead of being `kill`ed (49 waiters were observed at 06:38Z). Stop keeper, merge daemon (stop file kept) and stack-watch by their stop files and pids. |
| +1:00 | One terminal message | `owner-say.sh --mode terminal`: "post the closing progress comment and write the handoff; do not post prose on the estimate issue; then `/goal pause`". No auto-resume, `watchdog/goal-hold` written. The *content* of the closing report is not dictated here — it is a standing duty in `local/personas/main.md` (§6). |
| +2:00 | Crontab | Back up `crontab -l` verbatim to `$W/crontab.<ts>.bak`, **failing the phase if `crontab -l` returns nothing**, then install the paused crontab from a file under `$W`. Never in-place `sed`, never from `/tmp`. |
| deadline −2:00 | Kill leftovers | Anchored patterns only (`^bash <owner-bin>/lane.sh `, `^bash [^ ]*autofix\.sh`, fix-lane, conflict-resolve, dispatchers, `python3 [^ ]*account_router\.py`, `^node [^ ]*codex(\.js)?( \|$).* exec( \|$)`): SIGTERM, SIGKILL after 20 s. Partial work stays in the worker's worktree; never `git clean`. |
| deadline | Confirm and record | Confirm `Goal paused` in the pane; write `watchdog/pause-state.json`; append `stages.jsonl` + an `events.d/` entry; commit and push telemetry. |

`pause-state.json` is the single record:
`{caps: {…, taken from run-mode, not from the already-zeroed live files}, speed,
estimate_cadence_min, crontab_backup, crontab_sha256, daemon_par, run_mode: {…},
measured_limits: {…}, main_goal: "paused", paused_at}`.

**Resume** — `results/telemetry/owner-tools/owner-resume.sh`, run only on the owner's word,
restores **from that record only**:

1. `run_mode.py resume` restores caps and speed and re-enters AIMD at the saved value.
2. `crontab "$W/crontab.<ts>.bak"` verbatim — no `sed` un-commenting. The 2026-09-12
   resume script's `sed -E 's#^\#PAUSED-2026[0-9]{4} ##'` would have resurrected the
   watchdog / astra-poll / heartbeat crons that have been deliberately commented since
   2026-09-09. If the live crontab differs from the sha the pause recorded, the script
   **refuses and prints the difference** rather than overwriting the owner's edits.
3. Restart daemon, stack-watch, keeper; deliver one resume message rendered from
   `run_mode.py show` (the current script hard-codes "primary 5 / second 39 / total 44",
   already wrong by 04:58Z on the day it ran).
4. Post-condition check: every cap file exists, is numeric and nonzero for an enabled
   account, health is not `down`, `watchdog/drain` is gone. A failure here is loud.

---

## 6. Reporting rules

| Channel | Content | Writer | Enforcement |
|---|---|---|---|
| Estimate issue (`run.estimate_issue`, #168) | **Exactly two lines**: the bold headline `**<ts> — implemented ≈ N% · days to go ≈ D**` and one `<sub>` provenance line. Nothing else, ever. | `local/bin/estimate_post.py`, called by `estimate.sh` from cron | `estimate_post.py` renders the body itself and refuses any other body. The issue number comes from run-mode and is validated at briefing time, so a missing `watchdog/estimate-issue` can no longer silently no-op the owner's only progress channel. `local/protocols/issues-prs.md` §6 and `local/personas/main.md` state the rule, so it survives the session that heard it. |
| Progress log (`run.progress_issue`, #27) | (a) One five-line progress comment every 30 minutes in `fast` mode: merges since the last post, live workers vs the occupancy floor, holes on main, the next three critical packets, blockers. (b) One hourly readiness report. (c) One line per stage boundary, merge, adopted mathematical correction, automatic PR retirement and repair. | (a) and (c) the main session as a standing duty in `local/personas/main.md`; (b) `local/bin/ready_report.py` from cron | The 30-minute comment is **skipped, not padded**, when nothing changed since the previous post. |
| Owner inbox (`run.owner_inbox_issue`, #500) | Permission, credential, access or scope grants only; ten plain lines; one id. Never progress, never a project-outcome decision. | main session | Unchanged rule; this design only sweeps the stale `#26` references out of `main.md`, `issues-prs.md`, `orchestrator.md`, `mathfix.md`, `sessions.md`, `AGENTS.md` and the `status-snapshot.sh` label (which prints "#26 open blockers" while querying issue 500). |

**The readiness report** (`ready_report.py`) is the mechanism for the owner's rule *"a
ready-to-merge PR left open needs a good reason"*. For every open PR it computes readiness
from the exact head (`local-ci/summary`, `local-review/summary`, unchecked ledger lines,
`CHANGES_REQUESTED`, draft) and, for each ready-but-open PR, **the reason it has not
merged, read from daemon state rather than guessed**: stale (base moved, minutes since),
refreshing (pid, lane, elapsed), failed marker (class + reason string), awaiting
adjudication, or `unexplained`. `unexplained` is the alarm case and should always be zero.
Output: one comment per hour on the progress issue in the form
`ready N, merged-this-hour M` plus one line per ready-but-open PR, and the same rows
appended to `merge-latency.jsonl`. A post is suppressed when the ready set and the reasons
are byte-identical to the previous hour and nothing merged, and forced at least every
6 hours.

**The closing report** is a standing duty, not a pause-message dictation: one comment on
the progress issue plus `results/telemetry/owner-handoffs/<date>-main.md` from the
committed `TEMPLATE.md`, **with every number measured by the session itself**
(`status-snapshot.sh`, `gh`) rather than copied from the operator's message — the
2026-09-12 handoff reads "Owner listed eight merges" because the operator's message was
the source.

---

## 7. What stays outside the repository, and how it is installed

Some things cannot live in the repository: they drive tmux, the crontab and the host's
process table, and they must be usable while the repository is mid-merge. On 2026-09-12
they lived in `/tmp` under names that no longer described their contents (`lane-v17.sh`
was really v20; `merge-daemon-v9h.sh` called `/tmp/merge-v2.sh`, a file that does not even
exist in the snapshot), were patched in place by `assert anchor in src` Python here-docs,
and ran in three simultaneous versions.

**The rule.** Operator scripts live in the repository under
`results/telemetry/owner-tools/` at honest names with a version header, and are **deployed**
to the host by one versioned installer. They are never edited on the host.

`results/telemetry/owner-tools/install.sh`:

```
install.sh [--force] [--compat-tmp] [--crons] [--dry-run]
```

1. Copies each tool from the checkout to `~/.cache/mipstarre-dev/owner-bin/`.
2. Writes a manifest `owner-bin/tools-version` (git describe + SHA, timestamp) and
   `owner-bin/manifest.sha256` with the SHA-256 of every installed file.
3. **Refuses** to overwrite a deployed copy whose hash matches no released version — a
   hand patch is detected, not silently clobbered. `--force` overwrites and moves the
   previous copy to `owner-bin/attic/<ts>/` rather than deleting it.
4. `--compat-tmp` additionally creates `/tmp/<name>.sh` **symlinks** into `owner-bin/`, so
   anything still invoking a historical `/tmp` path runs versioned code and nothing is ever
   edited in `/tmp`.
5. `--crons` calls `install-crons.sh`, which regenerates the whole crontab from run-mode
   (estimate every 30 min when `speed=fast`, every 6 h otherwise; readiness report hourly;
   the nudging crons left exactly as the mode file says), always backup-then-install from a
   file under `$W`. It never `sed`s the live crontab and it fails if `crontab -l` returns
   nothing.
6. Every tool prints `tool=<name> version=<sha>` as its first log line and records it in
   the lane's `.done` / `.needs-attention` marker, so a lane log names the code that
   produced it.
7. The daemon **refuses to start** (and posts one progress-log line) when a dependency is
   missing or its hash does not match the manifest, instead of failing per PR at merge
   time.

Inventory of what is installed rather than run from the checkout:

| Installed tool | Source of truth | Why outside `local/bin` |
|---|---|---|
| `merge-daemon.sh`, `merge.sh`, `daemon-scan.py`, `daemon.conf` | `results/telemetry/owner-tools/` | long-running host loop, must survive a mid-merge checkout |
| `owner-pause.sh`, `owner-resume.sh`, `owner-say.sh`, `goal-keeper.sh`, `install-crons.sh` | idem | drive tmux and the crontab |
| `capacityd.sh`, `status-snapshot.sh`, `estimate.sh` | idem | host loops / host census |
| `owner-bin-codex` (the PATH shim template) | idem | a PATH shim by construction |
| `local/bin/*` (dispatch, lane, janitor, ci, review, autofix, run_mode, capacity_controller, ready_report, estimate_post, pr_janitor) | the checkout, invoked by its **primary-checkout path** | pipeline scripts; a worktree copy can predate protocol fixes |

The owner's personal cron scripts that remain in `~/bin` get an entry in
`results/telemetry/owner-tools/README.md` naming their installed path and source of truth.

---

## 8. Implementation plan

Seven work items, disjoint file sets, each a reviewed PR closing one sub-issue of the
tracker in §10. Suggested order: **W1 → W2 → W3 → W5 → W6 → W4 → W7**; W7 is independent
and can land at any time.

Two files are deliberately **excluded from the disjointness accounting** because every
item appends to them and the union merge driver from W7 makes the appends conflict-free:
`local/protocols/EVOLUTION.md` (one dated entry per item, citing its trigger, per
`meta.md`) and the event log (one bullet per item). Do not restructure either.

### W1 — Owner briefing, run-mode, and the standing reports

`local/bin/run_mode.py`, `local/bin/ready_report.py`, `local/bin/estimate_post.py`,
`local/protocols/full-speed-mode.md`, `local/personas/main.md`,
`local/personas/orchestrator.md`, `local/personas/mathfix.md`,
`local/protocols/issues-prs.md`,
`results/telemetry/owner-tools/run-brief.template.json`,
`results/telemetry/owner-handoffs/TEMPLATE.md`,
`scripts/tests/test_run_mode.py`, `scripts/tests/test_ready_report.py`

Implements §1 and §6. `run_mode.py` with `apply/show/get/set/pause/resume`; strict
validation; atomic write; derived cap files that are never empty or non-numeric;
sha256 of the brief into `stages.jsonl` and one row in `design-decisions.md`.
`ready_report.py` in the style of `ready_packets.py` (GitHub is truth, `gh_common.py` for
every call); reasons read from daemon state, `unexplained` as the alarm case; hourly
comment with byte-identical suppression and a 6-hour floor. `estimate_post.py` renders the
exact two-line body and refuses any other. Docs: the runbook, the standing-reports section
of the main persona, the estimate/progress rule as a subsection of `issues-prs.md` §6, and
the `#26` → `#500` sweep in the four documents this item owns.
Local test: `python3 -m unittest scripts/tests/test_run_mode.py scripts/tests/test_ready_report.py`;
`run_mode.py apply --brief results/telemetry/owner-tools/run-brief.template.json --dry-run`
against a temp cache root.

### W2 — Dispatch and telemetry: failure classes, retry spool, branch claims, model override

`local/bin/dispatch.sh`, `local/bin/telemetry.py`, `local/bin/model_policy.py`,
`local/model-policy.json`, `local/bin/autofix.sh`, `local/bin/review.sh`,
`local/bin/codex-policy-shim.sh`, `local/protocols/sessions.md`,
`local/protocols/autofix.md`, `local/protocols/meta.md`, `AGENTS.md`,
`results/telemetry/events.md`,
`scripts/tests/test_dispatch_failure_class.py`,
`scripts/tests/test_dispatch_retry_and_claim.py`,
`scripts/tests/test_model_policy_override.py`

`classify_failure(events)` → `{failure_class, failure_detail, failure_endpoint,
retries_seen}` over the captured stream, patterns read from `local/capacity-policy.json`
(W3 ships the file; until then fall back to the built-in defaults) with `unknown` as the
safe default; `refused` added to `KNOWN_STATUSES` so a refusal is not scored as a failed
attempt. Key label derived from run-mode and passed for **both** accounts, validated
against `[a-z0-9.-]{1,40}` and never interpolated unquoted; `endpoint` recorded on every
row; `relay-1|space|unknown` still accepted for historical rows. Spool-and-retry per §4,
gated on endpoint health and never consuming a packet attempt. Branch claim with exit 5,
read-only reviewers exempt, released in `release_locks()`. Model override in
`load_policy`/`select_model` with `override_mode`/`override_source` in the session row, and
the `sol->astra` rewrite deleted from the shim. `autofix.sh`: `FIX_MODEL` default empty,
startup policy self-check, and `--loop [N]` (fix → checked-push → ci → review → re-read the
verdict for the **new** head) with distinct exit codes 0/3/4/2 replacing the log-tail grep
the `/tmp` loop used. Event sharding to `events.d/` with `events.md` keeping its history
and gaining a header. Docs: sessions.md §4.1 admission/claims, autofix.md loop and exit
codes, meta.md telemetry duty for `events.d/`, AGENTS.md telemetry-duty line, and the
`#26` → `#500` occurrences in sessions.md and AGENTS.md.
Local test: the three unittest files; `dispatch.sh --dry-run` for the claim and spool paths.

### W3 — Capacity controller, endpoint health, and the router

`local/bin/capacity_controller.py`, `local/capacity-policy.json`,
`local/bin/account_router.py`, `local/protocols/capacity.md`,
`results/telemetry/owner-tools/capacityd.sh`,
`results/telemetry/owner-tools/status-snapshot.sh`,
`scripts/tests/test_capacity_controller.py`,
`scripts/tests/test_capacity_health.py`,
`scripts/tests/test_capacity_state_roundtrip.py`,
`scripts/tests/test_account_router_drain.py`

Implements §2 Item 1 in full: AIMD with the exact increase/decrease rules above; per-
endpoint health with the 3-in-120 s trip and the single-flight half-open read-only probe;
`state.json` as the record with the legacy `max-codex*` files as derived outputs;
`max-codex` derived as the sum so it can never disagree; `external_reserved` subtraction;
`limit-estimate.json` with `measured_limit`, `observed_refusal_floor` and
`external_inferred`; one `capacity` row per tick in `stages.jsonl`;
`capacity_controller.py pause|resume` as the round-trip `run_mode.py` calls.
`account_router.py`: treat a `down` account as cap 0 (today `choose_account` *prefers* the
dead account, whose sessions keep dying and freeing slots — a self-accelerating outage),
and check `watchdog/drain` each loop, exiting cleanly with a distinct status. Both router
changes are **additive**: absent files reproduce today's behaviour exactly; the change
never widens capacity, only turns a waiting reservation into a clean refusal.
`status-snapshot.sh` prints per-account `live/cap (health) waiters` and the occupancy floor,
keeps the `== … | max-codex N` prefix stable for existing greps, and fixes the `#26` label.
Local test: the four unittest files, all against a temp cache root with synthetic
`sessions.jsonl`; the round-trip test must assert that no cap file is ever empty or
non-numeric after `pause` then `resume`.

### W4 — Operator-tools installer and the owner controls

`results/telemetry/owner-tools/install.sh`,
`results/telemetry/owner-tools/install-crons.sh`,
`results/telemetry/owner-tools/owner-pause.sh`,
`results/telemetry/owner-tools/owner-resume.sh`,
`results/telemetry/owner-tools/owner-say.sh`,
`results/telemetry/owner-tools/goal-keeper.sh`,
`results/telemetry/owner-tools/owner-bin-codex`,
`results/telemetry/owner-tools/estimate.sh`,
`results/telemetry/owner-tools/launch_qpbt_main.sh`,
`results/telemetry/owner-tools/README.md`,
`local/bin/main-session.sh`,
`scripts/tests/test_install_owner_tools.py`

Implements §5 and §7 and §2 Items 6–7. The installer with manifest, hash refusal,
`--force` + attic, `--compat-tmp` symlinks and `--crons`. One `owner-pause.sh` with the
phase table and the deadline from run-mode, replacing all four `/tmp` variants. One
`owner-resume.sh` restoring from `pause-state.json` only, with the crontab sha check and
the loud post-condition check. One `owner-say.sh --mode idle|interrupt|terminal` keeping
the last-four-lines idle rule and adding `terminal` + `watchdog/goal-hold`.
`goal-keeper.sh` rendering its goal from `run_mode.py show`, taking `TURN_MAX` from
run-mode, and draining `watchdog/main-inbox/`. `estimate.sh` made cheap enough for a
30-minute cadence: open PRs from the committed read-only
`results/telemetry/github-snapshot/open-pulls.json` instead of N `gh pr view` calls, branch
diffs in a throwaway worktree (never the primary checkout, which it currently leaves dirty
for `checked-push.sh`), the 24-h-ago count cached for the hour, `timeout` on the whole run,
and the body handed to `estimate_post.py`. Keep denominator 197 and the `<sub>` provenance
line so the `estimates.jsonl` series stays comparable. `main-session.sh` as the only
launcher, reading run-mode and going **through** the shim; `launch_qpbt_main.sh` reduced to
a retirement stub pointing at it.
Local test: `test_install_owner_tools.py` (manifest, hash refusal, attic, dry-run crontab
generation); `owner-pause.sh --dry-run` printing the phase plan and the computed deadline.

### W5 — Merge daemon and lane runner, promoted and self-repairing

`results/telemetry/owner-tools/merge-daemon.sh`,
`results/telemetry/owner-tools/merge.sh`,
`results/telemetry/owner-tools/daemon-scan.py`,
`results/telemetry/owner-tools/daemon.conf`,
`local/bin/lane.sh`, `local/bin/worktree_resolve.sh`,
`scripts/tests/test_lane_branch_identity.py`,
`scripts/tests/test_daemon_marker_classes.py`

Implements §3.2–§3.5 and §2 Item 5. `merge.sh` is the honest name of the missing
`/tmp/merge-v2.sh`. Daemon: adaptive PAR with logged inputs, classed JSON markers with the
class-based clearing rules, failure classification from the lane log, hand-off of
`merge`/`build` failures to the janitor's repair entry point, the retirement pass, and the
`merge-latency.jsonl` writer. `lane.sh` is the promoted v20 runner with: lane id derived
from the branch and cross-checked against `gh issue view`; **the `MIPSTARRE_SKIP_HOOKS=1`
fallback deleted**; registry-first worktree resolution via `worktree_resolve.sh`; the
launch lock held only around the dispatch; one `cap()` reading the per-account caps through
`account_router.py`; the pre-push build taken through `ci.sh`'s machine-wide lock; and a
bounded slot wait that parks `no-slot` instead of sleeping six hours. Gate behaviour is
otherwise byte-identical: same merge of `github/main`, same issue-#222 post-merge check,
same `pr_open.py` → `checked-push.sh` publication.
Local test: `test_lane_branch_identity.py` (mismatched id/branch/issue must fail closed;
no code path may set `MIPSTARRE_SKIP_HOOKS`), `test_daemon_marker_classes.py` (marker
parse, per-class backoff, tools-version clearing); `bash -n` on every script.

### W6 — The self-repair janitor

`local/bin/janitor.sh`, `local/bin/pr_janitor.py`,
`results/telemetry/owner-tools/fix-lane.sh`,
`local/briefs/lane-repair-merge.md`, `local/briefs/lane-repair-build.md`,
`scripts/tests/test_janitor_classify.py`, `scripts/tests/test_pr_janitor.py`

Implements §4. `janitor.sh` with the five passes, the `(pr, role, head_sha)` retry ledger
capped at 2, no date globs and no digit filters. `fix-lane.sh` becomes a thin, versioned
entry point the daemon and the janitor both call, taking its task text from the two
committed briefs. `pr_janitor.py` with the two mechanical conditions, one idempotent marker
comment, and a hard refusal to close an issue or a nonempty-diff PR.
Local test: `test_janitor_classify.py` (each reason string maps to its class; a clean
capture is never re-dispatched; the ledger caps at 2), `test_pr_janitor.py` (empty diff +
reachable head closes; either alone does not; the marker comment is posted once).

### W7 — Merge hygiene and build reachability

`.gitattributes`, `local/bin/worktree-setup.sh`, `local/bin/ci.sh`,
`scripts/check_umbrella_imports.py`, `local/protocols/ci.md`,
`MIPStarRE/QPBT/Combining/Points.lean`,
`scripts/tests/test_check_umbrella_imports.py`

Implements §3.1 and §3.6. The committed `.gitattributes` with the union driver for
`results/telemetry` `.md`/`.jsonl` (both the flat and the `**` forms) and for
`EVOLUTION.md`; the `git check-attr` assertion in `worktree-setup.sh` next to the hook
installation. `check_umbrella_imports.py` as a pure reachability check that prints the
missing `import` line and its re-export file and **never edits** a re-export file; wired
into the **existing** `local-ci/build` step body so the eight canonical contexts and
`pr_merge.py` gate 3 are untouched. The known orphan is fixed in the same PR by adding the
missing imports to `MIPStarRE/QPBT/Combining/Points.lean` (imports only; no statement, no
proof, no axiom is touched) so the guard does not turn CI red on arrival; if any further
orphan is found, ship the guard warn-only for one run and file the fix.
Local test: `python3 -m unittest scripts/tests/test_check_umbrella_imports.py`;
`python3 scripts/check_umbrella_imports.py --root .` must exit 0 on the branch;
`git check-attr merge -- results/telemetry/events.md` must print `merge: union`.

---

## 9. Deferred

Not in this design; each needs an owner decision, touches a proof-integrity or merge-gate
mechanism, or already has its own issue and PR.

1. **Merge train (`local/bin/pr_train.py`, gate 2b batching; audits MT1 and MT8).** This is
   the largest single throughput win and it is *not* rejected — it is out of scope here
   because it adds a new pass condition to `pr_merge.py` gate 2b, the staleness gate, and
   because it already has issue #502 and PR 507 (design-decisions D1, 2026-09-09 09:05).
   A second PR for the same issue would violate one-PR-per-issue. Constraints this design
   records for that PR: the receipt must be re-verified by recomputing the merge locally
   and never trusted as a file; it must name exact SHAs and be refused if the base moved;
   gates 1, 3, 4, 5, 6, 7 stay per-PR and unchanged; the train must assert the post-train
   `github/main^{tree}` equals the integration tree and stop with a report if it does not;
   candidates ordered by fewest changed files with conflicting heads dropped to the repair
   path; `train_max` default 8 with a bisect fallback so one bad PR does not drop the
   innocent ones.
2. **Priority-ordered admission and `drain --to N` (audit CAP-11).** Ordering waiters by
   role class and cancelling low-priority waiters back into the spool is valuable — 49
   waiters were observed behind 12 workers — but `account_router.reserve` is on the hot path
   of every dispatch and a regression there stops all work. Land it as a follow-up issue
   after W3 is running, with age escalation against starvation and tests for the existing
   invariants (dead-marker reaping, dry-run reserves nothing, explicit accounts never spill).
3. **The estimate-issue reformat guard (audit OI-5 second half).** Editing another
   session's GitHub comment is destructive and needs an explicit owner decision. The
   single-writer half (`estimate_post.py` refusing any non-conforming body) is in W1; the
   `--guard` that rewrites an offending comment is not.
4. **Any change to `.githooks/*`, `merge_loss_guard.py`, `checked-push.sh`, the seven
   `pr_merge.py` gates, the eight `local-ci/<step>` contexts, or the review-verdict
   contract.** Out of scope by rule. Note that W5 *removes* a bypass of the pre-push hook
   rather than changing it, which is permitted and is the point.
5. **Retiring `max-codex` entirely.** It is inert for admission but live for the lane
   runner's internal parallelism and for the operator display. W3 makes it a derived value
   with a documented "no admission meaning"; deleting it is a separate cleanup.
6. **Changing the Sol:Astra ratio policy, the `cores_per_build` default, the occupancy
   target, the estimate denominator (197), or the review round caps.** All owner or
   main-session policy decisions, not workflow mechanisms. `cores_per_build` ships as a
   config default of 16 so no one is asked a question at run time.
7. **A supervisor/service manager for the host loops.** `capacityd.sh` is a 20-line
   `while true; do …; sleep 60; done` started by the installer. Anything more is the
   "hardening the hardening" pattern that cost this project 17 hours on 2026-09-01.

---

## 10. The GitHub record

**Tracker issue title**

`Tracking: full speed mode v2 — one owner briefing, self-healing capacity, self-repairing merge path`

The seven work items are filed as native sub-issues of that tracker with
`local/bin/issue_new.py --parent <tracker>`, each carrying its file set and acceptance
criteria from §8, and each closed by exactly one reviewed PR. Prerequisite edges
(`gh_common.py add-blocked-by`) are: W3 blocked by W2 (failure classes), W5 blocked by W3
(the router `cap()`), W6 blocked by W5 (`lane.sh` and the marker classes), W4 blocked by W1
(`run_mode.py`). W7 has no prerequisites.

**Lead PR title**

`feat(local): owner run brief, run-mode and standing reports for full speed mode`
