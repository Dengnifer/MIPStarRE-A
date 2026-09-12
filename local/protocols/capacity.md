# Protocol — admission capacity

Normative for `local/bin/capacity_controller.py`, `local/capacity-policy.json` and the two
admission inputs of `local/bin/account_router.py`.  Read `local/protocols/meta.md` first and
`sessions.md` §4 alongside this: that document says who may start a session, this one says
how many may run at once.

The trigger is the full speed run of 2026-09-12.  The owner stated the concurrency limits
four times, a person edited the cap files ten times (39 → 29 → 20 → 18 → 14 → 12 → 6 → 14 →
22 → 0), and ~90 sessions died anyway: 69 into a primary endpoint that answered 503 for half
an hour, the rest above the second account's real provider limit.  Nothing measured the
limit and nothing noticed the dead endpoint.

## 1. What owns which number

| Number | Owner | Where it lives |
|---|---|---|
| **Ceiling** — the most the pipeline may ever run on a key | the owner's run brief | `run-mode.json`, as `nominal_limit - external_reserved` |
| **Cap** — how many it runs right now | the controller | `watchdog/capacity/state.json`, mirrored to the derived cap files |
| **Floor**, AIMD constants, health thresholds | the reviewed policy | `local/capacity-policy.json` |
| **Freeze** | the operator | `watchdog/capacity/hold` (touch file) |
| **Zero** | the pause path | `capacity_controller.py pause` (never `echo 0 >`) |

`ceiling_source` is validated to be the literal `"brief"`, so a knob file can never raise
the owner's limit.  The cap may sit below the ceiling forever and must never go above it.
`external_reserved` is the owner's statement that something outside the pipeline shares the
key (on 2026-09-12 a forked session, limited to two slots).  An **undeclared** sharer needs
no identification: it appears as refusals, AIMD walks the cap down, and the gap is recorded
as `external_inferred = nominal - external_reserved - measured_limit`.

## 2. The control loop

`results/telemetry/owner-tools/capacityd.sh` runs `capacity_controller.py tick` every 60 s —
a `while`/`sleep` loop with a stop file, and nothing more.  Each tick, per account:

1. **Counters** over the last `counter_window_s` (300 s), derived from the `failure_class`
   and `endpoint` fields of `results/telemetry/sessions.jsonl`.  Never a grep of a capture:
   the classification happens once, in `telemetry.py`, and everything downstream reads it.
2. **Additive increase.** `refusals_5m == 0` and `deaths_5m == 0` and `live >= cap - 1`,
   held continuously for a full `quiet_window_s` → `cap += 1`.  One slot per window, never
   more.  The `live >= cap - 1` term keeps the cap honest: a cap nobody uses is not evidence
   of headroom.
3. **Multiplicative decrease.** On the **first** refusal of a window,
   `cap = max(floor, min(cap, live_at_first_refusal - 1))`; on any further refusal inside it,
   `cap = max(floor, ceil(cap * decrease))`.  `live` is sampled at the tick that observes the
   refusal, the closest the controller gets to the moment the provider said no.
4. **Clamp** to `[floor, ceiling]`; when the two cross, the ceiling wins.
5. **Neutral unknowns.** A `failure_class` the policy does not name, including the literal
   `unknown`, is counted in neither direction.  It neither lowers the cap nor blocks the
   climb, so a reworded provider message degrades to today's static behaviour — the cap
   walks to the owner's ceiling and sits there, which is where a hand-set cap sat.  A
   "treat unknown as a refusal" rule would instead collapse the cap the first time a
   provider changed a string.

Ordering inside a tick: health, then decrease, then increase, then the clamp, then the
measurement.

## 3. Endpoint health

Independent of AIMD in both directions: a refusal never changes health, and a 5xx never runs
the AIMD arithmetic.  `watchdog/capacity/health-<account>.json` holds
`{state: up|degraded|down, since, consecutive_5xx, next_probe_at}` and the probe bookkeeping.

- `fivexx_threshold` (3) `endpoint_5xx` deaths inside `fivexx_window_s` (120 s) → **down**,
  and cap 0 at once.  This is the 05:30Z–05:58Z relay-us7 outage, answered on the day by a
  human typing `echo 0`.
- Below the threshold but above zero → **degraded**: the cap is not cut, but the climb stops.
- Recovery is half-open.  After `probe_backoff_s` (30 s, doubling to `probe_backoff_max_s`)
  the controller runs **one** probe — `codex exec --sandbox read-only`, a trivial prompt,
  that account's `CODEX_HOME`, bounded at `probe_timeout_s`, single-flight under
  `watchdog/capacity/probe-<account>.lock`.  `probes_to_recover` (2) consecutive successes
  leave `down` and restore cap **1**; one failure doubles the backoff.  **The cap never
  jumps back to its pre-outage value** — an endpoint that just came back is the last thing
  to hand twenty sessions.

The probe is a health check, not a work session: read-only, no persona, no task, no worktree
write, nothing appended to `sessions.jsonl`; its record is the health file and the `capacity`
row in `stages.jsonl`.  It is the one `codex` invocation in the layer outside `dispatch.sh`,
and it is confined to this paragraph.

`account_router.effective_caps` reads the health file and treats a `down` account as cap 0.
Without that, `choose_account` *prefers* the dead account — it picks the lower live/cap
ratio, and a dying endpoint keeps freeing slots — so an outage accelerates itself.  That is
how one hour of 503s cost 69 sessions.

## 4. The files, and which of them means anything

| Path (under `~/.cache/mipstarre-dev/`) | Written by | Meaning |
|---|---|---|
| `watchdog/capacity/state.json` | the controller, **solely** | the record: per account `cap`, `floor`, `ceiling`, `health`, `saved_cap`, `external_reserved`; plus `paused_at`, `brief_ref` |
| `watchdog/capacity/health-<account>.json` | the controller | §3 |
| `watchdog/capacity/limit-estimate.json` | the controller | §5 |
| `watchdog/capacity/hold` | the operator | §6 |
| `watchdog/max-codex-{primary,second}` | the controller | **derived**; these are what admission reads |
| `watchdog/max-codex` | the controller | **derived: the sum of the effective per-account caps.  It is a display and lane-parallelism value with no admission meaning.** |
| `watchdog/drain` | the pause path | §6 |

`max-codex` is computed as that sum in the same write as the per-account files, so it cannot
disagree with them; it is kept because `status-snapshot.sh` and the lane runner's `cap()`
read it (`sessions.md` §4.1 cross-references this row).  Retiring it is a separate cleanup.

A hand edit of a cap file is overwritten on the next tick (a hold file freezes that too).  The supported override is
`capacity_controller.py set ACCOUNT N`, which clamps to the ceiling, may go to 0 (the
replacement for `echo 0 > max-codex-primary`), records the change, and gives the operator's
number a full quiet window before AIMD moves again — AIMD will then climb back out of it, so
an account that is off for the whole run belongs in the brief as `enabled: false`, and an
account frozen at a number needs the `hold` file.  `run_mode.py apply` seeds a run by
calling `capacity_controller.py init` rather than writing the cap files itself, for the same
one-writer reason.  A cap file is never written empty or non-numeric: that failure is silent
and total, since every dispatch then exits 4 on `invalid literal for int()`.

## 5. Measurement carried forward

`limit-estimate.json` records per account: `nominal`, `external_reserved`, `cap_now`, `live`,
`waiters`, `refusals_5m`, `deaths_5m_by_class`, `measured_limit` (the highest concurrency
sustained `measured_hold_s` with zero refusals and zero deaths), `observed_refusal_floor`
(the lowest concurrency at which a refusal was seen), `external_inferred`, `health`,
`updated`.  `waiters` is the queue depth of the whole router, not a per-account number: a
waiter dispatched with `--account auto` is waiting on both accounts at once.

`run_mode.py apply` seeds the next run's starting cap at `min(brief ceiling, measured_limit)`,
so a run starts below the cliff instead of above it; the brief's nominal is always the
ceiling, so a stale low estimate costs a few minutes of ramp and never the run.  One
`capacity` row per tick goes to `results/telemetry/stages.jsonl`.

## 6. Operator controls

- **Hold** — `touch watchdog/capacity/hold` freezes the caps where they are.  Health handling
  continues (states are computed and recorded) but the probe does not run and no cap is
  rewritten: under a hold the operator owns the number, outage included.  It freezes the
  *tick*; `init`, `set`, `pause` and `resume` are explicit commands and act regardless, so a
  new brief applied under a hold still lands.
- **Pause / resume** — `pause` saves the pre-pause caps **inside** `state.json` as
  `saved_cap` and writes 0 everywhere; `resume` restores them and re-enters AIMD at the saved
  value.  Never a second file: on 2026-09-12 the pause chain wrote `caps-before-pause` in one
  format, a later phase overwrote it with another, and the resume script restored nothing.  A
  second `pause` never clobbers the first save, and `resume` still yields 0 for an account
  that is disabled in the brief or whose endpoint is `down` — health outranks a saved number.
- **Drain** — `touch watchdog/drain` makes `account_router.reserve` exit cleanly with status
  6 on its next poll, so queued dispatches release themselves.  Forty-nine waiters sat behind
  twelve workers at 06:38Z on 2026-09-12 and the only way to clear them was to kill the
  processes, discarding the dispatch requests with them.

## 7. Failure behaviour

| Condition | Behaviour |
|---|---|
| malformed or missing `capacity-policy.json` or `run-mode.json` | exit 2, **cap files untouched**; the supervisor logs and retries.  Never "zero capacity", never "unlimited" |
| a malformed row in `sessions.jsonl` | skipped; one bad row never stops the loop |
| a `failure_class` the policy does not name | neutral (§2.5) |
| two controllers racing | impossible: a tick takes `watchdog/capacity/controller.lock` non-blocking and a second tick exits 0 without working |
| a hold file during an outage | health is recorded, the probe does not run, the cap does not move |
| `pgrep` missing | the waiter count reports 0; it is advisory and never fails a tick |
| an absent health or drain file | `account_router` behaves exactly as it did before either existed |

## 8. The knob file

`local/capacity-policy.json` is reviewed code, not runtime state.  Per account it carries
`floor`, `aimd {increase, decrease, quiet_window_s}` and `health {fivexx_threshold,
fivexx_window_s, probe_backoff_s, probe_backoff_max_s, probes_to_recover}` over a `defaults`
block, plus:

- `failure_patterns` — the provider strings, as an **ordered** list of
  `{failure_class, counts_as, patterns}`.  `telemetry.py` matches in order and takes the
  first hit; `endpoint_5xx` precedes `retries_exhausted` because a session killed by an
  outage also ends with an exhausted reconnect, and the outage is the true cause.
  `counts_as` is `refusal` (drives the decrease), `death` (blocks the climb) or `neutral`.
- `priority_classes` — data only.  Nothing reads it yet; the admission ordering that would
  consume it is deferred, because `reserve` is on the hot path of every dispatch.

`floor` defaults to 1: an enabled, healthy account keeps one slot with which to discover that
it has more.  `enabled: false` in the brief, a paused run, a `down` endpoint and an explicit
`set 0` each take it below that floor.
