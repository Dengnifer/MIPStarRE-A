# Protocol: full speed mode — the briefing, the mode file, the standing reports

Normative for a *run*: a bounded period in which the fleet works at the owner's
stated capacity and speed. Read `local/protocols/meta.md` first, then this file
before starting or pausing a run.

The rule this protocol exists to enforce: **the owner gives one briefing and
afterwards receives only the estimate one-liner and the progress log.** Every
number the owner states lives in exactly one file, and every component reads it
through one tool. Nothing is transcribed by hand into a second place — on
2026-09-12 the caps were restated five times, edited by hand ten times, and a
resume script still announced "primary 5 / second 39 / total 44" forty minutes
after those numbers were wrong.

## 1. The briefing

The owner copies the committed template
`results/telemetry/owner-tools/run-brief.template.json` to
`~/.cache/mipstarre-dev/watchdog/run-brief.json` and edits the values. That is
the **only** artifact the owner authors for a run.

| Field | Meaning |
|---|---|
| `run.label` | free text, used in reports and telemetry |
| `run.start` | ISO-8601 instant the run begins |
| `run.dispatch_cutoff` | ISO-8601 instant after which no new dispatch starts (running work finishes), or the literal `until my word` for an open-ended run |
| `run.pause_deadline_min` | the deadline budget for the pause procedure (section 6) |
| `run.speed` | `fast` or `default` (section 5) |
| `run.occupancy_target` | a fraction in `(0, 1]` of the effective cap; the integer floor everything quotes is `run_mode.py get floor` |
| `run.progress_issue` | prose progress and the hourly readiness report |
| `run.estimate_issue` | the two-line estimate, and nothing else, ever |
| `run.owner_inbox_issue` | permission, credential, access and scope grants only |
| `accounts[].name` | any name matching `[a-z0-9][a-z0-9_-]{0,31}`; `primary` and `second` are ordinary entries, not a closed set |
| `accounts[].label` | the human name of the key ("space", "relay-us7") |
| `accounts[].endpoint` | the label failures and health are attributed to, so a key moved between homes keeps its identity |
| `accounts[].codex_home` | that account's `CODEX_HOME` |
| `accounts[].nominal_limit` | **a ceiling, never a target** (see below) |
| `accounts[].external_reserved` | slots on that key the pipeline must not use (a forked session sharing the key), subtracted from the ceiling |
| `accounts[].enabled` | `false` means the pipeline never dispatches there at all |
| `models.override` | `null` = **resolve from `run.speed`** (section 5): `fast` means `astra-all`, `default` means the published `local/model-policy.json`. `"astra-all"` forces the hard model at any speed; `"policy"` keeps the published policy at any speed. Whatever is in force is recorded in telemetry |

**Nothing else holds a capacity decision.** `accounts[].enabled` is the only
statement of which keys a run may use, and `run_mode.py apply`, `pause` and
`resume` DERIVE `watchdog/account-mode` from it (`both` when more than one
account is enabled, `primary` otherwise). That file is what the deployed PATH
shim reads before it lets a dispatch use a `CODEX_HOME` other than `~/.codex`;
while it says `primary` every such dispatch exits 4 with `primary-only policy`.
It was previously written by hand and nothing in the brief path touched it, so a
brief that enabled `second` with a `nominal_limit` of 30 could hold a cap of 28
and dispatch nowhere on that key, with the AIMD seeing only deaths — the
idle-slot failure of 2026-09-12 intervention 2. Read it with `run_mode.py get
account_mode`; `owner-resume.sh` exits 5 when the file and the brief disagree.
Never edit it.

## 1.1 The live accounts file

The brief is **one-shot**; the set of usable keys is **live**. The owner's real situation is
one to three endpoints, each with one or two keys, and each key's concurrency limit moving
during the run: the endpoint's admin reassigns slots, the owner wins them back, a key
becomes invalid, a key runs out of quota. On 2026-09-12 every one of those events reached
the pipeline as a message to a session that had to be idle to receive it.

`~/.cache/mipstarre-dev/watchdog/accounts.json` is therefore the source of truth for
admission. One entry per key:

```json
{"schema": "mipstarre-accounts/1",
 "accounts": [
   {"name": "second", "label": "space", "endpoint": "api.finite-dimensional.space",
    "codex_home": "~/.cache/mipstarre-dev/codex-home-yxy",
    "ceiling": 30, "external_reserved": 2, "enabled": true, "note": ""}]}
```

| Field | Meaning |
|---|---|
| `name` | `[a-z0-9][a-z0-9_-]{0,31}`; any number of entries |
| `label` / `endpoint` | the human name, and the label failures and health are attributed to |
| `codex_home` | that key's `CODEX_HOME`. **The key value itself is never in this file** — it lives in that directory, which only the owner touches |
| `ceiling` | **a ceiling, never a target** (below) |
| `external_reserved` | slots on the key the pipeline must not use. `external_reserved == ceiling` is legal and means the key has no slot for the pipeline right now — different from `enabled: false`, which is a decision |
| `enabled` | `false` is cap 0 immediately and no health probe; removing the entry is the same |
| `note` | the owner's own free text, echoed in the hourly per-key line and changing nothing |

**`run_mode.py apply` seeds this file from the brief when it is absent and NEVER overwrites
an existing one**, and where the file exists it is what `apply` reads. So re-applying a
brief to change the speed tier, the cutoff or an issue number cannot undo an hour of ceiling
edits; `rm` the file and re-apply to go back to the brief.

**The controller and the router re-read it on every tick and every reservation** (at most
60 s stale). Lowering a ceiling takes effect at the next tick; raising it lets the AIMD
creep continue rather than jumping the cap; `enabled: false` and a removed entry are cap 0
at once. An entry the owner adds gets its own cap file, its own health, its own
`cap.<name>` accessor and its own line in every report, with nothing restarted.

An **invalid** accounts file is a hard, named failure of the controller with the cap files
left exactly as they are — never a silent fall back to the brief, which would restore a
ceiling the owner has just lowered.

### Editing it

```bash
results/telemetry/owner-tools/accounts.sh list
results/telemetry/owner-tools/accounts.sh set second ceiling 20
results/telemetry/owner-tools/accounts.sh set second reserved 4
results/telemetry/owner-tools/accounts.sh disable second --note "quota gone"
results/telemetry/owner-tools/accounts.sh add third --endpoint api.third.example \
    --codex-home ~/.codex-third --ceiling 8
results/telemetry/owner-tools/accounts.sh probe second
results/telemetry/owner-tools/accounts.sh log -n 20
```

Every write is atomic (temp file + rename) and appends one line to
`watchdog/capacity/accounts.log`. A bad field is refused with the field named and the file
is left byte-identical.

### The GitHub channel

When the owner is away from a shell, a comment on the owner inbox issue
(`run.owner_inbox_issue`) in the fixed form

```
ACCOUNTS: <name> ceiling=<n> [reserved=<n>] [enabled=true|false] [note=<word>]
```

— one or more lines per comment — is applied by `local/bin/janitor.sh`'s `owner-accounts`
pass at its next sweep and answered with one reply per comment saying exactly what took
effect: `applied: second ceiling 30 -> 20`, or `rejected: … — <reason>`. Three rules make
it a control channel rather than a conversation:

* only comments written by the **repository owner login** recorded in `local/README.md` are
  applied (overridable with `MIPSTARRE_OWNER_LOGIN`); anyone else's are answered with a
  `rejected:` line naming them, so an attempt is visible rather than silent;
* a comment is applied **exactly once** — the reply carries
  `<!-- mipstarre-accounts comment=<id> -->` and an answered comment is skipped — so a sweep
  every minute cannot re-apply a ceiling the owner has since changed at the shell;
* the channel carries `ceiling`, `reserved`, `enabled` and `note` **only**. An endpoint or a
  codex home is a path on the owner's host and is set with `accounts.sh`, where a typo
  cannot travel through a public comment.

Comment bodies are untrusted text (`issues-prs.md` §4): only `ACCOUNTS:` lines are read at
all, every value is validated before anything is written, and nothing is interpolated into a
shell.

### Measured health

A key is disabled by measurement, not by opinion. `401`/`403`/invalid-key and
`INSUFFICIENT_BALANCE` disable it at the **first** occurrence — a `401` is not a statistic,
and retrying an invalid key at any concurrency produces nothing but dead sessions — and
`endpoint_5xx` disables it at three deaths inside two minutes, the 2026-09-12 outage. Both
write the reason into `watchdog/capacity/health.json`, one document for every key, and cap
it at 0. The way back is the same half-open, single-flight, read-only probe in both cases,
restoring cap **1** and letting AIMD climb; the key-invalid backoff starts at five minutes
rather than thirty seconds, because a key does not become valid again in thirty seconds.
`accounts.sh probe [name]` runs that probe now instead of waiting for the backoff.

**`nominal_limit` is a ceiling and never a target.** It is the highest
concurrency the key may ever reach. The controller may sit below it for the
whole run and must never go above it; a run that sits at 60 % of the ceiling
with zero refusals is behaving correctly, and "we are below the limit" is not a
defect to report. The number to compare live workers against is the occupancy
floor `run_mode.py get floor`, not the ceiling.

## 2. Applying it

### The run-start sequence, in order

Applying the brief configures a run; it does not start one. This is the whole
list — nothing else has to be remembered, and nothing here is optional:

```bash
local/bin/run_mode.py apply                                   # 1. the brief
results/telemetry/owner-tools/install.sh --crons --start-loops # 2. tools, crontab, capacityd
setsid nohup ~/.cache/mipstarre-dev/owner-bin/merge-daemon.sh \
    >> ~/.cache/mipstarre-dev/watchdog/lanes/daemon.log 2>&1 < /dev/null &   # 3. the merge queue
setsid nohup ~/.cache/mipstarre-dev/owner-bin/goal-keeper.sh > /dev/null 2>&1 < /dev/null &
setsid nohup ~/.cache/mipstarre-dev/owner-bin/stack-watch.sh \
    >> ~/.cache/mipstarre-dev/watchdog/lanes/stack-watch.log 2>&1 < /dev/null &
tmux new -s qpbt 'local/bin/main-session.sh'                  # 4. the main session
```

Step 2 is the one that is easy to skip and impossible to notice: without a
running `capacityd.sh` nothing writes `watchdog/max-codex-*` again, so there is
no AIMD, no 5xx trip and no half-open probe — the caps stay frozen at whatever
seeded them, which is exactly the 2026-09-12 situation the controller exists to
remove — and on a fresh host `lane.sh`'s `wait_for_slot` fails closed with
`no-capacity-record`. The five-minute crontab row installed in the same step
brings the loop back if it is killed; `capacityd.sh` takes a lock, so a start
that is already running is a no-op.

After a pause, `owner-resume.sh` performs steps 1-3 from the pause record and
checks afterwards that the controller and the daemon are actually running
(exit 5 if not); only the main session is started by hand.

### `run_mode.py apply`

```bash
local/bin/run_mode.py apply            # reads watchdog/run-brief.json
local/bin/run_mode.py apply --brief PATH --dry-run
```

`apply` validates strictly and **fails loudly at briefing time rather than at
05:00Z**. Each of these exits 2 naming the offending key, the template path and
the destination path: an unknown key anywhere in the document, a missing or
malformed `endpoint`, a non-integer limit, `external_reserved >=
nominal_limit`, `occupancy_target` outside `(0, 1]`, an unknown `speed` or
`models.override`, an issue number that is not a positive integer, the three
issue numbers not being distinct, and an account named outside
`{primary, second}`. A **missing brief is a hard error** naming the template and
the exact destination — never "zero capacity" and never "unlimited".

On success `apply`

1. writes `watchdog/run-mode.json` atomically (temp file + `os.replace`);
2. derives `watchdog/max-codex-primary`, `max-codex-second` and `max-codex`;
3. regenerates the deployed PATH shim for the briefed speed (section 5);
4. writes or removes `watchdog/model-override` from the **resolved**
   `models.override` (section 5), which is what makes that field *do*
   something: an override in force writes the runtime knob `model_policy.py`
   reads, no override removes it. Validating the field is not applying it, and
   until this step existed "every worker on the hard model" still needed a
   hand-edited knob file or a reviewed PR mid-run;
5. appends a `stages.jsonl` row carrying the brief's `sha256`;
6. appends one row to `results/telemetry/design-decisions.md`.

`run.main` (optional) carries the MAIN session's own launch values —
`model`, `effort`, `codex_home` — read back by `local/bin/main-session.sh`
through `run_mode.py get main.model|main.effort|main.codex_home`. Omitted, it
defaults to `gpt-6-astra` / `xhigh` / the ambient `CODEX_HOME`; briefed, the
brief wins, and the launcher prints which of the two it used.

**The starting cap per account** is

```
cap0 = clamp(1, nominal_limit - external_reserved,
             last_measured_limit or nominal_limit - external_reserved)
```

reading `watchdog/capacity/limit-estimate.json` when it exists, so a run starts
*below* the measured cliff instead of above it. A disabled or unlisted account
is 0. `max-codex` is mechanically the sum of the effective per-account caps; it
has **no admission meaning** (the router reads only the per-account files) and
exists because `status-snapshot.sh` and the lane runner read it.

**The cap files are never empty and never non-numeric.** `run_mode.py` refuses
to write one under any circumstance and reads each back after writing. The
2026-09-12 resume script wrote empty cap files from a `grep` that matched
nothing, after which every dispatch exited 4 with `invalid literal for int()`.

## 3. Reading it

`watchdog/run-mode.json` is the record; `run_mode.py` is the only writer of it
and the only accessor anything else uses.

```bash
run_mode.py show                 # human-readable dump (goal text, cycle text)
run_mode.py show --oneline       # the whole mode on ONE line (goal text, resume message)
run_mode.py get account_mode     # derived from accounts[].enabled; the PATH shim reads it
run_mode.py get speed
run_mode.py get floor            # int(occupancy_target * sum of effective caps)
run_mode.py get accounts          # the enabled account names
run_mode.py get cap.second
run_mode.py get endpoint.second
run_mode.py get codex_home.second
run_mode.py get progress_issue | estimate_issue | owner_inbox_issue
run_mode.py get dispatch_cutoff | pause_deadline_min | turn_max
```

`show --oneline` is what `owner-tools/goal-keeper.sh` puts in the `/goal` text
and what `owner-tools/owner-resume.sh` puts in the single resume message, so
neither names a cap, a floor or an issue number of its own. Both keep a
degraded fallback for the case where the run mode cannot be read at all.

An unknown key exits 2 and lists the known ones. `cap.<account>` and `floor`
prefer the live cap files, falling back to the record; an unreadable cap file
is reported as **unknown**, never as zero.

**Protocols, personas and scripts cite this file, never a literal number.** A
cap, a floor, a cadence, a turn limit or an issue number written into a script,
a goal text or a persona is a defect: it was wrong within the hour every time it
was done on 2026-09-12. If a document needs the number in prose, it names the
key (`run_mode.py get floor`), not the value.

An unreadable `run-mode.json` makes `show` and `get` exit 2. The caller treats
that as *unknown* — it stops and says so — and never as zero capacity.

## 4. The standing reports

| Channel | Content | Writer |
|---|---|---|
| Estimate issue (`run.estimate_issue`) | **exactly two lines**: the bold headline and one `<sub>` provenance line; never anything else | `local/bin/estimate_post.py`, called by `owner-tools/estimate.sh` from cron |
| Progress log (`run.progress_issue`) | (a) one five-line progress comment every 30 min in `fast` mode; (b) one hourly readiness report; (c) one line per stage boundary, merge, adopted mathematical correction, automatic PR retirement and repair | (a) and (c) the main session (`local/personas/main.md`, "Standing reports"); (b) `local/bin/ready_report.py` from cron |
| Owner inbox (`run.owner_inbox_issue`) | permission, credential, access or scope grants only; ten plain lines; one id | the main session |

`estimate_post.py` renders the body from values on the command line and refuses
any other body; there is no way to pass it prose. The issue number comes from
the run mode and was validated at briefing time, so a missing
`watchdog/estimate-issue` can no longer silently no-op the owner's only
progress channel.

`ready_report.py` implements the owner's rule *"a ready-to-merge PR left open
needs a good reason"*. It computes readiness on the exact head and, for each
ready-but-open PR, reads the reason from daemon state rather than guessing:
`refreshing` (pid, lane, elapsed), a `failed` marker (class and reason string),
`parked` (the lane's `needs-attention` reason), `awaiting-adjudication`,
`stale` (the base moved, minutes since), or `unexplained`. **`unexplained` is
the alarm case and should always be zero.** A post is suppressed when the ready
set and the reasons are unchanged and nothing merged, and forced at least every
six hours. The same rows go to `results/telemetry/merge-latency-<date>.jsonl`.

The hourly comment also carries **one line per key** — ceiling, effective cap,
live workers, refusals in the last ten minutes, health with the reason it was
disabled, and the owner's own `note` — so the state of every key reaches the
owner's own channel. Before it existed, "the yxy key is disabled and here is
why" was a message from a session, which is the prompt the live accounts file
exists to remove.

It also carries two counts the owner would otherwise have to audit by hand:

* **models** — sessions started in the window grouped by the model that actually
  ran, next to the override in force and, when the override names one model, the
  number of rows that disagree with it. A full speed run whose reviewers slipped
  onto the cheap model shows up here within the hour; before it existed the only
  check was reading `results/telemetry/sessions.jsonl` by hand.
* **dead sessions marked failed and NOT re-dispatched, per role** — the janitor's
  residue. `local/bin/janitor.sh` re-dispatches **`reviewer` only**: that is the
  one role whose re-run is a pure re-run of the same work (`review.sh`, the exact
  head, and the new verdict supersedes). A dead prover, orc or fixer is marked
  `failed` with a `residue` field in `watchdog/janitor/actions.jsonl` and is the
  OWNING SESSION'S to re-plan — the janitor does not invent a packet. Widening
  it means giving those roles a re-dispatch entry point first and then listing
  them in `MIPSTARRE_JANITOR_REDISPATCH_ROLES`; until then the count is on the
  progress issue so the remainder is visible without opening a file on the host.

The split between the two issues is normative in
`local/protocols/issues-prs.md` section 6.

## 5. Speed

`run.speed` selects the provider tier and the reporting cadence:

| | `fast` | `default` |
|---|---|---|
| shim | `service_tier="priority"` | no tier argument |
| estimate cadence | every 30 min | every 6 h |
| main-session turn cap | 8 min | 20 min |
| models (`models.override: null`) | `astra-all` | the published `local/model-policy.json` |

**In full speed mode every role, reviewers included, runs the hard model.**
Review is a semantic-alignment phase and needs the strong model as much as
proving does, so this is the *default* of a `fast` run rather than a field the
brief has to remember: `models.override: null` resolves to `astra-all` at
`fast` speed and to the published policy at `default` speed. A fast run that
wants the published policy writes the explicit word `"policy"`, so declining
the override is a recorded decision and not an omission; `"astra-all"` forces
the hard model at `default` speed. `run_mode.py get model_override` answers with
what is actually in force, `model_override_briefed` with what the owner wrote
and `model_override_source` with which of the two decided it.

Mid-run:

```bash
local/bin/run_mode.py set speed fast     # or: default
```

This **regenerates the deployed shim from the committed template**
`results/telemetry/owner-tools/owner-bin-codex` — it never patches the live file
by string surgery, which is how a 90-character `assert old in s` anchor became
load-bearing on 2026-09-12. When the deployed shim matches no rendering of the
template, the command **refuses and prints the diff**, so an emergency
hand-edit is never silently discarded; fold the edit into the committed
template, redeploy, and retry.

`set speed` also **re-resolves `models.override` for the new tier** and
rewrites the runtime knob, so the mode file and `watchdog/model-override` can
never disagree about which model is in force: switching to `fast` puts every
role on the hard model, switching back to `default` returns the routine roles
to the published policy, and an explicit `"astra-all"` or `"policy"` in the
brief survives both. It then **regenerates the crontab** through
`results/telemetry/owner-tools/install-crons.sh`, because the estimate cadence
lives there and a switch to `fast` that leaves the cadence at six hours is not a
switch. A missing or failing installer is reported on stdout and never fails the
speed change — fix it and run `install-crons.sh` by hand.

The command prints who picks the change up: worker sessions dispatched from now
on **yes**; lane and daemon children started from now on **yes**; sessions
already running **no**; **the running main TUI no** — it must be relaunched
through `local/bin/main-session.sh`, which reads the run mode.

Nothing in the layer carries a model of its own: `lane.sh` requests `auto`,
`autofix.sh` leaves `MIPSTARRE_FIX_MODEL` empty, and `dispatch.sh` asks
`model_policy.py`, which reads the knob. A hard-coded model anywhere else is a
defect — the 2026-09-12 `gpt-5.6-sol` lane default and the `watchdog/model.txt`
side channel each pinned a model behind the policy's back.

## 6. Pause and resume

The owner's word starts the deadline in `run.pause_deadline_min`. The procedure
is one tracked script, `results/telemetry/owner-tools/owner-pause.sh`, which
ends admission and hands the rest to the standing duties:

| T | Phase |
|---|---|
| +0:00 | `run_mode.py pause` — caps to 0, the pre-pause caps saved **inside the run mode**, `watchdog/drain` touched |
| +0:30 | queued dispatches release themselves on `watchdog/drain`; keeper, merge daemon and stack-watch stopped by their stop files |
| +1:00 | one terminal message to the main session (`owner-say.sh --mode terminal`); the *content* of the closing report is a standing duty, not a dictation |
| +2:00 | crontab backed up verbatim, then installed from a file; never an in-place `sed` |
| deadline −2:00 | leftover workers killed by anchored patterns; partial work stays in the worktree |
| deadline | confirm, write `watchdog/pause-state.json`, append telemetry, publish |

`run_mode.py pause` is idempotent: a second pause does not overwrite the saved
caps with the zeros the first one wrote. `run_mode.py resume` restores **from
the saved caps only** — never from a message, never from a second file that a
later phase can clobber — refuses to resume an enabled account into zero
capacity, and checks afterwards that every cap file exists, is numeric, and is
at least 1 for an enabled account. When `capacity_controller.py` is installed,
both commands go through its state document so the cap files keep exactly one
writer; without it they write the cap files directly.

Resume is run only on the owner's explicit word
(`results/telemetry/owner-tools/owner-resume.sh`).

## 7. Failure modes, by design

| Situation | Behaviour |
|---|---|
| missing or invalid brief | exit 2, naming the key, the template path and the destination path; nothing is written |
| unreadable `run-mode.json` | `show`/`get` exit 2; the caller treats the mode as unknown, never as zero |
| unreadable cap file | reported as unknown with a warning; the record's value is used; the file is never left empty |
| deployed shim hand-edited | `set speed` refuses and prints the diff; `apply` warns loudly and applies the caps anyway |
| `install-crons.sh` missing or failing during `set speed` | reported on stdout naming the command to run; the speed, the shim and the override are still changed |
| `capacity_controller.py` fails during pause | the caps are zeroed directly and the failure is reported (stopping admission is the safe direction) |
| `capacity_controller.py` fails during resume | the command refuses; the caps stay where they are (paused is the safe direction) |
| GitHub failure in `ready_report.py` / `estimate_post.py` | nonzero exit and **no partial comment**; at most one mutation per publishing step, adopting the stable marker comment when it already exists |

## 8. Records

Every `apply`, `set speed`, `pause` and `resume` appends one `stages.jsonl` row
(stage `operator`) and one row to `results/telemetry/design-decisions.md`. The
brief's `sha256` travels in the apply row, so a report can be tied to the exact
briefing that produced it.
