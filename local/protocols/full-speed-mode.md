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
| `accounts[].name` | `primary` or `second` — `account_router.py` knows exactly these two |
| `accounts[].label` | the human name of the key ("space", "relay-us7") |
| `accounts[].endpoint` | the label failures and health are attributed to, so a key moved between homes keeps its identity |
| `accounts[].codex_home` | that account's `CODEX_HOME` |
| `accounts[].nominal_limit` | **a ceiling, never a target** (see below) |
| `accounts[].external_reserved` | slots on that key the pipeline must not use (a forked session sharing the key), subtracted from the ceiling |
| `accounts[].enabled` | `false` means the pipeline never dispatches there at all |
| `models.override` | `null` = **resolve from `run.speed`** (section 5): `fast` means `astra-all`, `default` means the published `local/model-policy.json`. `"astra-all"` forces the hard model at any speed; `"policy"` keeps the published policy at any speed. Whatever is in force is recorded in telemetry |

**Nothing else holds a capacity decision.** `accounts[].enabled` is the only
statement of which keys a run may use, and `run_mode.py apply`, `pause` and
`resume` DERIVE `watchdog/account-mode` from it (`both` whenever `second` is
enabled, `primary` otherwise). That file is what the deployed PATH
shim reads before it lets a dispatch use a `CODEX_HOME` other than `~/.codex`;
while it says `primary` every such dispatch exits 4 with `primary-only policy`.
It was previously written by hand and nothing in the brief path touched it, so a
brief that enabled `second` with a `nominal_limit` of 30 could hold a cap of 28
and dispatch nowhere on that key, with the AIMD seeing only deaths — the
idle-slot failure of 2026-09-12 intervention 2. Read it with `run_mode.py get
account_mode`; `owner-resume.sh` exits 5 when the file and the brief disagree.
Never edit it.

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

The hourly comment also carries two counts the owner would otherwise have to
audit by hand:

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

There are **two owner words**, and they are different instructions.

`owner-pause.sh --cutoff` is the first: it stops **admission and nothing else**.
Caps to 0, `watchdog/drain` touched, queued dispatches release themselves, no
process is signalled and every daemon keeps running, so work already in flight
finishes and still merges. It may be given long before the pause — that lead is
the whole point, because the sessions still running when the pause word comes
are then only the ones that could not finish.

`owner-pause.sh` (no flag) is the pause word and starts the deadline in
`run.pause_deadline_min`. A pause given without a prior cutoff is not an error:
it closes admission itself and degrades to the landing rule below.

| T | Phase |
|---|---|
| +0:00 | `run_mode.py pause` — caps to 0, the pre-pause caps saved **inside the run mode** (and read back from `saved_caps` when a cutoff already zeroed the live ones), `watchdog/drain` **and** `watchdog/paused` touched, the daemon's failed markers snapshotted before the daemon is stopped |
| +0:30 | queued dispatches release themselves on `watchdog/drain`; keeper, merge daemon, stack-watch and capacityd stopped by their stop files |
| +1:00 | one terminal message to the main session (`owner-say.sh --mode terminal`); the *content* of the closing report is a standing duty, not a dictation |
| +2:00 | crontab backed up verbatim, then installed from a file; never an in-place `sed` |
| deadline − `landing_lead_s` | **the landing**: `pause_landing.py` classifies every live session and stops the **young** ones only, then writes the manifest |
| deadline − `last_call_s` | **the last call**: the mature leftovers are stopped, then the anchored pattern table sweeps the lane runners and helper loops no registry row names |
| deadline | confirm, write `watchdog/pause-state.json`, append telemetry, publish |

### The landing is age-based, not a blanket kill

A codex session has already paid for its input and its reasoning; only its
rollout survives a kill, so restarting it pays everything again. The 2026-09-12
pause killed 17 sessions mid-work, and on 2026-09-14 the fallout was reviewers
that "exited 143", kill-caused `daemon/pr<N>.failed` markers that made the
merge daemon skip those PRs for two hours, and lanes restarted from scratch on
heads that already carried a green CI and a finished review.

| Class | Rule |
|---|---|
| young (elapsed under `young_max_min`) | little sunk cost: stopped at the landing phase, whatever the role |
| mature reviewer or scout | usually finishes inside the window, and a resumed review re-reads its whole context anyway: runs to the last call, then **restarted from scratch** |
| mature writer (prover, mathfix, orc, …) | **checkpointed**: worktree untouched, codex thread id, worktree, step and elapsed time recorded, stopped at the last call, resumed on its own thread |

Every stop is one SIGTERM pass over the phase — the recorded `dispatch.sh` **and
the codex process it owns**, because a dispatcher's `trap … TERM` cannot run
while its `codex | tee` pipeline is the foreground job, so a TERM to the wrapper
alone leaves codex spending quota — then **one** `grace_s` sleep for the whole
phase, then SIGKILL to the survivors. Sleeping the grace per session made the
landing cost `grace_s x sessions`: with the 17 sessions of 2026-09-12 the last
call alone would have run four minutes past the owner's deadline. A pid is
signalled only while its command line still names the session the record names —
an unreadable command line is spared, not killed, because a recycled pid on a
128-core shared host is a real possibility — and whatever a SIGKILLed wrapper
could no longer release (its account slot, its branch claim, its spool row) is
released explicitly, so the resumed run admits its full cap. Every threshold lives in
`local/capacity-policy.json` under `landing`; no number is written into any
shell script, and `pause_landing.py` carries the same values as documented
fallbacks for the case where the policy file cannot be read.

### The manifest, and what the resume does with it

`watchdog/pause-state.json` gains a `landing` key: the resolved thresholds, the
lanes with their issue, branch, head, the step each reached and the statuses
already on that head, the stopped sessions with thread id, role, worktree,
elapsed time and whether each is resumable, and the `daemon/pr<N>.failed`
markers that appeared **during the pause** — recorded by difference against a
snapshot taken at T+0:00, before the merge daemon is stopped, so a marker that
records a real failure is never confused with one a kill caused. Snapshotting at
the landing phase instead made that list empty on every pause: by then the only
process that writes such a marker had been dead for ten minutes.

`owner-resume.sh` restores the caps, the crontab and the daemons as before, and
then — only after its post-condition check passes — replays that manifest:

* each parked lane is relaunched with `LANE_RESUME_STEP` and the environment it
  carried (`LANE_BRANCH`, `SKIP_REVIEW`, `MIPSTARRE_REVIEW_CMD`): the merge, the
  build and the push are skipped while the head is unchanged, CI is skipped when
  the head already carries `local-ci/summary` success, the review is skipped when
  it already carries `local-review/summary` success, and a head carrying both is
  not relaunched at all. `publish` is only for a lane that reached publication;
  one stopped at `warm` or `dispatch` resumes at `dispatch`, where `lane.sh`
  rebuilds `--resume` from its own thread record — resuming it at `publish` would
  skip lane.sh's completion gates and spend a CI run and a review on an
  unfinished proof;
* each checkpointed writer **the lane does not own** is resumed with
  `dispatch.sh --resume <thread>`, a continue prompt that points it at its own
  worktree, and the job class, effort, hardness reason, persona, sandbox and
  account the spool recorded, because `account_router` refuses a resume whose
  model differs from the thread's and the model is selected from those fields. A
  lane owns the sessions in its worktree: emitting both would put two writers
  into one worktree, so only the lane is relaunched;
* a stopped writer whose thread id was never captured gets a fresh dispatch with
  a continue-from-the-worktree prompt, and is named in the output — never
  silently dropped;
* each stopped reviewer is restarted from scratch;
* each recorded failed marker is removed, so the merge daemon stops skipping a
  PR that a kill, not a defect, marked.

The replay is stamped into the manifest, so a second `owner-resume.sh` launches
nothing again (`resume-exec --force` is the deliberate way back in), and one
launch that fails does not abort the rest of the plan.

`--no-work` restores the caps and the daemons only. Provers are told, in the
dispatch prompt and in `local/personas/prover.md`, to commit each proved lemma
before starting the next: a kill then costs at most the work since the last
commit, and the resumed session continues from the worktree.

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
