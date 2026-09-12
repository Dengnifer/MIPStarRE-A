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
| `run.compute.offload_hosts` | the extra build hosts this run may use, today `["chsh"]` or nothing (section 5.1). Optional; absent means this host only |
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
run_mode.py get speed
run_mode.py get floor            # int(occupancy_target * sum of effective caps)
run_mode.py get cap.second
run_mode.py get endpoint.second
run_mode.py get codex_home.second
run_mode.py get progress_issue | estimate_issue | owner_inbox_issue
run_mode.py get dispatch_cutoff | pause_deadline_min | turn_max
run_mode.py get offload          # yes only in full speed mode (section 5.1)
run_mode.py get offload_hosts | offload_reason
```

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

### 5.1 The chsh build farm

**What chsh is.** A second host, prepared on 2026-09-12: 192 aarch64 cores,
2 TB RAM, 10 TB free, Lean 4.32.0, a byte-identical copy of the Mathlib package
cache, a hardlink build seed and a checkout mirroring this one. ghz reaches it
at 86.7 MB/s over the internal address. A cold lane offload measured 14.9 s and
a one-file rebuild 17.2 s round trip, against 19 minutes for a full warm build
and a 61 s median CI build on a ghz loaded to 90-150 by other users.

**The owner's rule.** *In full speed mode the compute and the storage of chsh
are used alongside ghz; outside full speed mode chsh is never used.* So the
offload is a property of the run mode and of nothing else:

```
run_mode.py get offload  ==  yes   iff  run.speed is fast
                                   and  run.compute.offload_hosts lists chsh
                                   and  the run is not paused
```

Every other case — a default-speed run, a brief that does not list the host, a
paused run, an unreadable run mode, a run-mode document written before the
field existed — is `no`. There is no operator switch, no environment variable
that turns it *on*, and no file an agent can touch to enable it;
`MIPSTARRE_OFFLOAD=0` can only turn it further off. `run_mode.py get
offload_reason` prints the sentence that decided it.

**And no codex on chsh.** chsh's own internet is about 16 KB/s. It is a pure
build node fed from ghz by rsync: no worker session, no dispatch, no review, no
`codex` installation, ever. Nothing in this layer starts one there.

**What uses it.** `local/bin/lane.sh` (the pre-push build and the changed-module
build) and `local/bin/ci.sh` (the `local-ci/build` step) take their `lake build`
through `local/bin/offload-build.sh`, which calls
`results/telemetry/owner-tools/build-on-chsh.sh`. That script pushes the
worktree's sources (never `.lake`, `.git`, `.worktrees` or `results/telemetry`),
seeds the lane's `.lake/build` from the shared seed with `cp -al`, points
`.lake/packages` at the shared Mathlib cache, builds, and returns only the
artifacts that build wrote. **The pre-push per-file `lake env lean` gate stays
on ghz**, as does everything else that decides whether a branch may be
published: only the compilation moves.

**chsh is down: there is nothing to do.** Any ssh or rsync failure — an
unreachable host, missing host keys, a busy lane, a toolchain mismatch, a failed
artifact return — exits 64 or 65, and the caller then builds here. A lane never
fails because chsh is unreachable, and a run needs no intervention when it
happens; the lane log says which host built. A build that *failed* is a
different thing and is passed through unchanged: a proof that does not compile
on chsh does not compile here either, and a silent local retry would only spend
the machine's single full-build lease twice.

**How to verify that it was used.**

```bash
tail ~/.cache/mipstarre-dev/watchdog/chsh/offload.log   # one row per build, naming the host
grep '^offload: ' ~/.cache/mipstarre-dev/watchdog/lanes/<N>.build.log
local/bin/run_mode.py get offload_reason
results/telemetry/owner-tools/build-on-chsh.sh --dry-run <worktree>   # the plan, contacting nothing
```

A row reading `host=ghz reason=fallback-64` is the farm being unreachable and
the fallback working, not an incident. A run at `fast` speed whose log has no
`host=chsh` row at all is the thing to look at: check `get offload_reason`
first, then the known-hosts file below.

**The seed.** chsh's checkout and its hardlink seed go stale as `main` moves,
and a lane seeded from an old seed rebuilds the difference — slow, never wrong.
The merge daemon fires `build-on-chsh.sh --seed-refresh` after every merge; the
refresh is detached, takes its own lock, runs at most once an hour and returns
immediately while the offload is disabled. Its log is
`watchdog/chsh/seed-refresh.log`.

**Installation.** `results/telemetry/owner-tools/install.sh` deploys
`build-on-chsh.sh` under the hash manifest like every other operator tool, and
copies the host keys to `watchdog/chsh/known_hosts` (from
`$MIPSTARRE_CHSH_KNOWN_HOSTS`, default `/tmp/chsh-setup/known_hosts`). The keys
are runtime state, never committed, and the connection is
`StrictHostKeyChecking=yes` against that file: a missing file makes the offload
unusable — which costs a little build time and nothing else — and is never a
reason to accept an unknown host key. Nothing is installed on chsh.

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
| chsh unreachable, or its host keys missing | the offload exits 64, the lane or CI step builds on ghz and says so; no lane fails and nothing is to be done (section 5.1) |
| an unknown host in `run.compute.offload_hosts` | `apply` exits 2 naming the key and the known hosts; nothing is written |
| the run is paused, or the speed is `default` | `get offload` is `no` and chsh is not contacted at all |

## 8. Records

Every `apply`, `set speed`, `pause` and `resume` appends one `stages.jsonl` row
(stage `operator`) and one row to `results/telemetry/design-decisions.md`. The
brief's `sha256` travels in the apply row, so a report can be tied to the exact
briefing that produced it.
