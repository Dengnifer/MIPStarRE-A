# Template — the goal text

The goal is **one paragraph**, delivered to the main session as a single
`/goal` message and stored at `$KIT_STATE_DIR/goal-text`. The goal keeper
re-sends the whole text whenever the session idles without a goal, so it must
be self-contained and it must not grow: everything that changes belongs in
`$KIT_STATE_DIR/handoff.md`, not here.

Seven parts, in this order. Leave none of them out.

| # | Part | Why it is in the goal and not elsewhere |
|---|---|---|
| a | which cycle document to follow | the session may be relaunched with no memory |
| b | which sections of the state file to read first | the state file grows; the newest sections are the ones in force |
| c | the key and worker layout, with its caps | wrong layout burns a key or starves the project |
| d | the per-turn loop | the keeper re-sends this every time a turn ends badly |
| e | the hard prohibitions | each one is an incident that already happened |
| f | what to do when the key fails | the failure mode where the session can least think |
| g | what DONE means and the single stop action | otherwise nothing ever stops |

Write it as running prose, not as a list: it is pasted into a composer.

---

## Template

```
/goal Operate {{PROJECT_NAME}} continuously as the main session by the cycle in
local/protocols/main-cycle.md (read first the LAST sections of
{{STATE_DIR}}/handoff.md: {{NEWEST_SECTION_NAMES}}). Layout: you run
{{MAIN_LAYOUT}}; model work goes to at most {{WORKER_COUNT}} detached workers
through local/bin/dispatch.sh and local/bin/review.sh (caps {{CAPS}}); keep
every worker slot busy with independent tasks on different pull requests and
worktrees, and refill a slot as soon as it frees. Every turn: run
bash results/telemetry/owner-tools/status-snapshot.sh --prs, act on every actionable
line in the order of main-cycle.md section 2, gate reviewed pull requests, stage
trains in your own quiet window, record telemetry, post one comment on issue
{{PROGRESS_ISSUE}} per stage boundary, end the turn. Never {{PROHIBITIONS}}.
If {{WORKER_KEY}} is retired the caps drop: dispatch nothing more and continue
with model-free work. If {{MAIN_KEY}} fails, never switch keys: post one comment
on issue {{PROGRESS_ISSUE}} with the state of every in-flight item and run
/goal pause. DONE = {{DONE_DEFINITION}}. Stop only when the owner says so or
when DONE is reached: then post one final comment on issue {{PROGRESS_ISSUE}}
and run /goal pause.
```

**Placeholders**

| Placeholder | From |
|---|---|
| `{{PROJECT_NAME}}` | `project.name` |
| `{{STATE_DIR}}` | `$KIT_STATE_DIR` |
| `{{NEWEST_SECTION_NAMES}}` | the titles of the newest handoff sections |
| `{{MAIN_LAYOUT}}` | `session.main` — alone, or with N delegate threads |
| `{{WORKER_COUNT}}`, `{{CAPS}}` | `session.workers.lanes` and the cap files |
| `{{PROGRESS_ISSUE}}` | `issues.progress` |
| `{{PROHIBITIONS}}` | the hard "never"s in force (see below) |
| `{{MAIN_KEY}}`, `{{WORKER_KEY}}` | `session.main.key`, the worker key name |
| `{{DONE_DEFINITION}}` | `completion.md`, restated in the owner's words |

**The prohibitions worth naming explicitly**, because each one already went
wrong: never run a worker by hand outside the dispatch entry points; never
merge by hand; never do multi-minute work in your own turn; never spawn
sub-agent threads beyond `session.main.native_delegates`; never grow a pull
request to satisfy findings; never push the main branch outside the merge
service.

<!-- EXAMPLE — invented, for shape only. Do not copy the numbers.

/goal Operate WeakDep continuously as the main session by the cycle in
local/protocols/main-cycle.md (read first the LAST sections of
~/.cache/weakdep-dev/watchdog/handoff.md: "RESUME 2026-03-04" and "HANDOVER FROM
THE PREVIOUS MAIN"). Layout: you run alone on the main key with no delegate
thread; model work goes to at most two detached workers through
local/bin/dispatch.sh and local/bin/review.sh (caps 2/0/2); keep both workers
busy with independent tasks on different pull requests and worktrees, and refill
a slot as soon as it frees. Every turn: run
bash results/telemetry/owner-tools/status-snapshot.sh --prs, act on every actionable
line in the order of main-cycle.md section 2, gate reviewed pull requests, stage
trains in your own quiet window, record telemetry, post one comment on issue 12
per stage boundary, end the turn. Never run a worker by hand outside dispatch.sh,
never merge by hand, never do multi-minute work in your own turn, never spawn a
sub-agent thread, never grow a pull request to satisfy findings. If the worker
key is retired the caps drop: dispatch nothing more and continue with model-free
work. If the main key fails, never switch keys: post one comment on issue 12 with
the state of every in-flight item and run /goal pause. DONE = the repository is
ready to be attached as an artifact to a submission: zero sorry, the completion
gate passes on the declared commit, the official comparator accepts the challenge
for every headline theorem, and the status documents are truthful. Stop only when
the owner says so or when DONE is reached: then post one final comment on issue 12
and run /goal pause.

-->
