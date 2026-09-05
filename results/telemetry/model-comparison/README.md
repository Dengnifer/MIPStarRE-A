# codex model comparison — `gpt-5.6-sol` vs `gpt-6-astra`

The models did not historically run at the same provider-reported effort.
Debug probes on 2026-09-05 showed that the astra endpoint reported `medium` for
an `ultra` request, while it honoured `xhigh`; sol honoured its legacy `ultra`
request as `max`. Astra rows before the 22:25Z handoff boundary must therefore
be read as provider-reported `medium`. New astra dispatches request `xhigh`, and
sol retains `ultra`. The tables do not stratify these periods by effort.

A side product of the model switch on 2026-09-05: `gpt-6-astra` became the
default for codex sessions at 2026-09-05T15:46Z, and `gpt-5.6-sol` — used for
everything before that — is now kept by operator choice for "really easy"
subagents. This directory answers one question for the owner: **which roles can
sol keep?** It is a rough, re-runnable descriptive comparison, not an
experiment.

## Re-run

    python3 results/telemetry/model-comparison/compare.py

Standard library only, no arguments, finishes in seconds. It prints the report
and rewrites `latest.md`, then appends one dated line to the run log at the
bottom of this file. It reads `results/telemetry/sessions.jsonl`, the capture
and rollout event streams, the lane logs under
`~/.cache/mipstarre-dev/watchdog/lanes/`, and pull-request state; it writes
nothing outside this directory except a pull-request cache under
`~/.cache/mipstarre-dev/model-comparison/`.

## How the model is derived

New dispatcher rows in `sessions.jsonl` record the selected model and account.
`compare.py` prefers that explicit identity, retaining fallback for older rows,
and reports how many rows came from each source:

1. **registry** — the nonempty `model` field, explicitly pinned by the dispatcher.
2. **capture / rollout** — the codex event stream. The rollout named in the
   `rollout` field carries the model in three places (`session_meta`'s
   `base_instructions.provenance.model`, `turn_context.model`,
   `world_state.state.model`). The per-session capture
   (`results/telemetry/sessions/<name>.jsonl`, `codex exec --json`) carries no
   model field today; it is scanned first anyway so a future capture format is
   picked up for free.
3. **lane log** — `dispatch <role> for #N (model <name>, attempt k)` in
   `~/.cache/mipstarre-dev/watchdog/lanes/<issue>.lane.log`, used only when every
   such line for that issue names the same model. Lane logs are a runtime cache
   and cover only recent lanes.
4. **time rule** — last resort: sessions starting before 2026-09-05T15:46Z are
   attributed to sol, later ones to astra. This is the weakest source; it cannot
   see a per-dispatch `MIPSTARRE_CODEX_MODEL` override.

Models other than sol and astra appear as their own rows when they show up
(smoke tests have used `gpt-5.6-luna` and `gpt-5`).

New rows may also contain `requested_effort`, the effective override passed to
the CLI after dispatcher normalization. It is request telemetry, not a measured
provider response. Historical rows omit it, and the September 5 probes above
remain the evidence for provider-reported effort in those sessions.

## Reading the tables

One table per role. Roles come from `sessions.jsonl`, except that autofix
**fixer** sessions are split out: `local/bin/autofix.sh` dispatches them with
`--role prover --issue pr<N>`, so a prover row whose issue is `pr<N>` is a fixer
and a prover row whose issue is a bare issue number is a lane prover.

- `in tok med` is `usage.input`, which already includes cached input;
  `cached in` is `sum(cached_input) / sum(input)` over the group.
- Prover and fixer rows get an outcome pair: the share of sessions whose
  worktree branch matches a pull request at all, and the share of those that
  merged. Sessions on branches that were renamed or never pushed show up as not
  opened.
- Reviewer rows get the median number of ledger findings in the review the
  session produced, taken from `results/telemetry/reviews/` when exactly one
  body matches the PR and otherwise from the session's own `.last.md`; `n=` is
  how many sessions it was derivable for. Only three review bodies are archived
  under `results/telemetry/reviews/`, so almost every count comes from
  `.last.md`.

## The assignment bias — read this before drawing a conclusion

Models are **not** assigned at random. Sol ran everything up to the switch, so
its rows cover the whole history of the project including its messiest phases;
astra rows start after it. From the switch onward the operator deliberately
sends the *easy* subagents to sol, so any later sol/astra difference measures
the task mix at least as much as the model. Wall time also depends on machine
load, build-cache warmth and lane retries, and token counts depend on how much
context a persona was handed. Treat every number here as descriptive, and use
the outcome and findings columns — not the token or wall-time columns — when
deciding whether sol can keep a role.

## Run log

Appended by `compare.py`, one line per run.

- 2026-09-05T16:05Z — 570 sessions: gpt-5.6-sol 560, gpt-5.6-luna 4, gpt-6-astra 4, gpt-5 2
- 2026-09-05T17:22Z — 597 sessions: gpt-5.6-sol 560, gpt-6-astra 31, gpt-5.6-luna 4, gpt-5 2
- 2026-09-05T17:35Z — 605 sessions: gpt-5.6-sol 564, gpt-6-astra 35, gpt-5.6-luna 4, gpt-5 2
- 2026-09-05T17:41Z — 610 sessions: gpt-5.6-sol 565, gpt-6-astra 39, gpt-5.6-luna 4, gpt-5 2
- 2026-09-05T18:20Z — 622 sessions: gpt-5.6-sol 566, gpt-6-astra 50, gpt-5.6-luna 4, gpt-5 2
