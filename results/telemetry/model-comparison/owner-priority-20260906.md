# Owner priority: useful-work Astra effort comparisons

Recorded2026-09-06T03:36:00Z by qpbt-main. This decision is not a benchmark result.

Main remains `gpt-6-astra`/`max`. New or resumed workers remain on the primary
relay, with main selecting `max` or `xhigh` by role, difficulty, observed quality
and latency. The latest owner use of “high” means `xhigh`. Fan-out remains off.

Preserve observational comparisons here with raw-session provenance, configured
and server-verified effort (unknown when not evidenced), role/task outcomes,
difficulty, elapsed time, available tokens, validation and independent-review
quality, retries/build/service delays, and explicit sample counts. Task/session/
resume denominators must be distinguished; missing measurements are not zeros.
Assignments are not randomized: observations do not establish an effort effect.

Correct the comparison README's universal effective-ultra claim using the
recorded probes, without rewriting historical run logs or relabelling unverified
Sol/Astra runs. Existing Astra probes distinguish requested `ultra` from observed
completion `medium`, and verify the sampled `max` and `xhigh` requests. They are
configuration evidence, not useful-project quality samples. No new probe,
benchmark or filler session is authorized. Keep private credential-bearing debug
logs private; use sanitized published captures and precise provenance pointers.

The existing issue237 author owns runtime/dispatcher enforcement and the narrow
README factual correction. The existing issue247 policy lane owns the subsequent
research dataset/report and evidence-led guidance, avoiding a duplicate effort
implementation. Changes use ordinary validation/review and EVOLUTION records.
Posted issue26 items, including B7 and any later B8, remain human-owner decisions.

Durable repository evidence:
- `results/telemetry/owner-messages/qpbt-meta-20260905-230133/effort-probes.json`
- `results/telemetry/owner-messages/qpbt-meta-20260905-230133/effort-verification.md`
- `results/telemetry/owner-messages/qpbt-meta-20260905-230133/relay-throughput-limit-incident.json`
- `results/telemetry/owner-messages/qpbt-effort-admission-20260906.md`
- `results/telemetry/sessions.jsonl` and each row's published capture/final report
- `results/telemetry/events.md`,2026-09-06 relay-recovery/research boundary

The pending report must state usable sample counts and limitations explicitly;
no causal max-versus-xhigh conclusion is adopted by this owner priority.
