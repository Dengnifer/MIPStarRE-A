# Worker occupancy enforcement, 2026-09-08

The owner requires at least `ceil(0.8*(k-1))` useful active subagents almost all the time. At total capacity 10, main occupies one slot and workers have nine slots with a floor of eight. There is no additional reservation.

The previous allocation correction did not enforce replenishment. Its activity command recorded counts, while the persistent trigger merely queued prompts behind a long main turn. Independent observations confirmed that activity could fall to two despite available capacity.

Meta guided main to maintain an approved successor queue and delegate refill mechanics. Main selected all work and retained assignment, review and merge authority. The delegate started at 08:16:37Z. The attached receipts record actual natural completions and successor tool output, including recovery delays; configuration and queue acceptance are not counted as recovery. The primary coordinator recorded an observation-only policy acknowledgment at 08:49:30Z. Later capability verification established that its context exposed neither `collaboration.list_agents` nor `collaboration.followup_task`, so executable control never transferred. Main retained `/root/astra_refill_coordinator` without expiry until a successor demonstrates both operations and verified useful activity. The historical acknowledgment and its correction are both retained.

See `summary.json` for the bounded measurements, exact transition times, failed handoff, and final capability verification. The compact journals preserve worker identities and turn IDs without raw prompts, credentials or model content. Historical unclosed turns without recent activity are excluded. Six sampler regression tests cover completion, resume, stale activity, inherited history, interruption and root-scoped incremental reads.

These observations measure current worker activity, not endpoint request concurrency or mathematical productivity. They establish bounded behavior and retain limitations rather than asserting a guarantee about all future work. Session records are in `owner-sessions.jsonl`; unavailable per-helper usage remains null. Main owns normal telemetry publication.

The continuing episode is preserved in the refreshed delegate and vacancy-trigger
receipts in this directory. `/root/astra_refill_coordinator` remains the sole
demonstrated executable refill owner without expiry; the primary integration
coordinator observes activity and owns manual telemetry and service gates, but its
three observation-only handoff acknowledgments did not demonstrate native
`list_agents` or `followup_task` capability. Activity fell below the floor during
several completion boundaries and was restored by measured successor starts. The
archived status snapshot preserves the latest observed count at the publication
boundary; the journals retain the preceding observations at six, seven and eight.
These later records do not rewrite or backdate the earlier measurements.
