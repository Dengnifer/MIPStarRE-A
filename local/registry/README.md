# `local/registry/`

Small append-only registries that keep two workers from producing the same
result twice (issue #576).

## `declaration-claims.jsonl`

One JSON object per line, newest last, written only by
`local/bin/dup_check.py claim` / `claims-release`:

```json
{"action": "claim", "by": "meta", "issue": 576, "names": ["MIPStarRE.QPBT.foo"], "nodes": ["lem:foo"], "note": "…", "ts": "2026-09-17T12:00:00Z"}
{"action": "release", "issue": 576, "note": "merged", "ts": "2026-09-17T18:00:00Z"}
```

An issue's claim is **open** when its newest row is a `claim`. A new claim is
refused (exit 3) when one of its names is already held by another issue's open
claim, or when `github/main` already declares it; `--force` records it anyway
and still exits 3, so the override is visible in the log.

Nothing reads this file as a source of truth about the mathematics — the Lean
sources and the blueprint remain that. It records *intent*, so issue creation
and dispatch can see an overlap before a prover run pays for it.
