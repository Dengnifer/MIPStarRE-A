# W10 — hot-editable accounts file, CLI, GitHub control channel (owner request 2026-09-12)

Owner's situation: 1-3 endpoints, each with 1-2 API keys, each key with a concurrency limit between 5 and 40 that changes during a run
(the admin reassigns slots, the owner wins them back, a key can become invalid or run out of quota). The owner must be able to
update the set of available keys and their limits WITHOUT telling the meta session by prompt.

Design (agreed with the owner 2026-09-12):
1. One owner-owned file on ghz, `~/.cache/mipstarre-dev/watchdog/accounts.json`, is the source of truth: a list of entries
   {name, endpoint, codex_home, ceiling, external_reserved, enabled, note}. Any number of endpoints and keys, one entry per key. Key
   values never appear in it (they live in the codex home the entry points at, which only the owner touches). The run brief's
   `accounts` block becomes the INITIAL content of this file (`run_mode.py apply` writes it if absent, never overwrites an existing
   file) so the brief stays one-shot while the accounts file is live.
2. The capacity controller and the router re-read the file every tick (at most 60 s stale). `ceiling` is a ceiling, never a target:
   below it the controller keeps its AIMD discovery (multiplicative decrease on refusals, additive increase while refusals are zero,
   up to ceiling minus external_reserved). Lowering the ceiling takes effect at the next tick; raising it lets the additive creep
   continue. `enabled:false` means cap 0 immediately and no probes; removing an entry means the same.
3. Validity is measured: passive classification of live-session failures per key (401/403 invalid key, INSUFFICIENT_BALANCE,
   sustained 5xx) disables the key automatically with a reason in `watchdog/capacity/health.json`; a cheap probe (`codex exec` read-only
   "Reply OK") every N minutes while disabled re-enables it when it succeeds. The owner sees the state on the hourly #27 report: one
   line per key: ceiling, effective cap, live, refusals in the last 10 minutes, health, note.
4. Owner touchpoints, no prompt to the meta: (a) `results/telemetry/owner-tools/accounts.sh list|set <name> <field> <value>|enable
   <name>|disable <name>|add <name> --endpoint --codex-home --ceiling|remove <name>|probe [name]` validates and writes the file
   atomically (temp file + rename) and appends a line to `watchdog/capacity/accounts.log`; (b) a GitHub channel for when the owner is
   away from a shell: a comment on the owner inbox issue in the fixed form `ACCOUNTS: <name> ceiling=<n> [reserved=<n>]
   [enabled=true|false]` (one or more per comment) is applied by the janitor at its next sweep, only when the comment author is the
   repository owner login recorded in local/README.md or the brief, and echoed back with a confirmation reply (`applied: ...` or
   `rejected: ...`) so the owner knows it took effect.
5. Generalize away from the historical two accounts: the router, the controller, dispatch.sh --account, lane slot counting and the
   pause/resume caps snapshot must handle N named accounts (no hard-coded "primary"/"second"); keep those two names working as
   entries for compatibility.
6. Tests: file validation (bad JSON, unknown field, negative ceiling, duplicate name), hot reload (edit between two ticks changes the
   effective cap), enabled:false -> cap 0, health disable/re-enable with stubbed probes, CLI atomic write, GitHub channel parsing and
   author check with a stubbed gh, N-account router selection. Runbook text in local/protocols/full-speed-mode.md and the owner-tools
   README: how to edit the file, the CLI, the #500 comment form, what the hourly line means.
