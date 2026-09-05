
## Token accounting (2026-09-05)

Every subagent's token cost is recorded: codex workers and reviewers in `sessions.jsonl` (`usage`: input, cached input, cache writes, output, reasoning tokens from the codex JSON stream, written by `local/bin/dispatch.sh`); Claude subagents in `owner-sessions.jsonl` (`tokens`: the total reported by the Claude Code harness per subagent, plus `tool_uses` and `wall_s`; start stubs carry `status: running` until the operator appends or patches the end record). `owner-tools/session-usage.py --md` regenerates `usage-summary.md` (totals by pool, model and role).
