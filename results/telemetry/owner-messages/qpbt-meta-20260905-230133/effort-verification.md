# ghz Astra effort verification

Recorded: 2026-09-05T23:26:36Z. CLI: `codex-cli 0.152.1`.

Fresh, ephemeral calls invoked `/home/drx/.local/bin/codex` directly, bypassing the worker shim. Each account used its existing Codex home and credentials. The prompt requested only `OK`, with tools prohibited, read-only sandbox and multi-agent fan-out disabled. Raw debug logs remain private under `/tmp` and are not part of this packet.

| Account | CLI request | Client trace | Completion log effort |
| --- | --- | --- | --- |
| primary | max | max | max |
| primary | ultra | ultra | medium |
| primary | xhigh | xhigh | xhigh |
| second | max | max | max |
| second | ultra | ultra | medium |
| second | xhigh | xhigh | xhigh |

Both accounts consistently distinguish `ultra` (completion log `medium`) from `max` (completion log `max`) and `xhigh` (completion log `xhigh`). This reproduces the historical Ultra observation and establishes that a fresh `max` request is accepted with maximum-effort metadata. It does not locate the transformation in the CLI, provider, or upstream API, nor prove actual backend compute. The outgoing wire body was not captured; do not call the client trace a wire measurement. Tiny-probe reasoning token counts are not an effort benchmark.

Official Codex documentation describes Ultra as maximum reasoning with automatic delegation, while the Astra API lists `max`. Thus `max` is consistent with maximum reasoning. The project still explicitly disables Codex fan-out; no fan-out or configuration change was made by the probes. The owner has been asked whether to use verified `max` or their literal `xhigh` fallback. Until answered, existing Astra xhigh remains in force.

Sources: [Codex models](https://learn.chatgpt.com/docs/models), [Subagents](https://learn.chatgpt.com/docs/agent-configuration/subagents), [Astra API model](https://developers.openai.com/api/docs/models/gpt-6-astra), [Reasoning guide](https://developers.openai.com/api/docs/guides/reasoning).

The reasoning guide notes that response effort metadata can remain request-level when configuration_update changes effective effort. These probes used fresh sessions with no such update.
