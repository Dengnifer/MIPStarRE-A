## Session summary
Enabled built-in search in [config.toml](/home/drx/.cache/mipstarre-dev/codex-home-cpa/config.toml):

```text
old: <no top-level web_search setting>
new: web_search = "live"
```

All existing key/value lines and mode `600` were preserved; one redundant trailing blank line was normalized. Other Codex-home configs and `~/.codex/config.toml` retained their hashes. Repository HEAD `391d6fc` remains clean.

Codex CLI `0.153.4` recognizes top-level `web_search`; official documentation specifies `live` and marks `features.web_search_request` legacy. citeturn0view0

Exact probe:

```bash
CODEX_HOME=/home/drx/.cache/mipstarre-dev/codex-home-cpa /home/drx/.local/bin/codex exec --skip-git-repo-check --sandbox read-only -m gpt-5.6-sol --json 'Use the built-in web search tool now, not shell commands or memory, to open https://linux.do/t/topic/2828197/9. State whether post 9 is readable and summarize its Codex web-search configuration claim in one sentence. If it is not readable, search the official OpenAI Codex configuration reference for the web_search setting instead. Include the exact source URL actually used.'
```

Exit `0`. Thread `01a0a018-f837-7431-adbc-f69f8027c48b` recorded OpenAI, `gpt-5.6-sol`, `ultra`, and read-only sandbox. JSON recorded a completed native `web_search_call` opening the exact linux.do URL. The probe reported post 9 was readable but contained no web-search configuration claim, only a CPA/New API login-loss question.

## Goal alignment
Owner task and required #27 evidence are complete in session `orc-cpa-web-search-20260914-01`. Only the authorized config was manually edited; no workers, CI, review, publication, or repository changes occurred.

## Recommendation
Stop.