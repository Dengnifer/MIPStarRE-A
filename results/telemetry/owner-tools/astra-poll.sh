#!/usr/bin/env bash
# astra-poll.sh — hourly (cron) check, via a codex subagent on ghz, whether the
# "astra" model is configured in ~/.codex/config.toml. Writes the answer to
# $STATE/astra.txt and, the first time astra appears, posts a note on the
# pinned Owner inbox (#26) so both the owner and the operator session see it.
set -u
export PATH="$HOME/.local/bin:$HOME/.elan/bin:/usr/local/bin:/usr/bin:/bin"
STATE="$HOME/.cache/mipstarre-dev/watchdog"; mkdir -p "$STATE"
OUT="$STATE/astra.txt"; LOG="$STATE/astra-poll.log"
CFG="$HOME/.codex/config.toml"
answer=$(cd "$HOME" && timeout 300 codex exec --sandbox read-only -m gpt-5.6-sol \
  "Read the file $CFG. If it defines a model, model_provider, or profile whose name or model id contains the substring 'astra', reply with exactly one line: ASTRA=<the exact model id to pass to codex -m>. Otherwise reply with exactly one line: ASTRA=none. No other text." 2>/dev/null \
  | grep -o 'ASTRA=[^[:space:]]*' | tail -1)
[ -n "$answer" ] || answer="ASTRA=unknown"
printf '%s %s\n' "$(date -u +%FT%TZ)" "$answer" >> "$LOG"
printf '%s\n' "$answer" > "$OUT"
case "$answer" in
  ASTRA=none|ASTRA=unknown) exit 0 ;;
esac
if [ ! -f "$STATE/astra-announced" ]; then
  gh api repos/Dengnifer/MIPStarRE-A/issues/26/comments \
    -f body="### NOTE — astra model detected ($(date -u +%Y-%m-%d\ %H:%MZ))
<!-- astra-poll -->
**What happened:** the hourly poller found \`${answer#ASTRA=}\` configured in codex on ghz. The owner session will switch subagent dispatches to it at the next dispatch (no action needed from the owner unless the id is wrong)." >/dev/null 2>&1 \
    && touch "$STATE/astra-announced"
fi
