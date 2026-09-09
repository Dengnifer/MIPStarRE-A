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
# Real availability check first: ask the relay for the astra model itself (codex must run
# inside a trusted git checkout on ghz; $HOME is not one, which made every earlier poll "unknown").
REPO="$HOME/MIPStarRE-qpbt"
answer=""
for cand in $(grep -o -E '[A-Za-z0-9._-]*astra[A-Za-z0-9._-]*' "$CFG" 2>/dev/null | sort -u) gpt-6-astra gpt-5.6-astra; do
  if (cd "$REPO" && timeout 240 codex exec --sandbox read-only --skip-git-repo-check -m "$cand" \
        "Reply with exactly one line: PROBE-OK" 2>/dev/null | grep -q "PROBE-OK"); then answer="ASTRA=$cand"; break; fi
done
[ -n "$answer" ] || answer="ASTRA=none"
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
**What happened:** the hourly poller reached \`${answer#ASTRA=}\` through the codex relay on ghz. The owner session will switch subagent dispatches to it at the next dispatch (no action needed from the owner unless the id is wrong)." >/dev/null 2>&1 \
    && touch "$STATE/astra-announced"
fi
