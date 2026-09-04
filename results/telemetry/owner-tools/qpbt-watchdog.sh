#!/usr/bin/env bash
# qpbt-watchdog.sh — owner-side stall guard for the MIPStarRE-qpbt operator session.
# Runs from cron (hourly). Detects: (1) github/main unchanged for too long,
# (2) open PRs that are fully green on their exact head but unmerged, (3) PRs past
# the review-round limit, (4) a paused/stalled/idle operator pane.  On a trip it
# nudges the tmux session with a standing instruction and, rate-limited, posts one
# plain-language comment on the pinned Owner inbox (#26) so the owner sees it.
# Lives OUTSIDE the repository on purpose (no PR, no review, no scope budget).
set -u
export PATH="$HOME/.local/bin:$HOME/.elan/bin:/usr/local/bin:/usr/bin:/bin"
REPO="$HOME/MIPStarRE-qpbt"; SLUG="Dengnifer/MIPStarRE-A"; SESSION="qpbt"; INBOX=26
STATE="$HOME/.cache/mipstarre-dev/watchdog"; mkdir -p "$STATE"
STALE_H="${QPBT_STALE_HOURS:-4}"        # main unchanged for this long => stall
GREEN_MIN="${QPBT_GREEN_MINUTES:-60}"   # green-but-unmerged PR older than this => stall
ROUNDS_MAX="${QPBT_ROUNDS_MAX:-2}"      # review rounds beyond this => churn
POST_EVERY_H="${QPBT_POST_EVERY_HOURS:-6}"
now=$(date +%s); log() { printf '%s %s\n' "$(date -u +%FT%TZ)" "$*" >> "$STATE/watchdog.log"; }

cd "$REPO" || exit 1
git fetch -q github 2>/dev/null || { log "fetch failed"; exit 0; }
main_age_h=$(( (now - $(git log -1 --format=%ct github/main)) / 3600 ))

green=(); churn=()
while read -r n head updated; do
  [ -n "$n" ] || continue
  st=$(gh api "repos/$SLUG/commits/$head/status" --jq '[.statuses[] | select(.context=="local-ci/summary" or .context=="local-review/summary") | .context+"="+.state] | sort | join(" ")' 2>/dev/null)
  rounds=$(gh api "repos/$SLUG/pulls/$n/reviews" --jq '[.[] | select(.body|contains("mipstarre-review"))] | length' 2>/dev/null || echo 0)
  age_min=$(( (now - $(date -d "$updated" +%s)) / 60 ))
  case "$st" in *"local-ci/summary=success"*"local-review/summary=success"*)
    [ "$age_min" -ge "$GREEN_MIN" ] && green+=("#$n") ;; esac
  [ "${rounds:-0}" -gt "$ROUNDS_MAX" ] && churn+=("#$n(${rounds} rounds)")
done < <(gh pr list --repo "$SLUG" --state open --json number,headRefOid,updatedAt --jq '.[] | "\(.number) \(.headRefOid) \(.updatedAt)"')

pane=$(tmux capture-pane -p -t "$SESSION" 2>/dev/null | tail -3)
pane_state=running
if [ -f "$STATE/owner-operator" ]; then pane_state=running   # the owner session is the operator; no codex pane expected
elif [ -z "$pane" ]; then pane_state=missing
elif ! printf '%s' "$pane" | grep -q "gpt-5.6-sol"; then pane_state=no-codex
elif printf '%s' "$pane" | grep -qi "Goal paused\|Goal stalled\|Goal marked blocked"; then pane_state=paused
fi

trips=()
[ "$main_age_h" -ge "$STALE_H" ] && trips+=("main unchanged for ${main_age_h}h")
[ ${#green[@]} -gt 0 ] && trips+=("green but unmerged: ${green[*]}")
[ ${#churn[@]} -gt 0 ] && trips+=("review churn: ${churn[*]}")
[ "$pane_state" != running ] && trips+=("operator pane: $pane_state")
log "main_age=${main_age_h}h green=[${green[*]:-}] churn=[${churn[*]:-}] pane=$pane_state trips=${#trips[@]}"
[ ${#trips[@]} -eq 0 ] && exit 0

# 1) nudge the operator (every run while tripped; harmless if it is already acting)
if [ "$pane_state" = running ] || [ "$pane_state" = paused ]; then
  msg="WATCHDOG (owner-side, automatic): $(IFS='; '; echo "${trips[*]}"). Standing owner rule: merge every PR whose exact head is CI-green and review-green NOW (pr_merge.py); adjudicate any PR past ${ROUNDS_MAX} review rounds at its current head under review.md section 12 instead of another round; never grow a PR to satisfy findings; then return to mathematics. Report in #27."
  printf '%s\n' "$msg" > "$STATE/nudge.txt"
  tmux load-buffer "$STATE/nudge.txt" && tmux paste-buffer -p -t "$SESSION" && sleep 1 && tmux send-keys -t "$SESSION" Enter
  sleep 2; tmux capture-pane -p -t "$SESSION" | tail -2 | grep -q "tab to queue" && tmux send-keys -t "$SESSION" Tab
  [ "$pane_state" = paused ] && { sleep 2; tmux send-keys -t "$SESSION" "/goal resume" Enter; sleep 1; tmux send-keys -t "$SESSION" Enter; }
fi

# 2) tell the owner, at most once per POST_EVERY_H hours
last=$(cat "$STATE/last-post" 2>/dev/null || echo 0)
if [ $(( now - last )) -ge $(( POST_EVERY_H * 3600 )) ]; then
  body="### WATCHDOG — the project looks stalled ($(date -u +%Y-%m-%d\ %H:%MZ))
<!-- watchdog status=open -->
**What I see:** $(IFS='; '; echo "${trips[*]}").
**What happened automatically:** the operator session was nudged to merge the green PRs, adjudicate churning ones, and go back to mathematics.
**What you can do:** nothing, unless the next watchdog report (in ${POST_EVERY_H}h) still shows the same — then check \`tmux attach -t $SESSION\` or ask Claude.
<details><summary>Details</summary>main age ${main_age_h}h; green-unmerged: ${green[*]:-none}; churn: ${churn[*]:-none}; pane: $pane_state</details>"
  gh api "repos/$SLUG/issues/$INBOX/comments" -f body="$body" >/dev/null 2>&1 && echo "$now" > "$STATE/last-post" && log "posted to #$INBOX"
fi
