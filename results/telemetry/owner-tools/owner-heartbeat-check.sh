#!/usr/bin/env bash
# owner-heartbeat-check.sh (cron, hourly): while the owner session is the operator, its
# wake-up loop touches $W/owner-heartbeat. If that file is older than 100 minutes the
# session's background wait most likely died with a Claude app restart; post ONE line to the
# owner inbox (#26) per silent gap so the owner can wake the session with any message.
W=$HOME/.cache/mipstarre-dev/watchdog
[ -e "$W/owner-operator" ] || exit 0
HB=$W/owner-heartbeat; [ -e "$HB" ] || exit 0
age=$(( $(date +%s) - $(stat -c %Y "$HB") ))
if [ "$age" -le 6000 ]; then rm -f "$W/owner-heartbeat.alerted"; exit 0; fi
[ -e "$W/owner-heartbeat.alerted" ] && exit 0
export PATH=$HOME/.local/bin:$PATH
printf "%s\n" "OPERATOR SILENT: the owner session has not woken up for $((age/60)) minutes (its background wake-up dies when the Claude app process restarts). Lanes on ghz keep running; green PRs may be waiting. Send any message to the session to wake it." > /tmp/hb-alert.md
gh api repos/Dengnifer/MIPStarRE-A/issues/26/comments -F body=@/tmp/hb-alert.md > /dev/null && touch "$W/owner-heartbeat.alerted"
