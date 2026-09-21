#!/usr/bin/env bash
# owner-heartbeat-check.sh — the stall guard, run from cron (hourly is enough).
# A stall guard must live OUTSIDE the thing it guards: while a chat session is the
# operator, its wake-up loop touches <state>/owner-heartbeat, and that loop dies silently
# whenever the app restarts.  When the marker is older than the limit (default 100
# minutes) this posts ONE line to the owner-inbox issue per silent gap, so the owner can
# wake the session with any message.  It does nothing unless <state>/owner-operator
# exists, so it is harmless to install early.
# Provenance: the origin's owner-tools/owner-heartbeat-check.sh (cache directory and
# issue number hard-coded).
set -u
HERE="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd -P)"
CFG="$HERE/../../../local/bin/session/config.sh"
# shellcheck source=/dev/null
[ -f "$CFG" ] && . "$CFG" 2>/dev/null
W="${KIT_STATE_DIR:-${KIT_CACHE_ROOT:-$HOME/.cache/paperlib-dev}/watchdog}"
LIMIT="${KIT_HEARTBEAT_LIMIT_SECONDS:-6000}"
export PATH="$HOME/.local/bin:$PATH"

[ -e "$W/owner-operator" ] || exit 0
HB="$W/owner-heartbeat"; [ -e "$HB" ] || exit 0
age=$(( $(date +%s) - $(stat -c %Y "$HB" 2>/dev/null || echo 0) ))
if [ "$age" -le "$LIMIT" ]; then rm -f "$W/owner-heartbeat.alerted"; exit 0; fi
[ -e "$W/owner-heartbeat.alerted" ] && exit 0

ISSUE="${KIT_OWNER_INBOX_ISSUE:-}"
SLUG="${KIT_GITHUB_SLUG:-}"
case "$SLUG" in ""|OWNER/*) SLUG="$(git -C "${KIT_REPO_ROOT:-$HERE/../../..}" remote get-url github 2>/dev/null | sed -nE -e 's#^.*github\.com[:/]##p' | sed -E 's#\.git$##')";; esac
[ -n "$ISSUE" ] && [ -n "$SLUG" ] || {
  echo "operator silent for $((age/60)) min, but no owner-inbox issue or repository is configured" >&2; exit 0; }

BODY="$W/heartbeat-alert.md"
printf '%s\n' "OPERATOR SILENT: the operating session has not woken up for $((age/60)) minutes (its background wake-up dies when the app process restarts). Work already started on the machine keeps running; green PRs may be waiting. Send any message to the session to wake it." > "$BODY"
gh api "repos/$SLUG/issues/$ISSUE/comments" -F body=@"$BODY" > /dev/null && touch "$W/owner-heartbeat.alerted"
