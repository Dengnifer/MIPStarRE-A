#!/usr/bin/env bash
# claim.sh — ONE atomic claim list for the main session and the Opus helpers.
#
# Repository copy of the operator's out-of-repo claim script (written after two
# workers repaired the same pull request at the same time).  The file format and
# the claim semantics are unchanged; the file location is configurable, so a unit
# test can drive the script without touching the operator's live list.
#
#   claim.sh claim   <main|opus> <fix|review|update|feature|report> <PR> "<note>"
#       -> exit 0 claimed, exit 3 held by someone else
#   claim.sh release <main|opus> <fix|review|update|feature|report> <PR> "<outcome and note>"
#   claim.sh check   <PR>
#       -> prints open claims, exit 3 if any, exit 0 and "free" otherwise
#
# File: $MIPSTARRE_CLAIM_FILE, default
# ${MIPSTARRE_CACHE_ROOT:-$HOME/.cache/mipstarre-dev}/watchdog/meta-dispatched.txt
# (append-only).  A PR has an open claim when the newest line of some
# "<party>-<kind> <PR> " prefix says "claimed" and no later line of that prefix
# says "released".  Any open claim blocks a new one, whatever its kind: the
# point is that exactly one worker touches a PR at a time.
#
# The number is a PR number, or an issue number for work that has no PR yet.
set -u
CACHE_ROOT="${MIPSTARRE_CACHE_ROOT:-$HOME/.cache/mipstarre-dev}"
F="${MIPSTARRE_CLAIM_FILE:-$CACHE_ROOT/watchdog/meta-dispatched.txt}"; L=$F.lock
mkdir -p "$(dirname "$F")" || { echo "cannot create $(dirname "$F")" >&2; exit 2; }
open_claims() { # PR -> prints open claim lines
  awk -v pr="$1" '$2==pr && ($1 ~ /^(main|opus)-[a-z]+$/) && ($3=="claimed" || $3=="released") { last[$1]=$0; st[$1]=$3 } END { for (k in st) if (st[k]=="claimed") print last[k] }' "$F" 2>/dev/null
}
cmd=${1:-}; case "$cmd" in
  check) pr=${2:?PR}; o=$(open_claims "$pr"); [ -z "$o" ] && { echo "free"; exit 0; }; echo "$o"; exit 3;;
  claim|release) party=${2:?party}; kind=${3:?kind}; pr=${4:?PR}; note=${5:-}
    case "$party" in main|opus) ;; *) echo "party must be main or opus" >&2; exit 2;; esac
    case "$pr" in ''|*[!0-9]*) echo "PR must be a number" >&2; exit 2;; esac
    exec 9>"$L"; flock 9
    if [ "$cmd" = claim ]; then o=$(open_claims "$pr"); if [ -n "$o" ]; then echo "HELD: $o"; exit 3; fi
      echo "$party-$kind $pr claimed $(date -u +%FT%TZ) $note" >> "$F"; echo "claimed"; exit 0
    else echo "$party-$kind $pr released $note $(date -u +%FT%TZ)" >> "$F"; echo "released"; exit 0; fi;;
  *) echo "usage: claim.sh claim|release <main|opus> <kind> <PR> [note] | check <PR>" >&2; exit 2;;
esac
