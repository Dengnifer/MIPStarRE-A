#!/usr/bin/env bash
# key-watch.sh — notice that an API key has stopped working, prove it, and take
# the key out of use.  A retired key is never brought back by this script.
#
# Provenance: the origin project's key-watch-v7.sh, including the rule it was
# rewritten for: pane text and worker logs are HINTS, never evidence.  A pane
# can quote an error string out of a diff, and that once retired two healthy
# keys and paused a whole day of work.  A key is retired only after a DIRECT
# probe of its own endpoint fails: once when the answer names a quota or auth
# refusal, twice 45 s apart for a bare 401/402/403/429/503.
#
#   key-watch.sh [watch]            the loop (default)
#   key-watch.sh once               one pass, then exit
#   key-watch.sh confirm <key> "<hint>"   run the decision and print it
#   key-watch.sh retire <key> "<reason>"  take a key out of use now
#   key-watch.sh status             what is retired and why
#   stop the loop with: touch "$KIT_STATE_DIR/key-watch.stop"
#
# Consequences: a worker key -> rotation off and the worker caps come down;
# the MAIN session's key -> the cutoff marker (no new work starts, running work
# finishes, the merge queue keeps merging; this is not a pause).
set -u
. "$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)/lib.sh"

# --- what counts as an error (all overridable; a conf file wins over the default)
[ -r "$KIT_STATE_DIR/key-watch.conf" ] && . "$KIT_STATE_DIR/key-watch.conf"
# codex's OWN error events, not the vocabulary of an error
HARD_RE="${KIT_KEYWATCH_HARD_RE:-unexpected status 40[123]|INSUFFICIENT_BALANCE|API_KEY_DISABLED|invalid_api_key|last status: 429 Too Many Requests|quota exhausted|rate_limit_exceeded}"
SOFT_RE="${KIT_KEYWATCH_SOFT_RE:-unexpected status 503}"
SOFT_MIN="${KIT_KEYWATCH_SOFT_MIN:-3}"
# an answer body that names a quota or auth refusal needs no second probe
BODY_RE="${KIT_KEYWATCH_BODY_RE:-quota exhausted|insufficient balance|insufficient_quota|INSUFFICIENT_BALANCE|API_KEY_DISABLED|invalid_api_key}"
CODES_RE="${KIT_KEYWATCH_CODES_RE:-^(401|402|403|429|503)$}"
PANE_RE="${KIT_KEYWATCH_PANE_RE:-Stream disconnected[^\\n]{0,80}(401|403|INSUFFICIENT_BALANCE|API_KEY_DISABLED)|unexpected status 40[13]}"
RECHECK_S="${KIT_KEYWATCH_RECHECK_S:-45}"
CONFIRM_GAP="${KIT_KEYWATCH_CONFIRM_GAP:-600}"
INTERVAL="${KIT_KEYWATCH_INTERVAL:-60}"
CAPTURE_DIR="${KIT_SESSION_CAPTURE_DIR:-$KIT_CACHE_ROOT/sessions}"

K="$KIT_STATE_DIR/key-disabled"
KEYROT="$KIT_CACHE_ROOT/keyrot"
KEYROT_OFF="$KIT_CACHE_ROOT/keyrot-off"
LOG="$KIT_STATE_DIR/key-watch.log"
kit_state_dir; mkdir -p "$K" 2>/dev/null || true
klog() { printf '%s %s\n' "$(kit_now)" "$*" >> "$LOG" 2>/dev/null || true; printf '%s\n' "$*"; }

main_key() { cat "$KIT_STATE_DIR/main-key" 2>/dev/null || printf '%s\n' "$KIT_MAIN_KEY"; }
cap_read() { cat "$KIT_STATE_DIR/$1" 2>/dev/null || echo 0; }
cap_write() { printf '%s\n' "$2" > "$KIT_STATE_DIR/$1"; }
caps_total() { cap_write max-codex "$(( $(cap_read max-codex-primary) + $(cap_read max-codex-second) ))"; }

comment_body() { # event, key, reason
  local tpl="$KIT_STATE_DIR/key-watch-comment.tmpl" out
  if [ -r "$tpl" ]; then
    out="$(mktemp "${TMPDIR:-/tmp}/kit-kw.XXXXXX")"
    kit_render "$tpl" "$out" "EVENT=$1" "KEY=$2" "REASON=$3" "TIME=$(date -u +%H:%MZ)" \
      "CAPS=$(cap_read max-codex-primary)/$(cap_read max-codex-second)/$(cap_read max-codex)" >/dev/null
    cat "$out"; rm -f "$out"; return 0
  fi
  printf '%s\n' "**Key watch $(date -u +%H:%MZ) — $1: $2**

$3

Worker caps are now primary $(cat_or 0 max-codex-primary) / second $(cat_or 0 max-codex-second) / total $(cat_or 0 max-codex). The key stays out of use until the owner says it has quota again; nothing switches keys by itself."
}
cat_or() { cat "$KIT_STATE_DIR/$2" 2>/dev/null || printf '%s' "$1"; }

# --- retirement -------------------------------------------------------------
kw_cutoff() { # reason
  [ -e "$KIT_STATE_DIR/cutoff" ] && return 0
  if kit_is_dry; then klog "DRY cutoff: $1"; return 0; fi
  printf '%s %s\n' "$(kit_now)" "$1" > "$KIT_STATE_DIR/cutoff"
  cap_write max-codex-primary 0; cap_write max-codex-second 0; cap_write max-codex 0
  kit_daemon_stop goal-keeper >/dev/null 2>&1 || true
  touch "$KIT_STATE_DIR/goal-keeper.stop"   # latched: nothing re-sends a goal into a cut-off session
  klog "CUTOFF: $1 — caps 0, goal keeper stopped. No new work starts; running work finishes; the merge queue keeps merging. This is NOT a pause."
  setsid nohup bash "${KIT_SAY:-$KIT_SESSION_DIR/say.sh}" --mode interrupt --grace 120 \
    "CUTOFF (key watch): the main session's API key no longer answers. Do not dispatch any new worker or delegate; let running work finish; the merge queue keeps merging approved work. Post one closing progress comment with the state of every in-flight item, then /goal pause and stay idle until the operator resumes you." \
    >> "$KIT_STATE_DIR/key-watch.say.log" 2>&1 < /dev/null &
  kit_issue_comment "$(comment_body 'CUTOFF' "$(main_key)" "$1")" >/dev/null
}

kw_retire() { # key, reason
  # one name per statement: bash expands a whole `local` line before it assigns,
  # so `local a=$1 b=$a` would read an unset b under set -u
  local key="${1:?key}" reason="${2:?reason}"
  local name cur
  name="$key"; cur="$(main_key)"
  [ "$key" = "$cur" ] && name=main
  [ -e "$K/$name" ] && { klog "$name is already retired ($(head -c 200 "$K/$name"))"; return 0; }
  if kit_is_dry; then klog "DRY retire $key (as '$name'): $reason"; return 0; fi
  printf '%s %s\n' "$(kit_now)" "$reason" > "$K/$name"
  if [ -d "$KEYROT/$key" ]; then
    mkdir -p "$KEYROT_OFF" 2>/dev/null || true
    mv "$KEYROT/$key" "$KEYROT_OFF/$key" 2>/dev/null || true
  fi
  if [ "$name" = main ]; then
    klog "RETIRED the main session's key '$key': $reason"
    kw_cutoff "the main session's key '$key' failed: $reason"
  else
    local n; n="$(cap_read max-codex-primary)"
    [ "$n" -gt 0 ] && cap_write max-codex-primary "$((n-1))"
    caps_total
    klog "RETIRED worker key '$key': $reason — rotation off, caps now $(cap_read max-codex-primary)/$(cap_read max-codex-second)/$(cap_read max-codex)"
    kit_issue_comment "$(comment_body 'key retired' "$key" "$reason")" >/dev/null
  fi
}

# --- the confirmed-failure decision ----------------------------------------
probe_once() { bash "$KIT_SESSION_DIR/probe-key.sh" "${1:?key}" 2>&1; }
probe_code() { printf '%s\n' "$1" | tail -n 1 | grep -o 'HTTP[0-9]*$' | sed 's/^HTTP//'; }

kw_confirm() { # key, hint -> prints "decision=<retire|transient|not-retired|throttled|already-retired>"
  local key="${1:?key}" hint="${2:-}" stamp now body code body2 code2 name="$1"
  [ "$key" = "$(main_key)" ] && name=main
  if [ -e "$K/$name" ]; then printf 'decision=already-retired key=%s\n' "$key"; return 0; fi
  stamp="$KIT_STATE_DIR/key-watch.confirm-$key"
  now="$(date +%s)"
  if [ -f "$stamp" ] && [ "$(( now - $(cat "$stamp" 2>/dev/null || echo 0) ))" -le "$CONFIRM_GAP" ]; then
    printf 'decision=throttled key=%s\n' "$key"; return 0
  fi
  printf '%s\n' "$now" > "$stamp" 2>/dev/null || true

  body="$(probe_once "$key")"; code="$(probe_code "$body")"
  if printf '%s\n' "$body" | grep -q -i -E "$BODY_RE"; then
    klog "$hint; a direct probe of '$key' names a quota/auth refusal (HTTP ${code:-000})"
    kw_retire "$key" "$hint; a direct probe confirms a quota/auth refusal (HTTP ${code:-000})"
    printf 'decision=retire key=%s probe=%s reason=body\n' "$key" "${code:-000}"; return 0
  fi
  if printf '%s\n' "${code:-000}" | grep -q -E "$CODES_RE"; then
    sleep "$RECHECK_S"
    body2="$(probe_once "$key")"; code2="$(probe_code "$body2")"
    if printf '%s\n' "${code2:-000}" | grep -q -E "$CODES_RE"; then
      kw_retire "$key" "$hint; two direct probes confirm (HTTP ${code:-000}, then HTTP ${code2:-000})"
      printf 'decision=retire key=%s probe=%s probe2=%s reason=two-probes\n' "$key" "${code:-000}" "${code2:-000}"; return 0
    fi
    klog "$hint; first probe of '$key' HTTP ${code:-000}, second HTTP ${code2:-000}: transient, NOT retired"
    printf 'decision=transient key=%s probe=%s probe2=%s\n' "$key" "${code:-000}" "${code2:-000}"; return 0
  fi
  klog "$hint, but a direct probe of '$key' answers HTTP ${code:-000}: NOT retired (pane text and worker logs are hints, not evidence)"
  printf 'decision=not-retired key=%s probe=%s\n' "$key" "${code:-000}"; return 0
}

# --- attribution ------------------------------------------------------------
key_of_home() { # CODEX_HOME path -> configured key name, empty when unknown
  local home="${1:-}" name
  [ -n "$home" ] || return 0
  while read -r name; do
    [ -n "$name" ] || continue
    [ "$(kit_key_home "$name")" = "$home" ] && { printf '%s\n' "$name"; return 0; }
  done <<EOF
$(kit_key_names)
EOF
  return 0
}

key_of_capture() { # a session capture file -> the key its process runs on
  local file="${1:?}" name p home
  name="$(basename "$file" .jsonl)"
  for p in $(pgrep -f 'codex' 2>/dev/null || true); do
    tr '\0' '\n' < "/proc/$p/cmdline" 2>/dev/null | grep -q -- "$name" || continue
    home="$(tr '\0' '\n' < "/proc/$p/environ" 2>/dev/null | grep '^CODEX_HOME=' | cut -d= -f2- | head -n 1)"
    key_of_home "$home"; return 0
  done
  return 0
}

# --- one pass ---------------------------------------------------------------
one_pass() {
  local f name hard soft key pane
  # (1) worker session captures written in the last few minutes
  if [ -d "$CAPTURE_DIR" ]; then
    for f in $(find "$CAPTURE_DIR" -maxdepth 1 -name '*.jsonl' -mmin -"${KIT_KEYWATCH_CAPTURE_AGE_MIN:-3}" 2>/dev/null || true); do
      name="$(basename "$f" .jsonl)"
      grep -q -x "$name" "$KIT_STATE_DIR/key-watch.handled" 2>/dev/null && continue
      hard="$(grep -E '^\{"type":"error"' "$f" 2>/dev/null | grep -c -E "$HARD_RE" || true)"
      soft="$(grep -E '^\{"type":"error"' "$f" 2>/dev/null | grep -c -E "$SOFT_RE" || true)"
      if [ "${hard:-0}" -ge 1 ] || [ "${soft:-0}" -ge "$SOFT_MIN" ]; then
        key="$(key_of_capture "$f")"
        if [ -z "$key" ]; then klog "errors in capture $name but no configured key could be attributed (hard=$hard soft=$soft)"; continue; fi
        printf '%s\n' "$name" >> "$KIT_STATE_DIR/key-watch.handled"   # one capture is a hint at most once
        kw_confirm "$key" "worker capture $name: $hard hard and $soft soft provider errors"
      fi
    done
  fi
  # (2) the main session's pane
  pane="$(kit_pane | tail -n 25)"
  if [ -n "$pane" ]; then
    if printf '%s\n' "$pane" | grep -q -E "$PANE_RE"; then
      kw_confirm "$(main_key)" "the main session's pane shows an auth/quota error"
    elif [ "$(printf '%s\n' "$pane" | grep -c -E "$SOFT_RE|Stream disconnected[^\\n]{0,60}503" || true)" -ge "$SOFT_MIN" ]; then
      kw_confirm "$(main_key)" "the main session's pane shows repeated 503"
    elif [ "$(printf '%s\n' "$pane" | grep -c 'exceeded retry limit, last status: 429' || true)" -ge "$SOFT_MIN" ]; then
      kw_confirm "$(main_key)" "the main session's pane shows repeated 429"
    fi
  fi
}

# --- entry point ------------------------------------------------------------
KW_ARGS=()
for _a in "$@"; do
  case "$_a" in --dry-run) KIT_DRY_RUN=1 ;; *) KW_ARGS+=("$_a") ;; esac
done
set -- ${KW_ARGS[@]+"${KW_ARGS[@]}"}
ACTION="${1:-watch}"; [ $# -gt 0 ] && shift

case "$ACTION" in
  confirm) kw_confirm "${1:?key}" "${2:-manual check}" ;;
  retire)  kw_retire "${1:?key}" "${2:?reason}" ;;
  status)
    printf 'main key: %s\n' "$(main_key)"
    printf 'caps: primary %s / second %s / total %s\n' "$(cap_read max-codex-primary)" "$(cap_read max-codex-second)" "$(cap_read max-codex)"
    printf 'cutoff: %s\n' "$([ -e "$KIT_STATE_DIR/cutoff" ] && head -c 160 "$KIT_STATE_DIR/cutoff" || echo 'no')"
    if [ -n "$(ls -A "$K" 2>/dev/null || true)" ]; then
      printf 'retired keys:\n'; for f in "$K"/*; do printf '  %s — %s\n' "$(basename "$f")" "$(head -c 160 "$f")"; done
    else printf 'retired keys: none\n'; fi
    ;;
  once) one_pass ;;
  watch)
    kit_is_dry || echo $$ > "$KIT_STATE_DIR/key-watch.pid"
    klog "key-watch started (pid $$): main key '$(main_key)', probe recheck ${RECHECK_S}s, interval ${INTERVAL}s"
    while true; do
      [ -e "$KIT_STATE_DIR/key-watch.stop" ] && { klog "stop file; exiting"; exit 0; }
      one_pass
      kit_is_dry && exit 0
      sleep "$INTERVAL"
    done
    ;;
  *) sed -n '1,24p' "$0" >&2; exit 3 ;;
esac
