#!/usr/bin/env bash
# lib.sh — shared helpers for every script in local/bin/session/.
#
# Provenance: generalized from the origin project's out-of-repo operator scripts
# (owner-say.sh, goal-keeper-v3.sh, key-watch-v7.sh, meta-pause-lib.sh).  Those
# read one hard-coded repo path, tmux session and key name; here everything comes
# from local/bin/session/config.sh (written by the configuration loader) with a
# documented env-variable fallback, so the same code runs on any machine.
#
# Sourced, never executed.  It is `set -u` safe and defines no global state
# beyond the KIT_* variables documented in the kit's configuration section.

# --- where we are -----------------------------------------------------------
KIT_SESSION_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
_kit_root_guess="$(cd "$KIT_SESSION_DIR/../../.." && pwd)"

# --- configuration: config.sh if it exists, else the documented env fallback --
# config.sh is shipped by the configuration loader and is AUTHORITATIVE for the
# names it exports: sourcing it overwrites them, so that running a tool from one
# project cannot leave another project's cache or tmux session behind.  A single
# run is steered by a script's own flags, not by those variables.  Before
# config.sh exists (a bare checkout, or a caller pointing KIT_CONFIG_SH at
# another project's copy) every value falls back to the environment variable of
# the same name and then to the kit's default.
KIT_CONFIG_SH="${KIT_CONFIG_SH:-$KIT_SESSION_DIR/config.sh}"
KIT_CONFIG_LOADED=0
if [ -r "$KIT_CONFIG_SH" ]; then
  # shellcheck disable=SC1090
  if . "$KIT_CONFIG_SH"; then KIT_CONFIG_LOADED=1
  else printf 'lib.sh: warning: %s failed to load; using defaults\n' "$KIT_CONFIG_SH" >&2; fi
fi

kit_expand_tilde() { # print $1 with a leading ~/ replaced by $HOME
  case "${1-}" in
    "~") printf '%s\n' "$HOME" ;;
    "~/"*) printf '%s\n' "$HOME/${1#\~/}" ;;
    *) printf '%s\n' "${1-}" ;;
  esac
}

KIT_REPO_ROOT="$(kit_expand_tilde "${KIT_REPO_ROOT:-$_kit_root_guess}")"
KIT_NAME="${KIT_NAME:-PaperLib}"
KIT_LEAN_ROOT="${KIT_LEAN_ROOT:-$KIT_NAME}"
KIT_TRACK="${KIT_TRACK:-main}"
KIT_GITHUB_SLUG="${KIT_GITHUB_SLUG:-OWNER/REPO}"
KIT_COMPARATOR_SLUG="${KIT_COMPARATOR_SLUG:-${KIT_GITHUB_SLUG}-comparator}"
KIT_CACHE_ROOT="$(kit_expand_tilde "${KIT_CACHE_ROOT:-$HOME/.cache/paperlib-dev}")"
KIT_STATE_DIR="$(kit_expand_tilde "${KIT_STATE_DIR:-$KIT_CACHE_ROOT/watchdog}")"
KIT_TMUX="${KIT_TMUX:-paperlib}"
KIT_TURN_MAX="${KIT_TURN_MAX:-25}"
KIT_PROGRESS_ISSUE="${KIT_PROGRESS_ISSUE:-}"
KIT_OWNER_INBOX_ISSUE="${KIT_OWNER_INBOX_ISSUE:-}"
KIT_TRACKER_ROOT="${KIT_TRACKER_ROOT:-}"
KIT_MAIN_MODEL="${KIT_MAIN_MODEL:-}"
KIT_MAIN_EFFORT="${KIT_MAIN_EFFORT:-}"
KIT_MAIN_KEY="${KIT_MAIN_KEY:-default}"
KIT_MAIN_DELEGATES="${KIT_MAIN_DELEGATES:-1}"
KIT_WORKER_MODEL="${KIT_WORKER_MODEL:-}"
KIT_WORKER_EFFORT="${KIT_WORKER_EFFORT:-}"
KIT_LANES="${KIT_LANES:-0}"
export KIT_REPO_ROOT KIT_NAME KIT_LEAN_ROOT KIT_TRACK KIT_GITHUB_SLUG KIT_COMPARATOR_SLUG
export KIT_CACHE_ROOT KIT_STATE_DIR KIT_TMUX KIT_TURN_MAX KIT_PROGRESS_ISSUE
export KIT_OWNER_INBOX_ISSUE KIT_TRACKER_ROOT KIT_MAIN_MODEL KIT_MAIN_EFFORT KIT_MAIN_KEY
export KIT_MAIN_DELEGATES KIT_WORKER_MODEL KIT_WORKER_EFFORT KIT_LANES
# The names the repository's inherited tools read.  config.sh owns them when it
# is there (it also decides to leave the slug unset while it is a placeholder,
# so that those tools fall back to the git remote); this only fills them in on
# the fallback path.
if [ "$KIT_CONFIG_LOADED" = 0 ]; then
  export MIPSTARRE_CACHE_ROOT="$KIT_CACHE_ROOT"
  case "$KIT_GITHUB_SLUG" in
    ""|OWNER/*) unset MIPSTARRE_GITHUB_REPO 2>/dev/null || true ;;
    *) export MIPSTARRE_GITHUB_REPO="$KIT_GITHUB_SLUG" ;;
  esac
fi

KIT_REPO_BASENAME="$(basename "$KIT_REPO_ROOT")"
KIT_DAEMON_DIR="$KIT_STATE_DIR/daemon"
# the TUI's status line ends in " · <some prefix>/<repo basename>"; never a
# hard-coded repository name (origin lesson: the idle regex was the one place
# the project name leaked into every operator script).
KIT_IDLE_MARK="${KIT_IDLE_MARK:- · }"
KIT_COMPOSER_PLACEHOLDER="${KIT_COMPOSER_PLACEHOLDER:-Ask Codex}"
KIT_BUSY_RE="${KIT_BUSY_RE:-esc to interrupt|Working \(}"

# --- small helpers ----------------------------------------------------------
# exported so that a --dry-run flag set by one script reaches the scripts it calls
export KIT_DRY_RUN="${KIT_DRY_RUN:-0}"
kit_is_dry() { [ "${KIT_DRY_RUN:-0}" = 1 ]; }
kit_now() { date -u +%FT%TZ; }

kit_state_dir() { mkdir -p "$KIT_STATE_DIR" "$KIT_DAEMON_DIR" "$KIT_STATE_DIR/key-disabled" 2>/dev/null || true; }

kit_log() { # one dated line on stdout and in the kit's own event log
  local line; line="$(kit_now) $*"
  if kit_is_dry; then printf 'DRY log %s\n' "$line"; return 0; fi
  printf '== %s\n' "$line"
  mkdir -p "$KIT_STATE_DIR" 2>/dev/null || true
  printf '%s\n' "$line" >> "$KIT_STATE_DIR/events-meta.log" 2>/dev/null || true
}

kit_die() { printf '%s\n' "$*" >&2; exit "${KIT_DIE_CODE:-2}"; }

kit_cfg() { # kit_cfg <dotted.path> [default] — one value out of the project configuration
  local path="${1:?path}" def="${2-}" out=""
  command -v python3 >/dev/null 2>&1 || { printf '%s\n' "$def"; return 0; }
  if [ -z "${KIT_PROJECT_JSON:-}" ] && [ -r "$KIT_REPO_ROOT/scripts/project_config.py" ]; then
    out="$(python3 "$KIT_REPO_ROOT/scripts/project_config.py" --root "$KIT_REPO_ROOT" get "$path" 2>/dev/null || true)"
  elif [ -r "${KIT_PROJECT_JSON:-$KIT_REPO_ROOT/local/project.json}" ]; then
    # the loader is not there yet (or this is a bare checkout): read the file directly
    out="$(python3 -c '
import json, sys
try:
    node = json.load(open(sys.argv[1], encoding="utf-8"))
except Exception:
    sys.exit(0)
for part in sys.argv[2].split("."):
    if isinstance(node, dict) and part in node:
        node = node[part]
    else:
        sys.exit(0)
if node is None or isinstance(node, (dict, list)):
    sys.exit(0)
print(node)' "${KIT_PROJECT_JSON:-$KIT_REPO_ROOT/local/project.json}" "$path" 2>/dev/null || true)"
  fi
  case "$out" in ""|None|null) printf '%s\n' "$def" ;; *) printf '%s\n' "$out" ;; esac
}

kit_key_names() { # every configured key NAME, one per line
  if [ -n "${KIT_KEYS:-}" ]; then printf '%s\n' $KIT_KEYS; return 0; fi
  local f="${KIT_PROJECT_JSON:-$KIT_REPO_ROOT/local/project.json}" out=""
  if command -v python3 >/dev/null 2>&1 && [ -r "$f" ]; then
    out="$(python3 -c '
import json, sys
try:
    keys = json.load(open(sys.argv[1], encoding="utf-8")).get("keys") or {}
except Exception:
    keys = {}
for name in keys:
    print(name)' "$f" 2>/dev/null || true)"
  fi
  [ -n "$out" ] || out="$KIT_MAIN_KEY"
  printf '%s\n' "$out"
}

kit_key_home() { # kit_key_home <key-name> — the CODEX_HOME directory of a configured key
  # Fallback order, all documented: KIT_KEY_HOME_<KEY> (key upper-cased, '-' -> '_'),
  # then keys.<key>.codex_home from the project configuration, then $KIT_CODEX_HOME,
  # then ~/.codex.  The kit never reads, stores or prints the key itself.
  local key="${1:?key}" var home
  var="KIT_KEY_HOME_$(printf '%s' "$key" | tr 'a-z-' 'A-Z_')"
  home="${!var-}"
  [ -n "$home" ] || home="$(kit_cfg "keys.$key.codex_home" "")"
  [ -n "$home" ] || home="${KIT_CODEX_HOME:-$HOME/.codex}"
  kit_expand_tilde "$home"
}

kit_key_limit() { # kit_key_limit <key-name> — concurrent sessions allowed on that key
  local key="${1:?key}" var lim
  var="KIT_KEY_LIMIT_$(printf '%s' "$key" | tr 'a-z-' 'A-Z_')"
  lim="${!var-}"
  [ -n "$lim" ] || lim="$(kit_cfg "keys.$key.limit" "1")"
  printf '%s\n' "$lim"
}

# --- tmux ------------------------------------------------------------------
kit_tmux() { # every tmux call goes through here so --dry-run touches nothing
  if kit_is_dry; then printf 'DRY tmux %s\n' "$*"; return 0; fi
  tmux "$@"
}

kit_pane() { # raw pane text ("$@" is appended to capture-pane)
  kit_is_dry && return 0
  tmux capture-pane -p -t "$KIT_TMUX" "$@" 2>/dev/null || true
}

kit_pane_tail() { # last N non-empty pane lines (default 4 — the origin's rule)
  kit_pane | grep -v '^[[:space:]]*$' | tail -n "${1:-4}"
}

kit_busy() { # a turn is running
  kit_pane_tail 4 | grep -q -E "$KIT_BUSY_RE"
}

kit_status_line_seen() { # the TUI status line of THIS repository is on screen
  local pane="${1-}"
  [ -n "$pane" ] || pane="$(kit_pane_tail 4)"
  [ -n "$pane" ] || return 1
  printf '%s\n' "$pane" | grep -q -F "$KIT_IDLE_MARK" || return 1
  printf '%s\n' "$pane" | grep -q -F "$KIT_REPO_BASENAME"
}

kit_idle() { # idle = our status line on screen and no turn running (last 4 lines only)
  local pane; pane="$(kit_pane_tail 4)"
  kit_status_line_seen "$pane" || return 1
  ! printf '%s\n' "$pane" | grep -q -E "$KIT_BUSY_RE"
}

kit_wait_idle() { # kit_wait_idle <max_seconds> [step]
  local max="${1:-600}" step="${2:-5}" t=0
  while ! kit_idle; do
    sleep "$step"; t=$((t+step))
    [ "$t" -ge "$max" ] && return 1
  done
  return 0
}

# --- the main TUI process ---------------------------------------------------
# Anchored pattern only (origin lesson: an unanchored `pkill -f <substring>`
# matched the login shell and the workers' own command lines).  Override with
# KIT_MAIN_PID_CMD when the codex binary is launched in an unusual way.
kit_main_pid() {
  if [ -n "${KIT_MAIN_PID_CMD:-}" ]; then
    eval "$KIT_MAIN_PID_CMD" 2>/dev/null | head -n 1
    return 0
  fi
  local esc; esc="$(printf '%s' "$KIT_REPO_ROOT" | sed 's/[][\.*^$(){}?+|/]/\\&/g')"
  pgrep -f "^([^ ]+ ){0,2}[^ ]*codex .*-C $esc( |$)" 2>/dev/null | head -n 1
}

# --- detached helpers (pid / stop / log triple in the state directory) -------
kit_daemon_alive() { # kit_daemon_alive <name>
  local p; p="$(cat "$KIT_STATE_DIR/${1:?name}.pid" 2>/dev/null || true)"
  [ -n "$p" ] && kill -0 "$p" 2>/dev/null
}

kit_daemon_start() { # kit_daemon_start <name> -- <command...>
  local name="${1:?name}"; shift; [ "${1-}" = "--" ] && shift
  if kit_daemon_alive "$name"; then
    printf '%s already running (pid %s)\n' "$name" "$(cat "$KIT_STATE_DIR/$name.pid")"; return 0
  fi
  if kit_is_dry; then printf 'DRY start %s: %s\n' "$name" "$*"; return 0; fi
  kit_state_dir
  rm -f "$KIT_STATE_DIR/$name.stop"
  setsid nohup "$@" >> "$KIT_STATE_DIR/$name.log" 2>&1 < /dev/null &
  sleep 1
  if kit_daemon_alive "$name"; then
    printf '%s started (pid %s)\n' "$name" "$(cat "$KIT_STATE_DIR/$name.pid")"
  else
    printf '%s started (no pid file yet; see %s)\n' "$name" "$KIT_STATE_DIR/$name.log"
  fi
}

kit_daemon_stop() { # kit_daemon_stop <name> [wait_seconds]
  local name="${1:?name}" wait="${2:-10}" p i
  if kit_is_dry; then printf 'DRY stop %s\n' "$name"; return 0; fi
  kit_state_dir
  touch "$KIT_STATE_DIR/$name.stop"
  p="$(cat "$KIT_STATE_DIR/$name.pid" 2>/dev/null || true)"
  [ -n "$p" ] && kill "$p" 2>/dev/null
  for i in $(seq 1 "$wait"); do kit_daemon_alive "$name" || break; sleep 1; done
  # the stop file has done its work; leaving it would block the next start
  rm -f "$KIT_STATE_DIR/$name.stop"
  kit_daemon_alive "$name" && { printf '%s did not stop (pid %s)\n' "$name" "$p"; return 1; }
  printf '%s stopped\n' "$name"; return 0
}

# --- the progress issue -----------------------------------------------------
kit_issue_comment() { # kit_issue_comment "<markdown>" — silent no-op when nothing is configured
  local body="${1-}"
  [ -n "$KIT_PROGRESS_ISSUE" ] || { printf 'no progress issue configured; not commenting\n'; return 0; }
  [ -n "$KIT_GITHUB_SLUG" ] || return 0
  if kit_is_dry; then printf 'DRY comment on %s#%s: %s\n' "$KIT_GITHUB_SLUG" "$KIT_PROGRESS_ISSUE" "$(printf '%s' "$body" | head -n 1)"; return 0; fi
  command -v gh >/dev/null 2>&1 || { printf 'gh is not installed; not commenting\n'; return 0; }
  timeout 60 gh issue comment "$KIT_PROGRESS_ISSUE" -R "$KIT_GITHUB_SLUG" -b "$body" >/dev/null 2>&1 \
    || printf 'could not comment on %s#%s\n' "$KIT_GITHUB_SLUG" "$KIT_PROGRESS_ISSUE"
}

# --- template rendering -----------------------------------------------------
kit_render() { # kit_render <template> <out> KEY=VALUE...  ({{KEY}} -> VALUE, literal)
  local tpl="${1:?template}" out="${2:?out}"; shift 2
  [ -r "$tpl" ] || { printf 'template not found: %s\n' "$tpl" >&2; return 2; }
  KIT_RENDER_PAIRS="$(printf '%s\n' "$@")" python3 -c '
import os, sys
tpl, out = sys.argv[1], sys.argv[2]
text = open(tpl, encoding="utf-8").read()
for pair in os.environ.get("KIT_RENDER_PAIRS", "").splitlines():
    if not pair.strip():
        continue
    key, _, value = pair.partition("=")
    text = text.replace("{{" + key.strip() + "}}", value)
open(out, "w", encoding="utf-8").write(text)
' "$tpl" "$out"
}
