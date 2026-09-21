#!/usr/bin/env bash
# keyrot-install.sh [--dry-run] — install the worker routing layer on this machine.
#
# It does exactly four things:
#   1. copies local/bin/service/codex-shim to <cache_root>/owner-bin/codex, atomically;
#   2. creates one rotation home directory per key in local/project.json, each holding
#      `.limit` (how many sessions may run on that key at once) and `home` (the CODEX_HOME
#      that already holds that key's login);
#   3. renders `session.workers.models_allowed` into <state>/models-allowed, the file the
#      shim enforces its allowlist from (an empty list removes the file = no restriction);
#   4. decides the <state>/no-default-home guard: it is WRITTEN when the default
#      CODEX_HOME is not one of the configured keys, so a worker that finds no free
#      rotation slot cannot silently fall back to a home this project never named, and
#      REMOVED when the default home is one of them.  This is the only place that writes
#      that file: it is a property of the machine's shim installation, not of a session,
#      so resume.sh and the rest of local/bin/session/ leave it alone.
#
# It never reads, writes, copies or prints a key: a key is a NAME here and a directory
# path there.  A key whose CODEX_HOME does not exist is reported and skipped, not invented.
#
# NEVER overwrite a running script in place — bash reads a script lazily and three lanes
# once crashed mid-run because of it.  The shim is written to a temporary file next to its
# destination, checked with `bash -n`, and moved into place in one step; a previous copy
# is kept as codex.before-<timestamp>.
#
# After installing, put <cache_root>/owner-bin first on PATH (service-lib.sh does this for
# every service script) so `codex` means the shim.
#
# Provenance: kit-src/tmp-scripts/keyrot-install.sh, which patched the live shim with an
# inline Python rewrite and hard-coded two key names and one cache directory.
set -u
KIT_SERVICE_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd -P)"
# shellcheck source=/dev/null
. "$KIT_SERVICE_DIR/service-lib.sh"

DRY=0
case "${1:-}" in --dry-run) DRY=1 ;; "") ;; *) echo "usage: keyrot-install.sh [--dry-run]" >&2; exit 2 ;; esac

BIN="$KIT_CACHE_ROOT/owner-bin"
ROT="$KIT_CACHE_ROOT/keyrot"
SHIM="$KIT_SERVICE_DIR/codex-shim"
[ -f "$SHIM" ] || { echo "keyrot-install: $SHIM is missing" >&2; exit 2; }
bash -n "$SHIM" || { echo "keyrot-install: the shim does not parse; nothing installed" >&2; exit 2; }

# keys: "<name> <codex_home> <limit>" per line, from local/project.json when it is
# readable, otherwise the single default key.
keys() {
  python3 - "$KIT_REPO_ROOT" <<'PY' 2>/dev/null || echo "default $HOME/.codex 1"
import os, sys
sys.path.insert(0, os.path.join(sys.argv[1], "scripts"))
try:
    import project_config
    cfg = project_config.load(sys.argv[1])
except Exception:
    raise SystemExit(1)
rows = (cfg.get("keys") or {})
if not rows:
    raise SystemExit(1)
for name, row in rows.items():
    home = os.path.expanduser(str((row or {}).get("codex_home") or "~/.codex"))
    limit = (row or {}).get("limit") or 1
    print(f"{name} {home} {limit}")
PY
}

# The worker model allowlist, one model per line; empty output = no restriction.
models_allowed() {
  python3 - "$KIT_REPO_ROOT" <<'PYCFG' 2>/dev/null || true
import os, sys
sys.path.insert(0, os.path.join(sys.argv[1], "scripts"))
try:
    import project_config
    cfg = project_config.load(sys.argv[1])
except Exception:
    raise SystemExit(0)
for model in project_config.models_allowed(cfg):
    print(model)
PYCFG
}

# Directory identity without readlink -f (which is not everywhere): resolve when it exists.
real_dir() { if [ -d "$1" ]; then (cd "$1" && pwd -P); else printf '%s' "${1%/}"; fi; }
DEFAULT_HOME="$(real_dir "${CODEX_DEFAULT_HOME:-$HOME/.codex}")"
default_is_configured() {
  local name home limit
  while read -r name home limit; do
    [ -n "$name" ] || continue
    [ "$(real_dir "$home")" = "$DEFAULT_HOME" ] && return 0
  done <<EOF
$(keys)
EOF
  return 1
}

if [ "$DRY" -eq 1 ]; then
  echo "would install: $SHIM -> $BIN/codex"
  keys | while read -r name home limit; do
    [ -n "$name" ] || continue
    if [ -d "$home" ]; then echo "would create: $ROT/$name (.limit $limit, home $home)"
    else echo "would SKIP: key '$name' — its CODEX_HOME $home does not exist"; fi
  done
  if [ -n "$(models_allowed)" ]; then
    echo "would write: $KIT_STATE_DIR/models-allowed ($(models_allowed | tr '\n' ' '))"
  else
    echo "would remove: $KIT_STATE_DIR/models-allowed (no allowlist configured)"
  fi
  if default_is_configured; then
    echo "would remove: $KIT_STATE_DIR/no-default-home (the default home $DEFAULT_HOME is a configured key)"
  else
    echo "would write: $KIT_STATE_DIR/no-default-home (the default home $DEFAULT_HOME is not a configured key)"
  fi
  exit 0
fi

mkdir -p "$BIN" "$ROT" "$KIT_STATE_DIR"
TMP="$BIN/.codex.new.$$"
cp "$SHIM" "$TMP" && chmod 755 "$TMP" || { echo "keyrot-install: cannot stage the shim in $BIN" >&2; exit 2; }
bash -n "$TMP" || { rm -f "$TMP"; echo "keyrot-install: staged shim does not parse" >&2; exit 2; }
if [ -e "$BIN/codex" ]; then
  cp -p "$BIN/codex" "$BIN/codex.before-$(date -u +%Y%m%dT%H%M%SZ)"
fi
mv -f "$TMP" "$BIN/codex"
kit_log "shim installed: $BIN/codex"

installed=0; skipped=0
while read -r name home limit; do
  [ -n "$name" ] || continue
  if [ ! -d "$home" ]; then
    echo "key '$name': CODEX_HOME $home does not exist — skipped (log in there first)"
    skipped=$((skipped+1)); continue
  fi
  mkdir -p "$ROT/$name"
  echo "$limit" > "$ROT/$name/.limit"
  echo "$home"  > "$ROT/$name/home"
  echo "key '$name': limit $limit, home $home"
  installed=$((installed+1))
done <<EOF
$(keys)
EOF

# The worker model allowlist: a repository fact rendered into the state directory,
# because the shim must not need the checkout to answer "may I run this model?".
ALLOWED="$(models_allowed)"
if [ -n "$ALLOWED" ]; then
  printf '%s\n' "$ALLOWED" > "$KIT_STATE_DIR/models-allowed"
  echo "worker models allowed: $(printf '%s' "$ALLOWED" | tr '\n' ' ')"
else
  rm -f "$KIT_STATE_DIR/models-allowed"
  echo "worker models allowed: any (session.workers.models_allowed is empty)"
fi

# The no-default-home guard (see the header): on when the default CODEX_HOME is not
# one of this project's keys, off when it is.
if default_is_configured; then
  rm -f "$KIT_STATE_DIR/no-default-home"
  echo "default home $DEFAULT_HOME is a configured key: a worker may fall back to it"
else
  printf '%s the default CODEX_HOME %s is not one of the configured keys; a worker with no free rotation slot must not start\n' \
    "$(date -u +%FT%TZ)" "$DEFAULT_HOME" > "$KIT_STATE_DIR/no-default-home"
  echo "default home $DEFAULT_HOME is NOT a configured key: wrote $KIT_STATE_DIR/no-default-home"
fi

kit_log "rotation homes: $installed installed, $skipped skipped"
kit_plog "keyrot-install: $installed rotation home(s) under $ROT, shim at $BIN/codex"
echo "PATH must start with $BIN for the shim to take effect."
