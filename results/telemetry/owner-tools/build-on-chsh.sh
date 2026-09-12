#!/usr/bin/env bash
# build-on-chsh.sh — offload one worktree's Lean build to the chsh build farm.
#
#   build-on-chsh.sh [--dry-run] <worktree-path> [lake targets ...]
#   build-on-chsh.sh --check                  # is the offload enabled right now?
#   build-on-chsh.sh [--dry-run] --seed-refresh
#
# Runs ON ghz.  chsh is a pure build node: 192 aarch64 cores, a byte-identical
# copy of the Mathlib package cache, the same Lean toolchain and a hardlink
# build seed, fed from ghz by rsync over the internal link (86.7 MB/s).
#
# THE OWNER'S RULE (local/protocols/full-speed-mode.md): chsh is used only in
# full speed mode and never otherwise, and no codex session ever runs there.
# The rule is enforced here as well as in the callers: without `--dry-run`
# this script refuses to contact chsh unless `run_mode.py get offload` says
# `yes`, which happens only when the run is fast, unpaused and lists the host.
# An unreadable run mode is `no` — unknown is never "use the second host".
#
# What a build does:
#   1. rsync the worktree's sources to chsh builds/<lane>/ (excluding .lake,
#      .git, .worktrees and results/telemetry)
#   2. seed <lane>/.lake/build from the DATA seed with `cp -al` (hardlinks, one
#      filesystem, no data copied) and point <lane>/.lake/packages at the
#      shared Mathlib cache
#   3. run `lake build [targets]` in the lane on chsh
#   4. rsync back only the files that build wrote under .lake/build/{lib,ir}
#      (Mathlib lives in .lake/packages and is never touched)
#   5. exit with lake's exit code
#
# Exit codes — the caller must be able to tell "chsh is unusable" from "the
# proof does not compile", because the first falls back to a local build and
# the second must not:
#   0        the build succeeded on chsh and its artifacts are in the worktree
#   64       chsh is UNUSABLE (offload disabled, missing known-hosts, ssh or
#            rsync failure, lane busy, toolchain mismatch).  Build locally.
#   65       the build ran but its artifacts could not be returned.  Build
#            locally; the worktree may hold a partial set.
#   2        usage error
#   anything else  lake's own exit code — a real build failure, passed through
#
# `--seed-refresh` rsyncs the primary checkout to chsh and rebuilds the seed
# (the whole of "step 4" of the 2026-09-12 report).  It takes its own lock,
# runs at most once an hour, and is a no-op while the offload is disabled.
# It is slow (up to ~20 min) and is meant to be run detached; the merge daemon
# starts it after a merge.
#
# Environment: MIPSTARRE_CACHE_ROOT MIPSTARRE_CHECKOUT MIPSTARRE_RUN_MODE
#              CHSH_HOST CHSH_ADDR CHSH_PORT CHSH_KNOWN_HOSTS CHSH_SSH_BIN
#              CHSH_SSH_OPTS CHSH_BUILDS CHSH_SEED CHSH_PACKAGES CHSH_CHECKOUT
#              CHSH_SEED_MIN_INTERVAL_S CHSH_BUILD_TIMEOUT_S
set -uo pipefail

PROG="build-on-chsh.sh"

EXIT_UNUSABLE=64
EXIT_NO_ARTIFACTS=65

CACHE_ROOT="${MIPSTARRE_CACHE_ROOT:-$HOME/.cache/mipstarre-dev}"
STATE="$CACHE_ROOT/watchdog/chsh"
LOCKDIR="${CHSH_LOCKDIR:-$STATE/locks}"
OFFLOAD_LOG="${CHSH_OFFLOAD_LOG:-$STATE/offload.log}"

# The ssh alias on ghz points at the slow external address; the fast internal
# one is given explicitly here, with the host keys the installer deployed.
CHSH_HOST="${CHSH_HOST:-chsh}"
CHSH_ADDR="${CHSH_ADDR:-192.168.1.18}"
CHSH_PORT="${CHSH_PORT:-22}"
CHSH_KNOWN_HOSTS="${CHSH_KNOWN_HOSTS:-$STATE/known_hosts}"
CHSH_SSH_BIN="${CHSH_SSH_BIN:-ssh}"
CHSH_SSH_OPTS="${CHSH_SSH_OPTS:--o BatchMode=yes -o StrictHostKeyChecking=yes -o ConnectTimeout=20 -o ServerAliveInterval=15 -o ServerAliveCountMax=6 -o HostName=$CHSH_ADDR -p $CHSH_PORT -o UserKnownHostsFile=$CHSH_KNOWN_HOSTS}"
CHSH_BUILDS="${CHSH_BUILDS:-/data/users/drx/mipstarre-cache/builds}"
CHSH_SEED="${CHSH_SEED:-/data/users/drx/mipstarre-cache/seed/build}"
CHSH_PACKAGES="${CHSH_PACKAGES:-/home/drx/.cache/mipstarre-dev/packages/185353eebe93a5ab}"
CHSH_CHECKOUT="${CHSH_CHECKOUT:-/home/drx/MIPStarRE-qpbt}"
SEED_MIN_INTERVAL_S="${CHSH_SEED_MIN_INTERVAL_S:-3600}"
BUILD_TIMEOUT_S="${CHSH_BUILD_TIMEOUT_S:-2700}"
RSYNC_BIN="${CHSH_RSYNC_BIN:-rsync}"

DRY=0; CHECK=0; SEED_REFRESH=0
ARGS=()
while [ "$#" -gt 0 ]; do
  case "$1" in
    --dry-run) DRY=1 ;;
    --check) CHECK=1 ;;
    --seed-refresh) SEED_REFRESH=1 ;;
    -h|--help) sed -n '2,50p' "${BASH_SOURCE[0]}" | sed 's/^# \{0,1\}//'; exit 0 ;;
    --) shift; while [ "$#" -gt 0 ]; do ARGS+=("$1"); shift; done; break ;;
    -*) printf '%s: unknown option %s\n' "$PROG" "$1" >&2; exit 2 ;;
    *) ARGS+=("$1") ;;
  esac
  shift
done
set -- ${ARGS[@]+"${ARGS[@]}"}

now() { date -u +%FT%TZ; }
log() { printf '[%s %s] %s\n' "$PROG" "$(now)" "$*" >&2; }
say() { printf '+ %s\n' "$*"; }          # --dry-run transcript, on stdout
unusable() { log "chsh unusable: $*"; exit "$EXIT_UNUSABLE"; }
usage_error() { printf '%s: %s\n' "$PROG" "$*" >&2; exit 2; }

offload_log() { # <line>
  mkdir -p "$(dirname "$OFFLOAD_LOG")" 2>/dev/null || return 0
  printf '%s %s\n' "$(now)" "$*" >> "$OFFLOAD_LOG" 2>/dev/null || true
}

# --- the gate ---------------------------------------------------------------
# ONE definition of "may this run use chsh", and it is the run mode's:
# run_mode.py answers `yes` only for a fast, unpaused run that lists the host.
run_mode_py() {
  local candidate
  for candidate in "${MIPSTARRE_RUN_MODE:-}" \
                   "${MIPSTARRE_CHECKOUT:-}/local/bin/run_mode.py" \
                   "$HOME/MIPStarRE-qpbt/local/bin/run_mode.py"; do
    case "$candidate" in ''|'/local/bin/run_mode.py') continue ;; esac
    [ -r "$candidate" ] && { printf '%s\n' "$candidate"; return 0; }
  done
  return 1
}

offload_enabled() { # 0 = yes
  local py answer
  py="$(run_mode_py)" || return 1
  answer="$(python3 "$py" get offload 2>/dev/null | head -n 1 | tr -d '[:space:]')"
  [ "$answer" = "yes" ]
}

if [ "$CHECK" = 1 ]; then
  [ "$SEED_REFRESH" = 0 ] && [ "$#" -eq 0 ] || usage_error "--check takes no other argument"
  if offload_enabled; then echo "offload enabled (chsh)"; exit 0; fi
  echo "offload disabled (the run is not fast, is paused, or does not list chsh)"
  exit 1
fi

# --- ssh plumbing -----------------------------------------------------------
read -r -a SSH_OPT_ARR <<< "$CHSH_SSH_OPTS"
RSYNC_SHELL="$CHSH_SSH_BIN $CHSH_SSH_OPTS"

rsh() { # <remote command>
  if [ "$DRY" = 1 ]; then say "$CHSH_SSH_BIN $CHSH_SSH_OPTS $CHSH_HOST '$1'"; return 0; fi
  "$CHSH_SSH_BIN" "${SSH_OPT_ARR[@]}" "$CHSH_HOST" "$1" < /dev/null
}

require_known_hosts() {
  [ "$DRY" = 1 ] && return 0
  [ -r "$CHSH_KNOWN_HOSTS" ] || unusable \
    "no known-hosts file at $CHSH_KNOWN_HOSTS; install it with
     results/telemetry/owner-tools/install.sh (it copies the file the chsh
     session left on this host).  Never StrictHostKeyChecking=no."
}

require_enabled() {
  if [ "$DRY" = 1 ]; then
    if offload_enabled; then
      say "# run mode: the offload is ENABLED (fast, unpaused, chsh listed)"
    else
      say "# run mode: the offload is DISABLED; a real run would stop here with"
      say "#           exit $EXIT_UNUSABLE and the caller would build locally"
    fi
    return 0
  fi
  offload_enabled || unusable \
    "the run mode does not enable the offload (chsh is used only in full speed
     mode; run_mode.py get offload said no)"
}

# --- seed refresh -----------------------------------------------------------
# chsh's checkout and its hardlink seed go stale as main moves; a lane seeded
# from an old seed rebuilds the difference — slow, never wrong.  This is the
# report's step 4: push the primary checkout, rebuild, replace the seed.
seed_refresh() {
  local checkout stamp age
  checkout="${MIPSTARRE_CHECKOUT:-$HOME/MIPStarRE-qpbt}"
  [ -f "$checkout/lakefile.toml" ] || unusable "no checkout at $checkout"
  require_enabled
  require_known_hosts

  mkdir -p "$LOCKDIR" "$STATE"
  stamp="$STATE/seed-refresh.stamp"
  if [ "$DRY" = 0 ]; then
    exec 8>"$LOCKDIR/seed-refresh.lock"
    flock -n 8 || { log "a seed refresh is already running"; exit 0; }
    if [ -e "$stamp" ]; then
      age=$(( $(date +%s) - $(stat -c %Y "$stamp" 2>/dev/null || echo 0) ))
      if [ "$age" -lt "$SEED_MIN_INTERVAL_S" ]; then
        log "seed refreshed ${age}s ago (< ${SEED_MIN_INTERVAL_S}s); nothing to do"
        exit 0
      fi
    fi
    : > "$stamp"
  fi

  log "seed refresh: pushing $checkout to $CHSH_HOST:$CHSH_CHECKOUT"
  if [ "$DRY" = 1 ]; then
    say "$RSYNC_BIN -a --delete --exclude=/.lake --exclude=/.git --exclude=/.worktrees --exclude=/results/telemetry -e '$RSYNC_SHELL' $checkout/ $CHSH_HOST:$CHSH_CHECKOUT/"
  else
    "$RSYNC_BIN" -a --delete --info=stats1 \
      --exclude='/.lake' --exclude='/.git' --exclude='/.worktrees' \
      --exclude='/results/telemetry' \
      -e "$RSYNC_SHELL" "$checkout/" "$CHSH_HOST:$CHSH_CHECKOUT/" \
      || unusable "seed refresh: source rsync failed"
  fi

  rsh "set -e; export PATH=\$HOME/.elan/bin:\$PATH; cd '$CHSH_CHECKOUT'; \
       lake build MIPStarRE.QPBT; mkdir -p '$CHSH_SEED'; \
       rsync -a --delete .lake/build/ '$CHSH_SEED/'" \
    || unusable "seed refresh: the rebuild on $CHSH_HOST failed"
  [ "$DRY" = 0 ] && offload_log "seed-refresh host=$CHSH_HOST rc=0 checkout=$checkout"
  log "seed refresh done"
  exit 0
}

[ "$SEED_REFRESH" = 1 ] && { [ "$#" -eq 0 ] || usage_error "--seed-refresh takes no worktree"; seed_refresh; }

# --- one worktree's build ---------------------------------------------------
[ "$#" -ge 1 ] || usage_error "usage: $PROG [--dry-run] <worktree-path> [lake targets ...]"
SRC="$1"; shift
TARGETS=("$@")

[ -d "$SRC" ] || unusable "no such worktree: $SRC"
SRC="$(cd "$SRC" && pwd -P)"
[ -f "$SRC/lakefile.toml" ] || unusable "$SRC has no lakefile.toml"
[ -f "$SRC/lean-toolchain" ] || unusable "$SRC has no lean-toolchain"
NAME="$(basename "$SRC")"
case "$NAME" in
  ''|.|..) unusable "unusable lane name: $NAME" ;;
  *[!A-Za-z0-9._-]*) unusable "lane name has unsafe characters: $NAME" ;;
esac
# Targets are interpolated into a remote shell command.
for t in ${TARGETS[@]+"${TARGETS[@]}"}; do
  case "$t" in
    ''|*[!A-Za-z0-9._:+-]*) unusable "refusing unsafe lake target: $t" ;;
  esac
done
LANE="$CHSH_BUILDS/$NAME"
TARGET_TEXT="${TARGETS[*]:-(default)}"

require_enabled
require_known_hosts

# One offload per worktree.  A local `lake build` of the same worktree is
# serialized by the caller's machine-wide full-build lease (DESIGN.md
# invariant 7), which lane.sh and ci.sh still hold across the offload.
if [ "$DRY" = 0 ]; then
  mkdir -p "$LOCKDIR"
  exec 9>"$LOCKDIR/$NAME.lock"
  flock -n 9 || unusable "another $PROG already runs for $NAME"
fi

STARTED="$(date +%s)"
log "lane $CHSH_HOST:$LANE (worktree $SRC, targets $TARGET_TEXT)"

WANT_TOOLCHAIN="$(tr -d '[:space:]' < "$SRC/lean-toolchain")"
if [ "$DRY" = 1 ]; then
  say "$CHSH_SSH_BIN ... $CHSH_HOST 'cat $CHSH_CHECKOUT/lean-toolchain'   # must equal $WANT_TOOLCHAIN"
else
  HAVE_TOOLCHAIN="$(rsh "tr -d '[:space:]' < '$CHSH_CHECKOUT/lean-toolchain'")" \
    || unusable "cannot reach $CHSH_HOST"
  [ "$WANT_TOOLCHAIN" = "$HAVE_TOOLCHAIN" ] \
    || unusable "toolchain mismatch: the worktree wants $WANT_TOOLCHAIN, $CHSH_HOST has $HAVE_TOOLCHAIN (run --seed-refresh)"
fi

# ---- 1. lane skeleton + hardlink seed --------------------------------------
rsh "set -e; \
  [ -d '$CHSH_SEED' ] || { echo 'seed missing: $CHSH_SEED' >&2; exit 1; }; \
  mkdir -p '$LANE/.lake/build'; \
  if [ ! -e '$LANE/.lake/build/lib' ]; then cp -al '$CHSH_SEED/.' '$LANE/.lake/build/'; fi; \
  ln -sfn '$CHSH_PACKAGES' '$LANE/.lake/packages'; \
  rm -f '$LANE/.lake/.offload-stamp'; touch '$LANE/.lake/.offload-stamp'" \
  || unusable "lane preparation failed on $CHSH_HOST"

# ---- 2. push sources -------------------------------------------------------
log "pushing sources"
if [ "$DRY" = 1 ]; then
  say "$RSYNC_BIN -a --delete --exclude=/.lake --exclude=/.git --exclude=/.worktrees --exclude=/results/telemetry -e '$RSYNC_SHELL' $SRC/ $CHSH_HOST:$LANE/"
else
  "$RSYNC_BIN" -a --delete --info=stats1 \
    --exclude='/.lake' --exclude='/.git' --exclude='/.worktrees' \
    --exclude='/results/telemetry' \
    -e "$RSYNC_SHELL" "$SRC/" "$CHSH_HOST:$LANE/" \
    || unusable "source rsync to $CHSH_HOST failed"
fi

# ---- 3. build --------------------------------------------------------------
# The remote command reports lake's code in a sentinel line: ssh's own 255
# (a dropped connection) must not be mistaken for a failed proof, and a failed
# proof must not be mistaken for an unreachable host.
log "lake build $TARGET_TEXT on $CHSH_HOST"
RC=0
if [ "$DRY" = 1 ]; then
  say "$CHSH_SSH_BIN ... $CHSH_HOST 'cd $LANE && timeout $BUILD_TIMEOUT_S lake build ${TARGETS[*]:-}'"
else
  BUILD_OUT="$(rsh "cd '$LANE' && PATH=\$HOME/.elan/bin:\$PATH timeout $BUILD_TIMEOUT_S lake build ${TARGETS[*]:-}; printf '\n__chsh_rc=%s\n' \"\$?\"" 2>&1)"
  printf '%s\n' "$BUILD_OUT"
  SENTINEL="$(printf '%s\n' "$BUILD_OUT" | grep -o '__chsh_rc=[0-9]*' | tail -n 1)"
  if [ -z "$SENTINEL" ]; then
    offload_log "lane=$NAME host=$CHSH_HOST rc=unusable reason=ssh-failed targets=$TARGET_TEXT"
    unusable "the build command did not report an exit code (ssh transport failed)"
  fi
  RC="${SENTINEL#__chsh_rc=}"
  log "lake exit code $RC"
fi

# ---- 4. bring back what the build wrote ------------------------------------
RETURNED="dry-run"
if [ "$DRY" = 1 ]; then
  say "$CHSH_SSH_BIN ... $CHSH_HOST 'cd $LANE/.lake/build && find lib ir -type f -newer $LANE/.lake/.offload-stamp -print0'"
  say "$RSYNC_BIN -a --from0 --files-from=<list> -e '$RSYNC_SHELL' $CHSH_HOST:$LANE/.lake/build/ $SRC/.lake/build/"
  say "exit <lake exit code>"
  exit 0
fi
LIST="$(mktemp "${TMPDIR:-/tmp}/build-on-chsh.XXXXXX")"
trap 'rm -f "$LIST"' EXIT
if rsh "cd '$LANE/.lake/build' && find lib ir -type f -newer '$LANE/.lake/.offload-stamp' -print0" \
     > "$LIST" 2>/dev/null && [ -s "$LIST" ]; then
  RETURNED="$(tr -cd '\0' < "$LIST" | wc -c | tr -d ' ')"
  log "returning $RETURNED changed artifacts"
  mkdir -p "$SRC/.lake/build"
  if ! "$RSYNC_BIN" -a --from0 --files-from="$LIST" --info=stats1 \
       -e "$RSYNC_SHELL" "$CHSH_HOST:$LANE/.lake/build/" "$SRC/.lake/build/"; then
    log "artifact rsync failed; the worktree may hold a partial artifact set"
    offload_log "lane=$NAME host=$CHSH_HOST rc=no-artifacts targets=$TARGET_TEXT seconds=$(( $(date +%s) - STARTED ))"
    exit "$EXIT_NO_ARTIFACTS"
  fi
else
  RETURNED=0
  log "no new artifacts to return"
fi

offload_log "lane=$NAME host=$CHSH_HOST rc=$RC targets=$TARGET_TEXT artifacts=$RETURNED seconds=$(( $(date +%s) - STARTED ))"
exit "$RC"
