#!/usr/bin/env bash
# warm-worktree.sh — consumer side of the hot main build cache.
#
# Usage:
#   local/bin/warm-worktree.sh [<worktree>] [options]
#
#   <worktree>          Tree to warm (default: the git toplevel of $PWD).
#   --force             Re-clone the snapshot even if this worktree is already
#                       warmed or already has a populated .lake/build.
#   --build             After warming, also run a full `lake build` (takes the
#                       machine-wide full-build lock).
#   --no-build          On the cold path, do not run `lake build` (fetch packages
#                       only) — the caller accepts an unbuilt tree.
#   --force-cold        Ignore the snapshot store entirely and take the cold path.
#   --skip-packages     Do not run `lake exe cache get` (tier 2 already present).
#   --lock-timeout <s>  Max seconds to wait for the full-build lock (default 43200;
#                       0 = wait forever).
#   --status            Report what this worktree would do, change nothing.
#   -h | --help         Show this text.
#
# Local replacement for the *restore* half of the GitHub Actions build cache in
# .github/workflows/pr-ci.yml:143-149 (restore-keys prefix-match on
# hashFiles('lean-toolchain','lake-manifest.json','lakefile.toml')).  The cache
# there is saved only from main (pr-ci.yml:137-142, 161-167); here the warmer
# (local/bin/cache-warmer.sh) is the only writer and this script only ever reads.
# Protocol: local/protocols/build-cache.md.
#
# Two-tier cache split, which this script must not conflate:
#   tier 1  .lake/build    — this project's oleans; cloned copy-on-write from the
#                            warmer's snapshot, private and writable per worktree.
#   tier 2  .lake/packages — Mathlib and friends; fetched per worktree with
#                            `lake exe cache get`.  Never symlinked: a shared
#                            packages tree is mutated for everyone by any
#                            consumer that runs `lake update`.
#
# Runtime state lives under ~/.cache/mipstarre-dev/ and never in the repo.

set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"

# ---------------------------------------------------------------- configuration

CACHE_ROOT="${MIPSTARRE_CACHE_ROOT:-$HOME/.cache/mipstarre-dev}"
HOT_MAIN="$CACHE_ROOT/hot-main"
HOT_REPO="$HOT_MAIN/repo"
SNAPSHOTS="$HOT_MAIN/snapshots"
CURRENT_LINK="$HOT_MAIN/current"
# Machine-wide, shared with the warmer and with local/bin/ci.sh.  The env var
# name matches ci.sh's so a single setting reconciles both if their defaults
# ever disagree (see build-cache.md §7).
FULL_BUILD_LOCK="${MIPSTARRE_FULL_BUILD_LOCK:-$CACHE_ROOT/.full-build-lock}"
TELEMETRY_LOCK="$CACHE_ROOT/.telemetry-lock"
LOG_DIR="$CACHE_ROOT/logs"

WORKTREE=""
FORCE=0
WANT_BUILD=0
NO_BUILD=0
FORCE_COLD=0
SKIP_PACKAGES=0
STATUS_ONLY=0
LOCK_TIMEOUT="${MIPSTARRE_FULL_BUILD_LOCK_TIMEOUT:-43200}"

FULL_BUILD_LOCK_HELD=0
INCOMING_DIR=""

# ---------------------------------------------------------------------- helpers

log()  { printf '[warm-worktree] %s\n' "$*" >&2; }
warn() { printf '[warm-worktree] WARNING: %s\n' "$*" >&2; }
die()  { printf '[warm-worktree] ERROR: %s\n' "$*" >&2; exit 1; }

usage() {
  cat <<'EOF'
Usage: local/bin/warm-worktree.sh [<worktree>] [options]

  <worktree>          Tree to warm (default: the git toplevel of $PWD).
  --force             Re-clone the snapshot even if already warmed/populated.
  --build             Also run a full `lake build` under the machine-wide lock.
  --no-build          On the cold path, fetch packages but do not build.
  --force-cold        Ignore the snapshot store; take the cold path.
  --skip-packages     Do not run `lake exe cache get`.
  --lock-timeout <s>  Seconds to wait for the full-build lock (0 = forever).
  --status            Report the planned action and exit without changing anything.
  -h | --help         Show this text.

Environment: MIPSTARRE_CACHE_ROOT, MIPSTARRE_FULL_BUILD_LOCK_TIMEOUT,
MIPSTARRE_TELEMETRY_DIR.
EOF
}

iso_now()   { date +%Y-%m-%dT%H:%M:%S%z; }
epoch_now() { date +%s; }
stamp_id()  { date -u +%Y%m%dT%H%M%SZ; }

# Ported from .githooks/pre-push: clear Git's per-invocation environment before
# invoking Lake or nested git operations, or an outer hook's GIT_DIR leaks into
# the vendored package checkouts and they resolve the wrong repository.
run_outside_git_env() (
  if command -v git >/dev/null 2>&1; then
    for name in $(git rev-parse --local-env-vars); do
      unset "$name" || true
    done
  fi
  "$@"
)

sha256_stdin() {
  if command -v shasum >/dev/null 2>&1; then
    shasum -a 256 | awk '{print $1}'
  elif command -v sha256sum >/dev/null 2>&1; then
    sha256sum | awk '{print $1}'
  else
    die "no sha256 tool found (need shasum or sha256sum)"
  fi
}

# keyhash = sha256 over the concatenation, in this fixed order, of
#   lean-toolchain, lake-manifest.json, lakefile.toml
# MUST stay byte-identical to the copy in cache-warmer.sh (see the note there).
compute_keyhash() {
  local root="$1" f
  for f in lean-toolchain lake-manifest.json lakefile.toml; do
    [ -f "$root/$f" ] || die "missing $f under $root; cannot compute the cache keyhash"
  done
  cat "$root/lean-toolchain" "$root/lake-manifest.json" "$root/lakefile.toml" | sha256_stdin
}

ensure_lean_on_path() {
  if [ -d "$HOME/.elan/bin" ]; then
    case ":$PATH:" in
      *":$HOME/.elan/bin:"*) ;;
      *) PATH="$HOME/.elan/bin:$PATH"; export PATH ;;
    esac
  fi
  command -v lake >/dev/null 2>&1 || die \
    "lake not found on PATH. Run local/bin/worktree-setup.sh first, or install elan."
}

# --------------------------------------------------------------- lock primitives
# Same protocol and same lock directory as cache-warmer.sh: mkdir(2) to acquire,
# rename-then-delete to break a stale holder so exactly one breaker wins.

lock_info_field() { # <lockdir> <key>
  local dir="$1" key="$2" line
  [ -f "$dir/info" ] || { printf ''; return 0; }
  while IFS= read -r line; do
    case "$line" in
      "$key="*) printf '%s' "${line#*=}"; return 0 ;;
    esac
  done < "$dir/info"
  printf ''
}

# Portable directory mtime, used as a last-resort acquisition time for a lock
# written by another script in a different metadata layout.
lock_dir_mtime() { # <lockdir>
  stat -f %m "$1" 2>/dev/null || stat -c %Y "$1" 2>/dev/null || printf ''
}

# local/bin/ci.sh records the holder as `owner` (pid / ISO time / tag, one per
# line) rather than `info`.  Read both layouts, so that neither script mistakes a
# live lock held by the other for an unreadable — and therefore breakable — one.
lock_pid() { # <lockdir>
  local dir="$1" pid
  pid="$(lock_info_field "$dir" pid)"
  if [ -z "$pid" ] && [ -f "$dir/owner" ]; then
    pid="$(head -n 1 "$dir/owner" 2>/dev/null || true)"
  fi
  printf '%s' "$pid"
}

lock_is_stale() { # <lockdir> <ttl-seconds>
  local dir="$1" ttl="$2" pid host started age
  pid="$(lock_pid "$dir")"
  host="$(lock_info_field "$dir" host)"
  # An absent host field means the lock came from a script that does not record
  # one; on a single-machine setup that is this host, so pid liveness stays
  # authoritative and a live holder is never broken.
  if [ -n "$pid" ] && { [ -z "$host" ] || [ "$host" = "$(hostname)" ]; }; then
    case "$pid" in
      ''|*[!0-9]*) ;;
      *)
        if kill -0 "$pid" 2>/dev/null; then
          return 1
        fi
        return 0
        ;;
    esac
  fi
  started="$(lock_info_field "$dir" started_epoch)"
  case "$started" in
    ''|*[!0-9]*) started="$(lock_dir_mtime "$dir")" ;;
  esac
  case "$started" in
    ''|*[!0-9]*) return 0 ;;
  esac
  age=$(( $(epoch_now) - started ))
  [ "$age" -gt "$ttl" ]
}

break_lock() { # <lockdir>
  local dir="$1" doomed
  doomed="$1.stale.$$.$(epoch_now)"
  if mv "$dir" "$doomed" 2>/dev/null; then
    warn "broke stale lock $dir (pid=$(lock_pid "$doomed") held since $(lock_info_field "$doomed" started)$(lock_info_field "$doomed" purpose))"
    rm -rf "$doomed"
  fi
}

acquire_full_build_lock() { # <timeout-seconds; 0 = wait forever>
  local timeout="$1" waited=0 announced=0 ttl="${MIPSTARRE_LEASE_TTL:-43200}"
  mkdir -p "$CACHE_ROOT"
  while ! mkdir "$FULL_BUILD_LOCK" 2>/dev/null; do
    if lock_is_stale "$FULL_BUILD_LOCK" "$ttl"; then
      break_lock "$FULL_BUILD_LOCK"
      continue
    fi
    if [ "$announced" -eq 0 ]; then
      log "waiting for the machine-wide full-build lock (held by pid=$(lock_pid "$FULL_BUILD_LOCK"))"
      announced=1
    fi
    if [ "$timeout" -ne 0 ] && [ "$waited" -ge "$timeout" ]; then
      return 1
    fi
    sleep 10
    waited=$((waited + 10))
  done
  {
    printf 'pid=%s\n' "$$"
    printf 'host=%s\n' "$(hostname)"
    printf 'started=%s\n' "$(iso_now)"
    printf 'started_epoch=%s\n' "$(epoch_now)"
    printf 'purpose=consumer-full-build\n'
  } > "$FULL_BUILD_LOCK/info"
  # Also publish the holder in the layout local/bin/ci.sh reads.
  printf '%s\n%s\n%s\n' "$$" "$(iso_now)" "warm-worktree $WORKTREE" > "$FULL_BUILD_LOCK/owner"
  FULL_BUILD_LOCK_HELD=1
  return 0
}

release_full_build_lock() {
  if [ "$FULL_BUILD_LOCK_HELD" -eq 1 ]; then
    rm -rf "$FULL_BUILD_LOCK"
    FULL_BUILD_LOCK_HELD=0
  fi
}

cleanup() {
  local rc=$?
  if [ -n "$INCOMING_DIR" ] && [ -d "$INCOMING_DIR" ]; then
    rm -rf "$INCOMING_DIR"
  fi
  release_full_build_lock
  exit "$rc"
}
trap cleanup EXIT INT TERM

# ------------------------------------------------------------------- telemetry

resolve_primary_repo() {
  local common root
  if common="$(run_outside_git_env git -C "$SCRIPT_DIR" rev-parse --path-format=absolute --git-common-dir 2>/dev/null)" \
     && [ -n "$common" ]; then
    root="$(dirname "$common")"
    if [ -d "$root/local/bin" ]; then
      printf '%s' "$root"
      return 0
    fi
  fi
  ( cd "$SCRIPT_DIR/../.." && pwd )
}

append_build_telemetry() { # <kind> <outcome> <seconds> <trigger> <sha> <note>
  local dir file waited=0
  dir="${MIPSTARRE_TELEMETRY_DIR:-$(resolve_primary_repo)/results/telemetry}"
  file="$dir/builds.jsonl"
  if ! mkdir -p "$dir" 2>/dev/null; then
    warn "cannot create the telemetry directory $dir; build record dropped"
    return 0
  fi
  while ! mkdir "$TELEMETRY_LOCK" 2>/dev/null; do
    if [ "$waited" -ge 5 ]; then
      warn "telemetry lock busy; appending without serialization"
      break
    fi
    sleep 1
    waited=$((waited + 1))
  done
  if ! python3 - "$file" "$(iso_now)" "$@" <<'PY'
import json
import sys

path, ts, kind, outcome, seconds, trigger, sha, note = sys.argv[1:9]


def clean(text, limit=400):
    return "".join(c for c in text if c == " " or c.isprintable())[:limit]


record = {
    "ts": ts,
    "kind": clean(kind, 32),
    "trigger": clean(trigger, 200),
    "outcome": clean(outcome, 32),
}
try:
    record["seconds"] = int(float(seconds))
except (TypeError, ValueError):
    record["seconds"] = None
if sha:
    record["sha"] = clean(sha, 64)
if note:
    record["note"] = clean(note)
with open(path, "a", encoding="utf-8") as handle:
    handle.write(json.dumps(record, ensure_ascii=False) + "\n")
PY
  then
    warn "failed to append build telemetry to $file"
  fi
  rmdir "$TELEMETRY_LOCK" 2>/dev/null || true
}

# ---------------------------------------------------------------- snapshot store

# Resolve `current` exactly ONCE to a concrete snapshot path.  The warmer
# publishes by rename, so a single readlink always yields a whole, immutable tree;
# re-resolving mid-run could straddle a publish.
resolve_snapshot() {
  [ -L "$CURRENT_LINK" ] || return 1
  local target
  target="$(readlink "$CURRENT_LINK")" || return 1
  [ -n "$target" ] || return 1
  [ -d "$target/build" ] || return 1
  [ -f "$target/STAMP" ] || return 1
  printf '%s' "$target"
}

stamp_field() { # <stamp-file> <key>
  local file="$1" key="$2" line value
  [ -f "$file" ] || return 1
  while IFS= read -r line; do
    case "$line" in
      "$key="*)
        value="${line#*=}"
        # The STAMP is on-disk data: validate, never eval or source it.
        case "$key" in
          keyhash)
            [ "${#value}" -eq 64 ] || return 1
            case "$value" in *[!0-9a-f]*) return 1 ;; esac
            ;;
          sha)
            case "$value" in ''|*[!0-9a-f]*) return 1 ;; esac
            ;;
          status)
            case "$value" in complete|partial) ;; *) return 1 ;; esac
            ;;
        esac
        printf '%s' "$value"
        return 0
        ;;
    esac
  done < "$file"
  return 1
}

# Copy-on-write clone.  On APFS this is near-instant and space-cheap; the clone is
# the worktree's own writable copy, which is what keeps the single-writer
# invariant intact (pr-ci.yml:138-142: many writers evicted the one good entry).
cow_copy() { # <src-dir> <dst-dir>
  if cp -c -R "$1" "$2" 2>/dev/null; then
    return 0
  fi
  warn "APFS clone (cp -c) unavailable for $1 -> $2 (different volume?); falling back to a full copy"
  rm -rf "$2"
  cp -R "$1" "$2"
}

dir_is_populated() { # <dir>
  [ -d "$1" ] || return 1
  [ -n "$(find "$1" -mindepth 1 -maxdepth 1 -print -quit 2>/dev/null)" ]
}

# The ProofWidgets fresh-state workaround (docgen.yml:56-69) plus the local
# dirty-tree variant recorded in results/telemetry/builds.jsonl (2026-08-30):
# `lake exe cache get` runs `lake update`, whose mathlib post-update hook prunes
# .lake/packages/proofwidgets/.lake/build/lib; the directory is missing on a
# never-built tree (uncaught exception aborts the whole fetch) and a dirty
# vendored tree blocks the revision checkout.  Pristine agent worktrees are
# exactly that fresh state.
proofwidgets_fresh_state_workaround() { # <tree>
  local tree="$1" pkg name
  [ -d "$tree/.lake/packages" ] || return 0
  # Only tracked modifications are reset.  `git clean` is deliberately NOT run
  # inside a vendored package: it would delete downloaded build output and cost
  # hours to refetch.  If an untracked byproduct still blocks the checkout, the
  # cache fetch fails loudly and the caller falls back to compiling from source.
  for pkg in "$tree"/.lake/packages/*; do
    [ -d "$pkg/.git" ] || continue
    name="$(basename "$pkg")"
    if [ -n "$(run_outside_git_env git -C "$pkg" status --porcelain --untracked-files=no 2>/dev/null || true)" ]; then
      log "resetting dirty vendored package tree: $name"
      run_outside_git_env git -C "$pkg" reset --hard >/dev/null 2>&1 \
        || warn "could not reset $name; the Mathlib cache fetch may abort"
    fi
  done
  if [ -d "$tree/.lake/packages/proofwidgets" ]; then
    mkdir -p "$tree/.lake/packages/proofwidgets/.lake/build/lib"
  fi
}

# ------------------------------------------------------------------------ stages

WARM_MARKER=""   # set once WORKTREE is known

read_marker_field() { # <key>
  local key="$1" line
  [ -f "$WARM_MARKER" ] || return 1
  while IFS= read -r line; do
    case "$line" in
      "$key="*) printf '%s' "${line#*=}"; return 0 ;;
    esac
  done < "$WARM_MARKER"
  return 1
}

write_marker() { # <snapshot-name> <keyhash> <snapshot-status>
  mkdir -p "$(dirname "$WARM_MARKER")"
  {
    printf 'snapshot=%s\n' "$1"
    printf 'keyhash=%s\n' "$2"
    printf 'snapshot_status=%s\n' "$3"
    printf 'warmed_at=%s\n' "$(iso_now)"
  } > "$WARM_MARKER"
}

clone_build_tier() { # <snapshot-dir> <snapshot-name> <keyhash> <snapshot-status>
  local snap="$1" name="$2" keyhash="$3" status="$4"
  local build="$WORKTREE/.lake/build"

  if [ "$FORCE" -eq 0 ]; then
    if [ "$(read_marker_field snapshot || true)" = "$name" ] \
       && [ "$(read_marker_field keyhash || true)" = "$keyhash" ]; then
      log "already warmed from $name; nothing to clone (use --force to redo)"
      return 0
    fi
    if dir_is_populated "$build"; then
      warn "$build is already populated and was not warmed from $name; leaving it alone (use --force to replace it)"
      return 0
    fi
  fi

  mkdir -p "$WORKTREE/.lake"
  INCOMING_DIR="$WORKTREE/.lake/build.incoming.$$"
  rm -rf "$INCOMING_DIR"
  log "cloning tier 1 (.lake/build) from $name (status=$status)"
  cow_copy "$snap/build" "$INCOMING_DIR"
  rm -rf "$build"
  mv "$INCOMING_DIR" "$build"
  INCOMING_DIR=""
  write_marker "$name" "$keyhash" "$status"
  log "tier 1 in place at $build"
}

fetch_packages_tier() { # <trigger>
  local trigger="$1" started elapsed
  if [ "$SKIP_PACKAGES" -eq 1 ]; then
    log "skipping tier 2 (.lake/packages) on request"
    return 0
  fi
  proofwidgets_fresh_state_workaround "$WORKTREE"
  started="$(epoch_now)"
  log "fetching tier 2 (.lake/packages) with lake exe cache get"
  # Per-worktree, never a symlink into the warmer's tree: a shared packages
  # directory is mutated for every consumer by any `lake update`.
  if ( cd "$WORKTREE" && run_outside_git_env lake exe cache get ); then
    elapsed=$(( $(epoch_now) - started ))
    append_build_telemetry "cache-get" "success" "$elapsed" "$trigger" "" \
      "worktree=$WORKTREE"
    return 0
  fi
  elapsed=$(( $(epoch_now) - started ))
  append_build_telemetry "cache-get" "failed" "$elapsed" "$trigger" "" \
    "worktree=$WORKTREE; lake exe cache get failed"
  warn "lake exe cache get failed; Mathlib oleans may have to be compiled from source"
  return 1
}

full_build() { # <trigger>
  local trigger="$1" started elapsed logfile outcome rc=0
  mkdir -p "$LOG_DIR"
  logfile="$LOG_DIR/worktree-build-$(stamp_id)-$$.log"
  # DESIGN.md #7: at most one full `lake build` machine-wide.  Single-file
  # `lake env lean` checks (the pre-push hook's per-file gate) take no lock.
  if ! acquire_full_build_lock "$LOCK_TIMEOUT"; then
    die "timed out after ${LOCK_TIMEOUT}s waiting for the machine-wide full-build lock $FULL_BUILD_LOCK"
  fi
  log "running a full lake build in $WORKTREE (log: $logfile)"
  started="$(epoch_now)"
  if ( cd "$WORKTREE" && run_outside_git_env lake build ) > "$logfile" 2>&1; then
    outcome="success"
  else
    outcome="failed"
    rc=1
  fi
  elapsed=$(( $(epoch_now) - started ))
  release_full_build_lock
  append_build_telemetry "rebuild" "$outcome" "$elapsed" "$trigger" "" \
    "worktree=$WORKTREE log=$logfile"
  if [ "$rc" -ne 0 ]; then
    warn "lake build failed; see $logfile"
  fi
  return "$rc"
}

# --------------------------------------------------------------------------- main

main() {
  while [ $# -gt 0 ]; do
    case "$1" in
      --force)         FORCE=1; shift ;;
      --build)         WANT_BUILD=1; shift ;;
      --no-build)      NO_BUILD=1; shift ;;
      --force-cold)    FORCE_COLD=1; shift ;;
      --skip-packages) SKIP_PACKAGES=1; shift ;;
      --lock-timeout)  LOCK_TIMEOUT="${2:?--lock-timeout needs a value}"; shift 2 ;;
      --status)        STATUS_ONLY=1; shift ;;
      -h|--help)       usage; exit 0 ;;
      -*)              usage >&2; die "unknown option: $1" ;;
      *)
        [ -z "$WORKTREE" ] || { usage >&2; die "more than one worktree given"; }
        WORKTREE="$1"; shift ;;
    esac
  done

  case "$LOCK_TIMEOUT" in
    ''|*[!0-9]*) die "--lock-timeout must be a non-negative integer" ;;
  esac

  if [ -z "$WORKTREE" ]; then
    WORKTREE="$(run_outside_git_env git rev-parse --show-toplevel 2>/dev/null || true)"
    [ -n "$WORKTREE" ] || die "no worktree given and $PWD is not inside a git worktree"
  fi
  [ -d "$WORKTREE" ] || die "worktree $WORKTREE does not exist"
  WORKTREE="$(cd "$WORKTREE" && pwd)"
  WARM_MARKER="$WORKTREE/.lake/.mipstarre-warm-stamp"

  # Single-writer invariant (DESIGN.md #1): a consumer must never be pointed at
  # the warmer's own trees, or its incremental build writes into the cache.
  case "$WORKTREE/" in
    "$SNAPSHOTS"/*|"$HOT_REPO"/*|"$HOT_REPO"/)
      die "refusing to warm $WORKTREE: it is inside the warmer's own tree. Only local/bin/cache-warmer.sh may write there." ;;
  esac

  local keyhash snap="" name="" snap_keyhash="" snap_status="" snap_sha=""
  keyhash="$(compute_keyhash "$WORKTREE")"

  if [ "$FORCE_COLD" -eq 1 ]; then
    warn "--force-cold: ignoring the snapshot store"
  elif snap="$(resolve_snapshot)"; then
    :
  else
    snap=""
  fi

  if [ -n "$snap" ]; then
    name="$(basename "$snap")"
    snap_keyhash="$(stamp_field "$snap/STAMP" keyhash || true)"
    snap_status="$(stamp_field "$snap/STAMP" status || true)"
    snap_sha="$(stamp_field "$snap/STAMP" sha || true)"
    if [ -z "$snap_keyhash" ] || [ -z "$snap_status" ]; then
      warn "snapshot $name has an unreadable or malformed STAMP; treating it as absent"
      snap=""
    elif [ "$snap_keyhash" != "$keyhash" ]; then
      # Gotcha 3: a restored cache may be OLDER than this worktree's base commit
      # (Lake's staleness is trace-hash based, not mtime based), but it must NEVER
      # cross a toolchain/manifest/lakefile boundary.  A lean-toolchain bump is
      # total invalidation.
      warn "cache keyhash mismatch: worktree=$keyhash snapshot=$snap_keyhash"
      warn "the snapshot was built from a different lean-toolchain / lake-manifest.json / lakefile.toml; falling back to the COLD path"
      warn "ask the warmer to build this configuration: local/bin/cache-warmer.sh --ref main"
      snap=""
    fi
  else
    if [ "$FORCE_COLD" -eq 0 ]; then
      warn "no usable snapshot published under $CURRENT_LINK; falling back to the COLD path"
      warn "seed the hot main cache with: local/bin/cache-warmer.sh --ref main"
    fi
  fi

  if [ "$STATUS_ONLY" -eq 1 ]; then
    printf 'worktree     : %s\n' "$WORKTREE"
    printf 'keyhash      : %s\n' "$keyhash"
    if [ -n "$snap" ]; then
      printf 'path         : WARM\n'
      printf 'snapshot     : %s\n' "$snap"
      printf '  sha        : %s\n' "$snap_sha"
      printf '  status     : %s\n' "$snap_status"
    else
      printf 'path         : COLD\n'
    fi
    printf 'tier1 present: %s\n' "$(dir_is_populated "$WORKTREE/.lake/build" && echo yes || echo no)"
    printf 'tier2 present: %s\n' "$(dir_is_populated "$WORKTREE/.lake/packages" && echo yes || echo no)"
    printf 'warmed from  : %s\n' "$(read_marker_field snapshot || echo '<none>')"
    return 0
  fi

  ensure_lean_on_path
  command -v python3 >/dev/null 2>&1 || warn "python3 not found; build telemetry will be skipped"

  local rc=0
  if [ -n "$snap" ]; then
    if [ "$snap_status" = "partial" ]; then
      # pr-ci.yml:161-162: a partial cache still spares the modules that compiled.
      warn "snapshot $name is PARTIAL (main did not build cleanly at ${snap_sha:0:12}); using it anyway"
    fi
    clone_build_tier "$snap" "$name" "$keyhash" "$snap_status"
    fetch_packages_tier "warm-worktree warm path snapshot=$name" || rc=1
    if [ "$WANT_BUILD" -eq 1 ]; then
      full_build "warm-worktree --build after snapshot=$name" || rc=1
    else
      log "warm path complete; run \`lake build\` in $WORKTREE to compile only this branch's delta"
    fi
  else
    fetch_packages_tier "warm-worktree cold path" || rc=1
    if [ "$NO_BUILD" -eq 1 ]; then
      warn "cold path with --no-build: $WORKTREE has no project oleans and the first build will be a full one"
    else
      full_build "warm-worktree cold path (no usable snapshot)" || rc=1
    fi
  fi

  return "$rc"
}

main "$@"
