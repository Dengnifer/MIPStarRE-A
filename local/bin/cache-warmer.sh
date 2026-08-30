#!/usr/bin/env bash
# cache-warmer.sh — single-writer warmer for the hot main build cache.
#
# Usage:
#   local/bin/cache-warmer.sh [options]
#
#   --ref <ref>          Branch/ref to warm (default: main; origin/<ref> preferred).
#   --sha <sha>          Warm this exact commit instead of resolving a ref.
#   --force              Rebuild and republish even if a complete snapshot exists.
#   --targets "<a b>"    Extra `lake build` targets after the default build.
#   --lock-timeout <s>   Max seconds to wait for the machine-wide full-build lock
#                        (default 43200; 0 = wait forever).
#   --lease-ttl <s>      Writer-lease staleness TTL in seconds (default 43200).
#   --keep <n>           Snapshots to retain after GC (default 2, minimum 1).
#   --gc-only            Run snapshot GC and exit.
#   --status             Print the published snapshot state and exit.
#   -h | --help          Show this text.
#
# Local replacement for the main-only GitHub Actions build cache in
# .github/workflows/pr-ci.yml:137-167 ("the cache is saved only from main and
# restored everywhere"); lean-action's per-run cache is disabled at
# pr-ci.yml:138-142 because per-PR saves evicted the one main-branch entry.
# Protocol: local/protocols/build-cache.md.
#
# Invariants (local/DESIGN.md #1, #7):
#   * Only this script writes into the snapshot store; consumers clone it
#     copy-on-write and never write back (local/bin/warm-worktree.sh).
#   * At most one full `lake build` machine-wide, via the shared lock
#     ~/.cache/mipstarre-dev/.full-build-lock.
#
# Runtime state lives under ~/.cache/mipstarre-dev/ and never in the repo.

set -euo pipefail

readonly WARMER_VERSION=1

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"

# ---------------------------------------------------------------- configuration

CACHE_ROOT="${MIPSTARRE_CACHE_ROOT:-$HOME/.cache/mipstarre-dev}"
HOT_MAIN="$CACHE_ROOT/hot-main"
HOT_REPO="$HOT_MAIN/repo"
SNAPSHOTS="$HOT_MAIN/snapshots"
CURRENT_LINK="$HOT_MAIN/current"
LEASE_DIR="$HOT_MAIN/.writer-lease"
# Machine-wide, shared with every consumer that runs a full build.  The env var
# name matches local/bin/ci.sh's so a single setting reconciles both if their
# defaults ever disagree (see build-cache.md §7).
FULL_BUILD_LOCK="${MIPSTARRE_FULL_BUILD_LOCK:-$CACHE_ROOT/.full-build-lock}"
TELEMETRY_LOCK="$CACHE_ROOT/.telemetry-lock"
LOG_DIR="$CACHE_ROOT/logs"

REF="main"
SHA=""
FORCE=0
EXTRA_TARGETS="${MIPSTARRE_WARM_TARGETS:-}"
LOCK_TIMEOUT="${MIPSTARRE_FULL_BUILD_LOCK_TIMEOUT:-43200}"
LEASE_TTL="${MIPSTARRE_LEASE_TTL:-43200}"
KEEP="${MIPSTARRE_SNAPSHOT_KEEP:-2}"
MODE="warm"

LEASE_HELD=0
FULL_BUILD_LOCK_HELD=0
STAGE_DIR=""

# ---------------------------------------------------------------------- helpers

log()  { printf '[cache-warmer] %s\n' "$*" >&2; }
warn() { printf '[cache-warmer] WARNING: %s\n' "$*" >&2; }
die()  { printf '[cache-warmer] ERROR: %s\n' "$*" >&2; exit 1; }

usage() {
  cat <<'EOF'
Usage: local/bin/cache-warmer.sh [options]

  --ref <ref>          Branch/ref to warm (default: main; origin/<ref> preferred).
  --sha <sha>          Warm this exact commit instead of resolving a ref.
  --force              Rebuild and republish even if a complete snapshot exists.
  --targets "<a b>"    Extra `lake build` targets after the default build.
  --lock-timeout <s>   Max seconds to wait for the machine-wide full-build lock
                       (default 43200; 0 = wait forever).
  --lease-ttl <s>      Writer-lease staleness TTL in seconds (default 43200).
  --keep <n>           Snapshots to retain after GC (default 2, minimum 1).
  --gc-only            Run snapshot GC and exit.
  --status             Print the published snapshot state and exit.
  -h | --help          Show this text.

Environment: MIPSTARRE_CACHE_ROOT, MIPSTARRE_WARM_TARGETS, MIPSTARRE_LEASE_TTL,
MIPSTARRE_FULL_BUILD_LOCK_TIMEOUT, MIPSTARRE_SNAPSHOT_KEEP, MIPSTARRE_TELEMETRY_DIR.
EOF
}

iso_now()   { date +%Y-%m-%dT%H:%M:%S%z; }
epoch_now() { date +%s; }
stamp_id()  { date -u +%Y%m%dT%H%M%SZ; }

# Run a command with Git's per-invocation environment cleared.  Ported verbatim in
# spirit from .githooks/pre-push (`run_outside_git_env`): a warmer invoked from a
# hook would otherwise leak GIT_DIR/GIT_INDEX_FILE into Lake's package checkouts,
# making nested git operations resolve the wrong repository.
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
# The local analog of pr-ci.yml's
#   hashFiles('lean-toolchain', 'lake-manifest.json', 'lakefile.toml')
# This definition MUST stay byte-identical to the copy in warm-worktree.sh, or
# every consumer silently takes the cold path forever.
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
    "lake not found on PATH. Install elan and the pinned toolchain first (local/bin/worktree-setup.sh asserts this)."
  command -v python3 >/dev/null 2>&1 || die "python3 not found on PATH (needed for atomic publish and telemetry)."
}

# --------------------------------------------------------------- lock primitives
#
# mkdir(2) is the atomic primitive.  A stale lock is broken by *renaming* the lock
# directory to a unique name first, so that when two warmers both judge a lock
# stale exactly one wins the rename and re-acquires.

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

  # Same host: the holder's liveness is authoritative, which is what lets the TTL
  # be generous.  A full Mathlib-scale build here took 25052 s
  # (results/telemetry/builds.jsonl, 2026-08-30), so an age-only rule with a
  # short TTL would break a live warmer's lease mid-build.
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

write_lock_info() { # <lockdir> <purpose>
  {
    printf 'pid=%s\n' "$$"
    printf 'host=%s\n' "$(hostname)"
    printf 'started=%s\n' "$(iso_now)"
    printf 'started_epoch=%s\n' "$(epoch_now)"
    printf 'purpose=%s\n' "$2"
  } > "$1/info"
  # Also publish the holder in the layout local/bin/ci.sh reads.
  printf '%s\n%s\n%s\n' "$$" "$(iso_now)" "$2" > "$1/owner"
}

acquire_lock() { # <lockdir> <ttl> <timeout-seconds; 0 = wait forever> <purpose>
  local dir="$1" ttl="$2" timeout="$3" purpose="$4" waited=0 announced=0
  mkdir -p "$(dirname "$dir")"
  while ! mkdir "$dir" 2>/dev/null; do
    if lock_is_stale "$dir" "$ttl"; then
      break_lock "$dir"
      continue
    fi
    if [ "$announced" -eq 0 ]; then
      log "waiting for the $purpose lock $dir (held by pid=$(lock_pid "$dir"))"
      announced=1
    fi
    if [ "$timeout" -ne 0 ] && [ "$waited" -ge "$timeout" ]; then
      return 1
    fi
    sleep 10
    waited=$((waited + 10))
  done
  write_lock_info "$dir" "$purpose"
  return 0
}

cleanup() {
  local rc=$?
  if [ -n "$STAGE_DIR" ] && [ -d "$STAGE_DIR" ]; then
    rm -rf "$STAGE_DIR"
  fi
  if [ "$FULL_BUILD_LOCK_HELD" -eq 1 ]; then
    rm -rf "$FULL_BUILD_LOCK"
    FULL_BUILD_LOCK_HELD=0
  fi
  if [ "$LEASE_HELD" -eq 1 ]; then
    rm -rf "$LEASE_DIR"
    LEASE_HELD=0
  fi
  exit "$rc"
}
trap cleanup EXIT INT TERM

# ------------------------------------------------------------------- telemetry
#
# One JSON line per full build (local/DESIGN.md, "Telemetry"):
#   results/telemetry/builds.jsonl — kind (warm|rebuild|cache-get), duration,
#   outcome, trigger.
# Telemetry never blocks or fails a build: every failure path degrades to a
# warning.  `note` is sanitized (non-printables stripped, truncated) because it
# can quote build output, which stays untrusted text even locally (DESIGN.md #6).

resolve_primary_repo() {
  # Prefer the primary checkout even when invoked from a linked worktree, so the
  # append-only JSONL does not fork per worktree and conflict at merge time.
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

snapshot_list_newest_first() {
  # Snapshot names are snap-<utc-timestamp>-<sha12>, so a reverse lexicographic
  # sort is a reverse chronological sort.
  [ -d "$SNAPSHOTS" ] || return 0
  find "$SNAPSHOTS" -mindepth 1 -maxdepth 1 -type d -name 'snap-*' 2>/dev/null \
    | sed 's|.*/||' | grep -v '\.tmp$' | LC_ALL=C sort -r || true
}

current_target() {
  [ -L "$CURRENT_LINK" ] || return 1
  local target
  target="$(readlink "$CURRENT_LINK")" || return 1
  [ -n "$target" ] || return 1
  [ -d "$target" ] || return 1
  printf '%s' "$target"
}

stamp_field() { # <stamp-file> <key>
  local file="$1" key="$2" line value
  [ -f "$file" ] || return 1
  while IFS= read -r line; do
    case "$line" in
      "$key="*)
        value="${line#*=}"
        # STAMP is on-disk data, not code: validate, never eval or source.
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

print_status() {
  local target stamp name
  printf 'cache root : %s\n' "$CACHE_ROOT"
  printf 'hot repo   : %s\n' "$HOT_REPO"
  if target="$(current_target)"; then
    stamp="$target/STAMP"
    printf 'current    : %s\n' "$target"
    printf '  sha      : %s\n' "$(stamp_field "$stamp" sha || echo '<unreadable>')"
    printf '  keyhash  : %s\n' "$(stamp_field "$stamp" keyhash || echo '<unreadable>')"
    printf '  status   : %s\n' "$(stamp_field "$stamp" status || echo '<unreadable>')"
    printf '  built    : %s\n' "$(stamp_field "$stamp" timestamp || echo '<unreadable>')"
  else
    printf 'current    : <none published>\n'
  fi
  printf 'snapshots  :\n'
  while IFS= read -r name; do
    [ -n "$name" ] || continue
    printf '  %s (%s)\n' "$name" "$(stamp_field "$SNAPSHOTS/$name/STAMP" status || echo unknown)"
  done <<< "$(snapshot_list_newest_first)"
}

gc_snapshots() {
  local keep="$KEEP" kept=0 name protected path
  if [ "$keep" -lt 1 ]; then
    keep=1
  fi
  protected="$(current_target || true)"
  while IFS= read -r name; do
    [ -n "$name" ] || continue
    path="$SNAPSHOTS/$name"
    kept=$((kept + 1))
    if [ "$kept" -le "$keep" ]; then
      continue
    fi
    # Never GC the snapshot `current` points at, even when it falls outside the
    # keep window: consumers resolve `current` once and must find a live tree.
    if [ -n "$protected" ] && [ "$path" = "$protected" ]; then
      log "GC keeping $name: it is the published 'current' snapshot"
      continue
    fi
    log "GC removing snapshot $name"
    rm -rf "$path"
  done <<< "$(snapshot_list_newest_first)"
  find "$SNAPSHOTS" -mindepth 1 -maxdepth 1 -type d -name 'snap-*.tmp' -mmin +60 \
    -exec rm -rf {} + 2>/dev/null || true
}

# Copy-on-write clone inside the cache volume; falls back to a full copy.
cow_copy() { # <src-dir> <dst-dir>
  if cp -c -R "$1" "$2" 2>/dev/null; then
    return 0
  fi
  warn "APFS clone (cp -c) unavailable for $1 -> $2; falling back to a full copy"
  rm -rf "$2"
  cp -R "$1" "$2"
}

# First-run seeding: when the hot checkout has no .lake/build but the PRIMARY
# checkout holds one under the same keyhash, clone it copy-on-write instead of
# recompiling ~9000 modules from source.  This is the local analogue of the
# parent CI's restore-by-key-prefix (pr-ci.yml:144-160): an older-than-target
# build is fine, Lake rebuilds the delta by trace hash; a keyhash mismatch
# (toolchain/manifest/lakefile moved) means the build is unusable and the cold
# path is correct.  Only .lake is copied — the hot checkout's git state stays
# authoritative.
seed_hot_repo_lake() { # <primary-repo>
  local primary="$1"
  [ -d "$HOT_REPO/.lake/build" ] && return 0
  [ -d "$primary/.lake/build" ] || return 0
  if [ "$(compute_keyhash "$primary")" != "$(compute_keyhash "$HOT_REPO")" ]; then
    warn "primary checkout keyhash differs from the hot checkout; not seeding .lake from it"
    return 0
  fi
  log "seeding $HOT_REPO/.lake from the primary checkout's built tree (copy-on-write)"
  mkdir -p "$HOT_REPO/.lake"
  if ! cow_copy "$primary/.lake/build" "$HOT_REPO/.lake/build"; then
    warn "seeding .lake/build from $primary failed; building from source instead"
    rm -rf "$HOT_REPO/.lake/build"
    return 0
  fi
  if [ ! -d "$HOT_REPO/.lake/packages" ] && [ -d "$primary/.lake/packages" ]; then
    if ! cow_copy "$primary/.lake/packages" "$HOT_REPO/.lake/packages"; then
      warn "seeding .lake/packages failed; lake exe cache get will fetch them"
      rm -rf "$HOT_REPO/.lake/packages"
    fi
  fi
}

# rename(2) over an existing symlink.  `mv` is NOT usable here: BSD mv stat()s the
# destination, follows the old `current` symlink to its directory, and would move
# the new link *inside* the snapshot instead of replacing it.
atomic_symlink() { # <target> <linkpath>
  python3 - "$1" "$2" <<'PY'
import os
import sys

target, link = sys.argv[1], sys.argv[2]
tmp = "%s.tmp.%d" % (link, os.getpid())
if os.path.islink(tmp) or os.path.exists(tmp):
    os.remove(tmp)
os.symlink(target, tmp)
os.replace(tmp, link)
PY
}

# ------------------------------------------------------------------ hot checkout

ensure_hot_repo() { # <primary-repo> <ref> -> prints the resolved sha
  local primary="$1" ref="$2" sha="" candidate
  mkdir -p "$HOT_MAIN"
  if [ ! -d "$HOT_REPO/.git" ]; then
    log "creating the hot main checkout at $HOT_REPO (clone of $primary)"
    run_outside_git_env git clone --no-checkout "$primary" "$HOT_REPO" >/dev/null 2>&1 \
      || die "failed to clone $primary into $HOT_REPO"
  fi
  run_outside_git_env git -C "$HOT_REPO" remote set-url origin "$primary" >/dev/null 2>&1 || true
  if ! run_outside_git_env git -C "$HOT_REPO" fetch --prune --tags origin >/dev/null 2>&1; then
    warn "git fetch from $primary failed; using whatever the hot checkout already holds"
  fi

  if [ -n "$SHA" ]; then
    sha="$(run_outside_git_env git -C "$HOT_REPO" rev-parse --verify "${SHA}^{commit}" 2>/dev/null || true)"
    [ -n "$sha" ] || die "commit '$SHA' does not resolve in $HOT_REPO"
  else
    # DESIGN.md #8: origin/main must resolve.  Prefer it; accept a local branch.
    for candidate in "origin/$ref" "$ref"; do
      sha="$(run_outside_git_env git -C "$HOT_REPO" rev-parse --verify "${candidate}^{commit}" 2>/dev/null || true)"
      [ -n "$sha" ] && break
    done
    [ -n "$sha" ] || die \
      "neither origin/$ref nor $ref resolves in $HOT_REPO. If $primary has no commits yet, make the first commit on '$ref' before warming."
  fi

  # .lake/ is gitignored, so a forced checkout never touches the build tree, and
  # `git clean` is deliberately not run (it would descend into vendored packages).
  run_outside_git_env git -C "$HOT_REPO" checkout --detach --force "$sha" >/dev/null 2>&1 \
    || die "failed to check out $sha in $HOT_REPO"
  printf '%s' "$sha"
}

# The ProofWidgets fresh-state workaround (docgen.yml:56-69).  `lake exe cache get`
# runs `lake update`, whose mathlib post-update hook prunes
# .lake/packages/proofwidgets/.lake/build/lib before fetching a cloud release; on a
# tree that has never built, the directory does not exist and the uncaught
# exception aborts the whole cache fetch.  Locally the same fetch also aborts when
# a vendored package tree is *dirty* — build byproducts such as
# widget/js/lake.trace block the revision checkout; see the 2026-08-30 failure and
# its retry in results/telemetry/builds.jsonl.  Both are fresh-state bugs, and a
# pristine checkout is exactly fresh state.
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

# ----------------------------------------------------------------------- publish

publish_snapshot() { # <sha> <keyhash> <status> <build-seconds> -> prints the name
  local sha="$1" keyhash="$2" status="$3" seconds="$4" name final
  name="snap-$(stamp_id)-${sha:0:12}"
  final="$SNAPSHOTS/$name"

  mkdir -p "$SNAPSHOTS"
  STAGE_DIR="$SNAPSHOTS/$name.tmp"
  rm -rf "$STAGE_DIR"
  mkdir -p "$STAGE_DIR"

  cow_copy "$HOT_REPO/.lake/build" "$STAGE_DIR/build"

  {
    printf 'sha=%s\n' "$sha"
    printf 'keyhash=%s\n' "$keyhash"
    printf 'timestamp=%s\n' "$(iso_now)"
    printf 'timestamp_epoch=%s\n' "$(epoch_now)"
    printf 'status=%s\n' "$status"
    printf 'build_seconds=%s\n' "$seconds"
    printf 'toolchain=%s\n' "$(tr -d '\r\n' < "$HOT_REPO/lean-toolchain")"
    printf 'snapshot=%s\n' "$name"
    printf 'warmer_version=%s\n' "$WARMER_VERSION"
  } > "$STAGE_DIR/STAMP"

  rm -rf "$final"
  mv "$STAGE_DIR" "$final"   # rename(2): a reader never sees a torn snapshot
  STAGE_DIR=""

  atomic_symlink "$final" "$CURRENT_LINK"
  printf '%s' "$name"
}

# --------------------------------------------------------------------------- main

main() {
  while [ $# -gt 0 ]; do
    case "$1" in
      --ref)          REF="${2:?--ref needs a value}"; shift 2 ;;
      --sha)          SHA="${2:?--sha needs a value}"; shift 2 ;;
      --force)        FORCE=1; shift ;;
      --targets)      EXTRA_TARGETS="${2:?--targets needs a value}"; shift 2 ;;
      --lock-timeout) LOCK_TIMEOUT="${2:?--lock-timeout needs a value}"; shift 2 ;;
      --lease-ttl)    LEASE_TTL="${2:?--lease-ttl needs a value}"; shift 2 ;;
      --keep)         KEEP="${2:?--keep needs a value}"; shift 2 ;;
      --gc-only)      MODE="gc"; shift ;;
      --status)       MODE="status"; shift ;;
      -h|--help)      usage; exit 0 ;;
      *)              usage >&2; die "unknown argument: $1" ;;
    esac
  done

  case "$LOCK_TIMEOUT$LEASE_TTL$KEEP" in
    ''|*[!0-9]*) die "--lock-timeout, --lease-ttl and --keep must be non-negative integers" ;;
  esac

  mkdir -p "$CACHE_ROOT" "$HOT_MAIN" "$SNAPSHOTS" "$LOG_DIR"

  if [ "$MODE" = "status" ]; then
    print_status
    return 0
  fi

  # The writer lease is what makes this the *single* writer (DESIGN.md #1).  It is
  # a separate lock from the full-build lock, so a consumer's incremental build can
  # proceed while the warmer sits idle between commits.
  acquire_lock "$LEASE_DIR" "$LEASE_TTL" 0 "warmer-writer-lease" \
    || die "could not acquire the writer lease at $LEASE_DIR"
  LEASE_HELD=1

  if [ "$MODE" = "gc" ]; then
    gc_snapshots
    return 0
  fi

  local primary sha keyhash target existing_sha existing_status
  local logfile started elapsed status outcome rc name

  primary="$(resolve_primary_repo)"
  [ -d "$primary/.git" ] || die "$primary is not a git repository; cannot seed the hot main checkout"

  ensure_lean_on_path
  sha="$(ensure_hot_repo "$primary" "$REF")"
  keyhash="$(compute_keyhash "$HOT_REPO")"
  log "target sha=$sha keyhash=$keyhash"

  if [ "$FORCE" -eq 0 ] && target="$(current_target)"; then
    existing_sha="$(stamp_field "$target/STAMP" sha || true)"
    existing_status="$(stamp_field "$target/STAMP" status || true)"
    if [ "$existing_sha" = "$sha" ] \
       && [ "$existing_status" = "complete" ] \
       && [ "$(stamp_field "$target/STAMP" keyhash || true)" = "$keyhash" ]; then
      log "a complete snapshot for $sha is already published; nothing to do (use --force to rebuild)"
      gc_snapshots
      return 0
    fi
  fi

  # One full `lake build` machine-wide (DESIGN.md #7).  The warmer WAITS instead of
  # aborting, and is never killed for a newer commit: pr-ci.yml:50 — "Do not cancel
  # main-branch runs: they seed the build cache."
  if ! acquire_lock "$FULL_BUILD_LOCK" "$LOCK_TIMEOUT" "$LOCK_TIMEOUT" "full-lake-build"; then
    die "timed out after ${LOCK_TIMEOUT}s waiting for the machine-wide full-build lock $FULL_BUILD_LOCK"
  fi
  FULL_BUILD_LOCK_HELD=1

  logfile="$LOG_DIR/warm-$(stamp_id)-${sha:0:12}.log"
  started="$(epoch_now)"
  status="partial"
  outcome="failed"
  rc=0

  log "building $sha in $HOT_REPO (log: $logfile)"
  seed_hot_repo_lake "$primary"
  proofwidgets_fresh_state_workaround "$HOT_REPO"
  printf '=== cache-warmer %s sha=%s keyhash=%s ===\n' "$(iso_now)" "$sha" "$keyhash" > "$logfile"

  # No `lake update` here.  `lake exe cache get` fetches Mathlib oleans into
  # .lake/packages; `lake update` would move lake-manifest.json out from under the
  # keyhash and mutate the vendored package trees (two-tier split, see
  # local/protocols/build-cache.md).
  if ! ( cd "$HOT_REPO" && run_outside_git_env lake exe cache get ) >> "$logfile" 2>&1; then
    warn "lake exe cache get failed; continuing to build from source (see $logfile)"
  fi

  if ( cd "$HOT_REPO" && run_outside_git_env lake build ) >> "$logfile" 2>&1; then
    status="complete"
    outcome="success"
  else
    rc=1
    # pr-ci.yml:161-162 — "Save even when the build failed: a partial cache still
    # spares the next run the modules that did compile."
    warn "lake build failed; publishing a PARTIAL snapshot (see $logfile)"
  fi

  if [ "$status" = "complete" ] && [ -n "$EXTRA_TARGETS" ]; then
    # shellcheck disable=SC2086
    if ! ( cd "$HOT_REPO" && run_outside_git_env lake build $EXTRA_TARGETS ) >> "$logfile" 2>&1; then
      status="partial"
      outcome="failed"
      rc=1
      warn "extra targets ($EXTRA_TARGETS) failed; the snapshot is flagged partial"
    fi
  fi

  elapsed=$(( $(epoch_now) - started ))

  rm -rf "$FULL_BUILD_LOCK"
  FULL_BUILD_LOCK_HELD=0

  if [ ! -d "$HOT_REPO/.lake/build" ]; then
    append_build_telemetry "warm" "failed" "$elapsed" "cache-warmer ref=$REF" "$sha" \
      "no .lake/build produced; nothing published; log=$logfile"
    die "no .lake/build directory was produced; nothing to publish (see $logfile)"
  fi

  name="$(publish_snapshot "$sha" "$keyhash" "$status" "$elapsed")"
  log "published $name (status=$status, ${elapsed}s); current -> $SNAPSHOTS/$name"

  gc_snapshots
  append_build_telemetry "warm" "$outcome" "$elapsed" "cache-warmer ref=$REF" "$sha" \
    "snapshot=$name status=$status keyhash=$keyhash log=$logfile"

  return "$rc"
}

main "$@"
