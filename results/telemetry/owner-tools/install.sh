#!/usr/bin/env bash
# install.sh — the ONE deployment path for the operator tools (design full-speed-v2 §7).
#
# Operator scripts drive tmux, the crontab and the host process table, so they cannot be
# run from the checkout (which is mid-merge for minutes at a time).  They are therefore
# COPIED to ~/.cache/mipstarre-dev/owner-bin/ by this installer and never edited on the
# host: on 2026-09-12 three versions of the lane runner ran at once, `merge-daemon-v9h.sh`
# called a `/tmp/merge-v2.sh` that does not exist, and the shim was patched by an
# `assert old in s` here-doc against a 90-character substring.
#
# Usage:
#   install.sh [--force] [--compat-tmp] [--crons] [--start-loops] [--dry-run]
#   install.sh --verify                 # dependency/hash check (the merge daemon's gate)
#   install.sh --record <name>          # re-record a regenerated file (run_mode.py set speed)
#
# Options:
#   --force        overwrite a deployed copy whose hash matches no released version.
#                  The previous copy is MOVED to owner-bin/attic/<ts>/, never deleted.
#   --start-loops  start capacityd.sh (the 60 s capacity controller loop) if it is not
#                  running, and fire one detached build-on-chsh.sh --seed-refresh (which
#                  returns immediately unless the run is fast and lists chsh)
#                  already running and no stop file holds it.  Without a running
#                  controller nothing writes watchdog/max-codex-*, the caps stay frozen
#                  at whatever seeded them, there is no AIMD, no 5xx trip and no
#                  half-open probe — the 2026-09-12 situation, recovered by hand — and on
#                  a fresh host lane.sh:wait_for_slot fails closed with
#                  `no-capacity-record`.  The merge daemon and the goal keeper are NOT
#                  started here: owner-resume.sh owns those (design §5).
#   --compat-tmp   create /tmp/<name> SYMLINKS into owner-bin/ so anything still invoking
#                  a historical /tmp path runs versioned code.  Nothing is ever written or
#                  edited in /tmp; an existing regular file there is refused, not clobbered.
#   --crons        run install-crons.sh afterwards (crontab regenerated from run-mode).
#                  Also installs the chsh build farm's known-hosts file (below).
#   --dry-run      print the plan and touch nothing (implies --dry-run for --crons too).
#   --dest DIR     install into DIR instead of $MIPSTARRE_CACHE_ROOT/owner-bin (tests).
#   --compat-dir D create the compat symlinks in D instead of /tmp (tests).
#   --speed S      render the PATH shim for speed S instead of asking run_mode.py (tests).
#
# What is written under owner-bin/:
#   <tool>              the deployed copy, mode from the table below
#   tools-version       describe= sha= short= installed_at= source= installer=  (one release)
#   manifest.sha256     "<sha256>  <name>" for every file deployed now (sha256sum format)
#   manifest.accepted   every hash this release accepts for a name; the PATH shim has two
#                       (the fast and the default rendering), because run_mode.py set speed
#                       regenerates it in place
#   repo-root           the checkout this release was installed from
#
# Outside owner-bin/ this installer also places the chsh build farm's host keys at
# $MIPSTARRE_CACHE_ROOT/watchdog/chsh/known_hosts, copied from $MIPSTARRE_CHSH_KNOWN_HOSTS,
# then the durable copy under the cache root, then /tmp/chsh-setup/known_hosts (where the
# 2026-09-12 side session left them, and which a reboot or a /tmp sweep removes).  The
# first install keeps its own copy at watchdog/chsh/known_hosts.source so the keys outlive
# /tmp, and `--verify` says so when the file is missing or empty instead of leaving the
# absence of `host=chsh` rows as the only signal.  They are runtime
# state, not a committed file, and build-on-chsh.sh uses them with
# StrictHostKeyChecking=yes.  Without them the offload exits 64 and every lane simply
# builds on ghz — a missing file is a warning here, never a failed install.
#   attic/<ts>/         the previous copy of every file this run replaced, plus its manifest
#
# Refusal rule (the point of the installer): a deployed file whose hash is neither the
# incoming one, nor the manifest row, nor an accepted variant, nor a hash recorded in an
# attic manifest, is a HAND PATCH.  It is reported and the install stops with exit 4.
# --force is the only way past, and it keeps the patch in the attic.
#
# Exit codes: 0 ok · 2 usage · 3 --verify found a missing file or a hash mismatch ·
#             4 a hand patch was refused · 5 a required source file is missing
set -euo pipefail

PROG="install.sh"

usage() { sed -n '2,60p' "${BASH_SOURCE[0]}" | sed 's/^# \{0,1\}//'; }

FORCE=0; COMPAT=0; CRONS=0; DRY=0; VERIFY=0; RECORD=""; START_LOOPS=0
DEST=""; SPEED=""; COMPAT_DIR="${MIPSTARRE_COMPAT_DIR:-/tmp}"
while [ "$#" -gt 0 ]; do
  case "$1" in
    --force) FORCE=1 ;;
    --compat-tmp) COMPAT=1 ;;
    --crons) CRONS=1 ;;
    --start-loops) START_LOOPS=1 ;;
    --dry-run) DRY=1 ;;
    --verify) VERIFY=1 ;;
    --record) RECORD="${2:-}"; [ -n "$RECORD" ] || { echo "$PROG: --record needs a tool name" >&2; exit 2; }; shift ;;
    --dest) DEST="${2:-}"; [ -n "$DEST" ] || { echo "$PROG: --dest needs a directory" >&2; exit 2; }; shift ;;
    --compat-dir) COMPAT_DIR="${2:-}"; [ -n "$COMPAT_DIR" ] || { echo "$PROG: --compat-dir needs a directory" >&2; exit 2; }; shift ;;
    --speed) SPEED="${2:-}"; [ -n "$SPEED" ] || { echo "$PROG: --speed needs fast or default" >&2; exit 2; }; shift ;;
    -h|--help) usage; exit 0 ;;
    *) echo "$PROG: unknown argument '$1'" >&2; usage >&2; exit 2 ;;
  esac
  shift
done

CACHE_ROOT="${MIPSTARRE_CACHE_ROOT:-$HOME/.cache/mipstarre-dev}"
DEST="${DEST:-$CACHE_ROOT/owner-bin}"
TS="$(date -u +%Y%m%dT%H%M%SZ)"

CHSH_STATE="$CACHE_ROOT/watchdog/chsh"
CHSH_KNOWN_HOSTS_SRC="${MIPSTARRE_CHSH_KNOWN_HOSTS:-/tmp/chsh-setup/known_hosts}"

# The keys survive a reboot.  The default source is /tmp/chsh-setup/known_hosts,
# which is where the 2026-09-12 side session left them and which /tmp cleaning
# or a reboot removes; after that the offload exits 64 forever and every lane
# silently builds here, with the only signal being the ABSENCE of `host=chsh`
# rows in watchdog/chsh/offload.log.  So the first copy is kept under the cache
# root as the durable source, and it is preferred over /tmp on every later run.
CHSH_KNOWN_HOSTS_KEEP="$CHSH_STATE/known_hosts.source"

chsh_known_hosts_source() { # the file to install from, or nothing
  local candidate
  for candidate in "${MIPSTARRE_CHSH_KNOWN_HOSTS:-}" \
                   "$CHSH_KNOWN_HOSTS_KEEP" \
                   "$CHSH_KNOWN_HOSTS_SRC"; do
    [ -n "$candidate" ] && [ -s "$candidate" ] && { printf '%s\n' "$candidate"; return 0; }
  done
  return 1
}

install_chsh_known_hosts() {
  local src
  if ! src="$(chsh_known_hosts_source)"; then
    echo "$PROG: no chsh known-hosts at $CHSH_KNOWN_HOSTS_SRC or $CHSH_KNOWN_HOSTS_KEEP;" \
         "the build farm stays unusable and lanes build on this host"
    return 0
  fi
  mkdir -p "$CHSH_STATE"
  if [ ! -r "$CHSH_KNOWN_HOSTS_KEEP" ] || ! cmp -s "$src" "$CHSH_KNOWN_HOSTS_KEEP"; then
    cp "$src" "$CHSH_STATE/.known_hosts.keep.new"
    chmod 600 "$CHSH_STATE/.known_hosts.keep.new"
    mv "$CHSH_STATE/.known_hosts.keep.new" "$CHSH_KNOWN_HOSTS_KEEP"
    echo "$PROG: chsh host keys kept at $CHSH_KNOWN_HOSTS_KEEP (from $src)"
  fi
  if [ -r "$CHSH_STATE/known_hosts" ] && cmp -s "$src" "$CHSH_STATE/known_hosts"; then
    echo "$PROG: chsh known_hosts unchanged ($CHSH_STATE/known_hosts)"
    return 0
  fi
  cp "$src" "$CHSH_STATE/.known_hosts.new"
  chmod 644 "$CHSH_STATE/.known_hosts.new"
  mv "$CHSH_STATE/.known_hosts.new" "$CHSH_STATE/known_hosts"
  echo "$PROG: chsh known_hosts installed at $CHSH_STATE/known_hosts (from $src)"
}

# --verify reports the keys.  Never an exit-3 failure: a run that does not list
# chsh does not need them, and a missing file costs build minutes and nothing
# else.  What it must never be is invisible.
verify_chsh_known_hosts() {
  if [ -s "$CHSH_STATE/known_hosts" ]; then
    printf '%s: chsh known_hosts present (%s bytes)\n' "$PROG" \
      "$(wc -c < "$CHSH_STATE/known_hosts" | tr -d ' ')"
    return 0
  fi
  echo "$PROG: WARNING: $CHSH_STATE/known_hosts is missing or empty." >&2
  echo "$PROG: the chsh build farm is UNUSABLE (every offload exits 64 and lanes" >&2
  echo "$PROG: build on this host).  If the brief lists chsh, re-run install.sh;" >&2
  echo "$PROG: the durable copy is $CHSH_KNOWN_HOSTS_KEEP." >&2
  return 0
}

# --- the checkout this installer belongs to --------------------------------------------
# When install.sh is run from owner-bin (--verify / --record on the host) it cannot derive
# the checkout from its own path, so fall back to the recorded repo-root.
SELF_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
ROOT=""
if [ -f "$SELF_DIR/../../../AGENTS.md" ]; then
  ROOT="$(cd "$SELF_DIR/../../.." && pwd)"
elif [ -n "${MIPSTARRE_REPO_ROOT:-}" ]; then
  ROOT="$MIPSTARRE_REPO_ROOT"
elif [ -r "$DEST/repo-root" ]; then
  ROOT="$(cat "$DEST/repo-root")"
else
  ROOT="$HOME/MIPStarRE-qpbt"
fi
SRC="$ROOT/results/telemetry/owner-tools"

sha256_of() {
  local f="$1"
  if command -v sha256sum >/dev/null 2>&1; then sha256sum "$f" | awk '{print $1}'
  elif command -v shasum >/dev/null 2>&1; then shasum -a 256 "$f" | awk '{print $1}'
  elif command -v openssl >/dev/null 2>&1; then openssl dgst -sha256 "$f" | awk '{print $NF}'
  else python3 -c 'import hashlib,sys;print(hashlib.sha256(open(sys.argv[1],"rb").read()).hexdigest())' "$f"
  fi
}

# name|source|mode|required — the inventory of §7.  "optional" entries belong to work items
# that may not have landed yet (W3 capacityd, W5 merge daemon); a missing optional source is
# a warning, a missing required source is a hard failure.
tool_table() {
  cat <<'TBL'
install.sh|install.sh|755|required
install-crons.sh|install-crons.sh|755|required
owner-pause.sh|owner-pause.sh|755|required
owner-resume.sh|owner-resume.sh|755|required
owner-say.sh|owner-say.sh|755|required
goal-keeper.sh|goal-keeper.sh|755|required
estimate.sh|estimate.sh|755|required
status-snapshot.sh|status-snapshot.sh|755|required
codex|owner-bin-codex|755|required
stack-watch.sh|stack-watch.sh|755|optional
capacityd.sh|capacityd.sh|755|optional
merge-daemon.sh|merge-daemon.sh|755|optional
build-on-chsh.sh|build-on-chsh.sh|755|optional
merge.sh|merge.sh|755|optional
daemon-scan.py|daemon-scan.py|755|optional
daemon.conf|daemon.conf|644|optional
TBL
}

# historical /tmp name|installed tool — --compat-tmp points every name the 2026-09-12 run
# used at the one versioned copy.
compat_table() {
  cat <<'TBL'
owner-say.sh|owner-say.sh
owner-say-v3.sh|owner-say.sh
owner-say-v4.sh|owner-say.sh
owner-pause.sh|owner-pause.sh
owner-pause-v2.sh|owner-pause.sh
owner-pause-fast.sh|owner-pause.sh
final-pause.sh|owner-pause.sh
owner-resume.sh|owner-resume.sh
goal-keeper.sh|goal-keeper.sh
goal-keeper-v2.sh|goal-keeper.sh
stack-watch.sh|stack-watch.sh
stack-watch-v3.sh|stack-watch.sh
merge-daemon.sh|merge-daemon.sh
merge-daemon-v9h.sh|merge-daemon.sh
merge.sh|merge.sh
daemon-scan.py|daemon-scan.py
estimate.sh|estimate.sh
status-snapshot.sh|status-snapshot.sh
TBL
}

# --- the PATH shim is GENERATED, not copied ---------------------------------------------
# run_mode.py set speed regenerates the deployed shim from the same template by rewriting
# its one SPEED_ARGS= line, so both renderings are released versions of `codex`.  The
# rewrite is ANCHORED at the start of the line: the template documents both renderings in
# its header, and a comment that merely shows the line must never be rewritten with it.
SPEED_MARK='# @speed-args@ regenerated by run_mode.py set speed; do not edit by hand'
render_shim() { # render_shim <fast|default> <src> <out>
  local speed="$1" src="$2" out="$3" line n
  case "$speed" in
    fast) line="SPEED_ARGS=(-c 'service_tier=\"priority\"')   $SPEED_MARK" ;;
    *)    line="SPEED_ARGS=()   $SPEED_MARK" ;;
  esac
  n="$(grep -c '^SPEED_ARGS=' "$src" || true)"
  if [ "$n" != 1 ]; then
    echo "$PROG: $src has $n lines starting with SPEED_ARGS=; exactly one is required" >&2
    exit 5
  fi
  awk -v repl="$line" '
    /^SPEED_ARGS=/ { print repl; next } { print }' "$src" > "$out"
}

current_speed() {
  local s=""
  if [ -n "$SPEED" ]; then printf '%s\n' "$SPEED"; return 0; fi
  s="$(python3 "${MIPSTARRE_RUN_MODE:-$ROOT/local/bin/run_mode.py}" get speed 2>/dev/null || true)"
  s="$(printf '%s' "$s" | head -n 1 | tr -d '\r')"
  case "$s" in
    fast|default) printf '%s\n' "$s" ;;
    *) if [ -r "$DEST/codex" ] && grep -q 'service_tier' "$DEST/codex" 2>/dev/null
       then printf 'fast\n'; else printf 'default\n'; fi ;;
  esac
}

manifest_hash() { # manifest_hash <name> [manifest]
  { awk -v n="$1" '$2 == n { print $1 }' "${2:-$DEST/manifest.sha256}" 2>/dev/null || true; } | head -n 1
}

known_hashes() { # every hash this installation accepts for <name>
  local name="$1"
  awk -v n="$name" '$2 == n { print $1 }' "$DEST/manifest.sha256" 2>/dev/null || true
  awk -v n="$name" '$2 == n { print $1 }' "$DEST/manifest.accepted" 2>/dev/null || true
  if [ -d "$DEST/attic" ]; then
    find "$DEST/attic" -name manifest.sha256 -type f -print 2>/dev/null | while read -r m; do
      awk -v n="$name" '$2 == n { print $1 }' "$m" 2>/dev/null || true
    done
  fi
}

VERSION="$( { sed -n 's/^short=//p' "$DEST/tools-version" 2>/dev/null || true; } | head -n 1 )"
echo "tool=$PROG version=${VERSION:-unreleased}"

# --- --verify: the merge daemon's dependency gate ---------------------------------------
if [ "$VERIFY" -eq 1 ]; then
  rc=0
  [ -r "$DEST/manifest.sha256" ] || { echo "$PROG: no manifest at $DEST/manifest.sha256; run install.sh" >&2; exit 3; }
  while IFS='|' read -r name src mode req; do
    [ -n "$name" ] || continue
    want="$(manifest_hash "$name")"
    if [ -z "$want" ]; then
      if [ "$req" = required ]; then echo "$PROG: $name is not in the manifest" >&2; rc=3; fi
      continue
    fi
    if [ ! -e "$DEST/$name" ]; then echo "$PROG: $name is missing from $DEST" >&2; rc=3; continue; fi
    have="$(sha256_of "$DEST/$name")"
    [ "$have" = "$want" ] || { echo "$PROG: $name hash $have does not match the manifest ($want)" >&2; rc=3; }
  done <<EOF
$(tool_table)
EOF
  verify_chsh_known_hosts
  if [ "$rc" -eq 0 ]; then echo "$PROG: $DEST verified against the manifest"; fi
  exit "$rc"
fi

# --- --record: re-record one regenerated file (run_mode.py set speed) -------------------
if [ -n "$RECORD" ]; then
  [ -e "$DEST/$RECORD" ] || { echo "$PROG: $DEST/$RECORD does not exist" >&2; exit 3; }
  have="$(sha256_of "$DEST/$RECORD")"
  ok=0
  while read -r h; do [ "$h" = "$have" ] && ok=1; done <<EOF
$(known_hashes "$RECORD")
EOF
  [ "$ok" -eq 1 ] || {
    echo "$PROG: refusing to record $RECORD: hash $have is not a released version" >&2
    echo "$PROG: regenerate it from $SRC or re-run install.sh --force" >&2
    exit 4
  }
  if [ "$DRY" -eq 1 ]; then echo "$PROG: [dry-run] would record $RECORD $have"; exit 0; fi
  tmp="$DEST/.manifest.$$"
  awk -v n="$RECORD" '$2 != n' "$DEST/manifest.sha256" > "$tmp"
  printf '%s  %s\n' "$have" "$RECORD" >> "$tmp"
  LC_ALL=C sort -k2,2 "$tmp" -o "$tmp"
  mv "$tmp" "$DEST/manifest.sha256"
  echo "$PROG: recorded $RECORD $have"
  exit 0
fi

# --- plan --------------------------------------------------------------------------------
[ -d "$SRC" ] || { echo "$PROG: no source directory $SRC" >&2; exit 5; }
SPEED_NOW="$(current_speed)"
echo "$PROG: source $SRC"
echo "$PROG: dest   $DEST (speed=$SPEED_NOW$([ "$DRY" -eq 1 ] && echo ', dry run'))"

STAGE="${TMPDIR:-/tmp}/mipstarre-install.$$"
mkdir -p "$STAGE"
cleanup() { rm -rf "$STAGE"; }
trap cleanup EXIT

PLAN=""   # name|staged|mode|action
REFUSED=0
while IFS='|' read -r name src mode req; do
  [ -n "$name" ] || continue
  sfile="$SRC/$src"
  if [ ! -f "$sfile" ]; then
    if [ "$req" = required ]; then
      echo "$PROG: required source $sfile is missing" >&2; exit 5
    fi
    echo "$PROG: skip $name (optional source $src not in this checkout yet)"
    continue
  fi
  staged="$STAGE/$name"
  if [ "$name" = codex ]; then render_shim "$SPEED_NOW" "$sfile" "$staged"
  else cp "$sfile" "$staged"; fi
  newh="$(sha256_of "$staged")"
  action=install
  if [ -e "$DEST/$name" ]; then
    oldh="$(sha256_of "$DEST/$name")"
    if [ "$oldh" = "$newh" ]; then
      action=unchanged
    else
      ok=0
      while read -r h; do [ -n "$h" ] && [ "$h" = "$oldh" ] && ok=1; done <<EOF
$(known_hashes "$name")
EOF
      if [ "$ok" -eq 1 ]; then action=update
      elif [ "$FORCE" -eq 1 ]; then action=force
      else
        echo "$PROG: REFUSING $name: the deployed copy is a hand patch" >&2
        echo "$PROG:   $DEST/$name sha256 $oldh" >&2
        echo "$PROG:   matches no released version (manifest, accepted variants, attic)" >&2
        echo "$PROG:   copy it into $SRC as a reviewed change, or re-run with --force" >&2
        REFUSED=1
      fi
    fi
  fi
  PLAN="$PLAN$name|$staged|$mode|$action
"
done <<EOF
$(tool_table)
EOF

[ "$REFUSED" -eq 0 ] || { echo "$PROG: nothing installed" >&2; exit 4; }

printf '%s' "$PLAN" | while IFS='|' read -r name staged mode action; do
  [ -n "$name" ] && printf '  %-18s %s\n' "$name" "$action"
done

if [ "$DRY" -eq 1 ]; then
  echo "$PROG: [dry-run] no file written, no symlink created, no crontab touched"
  if khsrc="$(chsh_known_hosts_source)"; then
    echo "$PROG: [dry-run] would install $khsrc as $CHSH_STATE/known_hosts"
    echo "$PROG: [dry-run] would keep a durable copy at $CHSH_KNOWN_HOSTS_KEEP"
  else
    echo "$PROG: [dry-run] no chsh known-hosts at $CHSH_KNOWN_HOSTS_SRC or $CHSH_KNOWN_HOSTS_KEEP; the build farm stays unusable"
  fi
  if [ "$CRONS" -eq 1 ]; then
    "$SRC/install-crons.sh" --dry-run || exit $?
  fi
  if [ "$START_LOOPS" -eq 1 ]; then
    echo "$PROG: [dry-run] would start capacityd.sh (the 60 s capacity controller loop)"
    echo "$PROG: [dry-run] would start build-on-chsh.sh --seed-refresh detached (a no-op unless the run is fast and lists chsh)"
  fi
  exit 0
fi

# --- install ------------------------------------------------------------------------------
mkdir -p "$DEST"
ATTIC="$DEST/attic/$TS"
attic_of() { # keep the copy we are about to replace, and the manifest that described it
  mkdir -p "$ATTIC"
  cp -p "$DEST/$1" "$ATTIC/$1"
  if [ ! -f "$ATTIC/manifest.sha256" ] && [ -f "$DEST/manifest.sha256" ]; then
    cp -p "$DEST/manifest.sha256" "$ATTIC/manifest.sha256"
  fi
  return 0
}

NEW_MANIFEST="$STAGE/manifest.sha256"
: > "$NEW_MANIFEST"
printf '%s' "$PLAN" | {
  while IFS='|' read -r name staged mode action; do
    [ -n "$name" ] || continue
    case "$action" in
      update|force) attic_of "$name" ;;
    esac
    if [ "$action" != unchanged ]; then
      cp "$staged" "$DEST/.$name.new"
      chmod "$mode" "$DEST/.$name.new"
      mv "$DEST/.$name.new" "$DEST/$name"
    fi
    printf '%s  %s\n' "$(sha256_of "$DEST/$name")" "$name" >> "$NEW_MANIFEST"
  done
}
LC_ALL=C sort -k2,2 "$NEW_MANIFEST" -o "$NEW_MANIFEST"
cp "$NEW_MANIFEST" "$DEST/manifest.sha256"

# accepted variants: every rendering of the generated shim, plus the deployed hash of
# everything else.  run_mode.py set speed checks against this file before --record.
ACC="$STAGE/manifest.accepted"
cp "$NEW_MANIFEST" "$ACC"
if [ -f "$SRC/owner-bin-codex" ]; then
  for s in fast default; do
    render_shim "$s" "$SRC/owner-bin-codex" "$STAGE/codex.$s"
    printf '%s  %s\n' "$(sha256_of "$STAGE/codex.$s")" "codex" >> "$ACC"
  done
fi
if [ -f "$DEST/manifest.accepted" ]; then cat "$DEST/manifest.accepted" >> "$ACC"; fi
LC_ALL=C sort -u -k2,2 -k1,1 "$ACC" -o "$ACC"
cp "$ACC" "$DEST/manifest.accepted"

DESCRIBE="$(git -C "$ROOT" describe --tags --always --dirty 2>/dev/null || echo unknown)"
SHA="$(git -C "$ROOT" rev-parse HEAD 2>/dev/null || echo unknown)"
SHORT="$(git -C "$ROOT" rev-parse --short HEAD 2>/dev/null || echo unknown)"
{
  printf 'describe=%s\n' "$DESCRIBE"
  printf 'sha=%s\n' "$SHA"
  printf 'short=%s\n' "$SHORT"
  printf 'installed_at=%s\n' "$(date -u +%FT%TZ)"
  printf 'source=%s\n' "$SRC"
  printf 'speed=%s\n' "$SPEED_NOW"
  printf 'installer=%s\n' "$(sha256_of "$DEST/install.sh")"
} > "$DEST/tools-version"
printf '%s\n' "$ROOT" > "$DEST/repo-root"
echo "$PROG: installed $(wc -l < "$DEST/manifest.sha256" | tr -d ' ') files, release $SHORT ($DESCRIBE)"
if [ -d "$ATTIC" ]; then echo "$PROG: previous copies kept in $ATTIC"; fi

# --- the chsh build farm's host keys -------------------------------------------------------
install_chsh_known_hosts

# --- compat symlinks ----------------------------------------------------------------------
if [ "$COMPAT" -eq 1 ]; then
  mkdir -p "$COMPAT_DIR"
  n=0
  while IFS='|' read -r alias target; do
    [ -n "$alias" ] || continue
    [ -e "$DEST/$target" ] || continue
    link="$COMPAT_DIR/$alias"
    if [ -e "$link" ] && [ ! -L "$link" ]; then
      echo "$PROG: $link is a regular file; leaving it alone (use --force to replace)" >&2
      [ "$FORCE" -eq 1 ] || continue
      rm -f "$link"
    fi
    ln -sfn "$DEST/$target" "$link"
    n=$((n + 1))
  done <<EOF
$(compat_table)
EOF
  echo "$PROG: $n compat symlinks in $COMPAT_DIR (symlinks only; nothing is edited there)"
fi

# --- crontab -------------------------------------------------------------------------------
if [ "$CRONS" -eq 1 ]; then
  "$DEST/install-crons.sh" || exit $?
fi

# --- the capacity controller loop -----------------------------------------------------------
# The AIMD controller and the endpoint health machine are the whole answer to the ten hand
# cap edits and the 69 deaths into a 503 endpoint.  Copying capacityd.sh is not running it.
if [ "$START_LOOPS" -eq 1 ]; then
  CAPD="$DEST/capacityd.sh"
  CAP_STATE="$CACHE_ROOT/watchdog/capacity"
  if [ ! -x "$CAPD" ]; then
    echo "$PROG: no capacityd.sh at $CAPD; the capacity controller is NOT running" >&2
  elif [ -e "$CAP_STATE/capacityd.stop" ]; then
    echo "$PROG: $CAP_STATE/capacityd.stop holds capacityd; remove it (owner-resume.sh does)" >&2
  else
    mkdir -p "$CAP_STATE"
    setsid nohup bash "$CAPD" >> "$CAP_STATE/capacityd.out" 2>&1 < /dev/null &
    sleep 1
    CAPPID="$(cat "$CAP_STATE/capacityd.pid" 2>/dev/null || true)"
    if [ -n "$CAPPID" ] && kill -0 "$CAPPID" 2>/dev/null; then
      echo "$PROG: capacityd.sh running (pid $CAPPID, tick ${CAPACITY_TICK_S:-60}s)"
    else
      echo "$PROG: capacityd.sh did not come up; see $CAP_STATE/capacityd.log" >&2
    fi
  fi

  # --- the build farm's seed, once, at run start --------------------------------------
  # The merge daemon refreshes chsh's seed AFTER a merge, so at the start of a run the
  # seed is at whatever the last run left and the first offloaded lanes rebuild hours of
  # `main` on chsh before any merge lands.  This is a no-op while the offload is disabled
  # (the script's own gate returns immediately without contacting anything), so it costs a
  # default-speed run nothing and needs no condition here.
  CHSH_SH="$DEST/build-on-chsh.sh"
  if [ -r "$CHSH_SH" ]; then
    mkdir -p "$CHSH_STATE"
    setsid nohup bash "$CHSH_SH" --seed-refresh \
      >> "$CHSH_STATE/seed-refresh.log" 2>&1 < /dev/null &
    echo "$PROG: chsh seed refresh started detached (a no-op unless the run is fast and lists chsh); log $CHSH_STATE/seed-refresh.log"
  fi
fi
exit 0
