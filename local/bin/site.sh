#!/usr/bin/env bash
# site.sh — local replacement for the GitHub Pages component pipeline.
#
# Usage:
#   local/bin/site.sh blueprint   Build and publish the site-blueprint component
#                                 (leanblueprint pdf + texra-blueprint bbl/web
#                                 + homepage), replacing
#                                 .github/workflows/blueprint.yml and
#                                 .github/actions/package-blueprint-component.
#   local/bin/site.sh badges      Run scripts/generate_badges.py and publish the
#                                 site-badges component, replacing
#                                 .github/workflows/badges.yml.
#   local/bin/site.sh docs        Publish the site-docs component. Stub by
#                                 default: the doc-gen4 build is heavy (see
#                                 .github/workflows/docgen.yml:142-153); prints
#                                 a SKIP and how to enable it. Set
#                                 MIPSTARRE_SITE_DOCS_DIR=<tree containing
#                                 docs/> to publish an out-of-band build.
#   local/bin/site.sh assemble    Fetch the newest version of each component and
#                                 assemble the served site, replacing
#                                 .github/workflows/deploy-pages.yml.
#   local/bin/site.sh all         blueprint, badges, docs, then assemble.
#
# Runtime state (never in the repo; local/DESIGN.md:37-38):
#   ~/.cache/mipstarre-dev/site-components/<name>/<timestamp>/  component store
#   ~/.cache/mipstarre-dev/site-components/<name>/latest        newest version
#   ~/.cache/mipstarre-dev/site/_site                           served site
#   ~/.cache/mipstarre-dev/site/_site.prev                      previous site
#   ~/.cache/mipstarre-dev/site/.deploy-lock                    deploy mutex
#   ~/.cache/mipstarre-dev/site/logs/                           build logs
#
# Environment:
#   MIPSTARRE_CACHE_ROOT          runtime root (default ~/.cache/mipstarre-dev)
#   MIPSTARRE_SITE_SOURCE_ROOT    checkout to build from (default: this repo;
#                                 point it at the hot-main tree once the warmer
#                                 exists)
#   MIPSTARRE_SITE_KEEP           versions kept per component (default 3, min 1)
#   MIPSTARRE_SITE_LOCK_WAIT      seconds to queue for the deploy lock (600)
#   MIPSTARRE_SITE_HOMEPAGE_RAW=1 publish home_page/ unrendered when no Jekyll
#   MIPSTARRE_SITE_DOCS_DIR       tree containing docs/ to publish as site-docs
#   TEXRA_BLUEPRINT_VERSION       texra-blueprint pin (default v0.3.8)
#
# Protocol: local/protocols/site.md
set -euo pipefail

# --------------------------------------------------------------------------
# Locations
# --------------------------------------------------------------------------

PROG="$(basename "$0")"
SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
REPO_ROOT="$(cd "$SCRIPT_DIR/../.." && pwd)"

SOURCE_ROOT="${MIPSTARRE_SITE_SOURCE_ROOT:-$REPO_ROOT}"
CACHE_ROOT="${MIPSTARRE_CACHE_ROOT:-$HOME/.cache/mipstarre-dev}"

# Every path below is handed to tools that run with a different working
# directory (jekyll, leanblueprint), so relative roots must be resolved once,
# here, rather than silently meaning different things per stage.
if [ -d "$SOURCE_ROOT" ]; then
  SOURCE_ROOT="$(cd "$SOURCE_ROOT" && pwd)"
fi
case "$CACHE_ROOT" in
  /*) ;;
  *)  CACHE_ROOT="$PWD/$CACHE_ROOT" ;;
esac
STORE="$CACHE_ROOT/site-components"
SITE_DIR="$CACHE_ROOT/site"
LOG_DIR="$SITE_DIR/logs"
DEPLOY_LOCK="$SITE_DIR/.deploy-lock"

FETCH_COMPONENT="$SCRIPT_DIR/fetch-latest-component.sh"

# The texra-blueprint pin is cross-referenced in four parent workflows
# (.github/workflows/blueprint.yml:44, pr-ci.yml:206-208, docgen.yml, claude.yml)
# via comments. Gotcha 11 in the study map: centralize it locally instead of
# inheriting that drift risk. local/bin/env.sh is the intended home; until it
# exists the default below is the single local definition.
if [ -f "$SCRIPT_DIR/env.sh" ]; then
  # shellcheck disable=SC1091
  . "$SCRIPT_DIR/env.sh"
fi
TEXRA_BLUEPRINT_VERSION="${TEXRA_BLUEPRINT_VERSION:-v0.3.8}"
TEXRA_BLUEPRINT_PIN="git+https://github.com/LionSR/texra-blueprint@${TEXRA_BLUEPRINT_VERSION}"

KEEP="${MIPSTARRE_SITE_KEEP:-3}"
LOCK_WAIT="${MIPSTARRE_SITE_LOCK_WAIT:-600}"

COMPONENTS="site-blueprint site-docs site-badges"

# --------------------------------------------------------------------------
# Small helpers
# --------------------------------------------------------------------------

log()  { printf '%s\n' "$*"; }
warn() { printf 'warning: %s\n' "$*" >&2; }
die()  { printf '%s: %s\n' "$PROG" "$*" >&2; exit 1; }

usage() {
  sed -n '2,/^set -euo pipefail$/p' "$0" | grep '^#' | sed 's/^# \{0,1\}//'
}

ts_now() { date -u +%Y%m%dT%H%M%SZ; }

CLEANUP_PATHS=()
LOCKS_HELD=()

push_cleanup() { CLEANUP_PATHS[${#CLEANUP_PATHS[@]}]="$1"; }

cleanup() {
  local p l holder
  if [ "${#CLEANUP_PATHS[@]}" -gt 0 ]; then
    for p in "${CLEANUP_PATHS[@]}"; do
      [ -n "$p" ] && rm -rf -- "$p" || true
    done
  fi
  if [ "${#LOCKS_HELD[@]}" -gt 0 ]; then
    for l in "${LOCKS_HELD[@]}"; do
      holder=""
      if [ -f "$l/pid" ]; then
        holder="$(cat "$l/pid" 2>/dev/null || true)"
      fi
      if [ "$holder" = "$$" ]; then
        rm -rf -- "$l" || true
      fi
    done
  fi
}
trap cleanup EXIT

require_cmd() {
  command -v "$1" >/dev/null 2>&1 || die "required command '$1' not found on PATH"
}

# Git hooks export GIT_DIR/GIT_INDEX_FILE/... into their children; leaking them
# into leanblueprint, Lake, or generate_badges.py makes nested git operations
# resolve the wrong repository. .githooks/pre-push:19-24 clears them the same
# way, and gotcha 8 says any local orchestrator that may run under a hook must
# do it too.
run_clean_git_env() (
  if command -v git >/dev/null 2>&1; then
    for name in $(git rev-parse --local-env-vars); do
      unset "$name" || true
    done
  fi
  "$@"
)

# Atomic pointer swap: symlink into a temp name in the same directory, then
# rename(2) over the old pointer. `ln -sfn` unlinks first and leaves a window in
# which `latest` does not exist, which a concurrent assemble would read as "no
# component published" and turn into a refusal.
atomic_symlink() {
  local dir="$1" target="$2" name="$3"
  python3 - "$dir" "$target" "$name" <<'PY'
import os
import sys

directory, target, name = sys.argv[1], sys.argv[2], sys.argv[3]
tmp = os.path.join(directory, ".%s.tmp.%d" % (name, os.getpid()))
try:
    os.remove(tmp)
except FileNotFoundError:
    pass
os.symlink(target, tmp)
os.replace(tmp, os.path.join(directory, name))
PY
}

# mkdir(2) is the atomic primitive available everywhere; the pid file lets a
# crashed run's lock be reclaimed instead of wedging deploys forever.
lock_acquire() {
  local lock="$1" wait_s="$2" label="$3"
  local waited=0 holder=""
  mkdir -p "$(dirname "$lock")"
  while ! mkdir "$lock" 2>/dev/null; do
    holder=""
    if [ -f "$lock/pid" ]; then
      holder="$(cat "$lock/pid" 2>/dev/null || true)"
    fi
    if [ -n "$holder" ] && ! kill -0 "$holder" 2>/dev/null; then
      warn "reclaiming stale $label lock at $lock (pid $holder is gone)"
      rm -rf -- "$lock"
      continue
    fi
    if [ "$waited" -ge "$wait_s" ]; then
      die "$label lock held by pid ${holder:-unknown} at $lock after ${wait_s}s; \
retry later or remove the directory if you are sure nothing is running"
    fi
    if [ "$waited" -eq 0 ]; then
      log "==> waiting for the $label lock (held by pid ${holder:-unknown})..."
    fi
    sleep 1
    waited=$((waited + 1))
  done
  printf '%s\n' "$$" > "$lock/pid"
  printf '%s\n' "$label" > "$lock/label"
  LOCKS_HELD[${#LOCKS_HELD[@]}]="$lock"
}

lock_release() {
  local lock="$1" holder=""
  if [ -f "$lock/pid" ]; then
    holder="$(cat "$lock/pid" 2>/dev/null || true)"
  fi
  if [ "$holder" = "$$" ]; then
    rm -rf -- "$lock"
  fi
}

source_sha() {
  if command -v git >/dev/null 2>&1 && [ -e "$SOURCE_ROOT/.git" ]; then
    ( cd "$SOURCE_ROOT" && run_clean_git_env git rev-parse HEAD 2>/dev/null ) || echo "unknown"
  else
    echo "unknown"
  fi
}

# --------------------------------------------------------------------------
# Component store
# --------------------------------------------------------------------------

# Sets STAGING_DIR. Not a command substitution: that would run the body in a
# subshell and lose the cleanup registration.
STAGING_DIR=""
staging_dir() {
  # Staged inside the component directory so publishing is a same-filesystem
  # rename, i.e. atomic: a reader never sees a half-copied version.
  local name="$1"
  STAGING_DIR="$STORE/$name/.staging.$$"
  mkdir -p "$STORE/$name"
  rm -rf -- "$STAGING_DIR"
  mkdir -p "$STAGING_DIR"
  push_cleanup "$STAGING_DIR"
}

publish_component() {
  local name="$1" staged="$2"
  shift 2
  local dir="$STORE/$name"
  local base ts n stamp
  base="$(ts_now)"
  ts="$base"
  n=1
  while [ -e "$dir/$ts" ]; do
    ts="$base-$n"
    n=$((n + 1))
  done

  mv "$staged" "$dir/$ts"

  stamp="$dir/$ts.stamp"
  {
    printf 'component=%s\n' "$name"
    printf 'version=%s\n' "$ts"
    printf 'source_root=%s\n' "$SOURCE_ROOT"
    printf 'source_sha=%s\n' "$(source_sha)"
    printf 'builder=%s\n' "local/bin/site.sh"
    printf 'host=%s\n' "$(hostname 2>/dev/null || echo unknown)"
    while [ "$#" -gt 0 ]; do
      printf '%s\n' "$1"
      shift
    done
  } > "$stamp"

  # GC runs before the pointer swap: it then protects the version 'latest' still
  # points at, which is what makes an operator's rollback pin survive the next
  # publish. Either order keeps the reader-safety half of the invariant (the
  # target of 'latest' is never deleted under a concurrent fetch), because the
  # version published a moment ago cannot be in the delete set.
  gc_component "$name"
  atomic_symlink "$dir" "$ts" latest
  log "==> published $name version $ts"
}

# Artifact retention (30/90 days upstream) becomes a version budget. Gotcha 6:
# the version `latest` points at is never deleted, because assemble refuses to
# deploy a site with a missing component rather than blanking a section.
gc_component() {
  local name="$1" dir="$STORE/$name"
  local keep="$KEEP" latest_target="" kept=0 entry
  [ -d "$dir" ] || return 0
  case "$keep" in
    ''|*[!0-9]*) keep=3 ;;
  esac
  [ "$keep" -ge 1 ] || keep=1

  if [ -L "$dir/latest" ]; then
    latest_target="$(basename "$(readlink "$dir/latest")")"
  fi

  for entry in $(ls -1 "$dir" 2>/dev/null \
      | grep -E '^[0-9]{8}T[0-9]{6}Z(-[0-9]+)?$' \
      | sort -r); do
    [ -d "$dir/$entry" ] || continue
    if [ "$kept" -lt "$keep" ]; then
      kept=$((kept + 1))
      continue
    fi
    if [ "$entry" = "$latest_target" ]; then
      log "    gc: keeping $name/$entry (it is the 'latest' target)"
      continue
    fi
    log "    gc: removing $name/$entry"
    rm -rf -- "$dir/$entry" "$dir/$entry.stamp"
  done
}

# --------------------------------------------------------------------------
# blueprint — .github/workflows/blueprint.yml
# --------------------------------------------------------------------------

blueprint_tooling_hint() {
  cat >&2 <<EOF

The blueprint toolchain is installed with pipx (docs/ci-automation.md:515-516
prescribes the first two lines; the third carries the texra-blueprint pin that
.github/workflows/blueprint.yml:44 keeps in lockstep with pr-ci.yml:206-208,
docgen.yml, and claude.yml):

  pipx install leanblueprint
  pipx inject --include-apps --force leanblueprint plastex
  pipx inject --include-apps --force leanblueprint '$TEXRA_BLUEPRINT_PIN'

A TeX distribution with xetex, latexmk and the science packages must also be on
PATH (MacTeX, or 'brew install --cask mactex-no-gui'), plus graphviz/dot for the
dependency graph.
EOF
}

# Runs in a pipeline (subshell): the cd is local and set -e still aborts the
# render on the first failing step.
blueprint_render() {
  cd "$SOURCE_ROOT/blueprint"
  run_clean_git_env leanblueprint pdf
  if [ ! -s print/print.pdf ]; then
    printf '%s\n' "site.sh: leanblueprint pdf produced no output (print/print.pdf empty)"
    return 1
  fi
  # texra-blueprint web wraps leanblueprint web and fails when the renderer
  # meets a command it does not know; the log feeds the label checks below.
  run_clean_git_env texra-blueprint web
}

HOMEPAGE_KIND="none"
build_homepage() {
  local src="$1" dest="$2"
  [ -d "$src" ] || die "homepage source $src not found"

  if command -v bundle >/dev/null 2>&1 && [ -f "$src/Gemfile" ] \
      && ( cd "$src" && run_clean_git_env bundle exec jekyll --version >/dev/null 2>&1 ); then
    log "==> Homepage (bundle exec jekyll)..."
    ( cd "$src" && run_clean_git_env bundle exec jekyll build --source . --destination "$dest" )
    HOMEPAGE_KIND="jekyll-bundle"
    return 0
  fi
  if command -v jekyll >/dev/null 2>&1; then
    log "==> Homepage (jekyll)..."
    ( cd "$src" && run_clean_git_env jekyll build --source . --destination "$dest" )
    HOMEPAGE_KIND="jekyll"
    return 0
  fi

  if [ "${MIPSTARRE_SITE_HOMEPAGE_RAW:-}" = "1" ]; then
    warn "Jekyll not found; copying home_page/ unrendered (MIPSTARRE_SITE_HOMEPAGE_RAW=1)."
    warn "index.md and Liquid templates will NOT be rendered in the served site."
    mkdir -p "$dest"
    cp -R "$src/." "$dest/"
    rm -rf -- "$dest/Gemfile" "$dest/Gemfile.lock" "$dest/_config.yml" "$dest/_layouts"
    HOMEPAGE_KIND="raw"
    return 0
  fi

  cat >&2 <<EOF
$PROG: no Jekyll available to render $src.

.github/actions/package-blueprint-component/action.yml:22-26 builds the homepage
with actions/jekyll-build-pages. Locally, install Jekyll:

  (cd $src && bundle install)      # uses the committed Gemfile
  # or: gem install jekyll

Or set MIPSTARRE_SITE_HOMEPAGE_RAW=1 to publish home_page/ unrendered — the
component then satisfies the assembler but the homepage is raw Markdown.
EOF
  return 1
}

cmd_blueprint() {
  require_cmd python3
  [ -d "$SOURCE_ROOT/blueprint/src" ] \
    || die "no blueprint sources at $SOURCE_ROOT/blueprint/src"

  local missing=""
  command -v leanblueprint >/dev/null 2>&1 || missing="$missing leanblueprint"
  command -v texra-blueprint >/dev/null 2>&1 || missing="$missing texra-blueprint"
  if [ -n "$missing" ]; then
    printf '%s: missing blueprint tooling:%s\n' "$PROG" "$missing" >&2
    blueprint_tooling_hint
    return 1
  fi

  # The parent workflow's concurrency group is 'blueprint-build' with
  # cancel-in-progress: true. Locally a second render of the same working tree
  # would corrupt blueprint/web, and killing a running build wastes the work, so
  # the second invocation refuses immediately instead (gotcha 5: never kill a
  # running build for a newer commit — finish, then rebuild).
  lock_acquire "$SITE_DIR/.blueprint-lock" 0 "blueprint-build"

  mkdir -p "$LOG_DIR"
  local stamp_ts log_file bbl_log
  stamp_ts="$(ts_now)"
  log_file="$LOG_DIR/blueprint-$stamp_ts.log"
  bbl_log="$LOG_DIR/blueprint-$stamp_ts.bbl.log"

  # web.bbl is not committed: regenerate it from the \cite keys in the blueprint
  # sources (blueprint.yml:46-49). Its log is kept separate so the ERROR gate
  # below applies to exactly the pdf+web log the workflow gates on.
  log "==> texra-blueprint bbl (log: $bbl_log)"
  if ! ( cd "$SOURCE_ROOT" && run_clean_git_env texra-blueprint bbl ) 2>&1 | tee "$bbl_log"; then
    die "texra-blueprint bbl failed (log: $bbl_log)"
  fi

  log "==> leanblueprint pdf + texra-blueprint web (log: $log_file)"
  if ! blueprint_render 2>&1 | tee "$log_file"; then
    die "blueprint render failed (log: $log_file)"
  fi

  # Exit-code gates, not annotations: ::error in CI failed the job, and gotcha 8
  # says to keep the exit-code semantics when the annotations go away.
  if grep -q "^ERROR:" "$log_file"; then
    grep -n "^ERROR:" "$log_file" >&2 || true
    die "blueprint has unresolved labels (see ERROR lines above; log: $log_file)"
  fi
  if grep -q "WARNING: File not found:" "$log_file"; then
    grep -n "WARNING: File not found:" "$log_file" >&2 || true
    die "blueprint has missing files (see WARNING lines above; log: $log_file)"
  fi

  local staged
  staging_dir site-blueprint
  staged="$STAGING_DIR"

  log "==> Packaging site-blueprint..."
  cp -R "$SOURCE_ROOT/blueprint/web" "$staged/blueprint"
  cp "$SOURCE_ROOT/blueprint/print/print.pdf" "$staged/blueprint.pdf"
  build_homepage "$SOURCE_ROOT/home_page" "$staged/homepage" || return 1

  # Never publish a version that assemble-pages-site.sh:20-33 would reject: a
  # published-but-unusable 'latest' would block every deploy until the next
  # successful build.
  [ -d "$staged/homepage" ]   || die "packaged component has no homepage/"
  [ -d "$staged/blueprint" ]  || die "packaged component has no blueprint/"
  [ -s "$staged/blueprint.pdf" ] || die "packaged component has no blueprint.pdf"

  publish_component site-blueprint "$staged" \
    "homepage=$HOMEPAGE_KIND" \
    "texra_blueprint_pin=$TEXRA_BLUEPRINT_VERSION" \
    "log=$log_file"
  lock_release "$SITE_DIR/.blueprint-lock"
}

# --------------------------------------------------------------------------
# badges — .github/workflows/badges.yml
# --------------------------------------------------------------------------

cmd_badges() {
  require_cmd python3
  local generator="$SOURCE_ROOT/scripts/generate_badges.py"
  [ -f "$generator" ] || die "badge generator not found at $generator"

  local staged
  staging_dir site-badges
  staged="$STAGING_DIR"

  log "==> generate_badges.py..."
  # The generator resolves the repository from its own path and shells out to
  # git ls-files, so it reports on $SOURCE_ROOT. CI checks out with
  # fetch-depth: 0 (badges.yml:23-24); a local clone already has full history.
  if ! run_clean_git_env python3 "$generator" \
      --output-dir "$staged" \
      --blueprint-src "$SOURCE_ROOT/blueprint/src"; then
    printf '%s: the badge counts come from "git ls-files" in %s, so the checkout\n' \
      "$PROG" "$SOURCE_ROOT" >&2
    printf '%s: must have committed Lean sources and a tracked comparator challenge footer.\n' \
      "$PROG" >&2
    die "generate_badges.py failed — no site-badges version published"
  fi

  # badges.yml:34-38, verbatim: an empty generation must not replace the live
  # badge endpoints.
  local json_count
  json_count="$(find "$staged" -maxdepth 1 -name '*.json' | wc -l | tr -d ' ')"
  if [ "$json_count" -eq 0 ]; then
    die "no badge JSON generated — refusing to publish empty badges"
  fi
  log "    $json_count badge endpoint(s)"

  # The stamp lives beside the version directory, never inside it:
  # assemble-pages-site.sh copies site-badges/*.json wholesale, and the
  # non-empty guard counts *.json, so a stamp file in the payload would both
  # ship as a fake badge and satisfy the guard on its own.
  publish_component site-badges "$staged" "badge_count=$json_count"
}

# --------------------------------------------------------------------------
# docs — .github/workflows/docgen.yml (stub)
# --------------------------------------------------------------------------

cmd_docs() {
  local dir="${MIPSTARRE_SITE_DOCS_DIR:-}"

  if [ -z "$dir" ]; then
    cat <<EOF
==> SKIP site-docs: the doc-gen4 documentation build is not run by this script.

    Upstream (.github/workflows/docgen.yml) spends a weekly 330-minute budget on
    a full 'lake build', 'cd docbuild && lake build MIPStarRE:docs'
    (docgen.yml:142-145), the paper-gaps site (docgen.yml:127-133), and packs
    the result as site-docs (docgen.yml:150-153). That belongs to the build
    layer (local/protocols/build-cache.md), not to the site assembler.

    To publish a site-docs version, build it out of band and hand this command
    the tree:

      cd $SOURCE_ROOT/docbuild && lake build MIPStarRE:docs
      mkdir -p /tmp/site-docs
      cp -R $SOURCE_ROOT/docbuild/.lake/build/doc /tmp/site-docs/docs
      # optional: texra-blueprint --root . paper-gaps site /tmp/site-docs/paper-gaps
      MIPSTARRE_SITE_DOCS_DIR=/tmp/site-docs $PROG docs

    Until a site-docs version exists, 'assemble' refuses to deploy rather than
    removing deployed API docs (assemble-pages-site.sh:36). See
    local/protocols/site.md for the full recipe.
EOF
    return 0
  fi

  [ -d "$dir" ] || die "MIPSTARRE_SITE_DOCS_DIR=$dir is not a directory"
  [ -d "$dir/docs" ] \
    || die "MIPSTARRE_SITE_DOCS_DIR=$dir has no docs/ subdirectory (expected the doc-gen4 output tree)"

  local staged
  staging_dir site-docs
  staged="$STAGING_DIR"
  log "==> Packaging site-docs from $dir..."
  cp -R "$dir/docs" "$staged/docs"
  if [ -d "$dir/paper-gaps" ]; then
    log "    including paper-gaps/"
    cp -R "$dir/paper-gaps" "$staged/paper-gaps"
  fi
  publish_component site-docs "$staged" "imported_from=$dir"
}

# --------------------------------------------------------------------------
# assemble — .github/workflows/deploy-pages.yml
# --------------------------------------------------------------------------

cmd_assemble() {
  local assembler="$SOURCE_ROOT/scripts/assemble-pages-site.sh"
  [ -f "$assembler" ] || die "site assembler not found at $assembler"
  [ -f "$FETCH_COMPONENT" ] || die "component fetcher not found at $FETCH_COMPONENT"

  mkdir -p "$SITE_DIR" "$LOG_DIR"

  # The upstream analog is the job-level concurrency group 'github-pages-deploy'
  # with cancel-in-progress: false (deploy-pages.yml:14-16): deploys queue, they
  # are never cancelled. So this waits rather than failing fast.
  lock_acquire "$DEPLOY_LOCK" "$LOCK_WAIT" "deploy"

  local work="$SITE_DIR/.work.$$"
  rm -rf -- "$work"
  mkdir -p "$work/components"
  push_cleanup "$work"

  local name missing=""
  for name in $COMPONENTS; do
    # Pass the store root explicitly so the child never resolves a different
    # component store than the one this run published into.
    MIPSTARRE_CACHE_ROOT="$CACHE_ROOT" bash "$FETCH_COMPONENT" "$name" "$work/components/$name"
    if [ ! -d "$work/components/$name" ]; then
      missing="$missing $name"
    fi
  done

  # pid-scoped staging path: nothing else may ever delete another run's
  # in-progress assembly.
  local out="$SITE_DIR/_site.tmp.$$"
  rm -rf -- "$out"
  push_cleanup "$out"

  # assemble-pages-site.sh is ported as-is (it is already environment-free
  # bash). It does its own rm -rf "$OUT", which is why OUT is a staging path:
  # running it straight over the served root would 404 a live local server
  # mid-assembly (gotcha 5).
  if ! bash "$assembler" "$work/components" "$out"; then
    if [ -n "$missing" ]; then
      printf '%s: missing component(s):%s\n' "$PROG" "$missing" >&2
      printf '%s: build them first (%s blueprint / badges / docs)\n' "$PROG" "$PROG" >&2
    fi
    if [ -d "$SITE_DIR/_site" ]; then
      printf '%s: the served site at %s/_site is unchanged (last known good)\n' \
        "$PROG" "$SITE_DIR" >&2
    fi
    die "site assembly refused — nothing deployed"
  fi

  # Swap: two renames instead of one, because rename(2) cannot replace a
  # non-empty directory. The gap between them is microseconds and the previous
  # tree is kept as _site.prev for rollback.
  if [ -d "$SITE_DIR/_site" ]; then
    rm -rf -- "$SITE_DIR/_site.prev.tmp"
    mv "$SITE_DIR/_site" "$SITE_DIR/_site.prev.tmp"
  fi
  mv "$out" "$SITE_DIR/_site"
  rm -rf -- "$SITE_DIR/_site.prev"
  if [ -d "$SITE_DIR/_site.prev.tmp" ]; then
    mv "$SITE_DIR/_site.prev.tmp" "$SITE_DIR/_site.prev"
  fi

  {
    printf 'deployed=%s\n' "$(ts_now)"
    for name in $COMPONENTS; do
      if [ -L "$STORE/$name/latest" ]; then
        printf '%s=%s\n' "$name" "$(basename "$(readlink "$STORE/$name/latest")")"
      else
        printf '%s=none\n' "$name"
      fi
    done
  } > "$SITE_DIR/deployed.stamp"

  rm -rf -- "$work"
  lock_release "$DEPLOY_LOCK"

  log "==> Deployed to $SITE_DIR/_site"
  log "    serve it with: python3 -m http.server --directory $SITE_DIR/_site 8000"
  log "    previous tree kept at $SITE_DIR/_site.prev"
}

# --------------------------------------------------------------------------
# all
# --------------------------------------------------------------------------

# A stage that fails calls die, which exits. Running each stage in a subshell
# keeps one failed producer from aborting the rest — but bash does not run the
# EXIT trap of the parent inside a subshell, so reclaim this run's locks and
# staging directories explicitly afterwards. lock_release only removes a lock
# whose pid file names this process, so a concurrent run is never disturbed.
release_stage_state() {
  local name
  lock_release "$SITE_DIR/.blueprint-lock"
  lock_release "$DEPLOY_LOCK"
  for name in $COMPONENTS; do
    rm -rf -- "$STORE/$name/.staging.$$"
  done
  rm -rf -- "$SITE_DIR/.work.$$" "$SITE_DIR/_site.tmp.$$"
}

run_stage() {
  local name="$1"
  if ( "cmd_$name" ); then
    release_stage_state
    return 0
  fi
  release_stage_state
  return 1
}

cmd_all() {
  # Upstream each producer is its own workflow and each calls the deployer, so a
  # failing producer never blocks the refresh of the others: the deploy simply
  # keeps that component's last known good version. Same here — run every
  # producer, then assemble once, then report.
  local failed=""

  if ! run_stage blueprint; then
    failed="$failed blueprint"
    warn "blueprint stage failed; the previously published site-blueprint (if any) stays current"
  fi
  if ! run_stage badges; then
    failed="$failed badges"
    warn "badges stage failed; the previously published site-badges (if any) stays current"
  fi
  if ! run_stage docs; then
    failed="$failed docs"
  fi
  if ! run_stage assemble; then
    failed="$failed assemble"
  fi

  if [ -n "$failed" ]; then
    die "stage(s) failed:$failed"
  fi
  log "==> all stages complete"
}

# --------------------------------------------------------------------------
# Entry point
# --------------------------------------------------------------------------

main() {
  if [ "$#" -lt 1 ]; then
    usage >&2
    exit 2
  fi

  case "$1" in
    -h|--help|help)
      usage
      return 0
      ;;
  esac

  [ -f "$SOURCE_ROOT/scripts/assemble-pages-site.sh" ] \
    || die "$SOURCE_ROOT does not look like the MIPStarRE checkout (no scripts/assemble-pages-site.sh)"

  mkdir -p "$STORE" "$SITE_DIR"

  case "$1" in
    blueprint) cmd_blueprint ;;
    badges)    cmd_badges ;;
    docs)      cmd_docs ;;
    assemble)  cmd_assemble ;;
    all)       cmd_all ;;
    *)
      printf '%s: unknown subcommand %s\n\n' "$PROG" "$1" >&2
      usage >&2
      exit 2
      ;;
  esac
}

main "$@"
