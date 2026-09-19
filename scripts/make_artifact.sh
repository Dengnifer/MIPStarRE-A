#!/usr/bin/env bash
# make_artifact.sh — cut the ITP artifact snapshot from a tagged commit.
#
# The artifact is a RELEASE SNAPSHOT of the mathematical development, not the
# working repository (acting-main decision, 2026-09-19; the reviewer-facing
# description lives in docs/ARTIFACT.md).  Two independent mechanisms decide
# what ships, and a path must pass both:
#
#   1. the INCLUDE pathspecs below — an explicit allow-list, so a new top-level
#      directory never joins the artifact by accident;
#   2. the `export-ignore` attributes in .gitattributes, which `git archive`
#      applies on its own — so a plain `git archive` of this repository is
#      clean too.
#
# Excluded on purpose: the AI-workflow layer (results/telemetry/, local/,
# .github/, .githooks/, workflow-only scripts and docs) and the third-party
# paper mirrors under references/, whose redistribution terms are unsettled.
# Dropping the workflow layer also removes every tracked file that mentions the
# build host's home path, without rewriting history.
#
# The script FAILS on a leak-scan hit.  That is the point: a snapshot that
# leaks a home path, a key-shaped string or an e-mail address is not shipped.

set -euo pipefail

# --------------------------------------------------------------------------
# What ships
# --------------------------------------------------------------------------

# Allow-list, as `git archive` pathspecs.  Paths absent at the requested
# revision are dropped before the call, so an optional file such as LICENSE
# costs nothing while it is still missing.
INCLUDE=(
  MIPStarRE
  MIPStarRE.lean
  lakefile.toml
  lake-manifest.json
  lean-toolchain
  blueprint/src
  docs
  README.md
  LICENSE
  scripts/comparator
  scripts/blueprint_leanok_axioms.py
  scripts/make_artifact.sh
)

# Carved out of `docs/` above: pages that document the AI workflow rather than
# the mathematics, and would only confuse a reviewer.
EXCLUDE=(
  ':(exclude)docs/campaign'
  ':(exclude)docs/reports'
  ':(exclude)docs/ci-automation.md'
  ':(exclude)docs/ci-blueprint-sync.md'
  ':(exclude)docs/pr_review_management.md'
  ':(exclude)docs/stale_issue_audit.md'
  ':(exclude)docs/blueprint-script-coverage.md'
)

# --------------------------------------------------------------------------
# Leak scan
# --------------------------------------------------------------------------

# Anything matching one of these in the snapshot fails the run.
LEAK_PATTERNS=(
  '/home/[A-Za-z0-9._-]+'
  '/Users/[A-Za-z0-9._-]+'
  '\bsk-[A-Za-z0-9_-]{16,}'
  '\bghp_[A-Za-z0-9]{20,}'
  '\bgithub_pat_[A-Za-z0-9_]{20,}'
  '\bAKIA[0-9A-Z]{16}\b'
  '-----BEGIN [A-Z ]*PRIVATE KEY-----'
  '[A-Za-z0-9._%+-]+@[A-Za-z0-9.-]+\.[A-Za-z]{2,}'
)

# `<regex> :: <reason>`: a hit is forgiven only when it matches one of these
# AND the reason says why that is safe.  `::` separates the two because a
# regex may well contain `|`.  Keep the list short and the reasons honest —
# every entry is something a reviewer may read in the shipped files.
LEAK_ALLOW=(
  '@example\.(com|org|invalid) :: documentation placeholder domain reserved by RFC 2606'
)

# --------------------------------------------------------------------------
# Anonymization (--anonymize only)
# --------------------------------------------------------------------------

# `<regex> :: <replacement>`, applied to every text file in the snapshot.  The
# repository owner's GitHub name inside URLs is the main one; the rest are the
# identifying strings the 2026-09-19 readiness audit found outside the excluded
# workflow layer.
ANON_RULES=(
  'Dengnifer :: ANONYMIZED'
  'LionSR :: ANONYMIZED-UPSTREAM'
  'Ruixuan Deng :: Anonymous Author'
  'ruixuan\.deng@icloud\.com :: anonymous@example.invalid'
  'sirui-lu\.com :: anonymized-upstream.example.invalid'
)

SOURCE_REPO='Dengnifer/MIPStarRE-A'

# --------------------------------------------------------------------------

PROG=${0##*/}
die() { printf '%s: %s\n' "$PROG" "$*" >&2; exit 1; }
log() { printf '[%s] %s\n' "$PROG" "$*" >&2; }

usage() {
  cat <<'USAGE'
Usage: scripts/make_artifact.sh [options] <git-ref> <out-dir>

Cut the ITP artifact snapshot of the mathematical development from <git-ref>
and write a gzipped tarball plus its MANIFEST into <out-dir>.

Options:
  --anonymize   also rewrite the author-identifying strings listed in the
                script (for a double-blind venue); tags the tarball "-anon".
  --keep-tree   leave the unpacked snapshot beside the tarball for inspection.
  --no-pdf      skip the gap-note PDF build even when its Makefile is present.
  -h, --help    this text.

Exit status: 0 packaged, 1 usage or environment error, 2 leak scan failed.
See docs/ARTIFACT.md for what ships, what does not, and why.
USAGE
}

ANONYMIZE=0
KEEP_TREE=0
BUILD_PDF=1
ARGS=()
while [ $# -gt 0 ]; do
  case "$1" in
    --anonymize) ANONYMIZE=1 ;;
    --keep-tree) KEEP_TREE=1 ;;
    --no-pdf)    BUILD_PDF=0 ;;
    -h|--help)   usage; exit 0 ;;
    --) shift; ARGS+=("$@"); break ;;
    -*) die "unknown option $1 (try --help)" ;;
    *)  ARGS+=("$1") ;;
  esac
  shift
done
[ "${#ARGS[@]}" -eq 2 ] || { usage >&2; die "expected <git-ref> and <out-dir>"; }
REF=${ARGS[0]}
OUT_DIR=${ARGS[1]}

SCRIPT_DIR=$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)
REPO_ROOT=${MIPSTARRE_REPO_ROOT:-$(git -C "$SCRIPT_DIR" rev-parse --show-toplevel)}
git -C "$REPO_ROOT" rev-parse --git-dir >/dev/null 2>&1 || die "not a git repository: $REPO_ROOT"

COMMIT=$(git -C "$REPO_ROOT" rev-parse --verify "${REF}^{commit}" 2>/dev/null) \
  || die "cannot resolve git ref: $REF"
SHORT=$(git -C "$REPO_ROOT" rev-parse --short=12 "$COMMIT")

NAME="mipstarre-qpbt-artifact-$SHORT"
[ "$ANONYMIZE" -eq 1 ] && NAME="$NAME-anon"

mkdir -p "$OUT_DIR"
OUT_DIR=$(cd "$OUT_DIR" && pwd)
WORK=$(mktemp -d "${TMPDIR:-/tmp}/make-artifact.XXXXXXXX")
trap 'rm -rf "$WORK"' EXIT
SNAP="$WORK/$NAME"
mkdir -p "$SNAP"

# ---- 1. extract -----------------------------------------------------------

PATHSPECS=()
for path in "${INCLUDE[@]}"; do
  if git -C "$REPO_ROOT" cat-file -e "$COMMIT:$path" 2>/dev/null; then
    PATHSPECS+=("$path")
  else
    log "skipping absent path: $path"
  fi
done
[ "${#PATHSPECS[@]}" -gt 0 ] || die "none of the included paths exist at $SHORT"

log "extracting $SHORT into the snapshot"
git -C "$REPO_ROOT" archive --format=tar "$COMMIT" -- "${PATHSPECS[@]}" "${EXCLUDE[@]}" \
  | tar -x -C "$SNAP"
[ -n "$(find "$SNAP" -type f -print -quit)" ] || die "the snapshot is empty"

# ---- 2. gap-note PDFs (optional; another packet adds the Makefile) --------

GAP_PDF="skipped: --no-pdf"
if [ "$BUILD_PDF" -eq 1 ] && [ -f "$SNAP/docs/paper-gaps/Makefile" ]; then
  log "building the gap-note PDFs"
  if make -C "$SNAP/docs/paper-gaps" >"$WORK/gap-make.log" 2>&1; then
    GAP_PDF="built $(find "$SNAP/docs/paper-gaps" -name '*.pdf' | wc -l | tr -d ' ') PDF(s)"
  else
    GAP_PDF="build FAILED; the TeX sources ship unbuilt"
    log "$GAP_PDF"
    tail -n 20 "$WORK/gap-make.log" >&2 || true
  fi
elif [ "$BUILD_PDF" -eq 1 ]; then
  GAP_PDF="skipped: docs/paper-gaps/Makefile is not in this revision"
  log "$GAP_PDF"
fi

# ---- 3. anonymize ---------------------------------------------------------

# One pass over the tree; every later step reads this list instead of walking
# the snapshot again.
TEXT_LIST="$WORK/text-files"
find "$SNAP" -type f -print0 | while IFS= read -r -d '' file; do
  if LC_ALL=C grep -qI . "$file" 2>/dev/null; then printf '%s\0' "$file"; fi
done > "$TEXT_LIST"

if [ "$ANONYMIZE" -eq 1 ]; then
  log "anonymizing (${#ANON_RULES[@]} rules)"
  SED_ARGS=()
  for rule in "${ANON_RULES[@]}"; do
    SED_ARGS+=(-e "s#${rule%% :: *}#${rule#* :: }#g")
  done
  xargs -0 -r sed -i "${SED_ARGS[@]}" < "$TEXT_LIST"
  SOURCE_REPO=$(printf '%s' "$SOURCE_REPO" | sed "${SED_ARGS[@]}")
fi

# ---- 4. measurements ------------------------------------------------------

# Lean *code* lines: blank lines and lines lying wholly inside a line, block,
# doc or module-doc comment do not count.  The rule is the one behind the
# merge-title Lean delta; it is copied here — deliberately, so that the
# snapshot tool does not depend on the excluded workflow layer — from
# local/bin/pr_merge.py:lean_code_line_mask, by way of
# results/telemetry/owner-tools/lean-loc.py (issues #574 and #168).
LEAN_STATS=$(find "$SNAP/MIPStarRE" "$SNAP/MIPStarRE.lean" -name '*.lean' -print0 2>/dev/null \
  | python3 -c '
import sys
files = code = total = 0
for name in sys.stdin.buffer.read().split(b"\0"):
    if not name:
        continue
    lines = open(name, encoding="utf-8").read().split("\n")
    if lines and lines[-1] == "":
        lines.pop()
    depth, in_string, escaped = 0, False, False
    files += 1
    for line in lines:
        is_code, i = False, 0
        while i < len(line):
            ch, pair = line[i], line[i:i + 2]
            if depth:
                if pair == "/-":
                    depth += 1
                elif pair == "-/":
                    depth -= 1
                else:
                    i += 1
                    continue
                i += 2
            elif in_string:
                if escaped:
                    escaped = False
                elif ch == "\\":
                    escaped = True
                elif ch == "\"":
                    in_string = False
                i += 1
            elif pair == "--":
                break
            elif pair == "/-":
                depth += 1
                i += 2
            else:
                is_code = is_code or not ch.isspace()
                in_string = ch == "\""
                i += 1
        code += is_code
        total += 1
print(files, code, total)
') || LEAN_STATS="0 0 0"
read -r LEAN_FILES LEAN_CODE LEAN_TOTAL <<< "$LEAN_STATS"

TOOLCHAIN=$(tr -d '\r' < "$SNAP/lean-toolchain" 2>/dev/null | head -n 1) || TOOLCHAIN=unknown
MATHLIB_REV=$(python3 -c '
import json, sys
try:
    manifest = json.load(open(sys.argv[1], encoding="utf-8"))
except Exception:
    print("unknown"); raise SystemExit
for package in manifest.get("packages", []):
    if package.get("name") == "mathlib":
        print(package.get("rev") or "unknown"); break
else:
    print("unknown")
' "$SNAP/lake-manifest.json" 2>/dev/null) || MATHLIB_REV=unknown

# ---- 5. import self-containment ------------------------------------------

# Every `import MIPStarRE.…` in the snapshot must resolve to a file that is in
# the snapshot; imports of Mathlib and friends are supplied by lake.
MISSING_IMPORTS=$(grep -rhoE '^import +MIPStarRE[A-Za-z0-9_.]*' \
    "$SNAP/MIPStarRE" "$SNAP/MIPStarRE.lean" 2>/dev/null \
  | awk '{print $2}' | sort -u \
  | while read -r module; do
      rel=${module//.//}
      [ -f "$SNAP/$rel.lean" ] || printf '%s ' "$module"
    done)
if [ -n "$MISSING_IMPORTS" ]; then
  SELF_CONTAINED="NO — unresolved: $MISSING_IMPORTS"
else
  SELF_CONTAINED="yes — every MIPStarRE import resolves inside the snapshot"
fi

# ---- 6. MANIFEST ----------------------------------------------------------

FILE_COUNT=$(( $(find "$SNAP" -type f | wc -l | tr -d ' ') + 1 ))  # + this MANIFEST
MANIFEST="$SNAP/MANIFEST.txt"
{
  echo "MIPStarRE — QPBT formalization: artifact snapshot"
  echo
  echo "source repository : $SOURCE_REPO"
  echo "source ref        : $REF"
  echo "source commit     : $COMMIT"
  echo "snapshot built    : $(date -u +%FT%TZ)"
  echo "anonymized        : $([ "$ANONYMIZE" -eq 1 ] && echo yes || echo no)"
  echo
  echo "files             : $FILE_COUNT (including this MANIFEST)"
  echo "Lean files        : $LEAN_FILES (all of MIPStarRE/)"
  echo "Lean code lines   : $LEAN_CODE (of $LEAN_TOTAL physical lines)"
  echo "toolchain         : $TOOLCHAIN"
  echo "mathlib revision  : $MATHLIB_REV"
  echo "gap-note PDFs     : $GAP_PDF"
  echo "self-contained    : $SELF_CONTAINED"
  echo
  echo "Excluded from this snapshot, on purpose:"
  echo "  results/telemetry/, local/, .github/, .githooks/, audits/, home_page/,"
  echo "  docbuild/ and the workflow-only scripts and docs — the AI-workflow"
  echo "  layer that produced the development but is not part of it;"
  echo "  references/ — mirrors of five third-party papers whose redistribution"
  echo "  terms are unsettled.  Docstrings cite those papers by arXiv identifier;"
  echo "  the file:line locators in them refer to the mirror as it stood at the"
  echo "  source commit above, in the source repository."
  echo
  echo "See docs/ARTIFACT.md for what this contains and how to verify it."
} > "$MANIFEST"
printf '%s\0' "$MANIFEST" >> "$TEXT_LIST"

# ---- 7. leak scan ---------------------------------------------------------

log "leak scan over $FILE_COUNT files"
ALLOW_RE=""
for entry in "${LEAK_ALLOW[@]}"; do
  ALLOW_RE="${ALLOW_RE:+$ALLOW_RE|}${entry%% :: *}"
done

HITS="$WORK/leaks.txt"
: > "$HITS"
for pattern in "${LEAK_PATTERNS[@]}"; do
  xargs -0 -r grep -HnoE "$pattern" < "$TEXT_LIST" >> "$HITS" 2>/dev/null || true
done
if [ -n "$ALLOW_RE" ]; then
  grep -vE "$ALLOW_RE" "$HITS" > "$HITS.kept" || true
else
  cp "$HITS" "$HITS.kept"
fi
RAW=$(wc -l < "$HITS" | tr -d ' ')
KEPT=$(wc -l < "$HITS.kept" | tr -d ' ')
log "leak scan: $RAW raw hit(s), $(( RAW - KEPT )) allow-listed, $KEPT remaining"

if [ -s "$HITS.kept" ]; then
  echo "$PROG: LEAK SCAN FAILED — the snapshot was not packaged." >&2
  echo "$PROG: $KEPT hit(s); first 40, paths relative to the snapshot:" >&2
  sed "s|^$SNAP/||" "$HITS.kept" | head -n 40 >&2
  echo "$PROG: fix the source, or add a LEAK_ALLOW entry WITH a reason." >&2
  exit 2
fi
log "leak scan clean"

# ---- 8. package -----------------------------------------------------------

TARBALL="$OUT_DIR/$NAME.tar.gz"
tar -czf "$TARBALL" -C "$WORK" "$NAME"
cp "$MANIFEST" "$OUT_DIR/$NAME.MANIFEST.txt"
if [ "$KEEP_TREE" -eq 1 ]; then
  rm -rf "${OUT_DIR:?}/$NAME"
  cp -R "$SNAP" "$OUT_DIR/$NAME"
fi

if command -v sha256sum >/dev/null 2>&1; then
  SHA=$(sha256sum "$TARBALL" | awk '{print $1}')
else
  SHA=$(shasum -a 256 "$TARBALL" | awk '{print $1}')
fi

cat "$MANIFEST"
echo
echo "tarball : $TARBALL"
echo "size    : $(du -h "$TARBALL" | awk '{print $1}')"
echo "sha256  : $SHA"
