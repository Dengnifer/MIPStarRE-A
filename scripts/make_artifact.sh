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
# .github/, .githooks/, workflow-only scripts and docs).  Dropping it also
# removes every tracked file that mentions the build host's home path, without
# rewriting history.
#
# INCLUDED on purpose: the third-party paper sources under references/ (owner
# decision, 2026-09-19, following the companion LDT repository, which keeps its
# paper sources in the public repository).  They are what the Lean docstrings,
# the theorem index and the deviations page cite by `<file>.tex:<lines>`, so a
# snapshot without them cannot be checked against its sources.  They are
# third-party material kept for reference and are NOT covered by the Apache-2.0
# LICENSE that ships with the snapshot; the MANIFEST and docs/ARTIFACT.md say so.
#
# The script FAILS on a leak-scan hit.  That is the point: a snapshot that
# leaks a home path, a key-shaped string or an e-mail address is not shipped.
# The scan reads text, so any PDF in the snapshot has its text extracted with
# `pdftotext` first; if that is not possible the run stops rather than ship a
# binary nothing looked inside.  Generated PDFs are built after the
# anonymization pass, because `sed` cannot reach inside a finished PDF.

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
  references
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
EMAIL_LEAK_PATTERN='[A-Za-z0-9._%+-]+@[A-Za-z0-9.-]+\.[A-Za-z]{2,}'
LEAK_PATTERNS=(
  '/home/[A-Za-z0-9._-]+'
  '/Users/[A-Za-z0-9._-]+'
  '\bsk-[A-Za-z0-9_-]{16,}'
  '\bghp_[A-Za-z0-9]{20,}'
  '\bgithub_pat_[A-Za-z0-9_]{20,}'
  '\bAKIA[0-9A-Z]{16}\b'
  '-----BEGIN [A-Z ]*PRIVATE KEY-----'
  "$EMAIL_LEAK_PATTERN"
)

# `<regex> :: <reason>`: a hit is forgiven anywhere in the snapshot when the
# TEXT THAT MATCHED a leak pattern also matches this regex, and the reason says
# why that is safe.  `::` separates the two because a regex may well contain
# `|`.  Keep the list short and the reasons honest — every entry is something a
# reviewer may read in the shipped files.
LEAK_ALLOW=(
  '@example\.(com|org|invalid) :: documentation placeholder domain reserved by RFC 2606'
)

# `<path regex> :: <text regex> :: <reason>`: the same, but forgiven ONLY in the
# files whose snapshot-relative path matches.  Scoping is the whole point — a
# blanket entry for the paper-source case below would stop the scan catching a
# real address of ours anywhere in the development, which is exactly what it is
# for.
LEAK_ALLOW_IN=(
  '^references/ :: [A-Za-z0-9._%+-]+@[A-Za-z0-9.-]+\.[A-Za-z]{2,} :: '\
'corresponding-author addresses printed in the source papers themselves; third-party material '\
'reproduced as published, not a contact address of this development'
)

# --------------------------------------------------------------------------
# Anonymization (--anonymize only)
# --------------------------------------------------------------------------

# `<literal text> :: <replacement>`, applied to every text file in the snapshot.
# The repository owner's GitHub name inside URLs is the main one; the rest are
# the identifying strings the 2026-09-19 readiness audit found outside the
# excluded workflow layer.
#
# LITERAL, not a regex, and that is load-bearing: this script itself ships in
# the snapshot, so the pass runs over this very block, and a rule written in
# pre-escaped regex form would not match its own spelling here — the string it
# exists to remove would ride out in the rules list.  Stored plainly, each rule
# rewrites its own entry too.  The escaping for `sed` happens at the point of
# use, and step 4b fails the run if any of these strings survives.
ANON_RULES=(
  'Dengnifer :: ANONYMIZED'
  'LionSR :: ANONYMIZED-UPSTREAM'
  'Ruixuan Deng :: Anonymous Author'
  'ruixuan.deng@icloud.com :: anonymous@example.invalid'
  'sirui-lu.com :: anonymized-upstream.example.invalid'
)

SOURCE_REPO='Dengnifer/MIPStarRE-A'

# --------------------------------------------------------------------------

PROG=${0##*/}
die() { printf '%s: %s\n' "$PROG" "$*" >&2; exit 1; }
log() { printf '[%s] %s\n' "$PROG" "$*" >&2; }

# The authored snapshot must ship the one contact address that is the literal
# source of an anonymization rule. Derive it instead of spelling an escaped copy
# elsewhere in this script: an escaped copy would survive `sed`, while a generic
# script-wide e-mail exception would forgive unrelated addresses. Fail closed if
# the rules ever contain zero or multiple e-mail-valued source fields.
ANON_CONTACT=''
ANON_CONTACT_COUNT=0
for rule in "${ANON_RULES[@]}"; do
  literal=${rule%% :: *}
  if printf '%s\n' "$literal" | grep -qxE "$EMAIL_LEAK_PATTERN"; then
    ANON_CONTACT=$literal
    ANON_CONTACT_COUNT=$(( ANON_CONTACT_COUNT + 1 ))
  fi
done
[ "$ANON_CONTACT_COUNT" -eq 1 ] \
  || die "ANON_RULES must contain exactly one literal e-mail source field"

# Turn a literal ANON_RULES field into something `sed` reads as itself: the
# pattern side escapes the basic-regex metacharacters, the replacement side the
# two `sed` gives meaning to, and both escape `#`, the delimiter used below.
# The order inside the bracket expression is not free: `[` must not be followed
# by `.`, `=` or `:`, which would open a collating symbol instead.
sed_escape_pattern()     { printf '%s' "$1" | sed 's|[][*.^$\&#/]|\\&|g'; }
sed_escape_replacement() { printf '%s' "$1" | sed 's|[\&#]|\\&|g'; }

usage() {
  cat <<'USAGE'
Usage: scripts/make_artifact.sh [options] <git-ref> <out-dir>

Cut the ITP artifact snapshot of the mathematical development from <git-ref>
and write a gzipped tarball plus its MANIFEST into <out-dir>.

Options:
  --anonymize   also rewrite the author-identifying strings listed in the
                script (for a double-blind venue); tags the tarball "-anon".
                The run stops rather than package a snapshot in which one of
                those strings survived the rewrite.
  --keep-tree   leave the unpacked snapshot beside the tarball for inspection.
  --no-pdf      skip the gap-note PDF build even when its Makefile is present.
  -h, --help    this text.

Building the gap-note PDFs needs pdftotext (poppler-utils) as well, because a
PDF in the snapshot is scanned for leaks through its extracted text.

Exit status: 0 packaged, 1 usage or environment error, 2 the leak scan or the
anonymization check failed.
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

# ---- 2. anonymize ---------------------------------------------------------

# One pass over the tree; every later step reads this list instead of walking
# the snapshot again.  `grep -qI .` keeps the text files: both the anonymizer
# and the leak scan work on text, and step 4 adds the extracted text of any
# binary PDF to the same list.
TEXT_LIST="$WORK/text-files"
find "$SNAP" -type f -print0 | while IFS= read -r -d '' file; do
  if LC_ALL=C grep -qI . "$file" 2>/dev/null; then printf '%s\0' "$file"; fi
done > "$TEXT_LIST"

if [ "$ANONYMIZE" -eq 1 ]; then
  log "anonymizing (${#ANON_RULES[@]} rules)"
  SED_ARGS=()
  for rule in "${ANON_RULES[@]}"; do
    SED_ARGS+=(-e "s#$(sed_escape_pattern "${rule%% :: *}")#$(sed_escape_replacement "${rule#* :: }")#g")
  done
  xargs -0 -r sed -i "${SED_ARGS[@]}" < "$TEXT_LIST"
  SOURCE_REPO=$(printf '%s' "$SOURCE_REPO" | sed "${SED_ARGS[@]}")
fi

# ---- 3. gap-note PDFs (optional; another packet adds the Makefile) --------

# After the anonymization pass on purpose: these PDFs are typeset from TeX in
# the snapshot, so building them here means they are typeset from the rewritten
# TeX.  A PDF built before the pass would keep the identifying strings, which
# the pass cannot reach inside a finished PDF.

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
  # latexmk leaves its intermediates beside the PDFs in the same build
  # directory.  They are not part of the artifact, and two of the kinds it
  # writes -- `.fls` and `.fdb_latexmk` -- record the absolute path of the
  # directory the build ran in, so with TMPDIR under a home directory they
  # would carry a home path into the snapshot and the leak scan would refuse to
  # package a release.  Keep the PDFs, drop everything else it wrote.
  PRUNED=$(find "$SNAP/docs/paper-gaps" -type f ! -name '*.pdf' \
      ! -name '*.tex' ! -name '*.bib' ! -name '*.md' ! -name 'Makefile' \
      -print -delete 2>/dev/null | wc -l | tr -d ' ')
  find "$SNAP/docs/paper-gaps" -type d -empty -delete 2>/dev/null || true
  if [ "$PRUNED" -gt 0 ]; then
    GAP_PDF="$GAP_PDF; $PRUNED LaTeX build intermediate(s) pruned"
    log "pruned $PRUNED LaTeX build intermediate(s)"
  fi
elif [ "$BUILD_PDF" -eq 1 ]; then
  GAP_PDF="skipped: docs/paper-gaps/Makefile is not in this revision"
  log "$GAP_PDF"
fi

# ---- 4. PDF text, so the leak scan is not blind to the binaries -----------

# The leak scan reads the text-file list built in step 2, which by construction
# skips binaries; a PDF -- one built just above, or one tracked in git -- would
# otherwise ship without anything looking inside it.  Its text is extracted
# here and appended to the same list, under a path that maps back to the
# shipped file.  If it cannot be extracted the run stops: an unscanned binary
# is exactly what the header promises cannot ship.
PDF_TEXT_DIR="$WORK/pdf-text"
PDF_LIST="$WORK/pdfs"
find "$SNAP" -type f -name '*.pdf' > "$PDF_LIST"
PDF_COUNT=$(wc -l < "$PDF_LIST" | tr -d ' ')
PDF_SCAN="none in the snapshot"
if [ "$PDF_COUNT" -gt 0 ]; then
  command -v pdftotext >/dev/null 2>&1 || die \
    "$PDF_COUNT PDF(s) in the snapshot but pdftotext (poppler-utils) is not installed; the leak scan cannot read them"
  while IFS= read -r pdf; do
    rel=${pdf#"$SNAP"/}
    out="$PDF_TEXT_DIR/$rel.txt"
    mkdir -p "$(dirname "$out")"
    pdftotext -q "$pdf" "$out" 2>/dev/null \
      || die "cannot extract the text of $rel for the leak scan"
    printf '%s\0' "$out" >> "$TEXT_LIST"
  done < "$PDF_LIST"
  PDF_SCAN="$PDF_COUNT PDF(s), text extracted with pdftotext and scanned"
  log "$PDF_SCAN"
fi

# ---- 4b. the anonymization took, and is not taken on trust ----------------

# `--anonymize` promises the reader of docs/ARTIFACT.md that the strings in
# ANON_RULES are gone; nothing but this check makes the promise good, and a
# silent miss is worse than no flag at all, because a submitter would ship on
# it.  Every rule's literal text and its sed-regex-escaped spelling are looked
# for as FIXED strings in everything the leak scan will read: the text files as
# the pass left them, and the extracted text of every shipped PDF, which `sed`
# cannot reach at all.  Checking the escaped spelling is load-bearing: that was
# how the address survived in an earlier shipped allow-list entry.  The leak
# patterns above would not catch these on their own — three of the five are
# names, not address- or key-shaped.  A survivor stops the run, like a leak.
if [ "$ANONYMIZE" -eq 1 ]; then
  ANON_LEFT="$WORK/anon-left.txt"
  : > "$ANON_LEFT"
  for rule in "${ANON_RULES[@]}"; do
    literal=${rule%% :: *}
    escaped=$(sed_escape_pattern "$literal")
    xargs -0 -r grep -HnF -e "$literal" < "$TEXT_LIST" >> "$ANON_LEFT" 2>/dev/null || true
    if [ "$escaped" != "$literal" ]; then
      xargs -0 -r grep -HnF -e "$escaped" < "$TEXT_LIST" >> "$ANON_LEFT" 2>/dev/null || true
    fi
  done
  if [ -s "$ANON_LEFT" ]; then
    # Same path mapping as the leak-scan report: snapshot-relative, and a PDF's
    # extracted text named as the PDF that would have shipped.
    sed -i -e "s|^$PDF_TEXT_DIR/\(.*\)\.txt:|\1 (text extracted from the PDF):|" \
           -e "s|^$SNAP/||" "$ANON_LEFT"
    echo "$PROG: ANONYMIZATION INCOMPLETE — the snapshot was not packaged." >&2
    echo "$PROG: $(wc -l < "$ANON_LEFT" | tr -d ' ') surviving occurrence(s); first 40:" >&2
    head -n 40 "$ANON_LEFT" >&2
    echo "$PROG: a binary is the usual cause — rebuild it from the rewritten source, or drop it." >&2
    exit 2
  fi
  log "anonymization check: no rule text survives in the snapshot"
fi

# ---- 5. measurements ------------------------------------------------------

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

# ---- 6. import self-containment ------------------------------------------

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

# ---- 7. internal Markdown links -------------------------------------------

# A page that ships must not point at a page that does not.  The `docs/`
# carve-out is what makes this possible: a shipped page may link a workflow-only
# page the allow-list drops.  This is a report, not a gate -- a link may
# legitimately be waiting for a page another packet adds -- but it is recorded
# in the MANIFEST so that nobody has to discover it by clicking.
DEAD_LINKS=$(python3 - "$SNAP" <<'PY' || echo "check failed"
import os, re, sys

root = sys.argv[1]
link = re.compile(r"\[[^\]]*\]\(([^)\s]+)")
dead = total = 0
report = []
for base, _dirs, names in os.walk(root):
    for name in names:
        if not name.endswith(".md"):
            continue
        path = os.path.join(base, name)
        try:
            text = open(path, encoding="utf-8", errors="replace").read()
        except OSError:
            continue
        for match in link.finditer(text):
            target = match.group(1).split("#")[0].strip()
            if not target or "://" in target or target.startswith("mailto:"):
                continue
            total += 1
            if not os.path.exists(os.path.normpath(os.path.join(base, target))):
                dead += 1
                report.append("%s -> %s" % (os.path.relpath(path, root), target))
print("%d dead of %d checked" % (dead, total))
for line in sorted(set(report)):
    print("  dead link: " + line, file=sys.stderr)
PY
)
log "internal Markdown links: $DEAD_LINKS"

# ---- 7b. paper locators ---------------------------------------------------

# Now that the paper sources ship, a docstring's `references/<paper>/<file>.tex`
# locator is a path a reviewer can open in the snapshot — so a locator naming a
# file that is not there is worth saying out loud.  A report, not a gate: the
# locator may name a section the mirror splits differently, and a packaging
# script is the wrong place to decide that.  The MANIFEST carries the count so
# that it cannot rot unnoticed.
# The mirrors' file names are lower case throughout, so a locator whose file
# component carries a capital is a fill-in placeholder rather than a citation --
# `references/ldt-paper/FILE.tex` in the gap-note template and the row for it in
# the gap-note README.  Those are dropped here instead of being reported as
# absent every time.
LOC_LIST="$WORK/paper-locators"
grep -rhoE 'references/[A-Za-z0-9_-]+/[A-Za-z0-9_.-]+\.tex' \
    "$SNAP/MIPStarRE" "$SNAP/blueprint/src" "$SNAP/docs" 2>/dev/null \
  | grep -vE '/[A-Za-z0-9_.-]*[A-Z][A-Za-z0-9_.-]*\.tex$' \
  | sort -u > "$LOC_LIST" || true
LOC_TOTAL=$(wc -l < "$LOC_LIST" | tr -d ' ')
LOC_DEAD_LIST=$(while read -r locator; do
    [ -f "$SNAP/$locator" ] || printf '%s ' "$locator"
  done < "$LOC_LIST")
LOC_DEAD=$(printf '%s' "$LOC_DEAD_LIST" | wc -w | tr -d ' ')
if [ "$LOC_DEAD" -gt 0 ]; then
  PAPER_LOCATORS="$LOC_DEAD of $LOC_TOTAL cited files absent: $LOC_DEAD_LIST"
else
  PAPER_LOCATORS="all $LOC_TOTAL cited files are in the snapshot"
fi
log "paper locators: $PAPER_LOCATORS"

# ---- 8. MANIFEST ----------------------------------------------------------

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
  echo "pdf leak scan     : $PDF_SCAN"
  echo "internal links    : $DEAD_LINKS"
  echo "paper locators    : $PAPER_LOCATORS"
  echo "self-contained    : $SELF_CONTAINED"
  echo
  echo "Excluded from this snapshot, on purpose:"
  echo "  results/telemetry/, local/, .github/, .githooks/, audits/, home_page/,"
  echo "  docbuild/ and the workflow-only scripts and docs — the AI-workflow"
  echo "  layer that produced the development but is not part of it."
  echo
  echo "Third-party material included, on purpose:"
  echo "  references/ — the TeX sources of the five source papers.  The Lean"
  echo "  docstrings, the theorem index and the deviations page cite them as"
  echo "  references/<paper>/<file>.tex:<lines>.  Most resolve inside this snapshot;"
  echo "  the paper-locator report above names any exceptions.  These files are kept"
  echo "  here for reference; they are NOT covered by the Apache-2.0 LICENSE"
  echo "  that ships with this snapshot, and their own terms govern any further"
  echo "  use or redistribution."
  echo
  echo "See docs/ARTIFACT.md for what this contains and how to verify it."
} > "$MANIFEST"
printf '%s\0' "$MANIFEST" >> "$TEXT_LIST"

# ---- 9. leak scan ---------------------------------------------------------

log "leak scan over $FILE_COUNT files"

RAW_HITS="$WORK/leaks-raw.txt"
: > "$RAW_HITS"
for pattern in "${LEAK_PATTERNS[@]}"; do
  xargs -0 -r grep -HnoE "$pattern" < "$TEXT_LIST" >> "$RAW_HITS" 2>/dev/null || true
done

# `<path>:<line>:<matched text>`, with the path made snapshot-relative and the
# extracted text of a PDF mapped back to the PDF that ships — BEFORE any
# filtering, because both allow-lists are written against the shipped paths,
# and so is the failure report below.
HITS="$WORK/leaks.txt"
sed -e "s|^$PDF_TEXT_DIR/\(.*\)\.txt:|\1 (text extracted from the PDF):|" \
    -e "s|^$SNAP/||" "$RAW_HITS" > "$HITS"

# Drop the forgiven hits.  Both lists are matched against the text that matched
# a leak pattern, never against the path, so a file whose *name* contains an
# allow-listed string cannot launder a real hit; LEAK_ALLOW_IN additionally
# requires the file to be one of the paths named with it.
KEPT_HITS="$WORK/leaks-kept.txt"
cp "$HITS" "$KEPT_HITS"
drop_forgiven() {
  grep -vE "$1" "$KEPT_HITS" > "$KEPT_HITS.next" 2>/dev/null || true
  mv "$KEPT_HITS.next" "$KEPT_HITS"
}
drop_exact_finding() {
  awk -F: -v path="$1" -v text="$2" \
    'NF == 3 && $1 == path && $2 ~ /^[0-9]+$/ && $3 == text { next } { print }' \
    "$KEPT_HITS" > "$KEPT_HITS.next"
  mv "$KEPT_HITS.next" "$KEPT_HITS"
}
for entry in "${LEAK_ALLOW[@]}"; do
  drop_forgiven ":[0-9]+:.*(${entry%% :: *})"
done
for entry in "${LEAK_ALLOW_IN[@]}"; do
  rest=${entry#* :: }
  drop_forgiven "(${entry%% :: *})[^:]*:[0-9]+:.*(${rest%% :: *})"
done

# `grep -o` emits one scanner finding per matched address. Forgive only the
# exact contact text derived from ANON_RULES in the shipped script; if the same
# source line also contains another address, its separate finding remains.
drop_exact_finding 'scripts/make_artifact.sh' "$ANON_CONTACT"

RAW=$(wc -l < "$HITS" | tr -d ' ')
KEPT=$(wc -l < "$KEPT_HITS" | tr -d ' ')
log "leak scan: $RAW raw hit(s), $(( RAW - KEPT )) allow-listed, $KEPT remaining"

if [ -s "$KEPT_HITS" ]; then
  echo "$PROG: LEAK SCAN FAILED — the snapshot was not packaged." >&2
  echo "$PROG: $KEPT hit(s); first 40, paths relative to the snapshot:" >&2
  head -n 40 "$KEPT_HITS" >&2
  echo "$PROG: fix the source, or add a LEAK_ALLOW/LEAK_ALLOW_IN entry WITH a reason." >&2
  exit 2
fi
log "leak scan clean"

# ---- 10. package ----------------------------------------------------------

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
