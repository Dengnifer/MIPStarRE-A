#!/usr/bin/env bash
# local/kit/extract.sh — turn a checkout of the ORIGIN project (Dengnifer/MIPStarRE-A, the QPBT formalization) into the
# paper-agnostic kit tree. One-time / refresh tool of the kit maintainer; a project made FROM the kit never runs it.
# What it does, in order: (1) removes everything that belongs to the origin paper or the origin run (the list below is also the
# answer to "what do I delete to reuse the origin repo for another paper"); (2) empties the append-only telemetry registries but
# keeps their paths (local/bin/telemetry.py appends to them from the first turn); (3) moves the origin's protocol ledger to
# docs/origin/ (history is evidence, not law) and starts a fresh one; (4) replaces the origin's repository slugs by OWNER/REPO and
# the Lean root token MIPStarRE by the placeholder PaperLib (the env prefix MIPSTARRE_ and the cache dir name mipstarre-dev are
# deliberately left alone: they never collide with the token and renaming them buys nothing); (5) writes the minimal Lean and
# blueprint stubs so every hook and check has something to scan.
# Usage: bash local/kit/extract.sh   (from the repository root, clean work tree, git available)
set -euo pipefail
cd "$(git rev-parse --show-toplevel)"
[ -z "$(git status --porcelain)" ] || { echo "work tree not clean"; exit 2; }
ORIGIN=$(git rev-parse HEAD)
rmq() { git rm -r -q --ignore-unmatch "$@"; }
# ---- (1) origin paper + origin run ---------------------------------------------------------------------------------------
rmq MIPStarRE MIPStarRE.lean                                   # Lean sources
rmq references audits blueprint/src/chapter blueprint/src/references.bib
rmq docs/reports docs/campaign docs/decisions docs/QPBT-theorem-index.md docs/ldt_paper_summary.md docs/compile-time-audit.md \
    docs/diagonal-line-refactor.md docs/proof_frontier_review.md docs/api_surface.md docs/stale_issue_audit.md \
    docs/blueprint-script-coverage.md docs/external-lemmas-pedagogy.md docs/proof-hints.md proof-guide-bridge-lemmas-sorry-elim.md
for f in $(git ls-files docs/paper-gaps | grep -E '/(issue-|qpbt[_-]|naimark-dilation|truncation-combinatorics)'); do rmq "$f"; done
rmq local/briefs local/deploy
rmq scripts/comparator/expected scripts/comparator/challenge_qpbt_header.lean scripts/comparator/challenge_qpbt_footer.lean
rmq results/axioms.json results/faithfulness.json home_page/index.md
for d in sessions native-audits native-reviews owner-messages owner-audits registry-archive ci-incidents reviews owner-handoffs \
         github-snapshot reconciliation; do rmq "results/telemetry/$d"; done
for f in $(git ls-files results/telemetry/model-comparison | grep -v '/compare\.py$'); do rmq "$f"; done      # compare.py is tooling
for f in $(git ls-files 'results/telemetry/*.md' | grep -v -E '/(README|events|design-decisions)\.md$'); do rmq "$f"; done
for f in chain2.sh chain2-v2.sh merge-service-space-cap5.py astra-poll.sh adjudication-46-template.md adjudication-142-template.md \
         launch_qpbt_main.sh relaunch_qpbt_noescalation.sh qpbt-watchdog.sh; do rmq "results/telemetry/owner-tools/$f"; done
rmq scripts/tests/test_merge_service_space_cap5.py
# ---- (2) registries: keep the path, drop the records ----------------------------------------------------------------------
for f in $(git ls-files 'results/telemetry/*.jsonl') local/registry/declaration-claims.jsonl; do : > "$f"; done
printf '# Incident and observation log\n\nOne dated bullet per incident: symptom -> diagnosis -> fix -> lesson. Raw feed for\n`local/protocols/EVOLUTION.md` (see `local/protocols/meta.md`). Append-only.\n' > results/telemetry/events.md
printf '# Design decisions\n\nShort chronological index of owner and operator choices that shaped the workflow; each row points to the\nlonger primary record (an `events.md` bullet, an issue, a PR). Append-only.\n\n| date | decision | record |\n|---|---|---|\n' > results/telemetry/design-decisions.md
# ---- (3) the origin ledger becomes precedent ---------------------------------------------------------------------------------
mkdir -p docs/origin
git mv local/protocols/EVOLUTION.md docs/origin/EVOLUTION-origin.md
git mv local/protocols/useful-queue.md docs/origin/useful-queue-origin.md 2>/dev/null || true
# ---- (4) slugs, then the Lean root token (docs/origin is history and is left untouched) -------------------------------------
files() { git ls-files -z | grep -z -v '^docs/origin/' | xargs -0 grep -I -l -e "$1" 2>/dev/null || true; }
for f in $(files 'Dengnifer/MIPStarRE-A'); do sed -i 's#Dengnifer/MIPStarRE-A#OWNER/REPO#g' "$f"; done
for f in $(files 'Dengnifer/QPBT-comparator'); do sed -i 's#Dengnifer/QPBT-comparator#OWNER/REPO-comparator#g' "$f"; done
# links to the ANCESTOR project (LionSR/MIPStarRE: cited precedent issues and PRs) must stay valid: shield them from the rename
for f in $(files 'MIPStarRE'); do
  sed -i -e 's#LionSR/MIPStarRE#LionSR/@@ANCESTOR@@#g' -e 's#sirui-lu\.com/MIPStarRE#sirui-lu.com/@@ANCESTOR@@#g' \
         -e 's/MIPStarRE/PaperLib/g' -e 's/@@ANCESTOR@@/MIPStarRE/g' "$f"
done
# ---- (5) stubs ---------------------------------------------------------------------------------------------------------------
mkdir -p PaperLib blueprint/src/chapter references
printf 'import PaperLib.Basic\n' > PaperLib.lean
printf 'import Mathlib\n\n/-!\n# PaperLib\n\nPlaceholder root of the formalization. `scripts/bootstrap_project.py` renames the library; the skeleton stage replaces\nthis file.\n-/\n\nnamespace PaperLib\n\n/-- Placeholder so that every declaration scanner has one declaration to see. -/\ntheorem placeholder : True := trivial\n\nend PaperLib\n' > PaperLib/Basic.lean
printf '%% One \\input per chapter, in reading order. Written by the blueprint stage (local/protocols/bootstrap.md).\n' > blueprint/src/content.tex
printf '%% Bibliography of the blueprint. The bootstrap adds the paper being formalized.\n' > blueprint/src/references.bib
printf '# references/\n\nOne directory per source paper: `<key>-paper/` holding the arXiv e-print source, split into per-section files by\n`scripts/split_reference_paper.py`, plus `SOURCE.md` (what was fetched, when, from where). Written by the bootstrap.\n' > references/README.md
mkdir -p local/kit; echo "$ORIGIN" > local/kit/ORIGIN_COMMIT
git add -A
echo "extracted from $ORIGIN: $(git ls-files | wc -l) tracked files remain"
