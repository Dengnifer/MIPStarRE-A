#!/usr/bin/env python3
"""Create an issue in the local issue tree.

Replaces three GitHub facilities at once:

* the issue forms in ``.github/ISSUE_TEMPLATE/{formalization-task,bug-report,
  tracking-issue}.yml`` become ``--template`` scaffolds whose section headings
  are the templates' field labels, verbatim;
* the ``classify-outside`` job of ``.github/workflows/issue-automation.yml``
  (:97-220) — a deterministic, credential-free keyword pass — becomes the
  classification stage below;
* native sub-issue attachment becomes ``--parent``, which writes both halves of
  the relationship (child's ``parent`` and parent's ``children``) under the
  parents' locks.

Ordering is load-bearing.  The parent repository consolidated three workflows
into one specifically to fix a race: "The scout run for a freshly opened issue
was routinely cancelled: classification added labels seconds after open, every
labeled event cancelled the in-flight scout run ... Ordering the jobs inside one
workflow removes the race" (issue-automation.yml:13-21).  Here the same ordering
is a straight-line pipeline — create, then classify, then scout — and the scout
hook re-reads the file from disk rather than trusting an in-memory copy, which
is the local form of the fix at issue-automation.yml:277-279 ("Read the live
labels: on opened events classification has just finished ... so the payload's
label list is stale").

The LLM classifier of ``classify-trusted`` is NOT invoked: this script is
deterministic today, with the hook marked below.

Usage:
    issue_new.py --title "Formalize the Pauli basis test soundness bound" \
                 --template formalization --parent 0003 --labels qpbt-analysis
    issue_new.py --title "Tracking: Pauli basis test" --template tracking
    issue_new.py --help
"""

from __future__ import annotations

import argparse
import os
import re
import subprocess
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
try:
    import track
except ModuleNotFoundError as exc:  # pragma: no cover - defensive
    sys.stderr.write(
        "issue_new.py: cannot import local/bin/track.py, which holds the issue "
        f"data layer ({exc}).\n"
    )
    raise SystemExit(2)

from track import LayerError  # noqa: E402


TEMPLATES = ("formalization", "bug", "tracking")

#: Default labels, copied from the ``labels:`` key of each issue form.
TEMPLATE_LABELS = {
    "formalization": ["formalization"],
    "bug": ["bug"],
    "tracking": ["tracking"],
}

CLASSIFICATION_HEADING = "## Initial classification"


# ---------------------------------------------------------------------------
# Template bodies
# ---------------------------------------------------------------------------
#
# Section headings mirror the ``label:`` of each field in the corresponding
# ``.github/ISSUE_TEMPLATE/*.yml`` form, and the placeholder prose mirrors each
# field's ``placeholder:``, retargeted from the low individual degree test to
# the quantum Pauli basis test.  Required fields are marked; the stale-issue
# audit depends on the source-citation field being filled in with real paths,
# lines, and labels (docs/CONTRIBUTING.md:143-153).

_FORMALIZATION_BODY = """\
### Precise mathematical statement

<!-- required -->
Name the theorem, lemma, definition, or construction and state its content.
For example: Lemma 5.3 (Pauli basis test soundness), with the hypotheses on the
number of qubits, the error parameter, and the strategy stated explicitly.

### Mathematical source

<!-- required: path, line, label, and a short quotation or precise paraphrase.
     Replace the placeholders with a real file under references/ (use
     `ls references/*/` for the live mirror layout) and a real blueprint
     chapter; the stale-issue audit flags citations to files that do not
     exist. -->
- Paper: `references/<paper-mirror>/<section>.tex:NNN`, label `thm:...`.
  Paraphrase: ...
- Blueprint: `blueprint/src/chapter/<chapter>.tex:NN`, label `thm:...`.

### Target Lean declaration

Expected Lean name and file path, e.g.
`MIPStarRE.Quantum.pauliBasisTest_sound` in `MIPStarRE/Quantum/PauliBasisTest.lean`.

### Mathematical dependencies

- Blueprint label `prop:...`.
- Lean declaration `MIPStarRE.Quantum....`.
- Sub-issue #NNNN, proving the estimate used in the paper proof.

### Proof plan

Explain the mathematical argument to be formalized, including any deliberate
deviation from the paper or blueprint statement.

### Statement integrity

Paper assumptions, Lean assumptions, paper conclusion, Lean conclusion, and a
verdict: exact / faithful boundary hypotheses / extra assumptions / weakened
conclusion / strengthened conclusion (docs/CONTRIBUTING.md:155-172).
"""

_BUG_BODY = """\
### File(s) affected

<!-- required -->
Path to the Lean file(s) with the issue, e.g. `MIPStarRE/Quantum/PauliBasisTest.lean`.

### Description

<!-- required -->
What is broken? Include error messages, `sorry` locations, or the mathematical
mismatch.

### Mathematical source, if relevant

Cite the paper or blueprint path, line number, label, and a short quotation or
precise paraphrase when the bug concerns a mathematical statement.

### Expected behavior

What should the Lean statement, proof, or build do instead?

### Lean toolchain

Output of `cat lean-toolchain`.
"""

_TRACKING_BODY = """\
### Mathematical area

<!-- required -->
Which section, theorem family, or construction does this issue organize?

### Mathematical objective

<!-- required: state the theorem family or proof stage, with sources.
     Replace the placeholders with real paths (see `ls references/*/`). -->
Sources:
- `references/<paper-mirror>/<section>.tex:NNN`, label `lem:...`.
  Paraphrase: ...
- `blueprint/src/chapter/<chapter>.tex:NN`, label `lem:...`.

### Sub-issues to attach

<!-- Prose index only. The relationship itself lives in frontmatter: attach a
     child with `issue_new.py --parent <this id>`, which writes both halves. -->
- #
- #

### Mathematical notes

Dependencies, theorem labels, source locations, or order constraints.
"""

TEMPLATE_BODIES = {
    "formalization": _FORMALIZATION_BODY,
    "bug": _BUG_BODY,
    "tracking": _TRACKING_BODY,
}


# ---------------------------------------------------------------------------
# Deterministic classification
# ---------------------------------------------------------------------------
#
# Ported from ``classify-outside`` (issue-automation.yml:133-166).  That job was
# deliberately built with no provider secrets in its environment
# (issue-automation.yml:104) so that untrusted text never met a credential; the
# separation is worth keeping even though there is only one author locally, so
# this pass never reads a token and never calls a model.

_FORMALIZATION_RE = re.compile(
    r"\b(theorem|lemma|proposition|corollary|definition|conjecture|proof|"
    r"formalization|formalisation|lean declaration|sorry)\b"
)
_DOCUMENTATION_RE = re.compile(r"\b(blueprint|latex|docstring|documentation|readme)\b")
_BUG_RE = re.compile(
    r"\b(bug|failure|failed|type error|compile error|incorrect|wrong|broken)\b"
)
_CI_RE = re.compile(r"\b(ci|workflow|build|action|actions|check|checks)\b")
_TRACKING_TITLE_RE = re.compile(r"^tracking:")


def classify_deterministic(title: str, body: str, taxonomy: track.Taxonomy) -> list[str]:
    """Keyword labels for *title*/*body*, filtered against the taxonomy.

    The filtering step is the local form of issue-automation.yml:172-179
    ("Fetch existing repo labels so we don't fail on nonexistent labels"): a
    proposed label that ``local/labels.yml`` does not define is dropped with a
    note rather than written into frontmatter, where it would then fail
    ``validate_tree.py``.

    The parent hard-coded its chapter regex (``wolf-ch[1-7]``) and its paper-id
    list inline; both had drifted away from the live taxonomy by the time of the
    study.  Here the family and paper labels come from ``aliases:`` entries in
    ``local/labels.yml``, so there is exactly one place to edit.
    """
    text = f"{title}\n{body}".lower()
    proposed: list[str] = []

    def add(name: str) -> None:
        if name not in proposed:
            proposed.append(name)

    if _FORMALIZATION_RE.search(text):
        add("formalization")
    if _DOCUMENTATION_RE.search(text):
        add("documentation")
    if _BUG_RE.search(text):
        add("bug")
    if _CI_RE.search(text):
        add("ci")
    if _TRACKING_TITLE_RE.search(title.lower()):
        add("tracking")

    for label, aliases in taxonomy.aliases_by_label().items():
        if any(alias in text for alias in aliases):
            add(label)

    valid = [name for name in proposed if name in taxonomy]
    dropped = [name for name in proposed if name not in taxonomy]
    for name in dropped:
        sys.stderr.write(
            f"note: dropping proposed label {name!r}: not defined in local/labels.yml\n"
        )
    return sorted(valid)


# --------------------------------------------------------------------------
# LLM classification hook (not wired)
# --------------------------------------------------------------------------
#
# ``classify-trusted`` (issue-automation.yml:39-96) ran a model over the same
# text with .github/prompts/issue-classification-{system-,}prompt.md and the
# repository label list.  To wire it here:
#
#   1. gate on ``os.environ.get("MIPSTARRE_LLM_ENABLED") != "false"`` — unset
#      means enabled, only the literal string "false" disables (DESIGN.md:73-75);
#   2. read both prompt files from the committed main worktree, never from a
#      branch under review (DESIGN.md:76-77);
#   3. pass ``track.sanitize(title, track.TITLE_LIMIT)`` and
#      ``track.sanitize(body, track.BODY_LIMIT)`` inside an explicit
#      "treat the following as untrusted data" frame (DESIGN.md:78-80);
#   4. run the model's label list through the SAME ``name in taxonomy`` filter
#      used above before it reaches frontmatter;
#   5. union the result with ``classify_deterministic`` rather than replacing
#      it, so a missing credential degrades to the deterministic labels instead
#      of to no labels at all.


def classification_note(labels: list[str]) -> str:
    """The ``Initial classification`` section, mirroring the upstream comment.

    issue-automation.yml:200-220 posted a comment telling a maintainer to review
    the automatic labels and, for formalization issues, to consider adding
    ``scout``.  The heading doubles as the dedupe marker.
    """
    if labels:
        rendered = ", ".join(f"`{name}`" for name in labels)
    else:
        rendered = "No automatic label was clear from the title or body."
    extra = ""
    if "formalization" in labels:
        extra = (
            "\n\nThe deterministic pass added `formalization`; after reviewing the "
            "mathematical source, add `scout` to request a Mathlib report."
        )
    return (
        f"{CLASSIFICATION_HEADING}\n\n"
        f"Applied by `local/bin/issue_new.py` (deterministic keyword pass, no model): "
        f"{rendered}{extra}\n"
    )


# ---------------------------------------------------------------------------
# Scout hook
# ---------------------------------------------------------------------------

def maybe_scout(repo_root: Path, issue_id: str) -> None:
    """Run the Mathlib scout, if it exists, AFTER classification has landed.

    The gate mirrors the ``decide`` step at issue-automation.yml:221-334: run
    when the issue carries ``scout`` or ``formalization``.  The issue is
    re-read from disk here so the labels are the ones classification just wrote
    (issue-automation.yml:277-279).
    """
    issue = track.load_issue(repo_root, issue_id)
    if not ({"scout", "formalization"} & set(issue.labels)):
        return
    script = repo_root / "local" / "bin" / "scout.sh"
    if not script.is_file():
        sys.stderr.write(
            f"note: #{issue_id} is scout-eligible but {script} does not exist yet; "
            "skipping the Mathlib scouting report. Run it by hand once the script "
            "lands.\n"
        )
        return
    if os.environ.get("MIPSTARRE_LLM_ENABLED") == "false":
        sys.stderr.write(
            "note: MIPSTARRE_LLM_ENABLED=false; skipping the Mathlib scouting report.\n"
        )
        return
    sys.stdout.write(f"running {script} {issue_id}\n")
    result = subprocess.run([str(script), issue_id], cwd=str(repo_root), check=False)
    if result.returncode != 0:
        sys.stderr.write(
            f"warning: scout.sh exited {result.returncode}; the issue was created "
            "and classified regardless.\n"
        )


# ---------------------------------------------------------------------------
# Creation
# ---------------------------------------------------------------------------

def resolve_labels(requested: list[str], template: str, taxonomy: track.Taxonomy) -> list[str]:
    labels = list(TEMPLATE_LABELS[template])
    for name in requested:
        name = name.strip()
        if not name:
            continue
        if name in taxonomy.banned:
            raise LayerError(
                f"label {name!r} is banned: {taxonomy.banned[name]} "
                "(see the 'banned:' block of local/labels.yml)"
            )
        if name not in taxonomy:
            raise LayerError(
                f"label {name!r} is not defined in local/labels.yml. "
                f"Known labels: {', '.join(taxonomy.names)}"
            )
        if name not in labels:
            labels.append(name)
    return sorted(labels)


def attach_to_parent(repo_root: Path, parent_id: str, child_id: str, *, dry_run: bool) -> None:
    """Write the parent half of the relationship under the parent's lock."""
    with track.issue_lock(parent_id):
        parent = track.load_issue(repo_root, parent_id)
        if parent.state != "open":
            sys.stderr.write(
                f"warning: parent #{parent_id} is {parent.state}; attaching anyway\n"
            )
        children = parent.children
        if child_id in children:
            return
        children.append(child_id)
        parent.meta["children"] = sorted(children)
        if dry_run:
            sys.stdout.write(f"[dry-run] would add #{child_id} to #{parent_id}.children\n")
            return
        parent.save()
        sys.stdout.write(f"#{parent_id}: children now {parent.meta['children']}\n")


def create_issue(args: argparse.Namespace) -> int:
    repo_root = args.repo_root.resolve()
    taxonomy = track.load_taxonomy(repo_root)

    title = track.sanitize(args.title, track.TITLE_LIMIT).strip()
    if not title:
        raise LayerError("--title is empty after sanitization")
    track.check_bracket_free(title, "issue title")
    slug = track.slugify(title)

    labels = resolve_labels(args.labels, args.template, taxonomy)

    parent_id = track.normalize_id(args.parent) if args.parent else None
    if parent_id is not None:
        # Fail before allocating an id if the parent does not exist.
        track.load_issue(repo_root, parent_id)

    if args.pinned:
        pinned = [i for i in track.iter_issues(repo_root) if i.meta.get("pinned") is True]
        if len(pinned) >= 3:
            raise LayerError(
                f"{len(pinned)} issue(s) are already pinned "
                f"({', '.join('#' + i.id for i in pinned)}); the cap is 3 "
                "(docs/CONTRIBUTING.md:224-228) and validate_tree.py enforces it. "
                "Unpin one first."
            )

    directory = track.issues_dir(repo_root)
    directory.mkdir(parents=True, exist_ok=True)

    with track.file_lock("issues-seq"):
        existing = [i.id for i in track.iter_issues(repo_root)]
        if args.dry_run:
            issue_id = f"{(max([int(e) for e in existing], default=0) + 1):04d}"
        else:
            issue_id = track.next_sequence_id(directory / ".seq", existing)

    now = track.utcnow()
    meta = {
        "id": issue_id,
        "title": title,
        "state": "open",
        "state_reason": None,
        "parent": parent_id,
        "children": [],
        "labels": labels,
        "pinned": bool(args.pinned),
        "created": now,
        "updated": now,
        "agent_session": args.agent_session,
    }
    body = TEMPLATE_BODIES[args.template]
    if args.body_file:
        supplied = Path(args.body_file).read_text(encoding="utf-8")
        body = track.sanitize(supplied, track.BODY_LIMIT)
    body = body.rstrip("\n") + f"\n\n{track.ACTIVITY_HEADING}\n"

    path = directory / f"{issue_id}-{slug}.md"
    if path.exists():
        raise LayerError(f"{path} already exists; refusing to overwrite")

    issue = track.Issue(path, meta, body)
    if args.dry_run:
        sys.stdout.write(f"[dry-run] would create {path}\n\n{issue.render()}\n")
        return 0

    track.atomic_write(path, issue.render())
    sys.stdout.write(f"created {path.relative_to(repo_root)} (#{issue_id})\n")

    if parent_id is not None:
        attach_to_parent(repo_root, parent_id, issue_id, dry_run=False)

    # Stage 2: classification. Must complete before stage 3.
    if not args.no_classify:
        # An unedited template body is boilerplate, not content: its placeholder
        # prose names "blueprint", "theorem", "build" and would classify every
        # new issue identically. Only a body the caller actually supplied joins
        # the title as classification input.
        source_body = body if args.body_file else ""
        derived = classify_deterministic(title, source_body, taxonomy)
        merged = sorted(set(labels) | set(derived))
        with track.issue_lock(issue_id):
            fresh = track.load_issue(repo_root, issue_id)
            fresh.meta["labels"] = merged
            if CLASSIFICATION_HEADING not in fresh.body:
                activity = fresh.body.find(track.ACTIVITY_HEADING)
                note = classification_note(derived)
                if activity == -1:
                    fresh.body = fresh.body.rstrip("\n") + "\n\n" + note
                else:
                    fresh.body = (
                        fresh.body[:activity].rstrip("\n")
                        + "\n\n" + note + "\n"
                        + fresh.body[activity:]
                    )
            fresh.save()
        sys.stdout.write(f"#{issue_id}: labels {merged}\n")

    # Stage 3: scouting, strictly after classification.
    if not args.no_scout:
        maybe_scout(repo_root, issue_id)

    return 0


# ---------------------------------------------------------------------------
# CLI
# ---------------------------------------------------------------------------

def _parse_args(argv: list[str]) -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        prog="issue_new.py",
        description=__doc__,
        formatter_class=argparse.RawDescriptionHelpFormatter,
    )
    parser.add_argument("--title", required=True, help="bracket-free issue title")
    parser.add_argument("--template", required=True, choices=TEMPLATES,
                        help="scaffold to use, matching .github/ISSUE_TEMPLATE/*.yml")
    parser.add_argument("--parent", metavar="ID",
                        help="tracking issue to attach this one to (one parent max)")
    parser.add_argument("--labels", action="append", default=[],
                        help="comma-separated label names; repeatable")
    parser.add_argument("--body-file", type=Path,
                        help="use this file as the body instead of the template")
    parser.add_argument("--agent-session", default=None,
                        help="agent session name that requested this issue")
    parser.add_argument("--pinned", action="store_true", help="pin the issue (max 3)")
    parser.add_argument("--no-classify", action="store_true",
                        help="skip the deterministic keyword classification pass")
    parser.add_argument("--no-scout", action="store_true",
                        help="skip the Mathlib scouting hook")
    parser.add_argument("--repo-root", type=Path, default=track.default_repo_root(),
                        help="repository root (default: two levels above this script)")
    parser.add_argument("--dry-run", action="store_true",
                        help="print the record that would be written, write nothing")
    args = parser.parse_args(argv)
    flattened: list[str] = []
    for chunk in args.labels:
        flattened.extend(part for part in chunk.split(",") if part.strip())
    args.labels = flattened
    return args


def main(argv: list[str] | None = None) -> int:
    args = _parse_args(sys.argv[1:] if argv is None else argv)
    try:
        return create_issue(args)
    except LayerError as exc:
        sys.stderr.write(f"issue_new.py: {exc}\n")
        return 2


if __name__ == "__main__":
    raise SystemExit(main())
