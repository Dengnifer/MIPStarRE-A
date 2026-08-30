#!/usr/bin/env python3
"""Open a PR record in the local ``prs/`` registry.

Replaces "open a pull request on GitHub" plus the record-shaping half of
``.github/workflows/pr-cleanup.yml``, which used a model to rewrite bot PR
titles into ``type(scope): desc``, turn the body into a self-contained
mathematical note, copy labels from the linked issue, and add ``Addresses #N``.
The mechanical parts of that job — the body skeleton, the link footer, and the
label copy — are done here deterministically; the prose-rewriting part is left
as a hook (see ``NORMALIZATION HOOK`` below).

The branch-name lint is the load-bearing piece.  ``track.py`` recovers the
linked issue from a branch through the ``issue-(\\d+)`` regex ported from
issue-automation.yml:463-466, so a branch that does not embed its issue id is
invisible to every progress note downstream; and docs/CONTRIBUTING.md:122-124
records that ``]`` in a generated name broke part of the parent's automation
stack.  Both are rejected here rather than discovered at merge time.

Usage:
    pr_open.py --issue 0042 --branch issue-0042-pauli-soundness \
               --title "feat(Quantum): prove the Pauli basis test soundness bound"
    pr_open.py --issue 0042 --branch codex/issue-0042-pauli-soundness \
               --title "..." --closes
    pr_open.py --help
"""

from __future__ import annotations

import argparse
import re
import subprocess
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
try:
    import track
except ModuleNotFoundError as exc:  # pragma: no cover - defensive
    sys.stderr.write(
        "pr_open.py: cannot import local/bin/track.py, which holds the PR "
        f"data layer ({exc}).\n"
    )
    raise SystemExit(2)

from track import LayerError  # noqa: E402


#: DESIGN.md:106-107 — ``issue-<id>-<slug>`` for human/orchestrator branches,
#: ``codex/issue-<id>-<slug>`` for agent-created ones.  ``claude/`` is accepted
#: with a warning because branches imported from the parent workflow carry it
#: and ``track.skip_pr_opened_announcement`` still recognizes the prefix.
BRANCH_RE = re.compile(r"^(?:(codex|claude)/)?issue-(\d+)-([a-z0-9][a-z0-9-]*)$")

PR_BODY_TEMPLATE = """\
# {title}

### Motivation

<!-- Why this mathematical or documentation change is needed. Cite the issue
     and, when applicable, the paper/blueprint file, line, and label. -->

### Description

<!-- State precisely what changed: definitions introduced, lemmas/theorems
     proved, blueprint labels updated, and any deliberate difference from the
     paper statement. -->

### Testing

<!-- What was verified and how, e.g.
     lake env lean MIPStarRE/Quantum/PauliBasisTest.lean
     lake build MIPStarRE
     rg -n "sorry|axiom" MIPStarRE/Quantum/PauliBasisTest.lean || true -->

---
{footer}
"""


def lint_branch(branch: str, issue_id: str) -> None:
    """Reject a branch name that cannot carry its issue link safely."""
    if not branch:
        raise LayerError("--branch is required and must be non-empty")
    track.check_bracket_free(branch, "branch name", track.FORBIDDEN_REF_CHARS)
    if branch.endswith(".lock") or ".." in branch or branch.startswith("/") \
            or branch.endswith("/") or "@{" in branch:
        raise LayerError(
            f"branch {branch!r} is not a valid git refname "
            "(no '..', '@{', leading/trailing '/', or '.lock' suffix)"
        )
    match = BRANCH_RE.match(branch)
    if not match:
        raise LayerError(
            f"branch {branch!r} does not match the local convention "
            "'issue-<id>-<slug>' or 'codex/issue-<id>-<slug>' (DESIGN.md:106-107).\n"
            "The embedded id is what track.py's issue-(\\d+) regex reads to attach "
            "progress notes; a branch without it drops out of every tracking count."
        )
    prefix, embedded, _slug = match.groups()
    if prefix == "claude":
        sys.stderr.write(
            "warning: 'claude/' is a parent-workflow prefix; new agent branches "
            "should use 'codex/' (DESIGN.md:106-107).\n"
        )
    if track.normalize_id(embedded) != issue_id:
        raise LayerError(
            f"branch {branch!r} embeds issue {track.normalize_id(embedded)} but "
            f"--issue says {issue_id}; the two must agree or the merge-time "
            "progress notes land on the wrong issue"
        )


def git(repo_root: Path, *args: str) -> str | None:
    """Run a read-only git command; return stripped stdout, or None on failure."""
    try:
        result = subprocess.run(
            ["git", *args], cwd=str(repo_root),
            capture_output=True, text=True, check=False,
        )
    except FileNotFoundError:
        sys.stderr.write("warning: git is not on PATH; skipping branch resolution\n")
        return None
    if result.returncode != 0:
        return None
    return result.stdout.strip() or None


def build_footer(issue_id: str, closes: bool) -> str:
    """``Closes #N`` auto-closes on merge; ``Addresses #N`` keeps it open.

    docs/CONTRIBUTING.md:61-62.  ``pr_merge.py`` reads this footer through
    ``track.linked_issues``, so the exact keyword decides whether the issue is
    closed by the merge or merely receives a progress note.
    """
    return f"{'Closes' if closes else 'Addresses'} #{issue_id}"


# --------------------------------------------------------------------------
# NORMALIZATION HOOK (not wired)
# --------------------------------------------------------------------------
#
# pr-cleanup.yml ran a model over ``claude/``/``codex/`` PRs to rewrite the
# title into conventional-commit form and expand the body into a self-contained
# mathematical note.  To wire it here:
#
#   1. gate on ``os.environ.get("MIPSTARRE_LLM_ENABLED") != "false"`` and on
#      ``BRANCH_RE`` reporting a ``codex``/``claude`` prefix, matching the
#      upstream ``startsWith`` gate at pr-cleanup.yml:17-21;
#   2. read .github/prompts/pr-cleanup-prompt.md from the committed main
#      worktree, never from the branch being described (DESIGN.md:76-77);
#   3. pass the diff and the current body through ``track.sanitize`` — the
#      upstream job sanitized before interpolation for the same reason;
#   4. rewrite only the ``### Motivation``/``### Description`` sections and the
#      title in the record; never touch the footer, which is machine-read.


def create_pr(args: argparse.Namespace) -> int:
    repo_root = args.repo_root.resolve()
    issue_id = track.normalize_id(args.issue)
    issue = track.load_issue(repo_root, issue_id)
    if issue.state != "open":
        sys.stderr.write(
            f"warning: issue #{issue_id} is {issue.state}; opening a PR against a "
            "closed issue is unusual\n"
        )

    lint_branch(args.branch, issue_id)

    title = track.sanitize(args.title, track.TITLE_LIMIT).strip()
    if not title:
        raise LayerError("--title is empty after sanitization")
    track.check_bracket_free(title, "PR title")
    slug = track.slugify(title)

    taxonomy = track.load_taxonomy(repo_root)
    labels = sorted({name for name in issue.labels if name in taxonomy})
    for chunk in args.labels:
        for name in (part.strip() for part in chunk.split(",")):
            if not name:
                continue
            if name in taxonomy.banned:
                raise LayerError(f"label {name!r} is banned: {taxonomy.banned[name]}")
            if name not in taxonomy:
                raise LayerError(f"label {name!r} is not defined in local/labels.yml")
            if name not in labels:
                labels.append(name)
    labels = sorted(labels)

    head_sha = git(repo_root, "rev-parse", "--verify", f"{args.branch}^{{commit}}")
    if head_sha is None:
        sys.stderr.write(
            f"warning: branch {args.branch!r} does not resolve in this repository; "
            "head_sha stays null and pr_merge.py will refuse until ci.sh records "
            "one.\n"
        )

    directory = track.prs_dir(repo_root)
    directory.mkdir(parents=True, exist_ok=True)

    with track.file_lock("prs-seq"):
        existing = [p.id for p in track.iter_prs(repo_root)]
        if args.dry_run:
            pr_id = f"{(max([int(e) for e in existing], default=0) + 1):04d}"
        else:
            pr_id = track.next_sequence_id(directory / ".seq", existing)

    record_dir = directory / f"{pr_id}-{slug}"
    path = record_dir / "pr.md"
    if path.exists():
        raise LayerError(f"{path} already exists; refusing to overwrite")

    meta = {
        "id": pr_id,
        "branch": args.branch,
        "issue": issue_id,
        "base": args.base,
        "state": "open",
        "head_sha": head_sha,
        "ci_status": None,
        "review_state": None,
        "fix_iterations": 0,
        "auto_fix": not args.no_auto_fix,
        "labels": labels,
        "created": track.utcnow(),
        "merged_commit": None,
    }
    # The title lives in the body as its H1: DESIGN.md:101-105 fixes the PR
    # frontmatter fields and does not include one.
    body = PR_BODY_TEMPLATE.format(
        title=title, footer=build_footer(issue_id, args.closes)
    )
    record = track.PullRequest(path, meta, body)

    if args.dry_run:
        sys.stdout.write(f"[dry-run] would create {path}\n\n{record.render()}\n")
        return 0

    record_dir.mkdir(parents=True, exist_ok=True)
    # Per-SHA CI manifests and review verdicts (DESIGN.md:103-105) live here;
    # pr_merge.py refuses to merge when either directory is missing, so create
    # them up front and leave a marker explaining what belongs in each.
    for name, purpose in (
        ("ci", "one <head_sha>.json manifest per CI run, written by local/bin/ci.sh"),
        ("reviews", "one <head_sha>.md verdict per review, written by local/bin/review.sh"),
    ):
        sub = record_dir / name
        sub.mkdir(exist_ok=True)
        marker = sub / ".gitkeep"
        if not marker.exists():
            track.atomic_write(marker, f"# {purpose}\n")

    track.atomic_write(path, record.render())
    sys.stdout.write(f"created {path.relative_to(repo_root)} (PR #{pr_id})\n")
    sys.stdout.write(f"PR #{pr_id}: labels {labels} copied from #{issue_id}\n")

    return track.on_pr_opened(repo_root, pr_id, dry_run=False)


def _parse_args(argv: list[str]) -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        prog="pr_open.py",
        description=__doc__,
        formatter_class=argparse.RawDescriptionHelpFormatter,
    )
    parser.add_argument("--issue", required=True, metavar="ID",
                        help="issue this PR addresses")
    parser.add_argument("--branch", required=True,
                        help="branch name; must embed the issue id")
    parser.add_argument("--title", required=True,
                        help="conventional-commit title, e.g. 'feat(Quantum): ...'")
    parser.add_argument("--base", default="main", help="merge target (default: main)")
    parser.add_argument("--closes", action="store_true",
                        help="use 'Closes #N' (auto-close on merge) instead of "
                             "'Addresses #N' (keep open)")
    parser.add_argument("--labels", action="append", default=[],
                        help="extra labels beyond those copied from the issue")
    parser.add_argument("--no-auto-fix", action="store_true",
                        help="record auto_fix: false so the fix loop skips this PR")
    parser.add_argument("--repo-root", type=Path, default=track.default_repo_root(),
                        help="repository root (default: two levels above this script)")
    parser.add_argument("--dry-run", action="store_true",
                        help="print the record that would be written, write nothing")
    return parser.parse_args(argv)


def main(argv: list[str] | None = None) -> int:
    args = _parse_args(sys.argv[1:] if argv is None else argv)
    try:
        return create_pr(args)
    except LayerError as exc:
        sys.stderr.write(f"pr_open.py: {exc}\n")
        return 2


if __name__ == "__main__":
    raise SystemExit(main())
