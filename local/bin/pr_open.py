#!/usr/bin/env python3
"""Push a branch and open (or adopt) its pull request on GitHub.

Pre-0007 this wrote ``prs/<id>-<slug>/pr.md`` and never touched a remote.  GitHub
now holds every field that record carried — head SHA, CI statuses bound to that
SHA, the review verdict — leaving three jobs it does not do: branch hygiene
(``check_bracket_free`` over ``FORBIDDEN_REF_CHARS`` plus ``git check-ref-format``;
docs/CONTRIBUTING.md:122-124 records that a ``]`` in a generated name once broke
part of the parent's PR automation); refusing an empty diff instead of
manufacturing a placeholder commit to make a PR openable; and create-or-adopt, so
a second run adopts the head's unique open PR and PATCHes only the flags given
(gh_common.py:194-200).  The push is real — hooks run, one ref is written, never
``--all``, never a force.  Fail closed: a git or API failure exits 2 opening
nothing.

    pr_open.py --branch issue-42-pauli --issue 42 --title "feat(Quantum): ..." \
               --body-file /tmp/pr-body.md --label formalization
"""

from __future__ import annotations

import argparse
import re
import subprocess
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
import gh_common  # noqa: E402
from wf_util import (BODY_LIMIT, FORBIDDEN_REF_CHARS, TITLE_LIMIT,  # noqa: E402
                     LayerError, check_bracket_free, default_repo_root, sanitize)


CHECKED_PUSH = Path(__file__).resolve().with_name("checked-push.sh")

#: DESIGN.md:106-107 — ``issue-<id>-<slug>``, optionally ``codex/``-prefixed.
BRANCH_RE = re.compile(r"^(?:(codex|claude)/)?issue-(\d+)-([a-z0-9][a-z0-9-]*)$")

#: docs/CONTRIBUTING.md:61-62 — a closing keyword is what makes the merge close
#: the issue, so the footer is appended only when the body carries none.  GitHub's
#: nine auto-closing keywords, exactly; keep in sync with pr_merge.py CLOSES_RE so
#: every reference this footer honors is one the dependency gate also sees.
CLOSES_RE = re.compile(r"(?i)\b(?:close[sd]?|fix(?:e[sd])?|resolve[sd]?):?\s+#(\d+)")


def git(repo_root: Path, *args: str, check: bool = True) -> str:
    """Run git in *repo_root*; stripped stdout, or ``LayerError`` / ``""``."""
    proc = subprocess.run(["git", "-C", str(repo_root), *args],
                          capture_output=True, text=True)
    if proc.returncode == 0:
        return proc.stdout.strip()
    if check:
        raise LayerError(f"git {' '.join(args[:3])} failed: "
                         f"{(proc.stderr or proc.stdout).strip()[:500]}")
    return ""


def checked_push(repo_root: Path, remote: str, refspec: str) -> None:
    """Run the hook before opening the receive transport, then publish one ref."""
    proc = subprocess.run(
        [str(CHECKED_PUSH), "--repo-root", str(repo_root), remote, refspec],
        capture_output=True,
        text=True,
    )
    if proc.returncode != 0:
        detail = "\n".join(part.strip() for part in (proc.stdout, proc.stderr) if part.strip())
        raise LayerError(f"checked push failed ({proc.returncode}): {detail[-2000:]}")


def lint_branch(repo_root: Path, branch: str) -> None:
    """Reject a name, or a branch, that cannot safely become a PR head; the
    ``issue-<id>-<slug>`` convention only warns, since the issue link now
    travels in the body footer while ``agent.sh`` still derives names so."""
    check_bracket_free(branch, "branch name", FORBIDDEN_REF_CHARS)
    git(repo_root, "check-ref-format", "--branch", branch)
    if not git(repo_root, "rev-parse", "--verify", f"refs/heads/{branch}", check=False):
        raise LayerError(f"branch {branch!r} does not exist in {repo_root}; create "
                         "and commit on it before opening a PR")
    match = BRANCH_RE.match(branch)
    if not match or match.group(1) == "claude":
        sys.stderr.write(f"warning: branch {branch!r} is not a current-convention "
                         "'issue-<id>-<slug>' / 'codex/issue-<id>-<slug>' name "
                         "(DESIGN.md:106-107).\n")


def require_diff(repo_root: Path, base: str, branch: str) -> int:
    """Commits ahead of the base; raise when there are none."""
    for ref in (f"refs/remotes/github/{base}", base):
        count = git(repo_root, "rev-list", "--count", f"{ref}..{branch}", check=False)
        if count.isdigit():
            if int(count) == 0:
                raise LayerError(f"{branch} has no commits ahead of {ref}: nothing "
                                 "to review. Commit the work — never open a PR on "
                                 "an empty diff.")
            return int(count)
    raise LayerError(f"cannot resolve base {base!r} locally or as github/{base}")


def pr_create(title: str, head: str, base: str, body: str) -> int:
    """POST one PR; an ambiguous failure adopts, never retries (gh_common.py:216)."""
    try:
        created = gh_common.api("pulls", method="POST", mutation=True,
                                payload={"title": title, "head": head,
                                         "base": base, "body": body})
        return int(created["number"])
    except LayerError:
        adopted = gh_common.pr_for_branch(head)
        if adopted is not None:
            return int(adopted["number"])
        raise


def open_pr(args: argparse.Namespace) -> int:
    repo_root = args.repo_root.resolve()
    lint_branch(repo_root, args.branch)
    ahead = require_diff(repo_root, args.base, args.branch)

    title = sanitize(args.title, TITLE_LIMIT).strip() if args.title else ""
    if title:
        check_bracket_free(title, "PR title")
    raw = Path(args.body_file).read_text(encoding="utf-8") if args.body_file else ""
    body = sanitize(raw, BODY_LIMIT)  # untrusted on the way out too: it will be quoted back
    if args.issue and not any(int(n) == args.issue for n in CLOSES_RE.findall(body)):
        body = f"{body.rstrip()}\n\n---\nCloses #{args.issue}\n".lstrip()

    labels = [n.strip() for chunk in args.label for n in chunk.split(",") if n.strip()]
    missing = sorted(set(labels) - set(gh_common.list_labels())) if labels else []
    if missing:
        raise LayerError(f"labels not in the repository: {missing} — create them "
                         "on GitHub first or drop them")
    if args.dry_run:
        sys.stdout.write(f"[dry-run] would push refs/heads/{args.branch} ({ahead} "
                         f"ahead of {args.base}) and open {title!r} {labels}\n")
        return 0

    checked_push(repo_root, "github",
                 f"refs/heads/{args.branch}:refs/heads/{args.branch}")

    existing = gh_common.pr_for_branch(args.branch)
    if existing is not None:
        number = int(existing["number"])
        patch = {"title": title} if title else {}
        if args.body_file:
            patch["body"] = body
        elif args.issue:
            # No replacement body was supplied, so never overwrite the existing
            # description; append the footer to the CURRENT body iff no closing
            # reference to this issue is there yet.
            current = str(existing.get("body") or "")
            if not any(int(n) == args.issue for n in CLOSES_RE.findall(current)):
                patch["body"] = f"{current.rstrip()}\n\n---\nCloses #{args.issue}\n".lstrip()
        if patch:
            gh_common.api(f"pulls/{number}", method="PATCH", payload=patch,
                          mutation=True, idempotent=True)
        sys.stderr.write(f"adopted the open PR for {args.branch}\n")
    elif not title:
        raise LayerError("--title is required to open a new PR")
    else:
        number = pr_create(title, args.branch, args.base, body)

    if labels:  # idempotent by content: GitHub unions the label set.
        gh_common.api(f"issues/{number}/labels", method="POST",
                      payload={"labels": labels}, mutation=True, idempotent=True)
    sys.stdout.write(f"{number}\n")  # bare number for $(...) in the shell layer
    return 0


def _parse_args(argv: list[str]) -> argparse.Namespace:
    parser = argparse.ArgumentParser(prog="pr_open.py", description=__doc__,
                                     formatter_class=argparse.RawDescriptionHelpFormatter)
    add = parser.add_argument
    add("--branch", required=True, help="head branch; must exist locally with commits")
    add("--base", default="main", help="merge target (default: main)")
    add("--title", help="conventional-commit title; required to open a new PR")
    add("--body-file", type=Path, metavar="PATH", help="file holding the PR body")
    add("--label", action="append", default=[], metavar="NAME",
        help="repository label; repeatable, comma lists accepted")
    add("--issue", type=int, metavar="N", help="append a 'Closes #N' body footer")
    add("--repo-root", type=Path, default=default_repo_root(), help="repository root")
    add("--dry-run", action="store_true", help="print the plan, write nothing")
    return parser.parse_args(argv)


def main(argv: list[str] | None = None) -> int:
    args = _parse_args(sys.argv[1:] if argv is None else argv)
    try:
        return open_pr(args)
    except LayerError as exc:
        sys.stderr.write(f"pr_open.py: {exc}\n")
        return 2


if __name__ == "__main__":
    raise SystemExit(main())
