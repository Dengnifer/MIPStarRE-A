#!/usr/bin/env python3
"""Reject merge results that silently discard an incoming tree change.

The pending-merge mode compares the staged index with ``HEAD``, ``MERGE_HEAD``,
and all of their best merge bases.  The committed mode performs the same check for an
existing two-parent merge commit.  Outside recorded conflicts, a path may be
absent only when the branch deleted a path that existed at the merge base.

Usage:

    merge_loss_guard.py [--repo PATH]
    merge_loss_guard.py [--repo PATH] --commit REV
"""

from __future__ import annotations

import argparse
from dataclasses import dataclass
import os
from pathlib import Path
import subprocess
import sys
import tempfile
from typing import Mapping


@dataclass(frozen=True)
class TreeEntry:
    """The mode and object identity of one non-directory tree entry."""

    mode: bytes
    object_id: bytes


@dataclass(frozen=True)
class MergeTrees:
    """The tree states needed to distinguish branch work from merge loss."""

    bases: tuple[Mapping[bytes, TreeEntry], ...]
    branch: Mapping[bytes, TreeEntry]
    incoming: Mapping[bytes, TreeEntry]
    result: Mapping[bytes, TreeEntry]
    conflicts: frozenset[bytes] = frozenset()
    automatic: Mapping[bytes, TreeEntry] | None = None


@dataclass(frozen=True)
class Finding:
    """One path whose incoming state was discarded by the merge result."""

    kind: str
    path: bytes


class GuardError(RuntimeError):
    """A malformed or unsupported Git state that must fail closed."""


def git_environment() -> dict[str, str]:
    """Return an environment independent of the repository invoking a hook."""

    environment = os.environ.copy()
    local_variables = subprocess.run(
        ["git", "rev-parse", "--local-env-vars"],
        check=True,
        capture_output=True,
        text=True,
    ).stdout.splitlines()
    for variable in local_variables:
        environment.pop(variable, None)
    return environment


def run_git(repo: Path, *args: str) -> bytes:
    """Run Git in ``repo`` and return stdout, or raise an operator-facing error."""

    result = subprocess.run(
        ["git", "-C", os.fspath(repo), *args],
        check=False,
        capture_output=True,
        env=git_environment(),
    )
    if result.returncode != 0:
        detail = os.fsdecode(result.stderr.strip() or result.stdout.strip())
        raise GuardError(f"git {' '.join(args)} failed ({result.returncode}): {detail}")
    return result.stdout


def resolve(repo: Path, revision: str) -> str:
    """Resolve ``revision`` to one commit object name."""

    return os.fsdecode(run_git(repo, "rev-parse", "--verify", f"{revision}^{{commit}}").strip())


def read_tree(repo: Path, revision: str) -> dict[bytes, TreeEntry]:
    """Read every non-directory entry from ``revision`` without path decoding."""

    entries: dict[bytes, TreeEntry] = {}
    output = run_git(repo, "ls-tree", "-rz", "--full-tree", revision)
    for record in output.split(b"\0"):
        if not record:
            continue
        metadata, path = record.split(b"\t", 1)
        mode, _kind, object_id = metadata.split(b" ", 2)
        entries[path] = TreeEntry(mode, object_id)
    return entries


def read_index(repo: Path) -> dict[bytes, TreeEntry]:
    """Read the stage-zero index used to create a pending merge commit."""

    entries: dict[bytes, TreeEntry] = {}
    output = run_git(repo, "ls-files", "--stage", "-z")
    for record in output.split(b"\0"):
        if not record:
            continue
        metadata, path = record.split(b"\t", 1)
        mode, object_id, stage = metadata.split(b" ", 2)
        if stage != b"0":
            raise GuardError(
                f"unresolved index entry at {os.fsdecode(path)!r} (stage {os.fsdecode(stage)})"
            )
        entries[path] = TreeEntry(mode, object_id)
    return entries


def read_index_state(repo: Path) -> tuple[dict[bytes, TreeEntry], frozenset[bytes]]:
    """Read clean index entries and the paths retaining conflict stages."""

    entries: dict[bytes, TreeEntry] = {}
    conflicts: set[bytes] = set()
    output = run_git(repo, "ls-files", "--stage", "-z")
    for record in output.split(b"\0"):
        if not record:
            continue
        metadata, path = record.split(b"\t", 1)
        mode, object_id, stage = metadata.split(b" ", 2)
        if stage == b"0":
            entries[path] = TreeEntry(mode, object_id)
        else:
            conflicts.add(path)
    return entries, frozenset(conflicts)


def merge_bases(repo: Path, branch: str, incoming: str) -> tuple[str, ...]:
    """Return every best merge base used to classify branch-owned changes."""

    bases = run_git(repo, "merge-base", "--all", branch, incoming).splitlines()
    if not bases:
        raise GuardError(f"no merge base for {branch} and {incoming}")
    return tuple(os.fsdecode(base) for base in bases)


def pending_merge_head(repo: Path) -> str | None:
    """Return the sole pending ``MERGE_HEAD``, or ``None`` outside a merge."""

    git_path = os.fsdecode(run_git(repo, "rev-parse", "--git-path", "MERGE_HEAD").strip())
    path = Path(git_path)
    if not path.is_absolute():
        path = repo / path
    if not path.is_file():
        return None
    heads = [line.strip() for line in path.read_text(encoding="ascii").splitlines() if line.strip()]
    if len(heads) != 1:
        raise GuardError(f"expected one MERGE_HEAD, found {len(heads)}")
    return resolve(repo, heads[0])


def pending_conflicts(repo: Path) -> frozenset[bytes]:
    """Read Git's retained conflict-path section for a resolved pending merge."""

    git_path = os.fsdecode(run_git(repo, "rev-parse", "--git-path", "MERGE_MSG").strip())
    path = Path(git_path)
    if not path.is_absolute():
        path = repo / path
    if not path.is_file():
        return frozenset()
    conflicts: set[bytes] = set()
    in_conflicts = False
    for line in path.read_bytes().splitlines():
        stripped = line.lstrip(b"#").strip()
        if stripped == b"Conflicts:":
            in_conflicts = True
            continue
        if in_conflicts:
            if not line.startswith(b"#") or not stripped:
                break
            conflicts.add(stripped)
    return frozenset(conflicts)


def reconstructed_merge(
    repo: Path, branch: str, incoming: str
) -> tuple[dict[bytes, TreeEntry], frozenset[bytes]]:
    """Recover Git's clean merge entries and conflicts in a disposable local clone."""

    with tempfile.TemporaryDirectory(prefix="mipstarre-merge-audit-") as directory:
        clone = Path(directory) / "repo"
        clone_result = subprocess.run(
            [
                "git",
                "clone",
                "--quiet",
                "--shared",
                "--no-checkout",
                os.fspath(repo),
                os.fspath(clone),
            ],
            check=False,
            capture_output=True,
            env=git_environment(),
        )
        if clone_result.returncode != 0:
            detail = os.fsdecode(clone_result.stderr.strip() or clone_result.stdout.strip())
            raise GuardError(f"temporary local clone failed: {detail}")
        run_git(clone, "config", "user.email", "merge-loss-guard@example.invalid")
        run_git(clone, "config", "user.name", "MIPStarRE merge-loss guard")
        run_git(clone, "checkout", "--quiet", "--detach", branch)
        merge_result = subprocess.run(
            ["git", "-C", os.fspath(clone), "merge", "--no-commit", "--no-ff", incoming],
            check=False,
            capture_output=True,
            env=git_environment(),
        )
        merge_head_output = run_git(clone, "rev-parse", "--git-path", "MERGE_HEAD").strip()
        merge_head = Path(os.fsdecode(merge_head_output))
        if not merge_head.is_absolute():
            merge_head = clone / merge_head
        if merge_result.returncode not in (0, 1) or not merge_head.is_file():
            detail = os.fsdecode(merge_result.stderr.strip() or merge_result.stdout.strip())
            raise GuardError(f"automatic merge reconstruction failed: {detail}")
        return read_index_state(clone)


def pending_trees(repo: Path) -> tuple[MergeTrees, tuple[str, ...], str, str]:
    """Load a pending merge's base, pre-merge branch, incoming, and index trees."""

    incoming = pending_merge_head(repo)
    if incoming is None:
        raise GuardError("no merge is in progress")
    branch = resolve(repo, "HEAD")
    bases = merge_bases(repo, branch, incoming)
    automatic = None
    conflicts = pending_conflicts(repo)
    if len(bases) > 1:
        automatic, reconstructed = reconstructed_merge(repo, branch, incoming)
        conflicts |= reconstructed
    trees = MergeTrees(
        bases=tuple(read_tree(repo, base) for base in bases),
        branch=read_tree(repo, branch),
        incoming=read_tree(repo, incoming),
        result=read_index(repo),
        conflicts=conflicts,
        automatic=automatic,
    )
    return trees, bases, branch, incoming


def committed_trees(
    repo: Path, revision: str
) -> tuple[MergeTrees, tuple[str, ...], str, str]:
    """Load the four trees associated with a committed two-parent merge."""

    commit = resolve(repo, revision)
    topology = os.fsdecode(run_git(repo, "rev-list", "--parents", "-n", "1", commit)).split()
    parents = topology[1:]
    if len(parents) != 2:
        raise GuardError(f"{commit} is not a two-parent merge commit")
    branch, incoming = parents
    bases = merge_bases(repo, branch, incoming)
    automatic, conflicts = (
        (None, frozenset())
        if incoming in bases
        else reconstructed_merge(repo, branch, incoming)
    )
    trees = MergeTrees(
        bases=tuple(read_tree(repo, base) for base in bases),
        branch=read_tree(repo, branch),
        incoming=read_tree(repo, incoming),
        result=read_tree(repo, commit),
        conflicts=conflicts,
        automatic=automatic if len(bases) > 1 else None,
    )
    return trees, bases, branch, incoming


def inspect(trees: MergeTrees) -> list[Finding]:
    """Find incoming paths deleted or wholly reverted by the result.

    Deletion is branch-owned only when the path existed at a merge base and is
    absent from the pre-merge branch tree. Recorded conflicts are exempt.
    For multiple bases, Git's reconstructed clean result identifies incoming-only
    changes without comparing against incompatible raw bases. Combined changes
    remain the responsibility of normal review.
    """

    findings: list[Finding] = []
    paths = set(trees.branch) | set(trees.incoming) | set(trees.result)
    for base in trees.bases:
        paths.update(base)
    for path in sorted(paths):
        if path in trees.conflicts:
            continue
        base_entries = tuple(base.get(path) for base in trees.bases)
        branch_entry = trees.branch.get(path)
        incoming_entry = trees.incoming.get(path)
        result_entry = trees.result.get(path)

        if incoming_entry is not None and result_entry is None:
            branch_deleted = (
                any(entry is not None for entry in base_entries) and branch_entry is None
            )
            if not branch_deleted:
                findings.append(Finding("deleted", path))
            continue

        if trees.automatic is not None:
            if (
                incoming_entry != branch_entry
                and trees.automatic.get(path) == incoming_entry
                and result_entry == branch_entry
            ):
                findings.append(Finding("reverted", path))
            continue

        incoming_changed = all(incoming_entry != entry for entry in base_entries)
        if not incoming_changed or result_entry == incoming_entry:
            continue
        branch_matches_base = all(branch_entry == entry for entry in base_entries)
        if branch_matches_base and result_entry == branch_entry:
            findings.append(Finding("reverted", path))
    return findings


def short(object_id: str) -> str:
    return object_id[:12]


def report(
    findings: list[Finding], bases: tuple[str, ...], branch: str, incoming: str
) -> int:
    """Print a stable refusal report and return the intended process status."""

    if not findings:
        print(
            "MIPStarRE merge-loss guard: ok "
            f"(base {','.join(short(base) for base in bases)}, "
            f"branch {short(branch)}, incoming {short(incoming)})."
        )
        return 0

    print("MIPStarRE merge-loss guard: refusing a result that discards incoming changes.")
    print(f"  merge base(s):   {', '.join(bases)}")
    print(f"  pre-merge branch: {branch}")
    print(f"  incoming head:   {incoming}")
    for finding in findings:
        print(f"  {finding.kind.upper():8} {os.fsdecode(finding.path)}")
    print(
        "Outside recorded conflicts, a missing path is permitted only when it existed "
        "at the merge base and the pre-merge branch deleted it. Restore or combine the incoming content "
        "before committing."
    )
    return 1


def parse_args(argv: list[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--repo", type=Path, default=Path.cwd(), help="Git worktree root")
    parser.add_argument(
        "--commit",
        metavar="REV",
        help="audit an existing two-parent merge instead of the pending index",
    )
    return parser.parse_args(argv)


def main(argv: list[str] | None = None) -> int:
    args = parse_args(argv)
    repo = args.repo.resolve()
    try:
        if args.commit is None:
            incoming = pending_merge_head(repo)
            if incoming is None:
                return 0
            trees, bases, branch, incoming = pending_trees(repo)
        else:
            trees, bases, branch, incoming = committed_trees(repo, args.commit)
        return report(inspect(trees), bases, branch, incoming)
    except GuardError as error:
        print(f"MIPStarRE merge-loss guard: {error}", file=sys.stderr)
        return 2


if __name__ == "__main__":
    raise SystemExit(main())
