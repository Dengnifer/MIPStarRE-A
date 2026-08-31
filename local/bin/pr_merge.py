#!/usr/bin/env python3
"""Merge a GitHub pull request after all exact-head local gates pass."""

from __future__ import annotations

import argparse
import os
import re
import shutil
import subprocess
import sys
from contextlib import contextmanager
from dataclasses import dataclass
from datetime import datetime
from pathlib import Path
from typing import Any, Iterator, Sequence

sys.path.insert(0, str(Path(__file__).resolve().parent))
from github_api import (  # noqa: E402
    ADJUDICATION_LABEL,
    CIManifestEvidence,
    GitHub,
    GitHubError,
    PullIdentity,
    ReviewEvidence,
    fix_iteration_count,
    normalize_number,
    normalize_sha,
    pull_identity,
)


DEFAULT_FIX_CAP = 5
DISPOSITION_RE = re.compile(r"^Disposition:\s*\S.*$", re.MULTILINE)


class GateFailure(RuntimeError):
    """A merge-gate refusal with an operator-facing explanation."""


@dataclass(frozen=True)
class GateExpectation:
    """The immutable PR comparison accepted for this merge invocation."""

    branch: str
    base: str
    head_sha: str
    base_sha: str


@dataclass(frozen=True)
class GateSnapshot:
    """One complete evaluation of all merge evidence."""

    pull: dict[str, Any]
    identity: PullIdentity
    worktree: Path
    ci: CIManifestEvidence
    review: ReviewEvidence
    iterations: int


@dataclass(frozen=True)
class HeldLock:
    path: Path
    pid: int

    def require_owned(self, *, reject_cancel: bool = False) -> None:
        try:
            recorded = int((self.path / "pid").read_text(encoding="utf-8").strip())
        except (OSError, ValueError) as exc:
            raise GateFailure(f"reserved lock {self.path} lost its owner record") from exc
        if not self.path.is_dir() or recorded != self.pid:
            raise GateFailure(f"reserved lock {self.path} is no longer owned by this merge")
        if reject_cancel and (self.path / "cancel").exists():
            raise GateFailure(
                f"an auto-fix attempted to supersede the reserved merge lock {self.path}"
            )


def git(root: Path, *arguments: str, check: bool = True) -> str:
    result = subprocess.run(
        ["git", "-C", str(root), *arguments],
        text=True,
        capture_output=True,
        check=False,
    )
    if check and result.returncode != 0:
        raise GateFailure(
            result.stderr.strip() or f"git {' '.join(arguments)} failed"
        )
    return result.stdout.strip()


def primary_root(value: Path | None) -> Path:
    root = (value or Path.cwd()).resolve()
    common = git(root, "rev-parse", "--path-format=absolute", "--git-common-dir")
    common_path = Path(common)
    return common_path.parent if common_path.name == ".git" else root


def branch_worktree(root: Path, branch: str) -> Path | None:
    current: Path | None = None
    for line in git(root, "worktree", "list", "--porcelain").splitlines():
        if line.startswith("worktree "):
            current = Path(line.removeprefix("worktree "))
        elif line == f"branch refs/heads/{branch}" and current is not None:
            return current
    return None


def exact_local_head(root: Path, branch: str) -> tuple[str, Path]:
    if any(ch in branch for ch in "[]~^:?*\\ \t\r\n"):
        raise GateFailure(f"unsafe GitHub head branch {branch!r}")
    worktree = branch_worktree(root, branch)
    if worktree is None or not worktree.is_dir():
        raise GateFailure(f"no local worktree is registered for PR branch {branch!r}")
    symbolic = git(worktree, "symbolic-ref", "--quiet", "--short", "HEAD")
    if symbolic != branch:
        raise GateFailure(
            f"worktree {worktree} is on {symbolic!r}, expected {branch!r}"
        )
    return normalize_sha(git(worktree, "rev-parse", "HEAD")), worktree


def require_open_mergeable(pull: dict[str, Any], number: int) -> PullIdentity:
    if str(pull.get("state") or "").casefold() != "open":
        raise GateFailure(f"PR #{number} is not open")
    if bool(pull.get("draft")):
        raise GateFailure(f"PR #{number} is a draft")
    if pull.get("mergeable") is not True:
        state = pull.get("mergeable_state") or "unknown"
        raise GateFailure(f"PR #{number} is not proven mergeable (state={state})")
    return pull_identity(pull)


def require_ci(
    client: GitHub, number: int, head_sha: str, base_sha: str
) -> CIManifestEvidence:
    try:
        evidence = client.ci_evidence(number, head_sha, base_sha)
    except GitHubError as exc:
        raise GateFailure(f"invalid exact-head CI evidence: {exc}") from exc
    manifest = evidence.manifest
    if str(manifest.get("conclusion") or "") != "success":
        raise GateFailure("the exact-run CI manifest conclusion is not success")
    failures = [
        f"{step.get('step')}={step.get('outcome')}"
        for step in manifest.get("steps") or []
        if str(step.get("outcome") or "") not in {"success", "skipped"}
    ]
    if failures:
        raise GateFailure("exact-head CI gate failed: " + ", ".join(failures))
    return evidence


def row_order(row: dict[str, Any]) -> tuple[datetime, int]:
    raw_timestamp = str(row.get("submitted_at") or row.get("created_at") or "")
    identifier = row.get("id")
    if type(identifier) is not int or identifier <= 0 or not raw_timestamp:
        raise GateFailure("review ordering evidence lacks an id or timestamp")
    try:
        timestamp = datetime.fromisoformat(raw_timestamp.replace("Z", "+00:00"))
    except ValueError as exc:
        raise GateFailure("review ordering evidence has an invalid timestamp") from exc
    if timestamp.utcoffset() is None:
        raise GateFailure("review ordering evidence has a timezone-free timestamp")
    return timestamp, identifier


def require_review(
    client: GitHub, number: int, sha: str, base_sha: str | None = None
) -> ReviewEvidence:
    try:
        evidence = client.review_evidence(number, sha, base_sha)
    except GitHubError as exc:
        raise GateFailure(f"no valid exact-head review attestation: {exc}") from exc
    attestation = evidence.attestation
    ledger = attestation.row
    if (
        attestation.event != "COMMENT"
        or attestation.fallback != "none"
        or attestation.findings != 0
        or str(ledger.get("state") or "").upper() != "COMMENTED"
    ):
        raise GateFailure(
            "the selected exact-head review is not a clean COMMENT attestation"
        )
    ledger_order = row_order(ledger)
    for review in client.reviews(number):
        if str(review.get("commit_id") or "").lower() != sha:
            continue
        if str(review.get("state") or "").upper() != "CHANGES_REQUESTED":
            continue
        if row_order(review) > ledger_order:
            raise GateFailure("a later exact-head CHANGES_REQUESTED review is unresolved")
    return evidence


def require_adjudication(
    client: GitHub, pull: dict[str, Any], number: int, sha: str
) -> None:
    labels = {
        str(item.get("name") if isinstance(item, dict) else item)
        for item in (pull.get("labels") or [])
    }
    if ADJUDICATION_LABEL not in labels:
        raise GateFailure(f"adjudicated merge requires label {ADJUDICATION_LABEL!r}")
    marker = f"<!-- mipstarre:adjudication pr={number} head={sha} -->"
    matches: list[dict[str, Any]] = []
    for row in client.comments(number):
        body = str(row.get("body") or "")
        if body.startswith("ADJUDICATION") and marker in body:
            matches.append(row)
    if not matches:
        raise GateFailure("no current-head ADJUDICATION comment with a stable marker")
    matches.sort(key=row_order, reverse=True)
    body = str(matches[0].get("body") or "")
    if body.count(marker) != 1 or not DISPOSITION_RE.search(body):
        raise GateFailure(
            "the adjudication comment must contain one exact-head marker and a "
            "nonempty 'Disposition:' line"
        )


def require_no_live_fix(cache: Path, branch: str) -> None:
    lock = cache / "locks" / f"fix-{branch.replace('/', '-')}.lock"
    if not lock.is_dir():
        return
    try:
        pid = int((lock / "pid").read_text(encoding="utf-8").strip())
    except (OSError, ValueError):
        return
    try:
        os.kill(pid, 0)
    except OSError:
        return
    raise GateFailure(f"live auto-fix lock {lock} is held by pid {pid}")


@contextmanager
def reserve_runtime_lock(path: Path, label: str) -> Iterator[HeldLock]:
    """Atomically reserve one known runtime lock and release only our lease."""
    path.parent.mkdir(parents=True, exist_ok=True)
    try:
        path.mkdir()
    except FileExistsError as exc:
        try:
            holder = int((path / "pid").read_text(encoding="utf-8").strip())
        except (OSError, ValueError):
            holder = None
        state = f"live pid {holder}" if holder is not None else "unproven owner"
        if holder is not None:
            try:
                os.kill(holder, 0)
            except OSError:
                state = f"stale pid {holder}"
        raise GateFailure(f"cannot reserve runtime lock {path} ({state})") from exc
    held = HeldLock(path=path, pid=os.getpid())
    try:
        (path / "pid").write_text(f"{held.pid}\n", encoding="utf-8")
        (path / "label").write_text(label + "\n", encoding="utf-8")
        held.require_owned()
        yield held
    finally:
        try:
            owner = int((path / "pid").read_text(encoding="utf-8").strip())
        except (OSError, ValueError):
            owner = None
        if owner == held.pid:
            shutil.rmtree(path)


def require_merge_capability(client: GitHub) -> None:
    result = client.run(["pr", "merge", "--help"], retry=False)
    if "--match-head-commit" not in result.stdout:
        raise GateFailure(
            "installed gh lacks 'pr merge --match-head-commit'; upgrade before merging"
        )


def exact_local_base(root: Path, base: str) -> str:
    reference = f"refs/remotes/github/{base}^{{commit}}"
    try:
        return normalize_sha(git(root, "rev-parse", "--verify", reference))
    except (GateFailure, GitHubError) as exc:
        raise GateFailure(f"fetched GitHub base ref does not resolve: {reference}") from exc


def _require_expected(identity: PullIdentity, expected: GateExpectation) -> None:
    observed = GateExpectation(
        branch=identity.branch,
        base=identity.base,
        head_sha=identity.head_sha,
        base_sha=identity.base_sha,
    )
    if observed != expected:
        raise GateFailure(
            "PR head/base changed during merge gating "
            f"(expected={expected}, observed={observed})"
        )


def evaluate_gate(
    client: GitHub,
    number: int,
    expected: GateExpectation,
    root: Path,
    review_lock: HeldLock,
    fix_lock: HeldLock,
    cap: int,
    *,
    adjudicated: bool,
) -> GateSnapshot:
    """Evaluate the complete fail-closed gate from authoritative state."""
    review_lock.require_owned()
    pull = client.get_pull(number)
    identity = require_open_mergeable(pull, number)
    _require_expected(identity, expected)
    local_head, worktree = exact_local_head(root, expected.branch)
    local_base = exact_local_base(root, expected.base)
    if local_head != expected.head_sha or local_base != expected.base_sha:
        raise GateFailure(
            "local head/base do not match the immutable GitHub comparison "
            f"(local_head={local_head}, local_base={local_base})"
        )

    ci = require_ci(client, number, expected.head_sha, expected.base_sha)
    fix_lock.require_owned(reject_cancel=True)
    commits = client.pull_commits(number)
    iterations = fix_iteration_count(commits)
    if iterations > cap:
        raise GateFailure(
            f"fix iteration count {iterations} exceeds configured cap {cap}"
        )
    if adjudicated:
        require_adjudication(client, pull, number, expected.head_sha)

    # Rebind the comparison after all potentially paginated reads. The review
    # check is last so a same-head adverse review introduced during evaluation
    # cannot be hidden by an earlier clean-ledger read.
    final_pull = client.get_pull(number)
    final_identity = require_open_mergeable(final_pull, number)
    _require_expected(final_identity, expected)
    final_local_head, final_worktree = exact_local_head(root, expected.branch)
    final_local_base = exact_local_base(root, expected.base)
    if (
        final_local_head != expected.head_sha
        or final_local_base != expected.base_sha
        or final_worktree.resolve() != worktree.resolve()
    ):
        raise GateFailure("local head/base/worktree changed during gate evaluation")
    fix_lock.require_owned(reject_cancel=True)
    review = require_review(
        client, number, expected.head_sha, expected.base_sha
    )
    attested_worktree = Path(review.attestation.lanes[0].worktree).resolve()
    if attested_worktree != worktree.resolve():
        raise GateFailure(
            "review session telemetry is bound to a different feature worktree"
        )
    review_lock.require_owned()
    fix_lock.require_owned(reject_cancel=True)
    return GateSnapshot(
        pull=final_pull,
        identity=final_identity,
        worktree=worktree,
        ci=ci,
        review=review,
        iterations=iterations,
    )


def fast_forward_base(root: Path, base: str) -> None:
    git(
        root,
        "fetch",
        "--no-tags",
        "github",
        f"refs/heads/{base}:refs/remotes/github/{base}",
    )
    worktree = branch_worktree(root, base)
    if worktree is None:
        raise GateFailure(
            f"GitHub merged the PR, but no local checkout of base branch {base!r} exists"
        )
    if git(worktree, "status", "--porcelain"):
        raise GateFailure(
            f"GitHub merged the PR, but base worktree {worktree} is dirty; "
            "it was not advanced"
        )
    git(worktree, "merge", "--ff-only", f"refs/remotes/github/{base}")


def cleanup_feature(root: Path, branch: str, worktree: Path, merge_sha: str) -> None:
    if git(worktree, "status", "--porcelain"):
        raise GateFailure(
            f"PR merged, but feature worktree {worktree} is dirty; cleanup was skipped"
        )
    ancestor = subprocess.run(
        ["git", "-C", str(root), "merge-base", "--is-ancestor", branch, merge_sha],
        check=False,
    )
    if ancestor.returncode != 0:
        raise GateFailure(
            f"PR merged, but local branch {branch!r} is not contained in {merge_sha}; "
            "cleanup was skipped"
        )
    git(root, "worktree", "remove", str(worktree))
    git(root, "branch", "-d", branch)


def build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("number", help="GitHub pull-request number")
    parser.add_argument("--adjudicated", action="store_true")
    parser.add_argument("--dry-run", action="store_true")
    parser.add_argument("--fix-cap", type=int, default=None)
    parser.add_argument("--repo-root", type=Path)
    return parser


def run(args: argparse.Namespace) -> int:
    number = normalize_number(args.number, kind="PR number")
    root = primary_root(args.repo_root)
    cache = Path(
        os.environ.get("MIPSTARRE_CACHE_ROOT", Path.home() / ".cache/mipstarre-dev")
    )
    cap = args.fix_cap
    if cap is None:
        cap = int(os.environ.get("MIPSTARRE_FIX_CAP", str(DEFAULT_FIX_CAP)))
    if cap < 0:
        raise GateFailure("fix cap must be nonnegative")

    client = GitHub(repo_root=root)
    client.probe_authentication()
    require_merge_capability(client)
    review_path = cache / "locks" / f"review-{number}.lock"
    with reserve_runtime_lock(review_path, f"merge review pr={number}") as review_lock:
        pull = client.get_pull(number)
        identity = require_open_mergeable(pull, number)
        expected = GateExpectation(
            branch=identity.branch,
            base=identity.base,
            head_sha=identity.head_sha,
            base_sha=identity.base_sha,
        )
        fix_path = (
            cache
            / "locks"
            / f"fix-{expected.branch.replace('/', '-')}.lock"
        )
        with reserve_runtime_lock(
            fix_path, f"merge fix-reservation pr={number} branch={expected.branch}"
        ) as fix_lock:
            first = evaluate_gate(
                client,
                number,
                expected,
                root,
                review_lock,
                fix_lock,
                cap,
                adjudicated=args.adjudicated,
            )
            command = [
                "pr",
                "merge",
                str(number),
                "--repo",
                client.repo,
                "--merge",
                "--match-head-commit",
                expected.head_sha,
            ]
            # The same evaluator runs again as the final operation before the
            # guarded merge, catching same-head evidence and base races.
            final = evaluate_gate(
                client,
                number,
                expected,
                root,
                review_lock,
                fix_lock,
                cap,
                adjudicated=args.adjudicated,
            )
            if first.worktree.resolve() != final.worktree.resolve():
                raise GateFailure("feature worktree changed between gate evaluations")
            if args.dry_run:
                print("gate passed; would run: gh " + " ".join(command))
                return 0
            client.run(command, retry=False)
            merged = client.get_pull(number)
            if not merged.get("merged"):
                raise GateFailure(
                    "gh returned success but GitHub does not report the PR merged"
                )
            merge_sha = normalize_sha(
                str(merged.get("merge_commit_sha") or ""), kind="merge commit SHA"
            )
            feature_worktree = final.worktree
    fast_forward_base(root, expected.base)
    cleanup_feature(root, expected.branch, feature_worktree, merge_sha)
    print(f"merged GitHub PR #{number} at {merge_sha}")
    return 0


def main(argv: Sequence[str] | None = None) -> int:
    try:
        return run(build_parser().parse_args(argv))
    except (GateFailure, GitHubError, OSError, ValueError) as exc:
        sys.stderr.write(f"pr_merge.py: merge refused: {exc}\n")
        return 2


if __name__ == "__main__":
    raise SystemExit(main())
