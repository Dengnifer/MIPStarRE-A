#!/usr/bin/env python3
"""Integrate independently reviewed PR heads, check the result, and publish it.

Operator-only after deployment. Development and tests must use fixture repos.
Member evidence remains attached to its original SHA; combined CI is additional
evidence and never manufactures an independent review of the integration head.
"""

from __future__ import annotations

import argparse
from contextlib import ExitStack
from datetime import datetime, timezone
import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile

import gh_common
import pr_merge
from pr_merge import GateFailure, git, git_ok
from wf_util import LayerError, atomic_write, cache_root, file_lock, utcnow


def command(repo: Path, *args: str, env: dict | None = None) -> None:
    result = subprocess.run(args, cwd=repo, check=False, env=env)
    if result.returncode:
        raise LayerError(f"step {args[0]} failed ({result.returncode})")


def primary_at(repo: Path, base: str) -> None:
    common = Path(git(repo, "rev-parse", "--path-format=absolute", "--git-common-dir"))
    if common != repo / ".git":
        raise GateFailure("train requires the primary checkout")
    if git(repo, "symbolic-ref", "--short", "HEAD") != "main":
        raise GateFailure("primary checkout must be on main")
    if git(repo, "status", "--porcelain") or git(repo, "rev-parse", "HEAD") != base:
        raise GateFailure("primary checkout is dirty or main changed")
    if git(repo, "ls-remote", "github", "refs/heads/main").split() != [base, "refs/heads/main"]:
        raise GateFailure("remote main changed")


def members_at(repo: Path, numbers: list[int], base: str, adjudicated: set[int]) -> list[dict]:
    members, failures = [], []
    for number in numbers:
        try:
            row = pr_merge.run_gate(repo, number, adjudicated=number in adjudicated,
                                    integration_base=base)
            members.append({"number": number, "head": row["head_sha"],
                            "branch": row["branch"], "adjudicated": number in adjudicated})
        except LayerError as exc:
            failures.append(f"PR #{number}: {exc}")
    if failures:
        raise GateFailure("train preconditions failed:\n" + "\n".join(failures))
    return members


def integrate(repo: Path, worktree: Path, members: list[dict]) -> tuple[list[dict], list[int]]:
    accepted, dropped = [], []
    for member in members:
        head, number = member["head"], member["number"]
        before = git(worktree, "rev-parse", "HEAD")
        if git_ok(worktree, "merge-base", "--is-ancestor", head, before):
            raise GateFailure(f"PR #{number} is already contained in the train")
        result = subprocess.run(
            ["git", "merge", "--no-ff", "--no-commit", head], cwd=worktree,
            text=True, capture_output=True)
        if result.returncode:
            if not git(worktree, "diff", "--name-only", "--diff-filter=U"):
                raise LayerError(f"PR #{number}: merge failed: {result.stderr}")
            git(worktree, "merge", "--abort")
            if git(worktree, "rev-parse", "HEAD") != before or git(worktree, "status", "--porcelain"):
                raise GateFailure(f"PR #{number}: conflict abort did not restore the accepted train")
            dropped.append(number)
            print(f"dropped PR #{number}: merge conflict", flush=True)
            continue
        command(worktree, sys.executable, str(repo / "local/bin/merge_loss_guard.py"),
                "--repo", str(worktree))
        git(worktree, "commit", "-m", f"Merge PR #{number} into reviewed train")
        parents = git(worktree, "rev-list", "--parents", "-n", "1", "HEAD").split()[1:]
        if parents != [before, head]:
            raise GateFailure(f"PR #{number}: unexpected merge topology")
        accepted.append(member)
    return accepted, dropped


def ci_path(head: str) -> Path:
    return cache_root() / "ci-manifests" / f"prtrain-{head}-{head}.partial.json"


def check_combined_ci(data: dict) -> None:
    manifest = json.loads(ci_path(data["head"]).read_text(encoding="utf-8"))
    expected = {step: "success" for step in pr_merge.CI_STEPS}
    outcomes = {row["step"]: row["outcome"] for row in manifest["steps"]}
    if (manifest["head_sha"] != data["head"] or manifest["merge_base"] != data["base"]
            or manifest["worktree"] != data["worktree"] or manifest["conclusion"] != "success"
            or outcomes != expected or len(manifest["steps"]) != len(expected)):
        raise GateFailure(f"combined CI did not pass every step: {outcomes}")


def verify_manifest(path: Path, expected_main: str, expected_head: str, expected_ref: str) -> None:
    """Recheck after checked-push's expensive preflight, before transport opens."""
    data = json.loads(path.read_text(encoding="utf-8"))
    repo, worktree = Path(data["repo"]), Path(data["worktree"])
    if (expected_main != data["base"] or expected_head != data["head"]
            or expected_ref != "refs/heads/main"):
        raise GateFailure("publication tuple differs from the tested train")
    if len(data["members"]) < 2:
        raise GateFailure("fewer than two train members")
    primary_at(repo, data["base"])
    current = members_at(repo, [m["number"] for m in data["members"]], data["base"],
                         {m["number"] for m in data["members"] if m["adjudicated"]})
    if current != data["members"]:
        raise GateFailure("a train member head or branch changed")
    if git(worktree, "rev-parse", "HEAD") != data["head"] or git(worktree, "status", "--porcelain"):
        raise GateFailure("tested train changed")
    for member in current:
        if not git_ok(worktree, "merge-base", "--is-ancestor", member["head"], data["head"]):
            raise GateFailure(f"PR #{member['number']} is missing from the train")
    check_combined_ci(data)
    refs = {f"refs/heads/{m['branch']}": m["head"] for m in current}
    refs["refs/heads/main"] = data["base"]
    advertised = {ref: sha for sha, ref in
                  (line.split() for line in git(repo, "ls-remote", "github", *refs).splitlines())}
    if advertised != refs:
        raise GateFailure("remote main or member refs changed")
    primary_at(repo, data["base"])


def run_ci(repo: Path, data: dict) -> None:
    worktree = Path(data["worktree"])
    env = dict(os.environ, MIPSTARRE_TELEMETRY_DIR=str(worktree.parent / "telemetry"))
    # Bootstrap with trusted primary scripts; --no-build prevents a second full build.
    command(repo, str(repo / "local/bin/worktree-setup.sh"), str(worktree), "--no-build", env=env)
    try:
        command(repo, str(repo / "local/bin/ci.sh"), "--integration-head", data["head"],
                "--worktree", str(worktree), "--base", data["base"], env=env)
    except LayerError:
        if ci_path(data["head"]).exists():
            check_combined_ci(data)
        raise
    check_combined_ci(data)


def publication_outcome(repo: Path, head: str) -> str:
    """Reconcile an ambiguous push without retrying it or assuming a failed read is absence."""
    try:
        rows = git(repo, "ls-remote", "github", "refs/heads/main").split()
        if len(rows) != 2 or rows[1] != "refs/heads/main":
            return "unknown"
        remote = rows[0]
        if remote == head:
            return "published"
        git(repo, "fetch", "--no-tags", "github", remote)
        result = subprocess.run(["git", "merge-base", "--is-ancestor", head, remote], cwd=repo)
        if result.returncode == 0:
            return "published"
        if result.returncode == 1 and git(repo, "rev-parse", "--is-shallow-repository") == "false":
            return "refused"
    except (LayerError, OSError, ValueError) as exc:
        print(f"publication reconciliation failed: {exc}", file=sys.stderr)
    return "unknown"


def record(repo: Path, data: dict, outcome: str) -> None:
    """Retain publication state and transfer build telemetry only after gating ends."""
    atomic_write(Path(data["worktree"]).parent / "publication.json",
                 json.dumps({"head": data["head"], "outcome": outcome, "ts": utcnow()}) + "\n")
    with file_lock("train-telemetry"):
        telemetry = repo / "results/telemetry"
        telemetry.mkdir(parents=True, exist_ok=True)
        spools = [cache_root() / "ci-manifests" / f"train-{data['head']}.builds.jsonl",
                  Path(data["worktree"]).parent / "telemetry/builds.jsonl"]
        for spool in spools:
            if spool.exists():
                with (telemetry / "builds.jsonl").open("a", encoding="utf-8") as handle:
                    handle.write(spool.read_text(encoding="utf-8"))
                spool.unlink()
        members = ", ".join(f"#{m['number']}@{m['head']}" for m in data["members"])
        with (telemetry / "events.md").open("a", encoding="utf-8") as handle:
            handle.write(f"\n- {utcnow()} - Reviewed train {data['head']}: publication {outcome}; "
                         f"members {members}; conflicting PRs dropped: {data['dropped']}.\n")


def run_train(repo: Path, numbers: list[int], adjudicated: set[int]) -> int:
    if len(numbers) < 2 or len(set(numbers)) != len(numbers) or any(n <= 0 for n in numbers):
        raise GateFailure("provide at least two distinct positive PR numbers")
    if not adjudicated.issubset(numbers):
        raise GateFailure("--adjudicated must name a train member")
    if os.environ.get("MIPSTARRE_SKIP_HOOKS") == "1":
        raise GateFailure("a train cannot bypass hooks")
    with ExitStack() as stack:
        stack.enter_context(file_lock("pr-train"))
        for number in sorted(numbers):
            stack.enter_context(file_lock(f"pr-{number}"))
        git(repo, "fetch", "github", "main")
        base = git(repo, "rev-parse", "github/main")
        primary_at(repo, base)
        members = members_at(repo, numbers, base, adjudicated)
        runtime = cache_root() / "trains"
        runtime.mkdir(parents=True, exist_ok=True)
        directory = Path(tempfile.mkdtemp(prefix="train-", dir=runtime))
        worktree = directory / "worktree"
        branch = "train-" + datetime.now(timezone.utc).strftime("%Y%m%dT%H%M%S%fZ")
        git(repo, "worktree", "add", "-b", branch, str(worktree), base)
        print(f"train worktree: {worktree}", flush=True)
        data, outcome = None, "refused"
        try:
            members, dropped = integrate(repo, worktree, members)
            if len(members) < 2:
                raise GateFailure(f"fewer than two members remain; conflicts: {dropped}")
            data = {"repo": str(repo), "worktree": str(worktree), "base": base,
                    "head": git(worktree, "rev-parse", "HEAD"), "members": members,
                    "dropped": dropped}
            path = directory / "manifest.json"
            atomic_write(path, json.dumps(data, indent=2) + "\n")
            run_ci(repo, data)
            verify_manifest(path, base, data["head"], "refs/heads/main")
            outcome = "unknown"
            try:
                command(repo, str(repo / "local/bin/checked-push.sh"), "--repo-root", str(repo),
                        "--train-manifest", str(path), "github", f"refs/heads/{branch}:refs/heads/main")
            except (LayerError, OSError):
                outcome = publication_outcome(repo, data["head"])
                raise
            outcome = "published"
            print(f"published train {data['head']}", flush=True)
            # Preserve existing developer branches/worktrees, including conflicting members.
            git(repo, "fetch", "github", "main")
            if not pr_merge.fast_forward_base(repo, "main"):
                raise LayerError("train published; local main requires operator reconciliation")
            pr_merge.update_origin_alias(repo, "main")
            errors = []
            for member in members:
                try:
                    gh_common.ensure_pr_comment(
                        member["number"], f"mipstarre-train head={data['head']}",
                        f"Merged in reviewed train `{data['head']}`; member head `{member['head']}`.")
                except LayerError as exc:
                    errors.append(str(exc))
            git(repo, "worktree", "remove", "--force", str(worktree))
            if os.environ.get("MIPSTARRE_LAKE_ROOT"):
                command(repo, str(repo / "local/bin/lake-root.sh"), "cleanup", str(repo), branch)
            git(repo, "branch", "-d", branch)
            if errors:
                raise LayerError("train published; comment publication incomplete: " + "; ".join(errors))
            return 0
        except (LayerError, OSError, ValueError) as exc:
            print(f"train publication {outcome}; evidence: {directory}", file=sys.stderr)
            raise LayerError(str(exc)) from exc
        finally:
            if data is not None:
                record(repo, data, outcome)


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("prs", type=int, nargs="*")
    parser.add_argument("--repo-root", type=Path, default=Path(__file__).resolve().parents[2])
    parser.add_argument("--adjudicated", type=int, action="append", default=[])
    parser.add_argument("--verify-manifest", type=Path)
    parser.add_argument("--expected-main", default="")
    parser.add_argument("--expected-head", default="")
    parser.add_argument("--expected-ref", default="")
    args = parser.parse_args()
    try:
        if args.verify_manifest:
            verify_manifest(args.verify_manifest, args.expected_main, args.expected_head, args.expected_ref)
            return 0
        return run_train(args.repo_root.resolve(), args.prs, set(args.adjudicated))
    except (LayerError, OSError, ValueError, KeyError) as exc:
        print(f"pr_train.py: ERROR: {exc}", file=sys.stderr)
        return 1


if __name__ == "__main__":
    raise SystemExit(main())
